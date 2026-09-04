#!/usr/bin/env python3
"""
Generate C++ implementations of the "x2s" polynomial chains over the Goldilocks
prime field F_p where p = 2^64 - 2^32 + 1.

Input:  tools/x2s.res   (hand-found chains; see fast_poly.py / pol_kwise.py)
Output: tools/bench/framework/x2s_goldilocks_chains.h

The generated code contains, for each supported degree:
  - a fast evaluator (unrolled multiplications, like the hashing benchmarks)
  - a one-time coefficient extractor that runs the same chain over F[x]

This makes it possible to do apples-to-apples benchmarks:
  - evaluate the same polynomial via Horner (on extracted coefficients)
  - evaluate via the fast chain evaluator
"""

from __future__ import annotations

from dataclasses import dataclass
import re
from pathlib import Path
from typing import Iterable, List, Optional, Tuple


RE_BLOCK_DEGREE = re.compile(r"^(\d+)\s+good!$")


@dataclass(frozen=True)
class Gate:
    out: str
    left_vars: List[str]
    left_const: Optional[int]
    right_vars: List[str]
    right_const: Optional[int]


@dataclass(frozen=True)
class ChainBlock:
    degree: int
    program_text: str
    gates: List[Gate]
    final_vars: List[str]
    final_const: Optional[int]


RE_MUL = re.compile(r"^([A-Za-z]\w*)\s*=\s*\((.*?)\)\s*\*\s*\((.*?)\)\s*;\s*$")
RE_FINAL = re.compile(r"^P\s*=\s*(.*?)\s*;\s*$")


def _parse_affine(expr: str) -> Tuple[List[str], Optional[int]]:
    """
    Parse an affine sum like "a12 + x + y" into (vars, const_idx).
    Assumes at most one a_k constant in each affine form.
    """
    vars: List[str] = []
    const_idx: Optional[int] = None
    for tok in (t.strip() for t in expr.split("+")):
        if tok == "" or tok == "0":
            continue
        if tok == "x" or tok[0].isalpha():
            if tok.startswith("a"):
                m = re.match(r"^a(\d+)$", tok)
                if not m:
                    raise ValueError(f"Bad coefficient token: {tok!r}")
                idx = int(m.group(1))
                if const_idx is not None:
                    raise ValueError(f"Multiple a_k in one affine form: {expr!r}")
                const_idx = idx
            else:
                vars.append(tok)
        else:
            raise ValueError(f"Unexpected token in affine form: {tok!r} (from {expr!r})")
    return vars, const_idx


def _parse_program(program_text: str, degree: int) -> Tuple[List[Gate], List[str], Optional[int]]:
    gates: List[Gate] = []
    final_vars: List[str] = []
    final_const: Optional[int] = None

    defined: set[str] = {"x"}

    for raw in program_text.splitlines():
        line = raw.strip()
        if not line:
            continue

        m_mul = RE_MUL.match(line)
        if m_mul:
            out, left, right = m_mul.group(1), m_mul.group(2), m_mul.group(3)
            if out == "P":
                raise ValueError("Use 'P = ...;' as final line, not a multiplication.")
            if out in defined:
                raise ValueError(f"Variable redefined: {out}")

            left_vars, left_const = _parse_affine(left)
            right_vars, right_const = _parse_affine(right)

            for v in left_vars + right_vars:
                if v not in defined:
                    raise ValueError(f"Use-before-define: {v} in line {line!r}")
            if left_const is not None and not (0 <= left_const < degree):
                raise ValueError(f"Coefficient index out of range in {line!r}")
            if right_const is not None and not (0 <= right_const < degree):
                raise ValueError(f"Coefficient index out of range in {line!r}")

            gates.append(
                Gate(
                    out=out,
                    left_vars=left_vars,
                    left_const=left_const,
                    right_vars=right_vars,
                    right_const=right_const,
                )
            )
            defined.add(out)
            continue

        m_final = RE_FINAL.match(line)
        if m_final:
            expr = m_final.group(1)
            vars, const_idx = _parse_affine(expr)
            for v in vars:
                if v not in defined:
                    raise ValueError(f"Use-before-define: {v} in final line {line!r}")
            if const_idx is not None and not (0 <= const_idx < degree):
                raise ValueError(f"Coefficient index out of range in final line {line!r}")
            final_vars = vars
            final_const = const_idx
            continue

        # Ignore non-program log lines.

    if not final_vars and final_const is None:
        raise ValueError(f"Missing final line 'P = ...;' in:\n{program_text}")
    return gates, final_vars, final_const


def load_blocks(path: Path) -> List[ChainBlock]:
    out: List[ChainBlock] = []
    current_program_lines: List[str] = []

    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line:
            continue

        m_deg = RE_BLOCK_DEGREE.match(line)
        if m_deg:
            degree = int(m_deg.group(1))
            if not current_program_lines:
                raise ValueError(f"Degree line {line!r} appears before any program in {path}")
            program_text = "\n".join(current_program_lines) + "\n"
            gates, final_vars, final_const = _parse_program(program_text, degree)
            out.append(
                ChainBlock(
                    degree=degree,
                    program_text=program_text,
                    gates=gates,
                    final_vars=final_vars,
                    final_const=final_const,
                )
            )
            current_program_lines = []
            continue

        if RE_MUL.match(line) or RE_FINAL.match(line):
            current_program_lines.append(line)
            continue

        # Ignore log/diagnostic lines.

    if current_program_lines:
        raise ValueError(f"Trailing program without '<n> good!' line in {path}")
    return out


def _cpp_sum_terms(terms: List[str]) -> str:
    if not terms:
        return "0"
    return " + ".join(terms)


def _cpp_sum_terms_u128(terms: List[str]) -> str:
    if not terms:
        return "(__uint128_t)0"
    first, *rest = terms
    expr = f"(__uint128_t)({first})"
    for t in rest:
        expr += f" + ({t})"
    return expr


def _emit_header(blocks: List[ChainBlock], degrees: List[int]) -> str:
    lines: List[str] = []
    lines.append("// AUTO-GENERATED by tools/gen_x2s_goldilocks_chains.py; do not edit by hand.")
    lines.append("// Source chains: tools/x2s.res")
    lines.append("// Degrees: " + ", ".join(str(d) for d in degrees))
    lines.append("")
    lines.append("#pragma once")
    lines.append("")
    lines.append("#include <array>")
    lines.append("#include <cstddef>")
    lines.append("#include <cstdint>")
    lines.append("")
    lines.append('#include "randomgen.h"')
    lines.append("")
    lines.append("constexpr uint64_t GOLDILOCKS_P = 0xffffffff00000001ULL; // 2^64 - 2^32 + 1")
    lines.append("")
    lines.append("static inline uint64_t goldilocks_reduce_u64(uint64_t v) {")
    lines.append("  return (v >= GOLDILOCKS_P) ? (v - GOLDILOCKS_P) : v;")
    lines.append("}")
    lines.append("")
    lines.append("static inline uint64_t goldilocks_reduce_128(__uint128_t v) {")
    lines.append("  // Reduce modulo p = 2^64 - 2^32 + 1 using the identity 2^64 ≡ 2^32 - 1 (mod p).")
    lines.append("  uint64_t lo = (uint64_t)v;")
    lines.append("  uint64_t hi = (uint64_t)(v >> 64);")
    lines.append("")
    lines.append("  // First fold: lo + hi*(2^32 - 1).")
    lines.append("  __uint128_t t = (__uint128_t)lo + ((__uint128_t)hi << 32) - hi;")
    lines.append("")
    lines.append("  // Second fold: t < 2^96, so the high limb is at most 32 bits.")
    lines.append("  lo = (uint64_t)t;")
    lines.append("  hi = (uint64_t)(t >> 64);")
    lines.append("  __uint128_t u = (__uint128_t)lo + ((__uint128_t)hi << 32) - hi;")
    lines.append("")
    lines.append("  // Final fold (u < 2^65).")
    lines.append("  lo = (uint64_t)u;")
    lines.append("  hi = (uint64_t)(u >> 64);")
    lines.append("  __uint128_t w = (__uint128_t)lo + ((__uint128_t)hi << 32) - hi;")
    lines.append("  if (w >= GOLDILOCKS_P) w -= GOLDILOCKS_P;")
    lines.append("  return (uint64_t)w;")
    lines.append("}")
    lines.append("")
    lines.append("static inline uint64_t goldilocks_add(uint64_t a, uint64_t b) {")
    lines.append("  return goldilocks_reduce_128((__uint128_t)a + b);")
    lines.append("}")
    lines.append("")
    lines.append("static inline uint64_t goldilocks_sub(uint64_t a, uint64_t b) {")
    lines.append("  return (a >= b) ? (a - b) : (GOLDILOCKS_P - (b - a));")
    lines.append("}")
    lines.append("")
    lines.append("static inline uint64_t goldilocks_mul(uint64_t a, uint64_t b) {")
    lines.append("  return goldilocks_reduce_128((__uint128_t)a * b);")
    lines.append("}")
    lines.append("")
    lines.append("template <size_t DEG>")
    lines.append("struct GoldilocksPoly {")
    lines.append("  std::array<uint64_t, DEG + 1> c{};")
    lines.append("")
    lines.append("  static GoldilocksPoly zero() { return {}; }")
    lines.append("")
    lines.append("  static GoldilocksPoly one() {")
    lines.append("    GoldilocksPoly p;")
    lines.append("    p.c[0] = 1;")
    lines.append("    return p;")
    lines.append("  }")
    lines.append("")
    lines.append("  static GoldilocksPoly x() {")
    lines.append("    GoldilocksPoly p;")
    lines.append("    if constexpr (DEG >= 1) p.c[1] = 1;")
    lines.append("    return p;")
    lines.append("  }")
    lines.append("")
    lines.append("  static GoldilocksPoly constant(uint64_t v) {")
    lines.append("    GoldilocksPoly p;")
    lines.append("    p.c[0] = goldilocks_reduce_u64(v);")
    lines.append("    return p;")
    lines.append("  }")
    lines.append("")
    lines.append("  GoldilocksPoly operator+(const GoldilocksPoly& other) const {")
    lines.append("    GoldilocksPoly out;")
    lines.append("    for (size_t i = 0; i <= DEG; i++) out.c[i] = goldilocks_add(c[i], other.c[i]);")
    lines.append("    return out;")
    lines.append("  }")
    lines.append("")
    lines.append("  GoldilocksPoly operator-(const GoldilocksPoly& other) const {")
    lines.append("    GoldilocksPoly out;")
    lines.append("    for (size_t i = 0; i <= DEG; i++) out.c[i] = goldilocks_sub(c[i], other.c[i]);")
    lines.append("    return out;")
    lines.append("  }")
    lines.append("")
    lines.append("  GoldilocksPoly operator*(const GoldilocksPoly& other) const {")
    lines.append("    GoldilocksPoly out;")
    lines.append("    for (size_t i = 0; i <= DEG; i++) {")
    lines.append("      uint64_t acc = 0;")
    lines.append("      for (size_t j = 0; j <= i; j++) {")
    lines.append("        acc = goldilocks_add(acc, goldilocks_mul(c[j], other.c[i - j]));")
    lines.append("      }")
    lines.append("      out.c[i] = acc;")
    lines.append("    }")
    lines.append("    return out;")
    lines.append("  }")
    lines.append("};")
    lines.append("")

    for block in blocks:
        if block.degree not in degrees:
            continue
        d = block.degree
        lines.append(f"struct X2S_Goldilocks_{d} {{")
        lines.append(f"  static constexpr size_t DEGREE = {d};")
        lines.append(f"  std::array<uint64_t, {d}> ms;")
        lines.append("")
        lines.append("  void init() {")
        lines.append(f"    for (size_t i = 0; i < {d}; i++) {{")
        lines.append("      uint64_t r = getRandomUInt64();")
        lines.append("      if (r >= GOLDILOCKS_P) r -= GOLDILOCKS_P;")
        lines.append("      ms[i] = r;")
        lines.append("    }")
        lines.append("  }")
        lines.append("")
        lines.append("  uint64_t eval(uint64_t input) const {")
        lines.append("    uint64_t x = goldilocks_reduce_u64(input);")

        for gate in block.gates:
            left_terms: List[str] = []
            if gate.left_const is not None:
                left_terms.append(f"ms[{gate.left_const}]")
            left_terms += gate.left_vars
            right_terms: List[str] = []
            if gate.right_const is not None:
                right_terms.append(f"ms[{gate.right_const}]")
            right_terms += gate.right_vars

            sl = _cpp_sum_terms_u128(left_terms)
            sr = _cpp_sum_terms_u128(right_terms)
            lines.append(
                f"    uint64_t {gate.out} = goldilocks_mul(goldilocks_reduce_128({sl}), goldilocks_reduce_128({sr}));"
            )

        final_terms: List[str] = []
        if block.final_const is not None:
            final_terms.append(f"ms[{block.final_const}]")
        final_terms += block.final_vars
        sp = _cpp_sum_terms_u128(final_terms)
        lines.append(f"    uint64_t P = goldilocks_reduce_128({sp});")
        lines.append("    return P;")
        lines.append("  }")
        lines.append("")
        lines.append(f"  std::array<uint64_t, {d + 1}> coeffs() const {{")
        lines.append(f"    using Poly = GoldilocksPoly<{d}>;")
        lines.append("    Poly one = Poly::one();")
        lines.append("    Poly x = Poly::x();")

        for gate in block.gates:
            # Build polynomial versions of the affine terms.
            def poly_affine(vars: List[str], const_idx: Optional[int]) -> str:
                parts: List[str] = []
                for v in vars:
                    if v == "x":
                        parts.append("x")
                    else:
                        parts.append(v)
                if const_idx is not None:
                    parts.append(f"Poly::constant(ms[{const_idx}])")
                if not parts:
                    return "Poly::zero()"
                return "(" + " + ".join(parts) + ")"

            left_expr = poly_affine(gate.left_vars, gate.left_const)
            right_expr = poly_affine(gate.right_vars, gate.right_const)
            lines.append(f"    Poly {gate.out} = {left_expr} * {right_expr};")

        # Final polynomial.
        final_poly_parts: List[str] = []
        if block.final_const is not None:
            final_poly_parts.append(f"Poly::constant(ms[{block.final_const}])")
        for v in block.final_vars:
            if v == "x":
                final_poly_parts.append("x")
            else:
                final_poly_parts.append(v)
        if not final_poly_parts:
            final_poly_parts = ["Poly::zero()"]
        lines.append(f"    Poly P = ({' + '.join(final_poly_parts)});")
        lines.append("    return P.c;")
        lines.append("  }")
        lines.append("};")
        lines.append("")

    return "\n".join(lines) + "\n"


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    blocks = load_blocks(root / "tools" / "x2s.res")

    degrees = [13, 15, 17, 19, 21]
    by_deg = {b.degree: b for b in blocks}
    missing = [d for d in degrees if d not in by_deg]
    if missing:
        raise SystemExit(f"Missing blocks for degrees: {missing}")
    selected = [by_deg[d] for d in degrees]

    out_text = _emit_header(selected, degrees)
    out_path = root / "tools" / "bench" / "framework" / "x2s_goldilocks_chains.h"
    out_path.write_text(out_text, encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
