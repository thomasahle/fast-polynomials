#!/usr/bin/env python3
"""
Generate C++ implementations of the "x2s" Mersenne-field polynomial chains.

Input:  tools/x2s.res   (hand-found chains; see fast_poly.py / pol_kwise.py)
Output: tools/bench/framework/x2s_mersenne_chains.h

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


def _split_blocks(lines: Iterable[str]) -> List[List[str]]:
    blocks: List[List[str]] = []
    cur: List[str] = []
    for raw in lines:
        line = raw.strip()
        if not line:
            if cur:
                blocks.append(cur)
                cur = []
            continue
        cur.append(line)
    if cur:
        blocks.append(cur)
    return blocks


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
        if tok == "":
            continue
        if tok == "0":
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

        # Ignore non-program log lines (e.g., "jac test").

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


def _emit_eval_struct(block: ChainBlock) -> str:
    lines: List[str] = []
    lines.append(f"struct X2S_Mersenne_{block.degree} {{")
    lines.append(f"  static constexpr size_t DEGREE = {block.degree};")
    lines.append(f"  std::array<__uint128_t, {block.degree}> ms;")
    lines.append("")
    lines.append("  void init() {")
    lines.append(f"    for (size_t i = 0; i < {block.degree}; i++) ms[i] = getRandomUInt128() >> 39;")
    lines.append("  }")
    lines.append("")
    lines.append("  __uint128_t eval(uint64_t input) const {")
    lines.append("    __uint128_t x = input;")

    # Unrolled gate evaluation.
    for gate in block.gates:
        left_terms = []
        if gate.left_const is not None:
            left_terms.append(f"ms[{gate.left_const}]")
        left_terms += gate.left_vars
        right_terms = []
        if gate.right_const is not None:
            right_terms.append(f"ms[{gate.right_const}]")
        right_terms += gate.right_vars

        sl = _cpp_sum_terms(left_terms)
        sr = _cpp_sum_terms(right_terms)

        # Micro-opt: if one side is exactly x, use fast_large_mult_mod_2(affine, x).
        if sl == "x" and sr != "x":
            sl, sr = sr, sl
        func = "fast_large_mult_mod_2" if sr == "x" else "extra_large_mult_mod"
        if sr == "x":
            lines.append(
                f"    __uint128_t {gate.out} = mersenne_reduce({func}(mersenne_reduce({sl}), input));"
            )
        else:
            lines.append(
                f"    __uint128_t {gate.out} = mersenne_reduce({func}(mersenne_reduce({sl}), mersenne_reduce({sr})));"
            )

    # Final affine form (sum of selected wires + constant slot).
    final_terms: List[str] = []
    if block.final_const is not None:
        final_terms.append(f"ms[{block.final_const}]")
    final_terms += block.final_vars
    final_expr = _cpp_sum_terms(final_terms)
    lines.append(f"    __uint128_t P = {final_expr};")
    lines.append("    return mersenne_reduce(P);")
    lines.append("  }")
    lines.append("")
    lines.append("  __uint128_t eval_full(__uint128_t x) const {")
    lines.append("    x = mersenne_reduce(x);")

    for gate in block.gates:
        left_terms = []
        if gate.left_const is not None:
            left_terms.append(f"ms[{gate.left_const}]")
        left_terms += gate.left_vars
        right_terms = []
        if gate.right_const is not None:
            right_terms.append(f"ms[{gate.right_const}]")
        right_terms += gate.right_vars

        sl = _cpp_sum_terms(left_terms)
        sr = _cpp_sum_terms(right_terms)
        lines.append(
            f"    __uint128_t {gate.out} = mersenne_mul(mersenne_reduce({sl}), mersenne_reduce({sr}));"
        )

    final_terms2: List[str] = []
    if block.final_const is not None:
        final_terms2.append(f"ms[{block.final_const}]")
    final_terms2 += block.final_vars
    final_expr2 = _cpp_sum_terms(final_terms2)
    lines.append(f"    __uint128_t P = {final_expr2};")
    lines.append("    return mersenne_reduce(P);")
    lines.append("  }")
    lines.append("")
    lines.append(f"  std::array<__uint128_t, {block.degree + 1}> coeffs() const {{")
    lines.append(f"    using Poly = MersennePoly<{block.degree}>;")
    lines.append("    Poly one = Poly::one();")
    lines.append("    Poly x = Poly::x();")

    for gate in block.gates:
        left_poly_terms = list(gate.left_vars)
        right_poly_terms = list(gate.right_vars)

        left_sum = " + ".join(left_poly_terms) if left_poly_terms else "Poly::zero()"
        right_sum = " + ".join(right_poly_terms) if right_poly_terms else "Poly::zero()"

        if gate.left_const is not None:
            left_sum = f"({left_sum} + Poly::constant(ms[{gate.left_const}]))"
        if gate.right_const is not None:
            right_sum = f"({right_sum} + Poly::constant(ms[{gate.right_const}]))"

        lines.append(f"    Poly {gate.out} = ({left_sum}) * ({right_sum});")

    # Build final polynomial.
    poly_terms = list(block.final_vars)
    poly_sum = " + ".join(poly_terms) if poly_terms else "Poly::zero()"
    if block.final_const is not None:
        poly_sum = f"({poly_sum} + Poly::constant(ms[{block.final_const}]))"
    lines.append(f"    Poly P = {poly_sum};")
    lines.append("    return P.c;")
    lines.append("  }")
    lines.append("};")
    return "\n".join(lines)


def generate_header(blocks: List[ChainBlock]) -> str:
    degrees = ", ".join(str(b.degree) for b in blocks)
    out: List[str] = []
    out.append("// AUTO-GENERATED by tools/gen_x2s_mersenne_chains.py; do not edit by hand.")
    out.append("// Source chains: tools/x2s.res")
    out.append(f"// Degrees: {degrees}")
    out.append("")
    out.append("#pragma once")
    out.append("")
    out.append("#include <array>")
    out.append("#include <cstddef>")
    out.append("#include <cstdint>")
    out.append("")
    out.append('#if defined(__aarch64__) || defined(__arm64__) || defined(__ARM_NEON)')
    out.append('#include "multiplication_arm.h"')
    out.append("#else")
    out.append('#include "multiplication.h"')
    out.append("#endif")
    out.append("")
    out.append('#include "randomgen.h"')
    out.append("")
    out.append("constexpr __uint128_t MERSENNE_89 = ((__uint128_t)1 << 89) - 1;")
    out.append("")
    out.append("static inline __uint128_t mersenne_reduce(__uint128_t v) {")
    out.append("  // Reduce modulo p = 2^89 - 1 using the Mersenne folding trick:")
    out.append("  //   v mod p == (v_low + v_high) mod p, where v = v_low + 2^89 * v_high.")
    out.append("  // This is correct for any 0 <= v < 2^128.")
    out.append("  v = (v & MERSENNE_89) + (v >> 89);")
    out.append("  v = (v & MERSENNE_89) + (v >> 89);")
    out.append("  if (v >= MERSENNE_89) v -= MERSENNE_89;")
    out.append("  return v;")
    out.append("}")
    out.append("")
    out.append("static inline __uint128_t mersenne_add(__uint128_t a, __uint128_t b) {")
    out.append("  return mersenne_reduce(a + b);")
    out.append("}")
    out.append("")
    out.append("static inline __uint128_t mersenne_sub(__uint128_t a, __uint128_t b) {")
    out.append("  return (a >= b) ? (a - b) : (MERSENNE_89 - (b - a));")
    out.append("}")
    out.append("")
    out.append("static inline __uint128_t mersenne_mul(__uint128_t a, __uint128_t b) {")
    out.append("  return mersenne_reduce(extra_large_mult_mod(a, b));")
    out.append("}")
    out.append("")
    out.append("template <size_t DEG>")
    out.append("struct MersennePoly {")
    out.append("  // Polynomial in F[x] of degree <= DEG, coefficients reduced mod p.")
    out.append("  std::array<__uint128_t, DEG + 1> c{};")
    out.append("")
    out.append("  static MersennePoly zero() { return {}; }")
    out.append("")
    out.append("  static MersennePoly one() {")
    out.append("    MersennePoly p;")
    out.append("    p.c[0] = 1;")
    out.append("    return p;")
    out.append("  }")
    out.append("")
    out.append("  static MersennePoly x() {")
    out.append("    MersennePoly p;")
    out.append("    if constexpr (DEG >= 1) p.c[1] = 1;")
    out.append("    return p;")
    out.append("  }")
    out.append("")
    out.append("  static MersennePoly constant(__uint128_t v) {")
    out.append("    MersennePoly p;")
    out.append("    p.c[0] = mersenne_reduce(v);")
    out.append("    return p;")
    out.append("  }")
    out.append("")
    out.append("  MersennePoly operator+(const MersennePoly& other) const {")
    out.append("    MersennePoly out;")
    out.append("    for (size_t i = 0; i <= DEG; i++) out.c[i] = mersenne_add(c[i], other.c[i]);")
    out.append("    return out;")
    out.append("  }")
    out.append("")
    out.append("  MersennePoly operator-(const MersennePoly& other) const {")
    out.append("    MersennePoly out;")
    out.append("    for (size_t i = 0; i <= DEG; i++) out.c[i] = mersenne_sub(c[i], other.c[i]);")
    out.append("    return out;")
    out.append("  }")
    out.append("")
    out.append("  MersennePoly operator*(const MersennePoly& other) const {")
    out.append("    MersennePoly out;")
    out.append("    for (size_t i = 0; i <= DEG; i++) {")
    out.append("      __uint128_t acc = 0;")
    out.append("      for (size_t j = 0; j <= i; j++) {")
    out.append("        acc = mersenne_add(acc, mersenne_mul(c[j], other.c[i - j]));")
    out.append("      }")
    out.append("      out.c[i] = acc;")
    out.append("    }")
    out.append("    return out;")
    out.append("  }")
    out.append("};")
    out.append("")
    for block in blocks:
        out.append(_emit_eval_struct(block))
        out.append("")
    return "\n".join(out)


def main() -> None:
    repo = Path(__file__).resolve().parents[1]
    blocks = load_blocks(repo / "tools" / "x2s.res")
    header = generate_header(blocks)
    out_path = repo / "tools" / "bench" / "framework" / "x2s_mersenne_chains.h"
    out_path.write_text(header, encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
