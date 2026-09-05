#!/usr/bin/env python3
"""Shared plumbing for the uniform certificate scripts ``char2/verify_n<k>.py``.

Every ``python3 -m char2.verify_n<k>`` run (k = 5, 7, ..., 25) prints

  * the gate list of the circuit it certifies (and which display it is),
  * the explicit decoder,
  * the symbolic certificate (decode(encode(a)) = a in GF(2)[keys] and/or the
    unit-pivot table), reusing the existing symbolic scripts where they exist,
  * a numeric GF(2^64) round trip with a stated seed and count,

and ends with a single ``PASS n=<k>`` or ``FAIL n=<k>: ...`` line (exit 0/1).

This module holds what those scripts share: the GF(2^64) field, a ring adapter
so that the same decoder code runs symbolically (sympy, GF(2)[keys]) and
numerically, a gate-list circuit evaluator, the generic top-down unit-pivot
decoder (``q_i = c_row(i) + K_i(q_0..q_{i-1})`` with ``K_i`` the same row of the
circuit at ``A(q_0..q_{i-1}, 0, ...)``), and the report/PASS-FAIL plumbing.
"""

from __future__ import annotations

import contextlib
import io
import pathlib
import random
import re
import runpy
import sys
import time
import traceback
from dataclasses import dataclass
from typing import Callable, Optional, Sequence

from .gf2k import GF2k

REPO = pathlib.Path(__file__).resolve().parents[1]

# GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1): the modulus used by
# tools/bench/chainhash/verify5.py, verify7.py and the ChainHash implementation.
MOD64 = (1 << 64) | 0b11011
MASK64 = (1 << 64) - 1


class GF2_64(GF2k):
    """``GF2k(64, MOD64)`` with a 4-bit-windowed carry-less multiplication.

    ``GF2k.mul`` (a 64-step shift-and-add loop) is kept as the reference; see
    ``field64()`` which checks the fast product against it before use.
    """

    def mul(self, a: int, b: int) -> int:  # noqa: D401 - same contract as GF2k.mul
        a &= MASK64
        b &= MASK64
        t = [0] * 16
        for k in range(1, 16):
            t[k] = t[k & (k - 1)] ^ (a << ((k & -k).bit_length() - 1))
        r = 0
        for i in range(0, 64, 4):
            r ^= t[(b >> i) & 15] << i
        hi = r >> 64
        lo = r & MASK64
        red = (hi << 4) ^ (hi << 3) ^ (hi << 1) ^ hi
        lo ^= red & MASK64
        hi = red >> 64
        lo ^= (hi << 4) ^ (hi << 3) ^ (hi << 1) ^ hi
        return lo

    def sq(self, a: int) -> int:
        return self.mul(a, a)

    def reference_mul(self, a: int, b: int) -> int:
        return GF2k.mul(self, a, b)


def field64(*, checks: int = 200, seed: int = 64) -> GF2_64:
    """The GF(2^64) instance, after checking the windowed product against the reference loop."""
    F = GF2_64(64, MOD64)
    rng = random.Random(seed)
    for _ in range(checks):
        a = rng.getrandbits(64)
        b = rng.getrandbits(64)
        if F.mul(a, b) != F.reference_mul(a, b):
            raise AssertionError("windowed GF(2^64) product disagrees with the reference loop")
    for _ in range(checks):
        a = rng.getrandbits(64)
        if F.sq(F.root_pow2(a, 1)) != a or F.root_pow2(F.sq(a), 1) != a:
            raise AssertionError("GF(2^64) square root is not inverse to squaring")
    return F


# ---------------------------------------------------------------------------
# Ring adapters: the same decoder code runs over GF(2^64) and over GF(2)[keys]
# ---------------------------------------------------------------------------
class FieldRing:
    """Arithmetic of a ``GF2k`` instance in the adapter interface."""

    symbolic = False

    def __init__(self, F: GF2k):
        self.F = F
        self.zero = 0
        self.one = 1

    def add(self, a: int, b: int) -> int:
        return a ^ b

    def mul(self, a: int, b: int) -> int:
        return self.F.mul(a, b)

    def sq(self, a: int) -> int:
        return self.F.mul(a, a)

    def root(self, a: int, depth: int, hint=None) -> int:
        """The unique 2^depth-th root (Frobenius pivot) in the finite field."""
        return self.F.root_pow2(a, depth)

    def is_zero(self, a: int) -> bool:
        return a == 0

    def pow(self, a: int, e: int) -> int:
        return self.F.pow(a, e)

    def random(self, rng: random.Random) -> int:
        return rng.getrandbits(self.F.k)


class SympyRing:
    """A sympy ``ring(..., GF(2))`` in the adapter interface.

    ``root(a, depth, hint)`` is the symbolic form of a Frobenius pivot: it
    checks the literal identity ``a == hint^(2^depth)`` in GF(2)[keys] and
    returns ``hint`` (the decoder is then valid over every perfect field).
    """

    symbolic = True

    def __init__(self, R):
        self.R = R
        self.zero = R.zero
        self.one = R.one
        self.root_checks: list[bool] = []

    def add(self, a, b):
        return a + b

    def mul(self, a, b):
        return a * b

    def sq(self, a):
        return a * a

    def root(self, a, depth: int, hint=None):
        if hint is None:
            raise ValueError("symbolic Frobenius pivot needs the claimed root")
        ok = a == hint ** (1 << depth)
        self.root_checks.append(ok)
        if not ok:
            raise AssertionError(f"Frobenius pivot: radicand {a} is not ({hint})^(2^{depth})")
        return hint

    def is_zero(self, a) -> bool:
        return a == self.R.zero


def gf2_ring(names: Sequence[str]):
    """``(SympyRing, generators)`` for GF(2)[names]."""
    from sympy.polys.domains import GF
    from sympy.polys.rings import ring

    R, *gens = ring(",".join(names), GF(2))
    return SympyRing(R), list(gens)


def uses_only(poly, allowed, all_gens) -> bool:
    """True when the sympy ring element involves no generator outside ``allowed``."""
    allowed_ids = {id(g) for g in allowed}
    for g in all_gens:
        if id(g) in allowed_ids:
            continue
        if poly.degree(g) > 0:
            return False
    return True


# ---------------------------------------------------------------------------
# Polynomials in x over a ring adapter: ascending coefficient lists
# ---------------------------------------------------------------------------
def padd(R, p, q):
    size = max(len(p), len(q))
    out = []
    for i in range(size):
        a = p[i] if i < len(p) else R.zero
        b = q[i] if i < len(q) else R.zero
        out.append(R.add(a, b))
    return out


def pmul(R, p, q):
    out = [R.zero] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if R.is_zero(a):
            continue
        for j, b in enumerate(q):
            if R.is_zero(b):
                continue
            out[i + j] = R.add(out[i + j], R.mul(a, b))
    return out


def pcoeff(R, p, i):
    return p[i] if i < len(p) else R.zero


def pdegree(R, p) -> int:
    for i in range(len(p) - 1, -1, -1):
        if not R.is_zero(p[i]):
            return i
    return -1


def peq(R, p, q) -> bool:
    """Equality of polynomials in x regardless of trailing zero coefficients."""
    size = max(len(p), len(q))
    return all(pcoeff(R, p, i) == pcoeff(R, q, i) for i in range(size))


# ---------------------------------------------------------------------------
# Gate lists (the same shape as CIRCUITS of website/js/char2.js)
# ---------------------------------------------------------------------------
Factor = tuple[tuple[str, ...], Optional[int]]  # (wires XORed together, key index or None)


@dataclass(frozen=True)
class Gate:
    wire: str
    left: Factor
    right: Factor


@dataclass(frozen=True)
class Circuit:
    n: int
    gates: tuple[Gate, ...]
    out: Factor
    keyname: str = "a"

    @property
    def keys(self) -> int:
        return self.n


def G(wire: str, lt: Sequence[str], lk: Optional[int], rt: Sequence[str], rk: Optional[int]) -> Gate:
    return Gate(wire, (tuple(lt), lk), (tuple(rt), rk))


def _factor_poly(R, wires: dict, keys, f: Factor):
    taps, k = f
    p = [R.zero]
    for tap in taps:
        p = padd(R, p, wires[tap])
    if k is not None:
        p = padd(R, p, [keys[k]])
    return p


def eval_wires(spec: Circuit, keys, R) -> dict:
    wires = {"x": [R.zero, R.one]}
    for gate in spec.gates:
        wires[gate.wire] = pmul(R, _factor_poly(R, wires, keys, gate.left), _factor_poly(R, wires, keys, gate.right))
    return wires


def eval_circuit(spec: Circuit, keys, R):
    """Coefficients c_0..c_n of the circuit output (a list of length n+1 when monic of degree n)."""
    if len(keys) != spec.keys:
        raise ValueError(f"expected {spec.keys} keys, got {len(keys)}")
    wires = eval_wires(spec, keys, R)
    return _factor_poly(R, wires, keys, spec.out)


def _factor_text(spec: Circuit, f: Factor, bare_ok: bool = True) -> str:
    taps, k = f
    terms = list(taps) + ([f"{spec.keyname}{k}"] if k is not None else [])
    if len(terms) == 1 and bare_ok:
        return terms[0]
    return "(" + " + ".join(terms) + ")"


def gate_lines(spec: Circuit, output_name: str = "P") -> list[str]:
    lines = []
    for gate in spec.gates:
        lines.append(f"{gate.wire} = {_factor_text(spec, gate.left)} * {_factor_text(spec, gate.right)}")
    taps, k = spec.out
    terms = list(taps) + ([f"{spec.keyname}{k}"] if k is not None else [])
    lines.append(f"{output_name} = " + " + ".join(terms))
    return lines


def circuit_stats(spec: Circuit) -> tuple[int, int, int]:
    """(products, polynomial-level XORs, multiplication height) in the appendix convention."""
    depth = {"x": 0}
    xors = 0
    for gate in spec.gates:
        dmax = 0
        for taps, k in (gate.left, gate.right):
            xors += len(taps) - 1 + (1 if k is not None else 0)
            for tap in taps:
                dmax = max(dmax, depth[tap])
        depth[gate.wire] = dmax + 1
    taps, k = spec.out
    xors += len(taps) - 1 + (1 if k is not None else 0)
    height = max(depth[tap] for tap in taps)
    return len(spec.gates), xors, height


def print_circuit(spec: Circuit, title: str, expect: Optional[tuple[int, int]] = None, output_name: str = "P") -> bool:
    """Print the gate list and its counts; return whether the counts match ``expect = (height, xors)``."""
    print(f"Circuit ({title}), {spec.keys} keys, output monic of degree {spec.n}:")
    for line in gate_lines(spec, output_name):
        print("    " + line)
    mults, xors, height = circuit_stats(spec)
    text = f"    products = {mults}, polynomial XORs = {xors}, multiplication height = {height}"
    ok = True
    if expect is not None:
        ok = expect == (height, xors)
        text += f"  (displayed: h = {expect[0]}, {expect[1]} XORs -> {'match' if ok else 'MISMATCH'})"
    print(text)
    return ok


# ---------------------------------------------------------------------------
# Numeric evaluation of the existing scripts' symbolic polynomials
# ---------------------------------------------------------------------------
def eval_mpoly(mp, values, R):
    """Evaluate an ``MPoly`` of verify_n{15,19,21}_unitriangular_symbolic.py
    (a frozenset of exponent tuples over GF(2)) at ``values`` (one per variable)."""
    out = R.zero
    for mono in mp.terms:
        prod = R.one
        for v, e in zip(values, mono):
            if e:
                prod = R.mul(prod, R.pow(v, e))
        out = R.add(out, prod)
    return out


def _f2poly_names(fp) -> list:
    """The variable-name table of the module that defines ``fp``'s class
    (tools/char2_polynomial.py, re-exported by tools/char2_inverse_finder.py)."""
    return sys.modules[type(fp).__module__]._NAMES


def compile_f2poly(fp) -> list[tuple[tuple[str, int], ...]]:
    """An ``F2Poly`` (tools/char2_polynomial.py) as a list of monomials ((name, exponent), ...)."""
    names = _f2poly_names(fp)
    return [tuple((names[v], e) for v, e in mono) for mono in fp.t]


def eval_compiled(monomials, env: dict, R):
    """Evaluate ``compile_f2poly`` output at ``env`` (name -> ring element)."""
    out = R.zero
    cache: dict = {}
    for mono in monomials:
        prod = R.one
        for name, e in mono:
            key = (name, e)
            val = cache.get(key)
            if val is None:
                val = R.pow(env[name], e)
                cache[key] = val
            prod = R.mul(prod, val)
        out = R.add(out, prod)
    return out


def f2poly_text(fp, keyname: str = "a") -> str:
    """Display an ``F2Poly`` whose variables are q<i> and b<j> (b<j> = key a_j)."""
    names = _f2poly_names(fp)

    def mono_text(mono) -> str:
        if not mono:
            return "1"
        parts = []
        for v, e in sorted(mono, key=lambda ve: (names[ve[0]][0] != "q", names[ve[0]])):
            name = names[v]
            if name.startswith("b"):
                name = keyname + name[1:]
            parts.append(name + (f"^{e}" if e > 1 else ""))
        return "*".join(parts)

    if not fp.t:
        return "0"
    return " + ".join(sorted(mono_text(m) for m in fp.t))


# ---------------------------------------------------------------------------
# Generic top-down unit-pivot decoder
# ---------------------------------------------------------------------------
def decode_unit_pivots(
    spec: Circuit,
    keys_from_q: Callable,
    c,
    R,
    rows: Optional[Sequence[int]] = None,
    root_depths: Optional[Sequence[int]] = None,
    hints=None,
):
    """The paper's descending recurrence ``q_i = c_{row_i} + K_i(q_0..q_{i-1})``.

    ``K_i`` is row ``row_i`` of the circuit at the keys ``A(q_0, .., q_{i-1}, 0, .., 0)``
    (``keys_from_q``), so with ``q_i.. = 0`` the residual of that row is exactly
    ``q_i`` (unit pivot) or ``q_i^(2^d)`` (Frobenius pivot, ``root_depths[i] = d``).
    Returns the keys ``A(q)``.
    """
    n = spec.n
    rows = list(rows) if rows is not None else [n - 1 - i for i in range(n)]
    Q = [R.zero] * n
    for i in range(n):
        base = eval_circuit(spec, keys_from_q(Q, R), R)
        resid = R.add(c[rows[i]], pcoeff(R, base, rows[i]))
        depth = root_depths[i] if root_depths else 0
        Q[i] = R.root(resid, depth, None if hints is None else hints[i]) if depth else resid
    return keys_from_q(Q, R)


# ---------------------------------------------------------------------------
# Numeric round trip
# ---------------------------------------------------------------------------
def roundtrip(spec: Circuit, decode: Callable, R: FieldRing, *, seed: int, count: int, report: "Report") -> None:
    """keys -> coefficients -> keys on ``count`` random key vectors, and
    coefficients -> keys -> coefficients on ``count`` random monic coefficient vectors."""
    n = spec.n
    rng = random.Random(seed)
    bad_keys = 0
    for _ in range(count):
        keys = [R.random(rng) for _ in range(spec.keys)]
        c = eval_circuit(spec, keys, R)
        if pdegree(R, c) != n or c[n] != R.one or decode(c[:n]) != keys:
            bad_keys += 1
    bad_coeffs = 0
    for _ in range(count):
        c = [R.random(rng) for _ in range(n)]
        keys = decode(c)
        back = eval_circuit(spec, keys, R)
        if pdegree(R, back) != n or back[n] != R.one or back[:n] != c:
            bad_coeffs += 1
    print(
        f"Numeric round trip over GF(2^64) (modulus x^64+x^4+x^3+x+1), seed = {seed}: "
        f"{count} random key vectors (keys -> coefficients -> keys), {bad_keys} failures; "
        f"{count} random monic coefficient vectors (coefficients -> keys -> coefficients), {bad_coeffs} failures"
    )
    report.check(f"GF(2^64) round trip, {count} + {count} vectors, seed {seed}", bad_keys == 0 and bad_coeffs == 0)


# ---------------------------------------------------------------------------
# Running the existing scripts
# ---------------------------------------------------------------------------
def run_script_by_path(path: pathlib.Path):
    """Execute a stand-alone script file, capturing its stdout; returns (namespace, text)."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        ns = runpy.run_path(str(path), run_name="__verify_wrapped__")
    return ns, buf.getvalue()


def audit_chainhash_output(text: str) -> list[str]:
    """Problems in the printed report of tools/bench/chainhash/verify5.py or verify7.py.

    Those scripts print one line per check and never raise, so the wrapper
    reads their verdicts: every ``label: True`` line, the two ``ALL OK`` tables,
    the unit-pivot lines, the GF(2^64) round trip and the exhaustive small-field
    counts must all be clean.
    """
    problems = []
    for line in text.splitlines():
        if "MISMATCH" in line or "NOT unit" in line:
            problems.append(line.strip())
        if re.search(r":\s*False\b", line):
            problems.append(line.strip())
        if line.strip().endswith("FAIL"):
            problems.append(line.strip())
        m = re.search(r"GF\(2\^(\d+)\) exhaustive: (\d+) distinct images of (\d+), failures = (\d+)", line)
        if m and (m.group(2) != m.group(3) or m.group(4) != "0"):
            problems.append(line.strip())
        m = re.search(r"GF\(2\^64\) random round trips.*failures = (\d+)", line)
        if m and m.group(1) != "0":
            problems.append(line.strip())
    for needed in ("coefficient table: ALL OK", "row table: ALL OK", "GF(2^64) random round trips"):
        if needed not in text:
            problems.append(f"missing line: {needed!r}")
    return problems


def indent(text: str, prefix: str = "    ") -> str:
    return "\n".join(prefix + line for line in text.rstrip("\n").splitlines())


# ---------------------------------------------------------------------------
# Report plumbing
# ---------------------------------------------------------------------------
class Report:
    def __init__(self, n: int):
        self.n = n
        self.failures: list[str] = []
        self.start = time.time()

    def section(self, title: str) -> None:
        print(f"\n== {title}")

    def check(self, label: str, ok: bool, detail: str = "") -> bool:
        print(f"  [{'ok' if ok else 'FAIL'}] {label}" + (f": {detail}" if detail and not ok else ""))
        if not ok:
            self.failures.append(label + (f" ({detail})" if detail else ""))
        return ok

    def run(self, label: str, fn: Callable[[], object]) -> bool:
        """Run ``fn``; an exception (AssertionError included) is a failed check."""
        try:
            fn()
        except Exception as exc:  # noqa: BLE001 - every exception is a failed certificate
            traceback.print_exc()
            return self.check(label, False, f"{type(exc).__name__}: {exc}")
        return self.check(label, True)

    def finish(self) -> None:
        elapsed = time.time() - self.start
        print(f"\nElapsed: {elapsed:.1f} s")
        if self.failures:
            print(f"FAIL n={self.n}: " + "; ".join(self.failures))
            sys.exit(1)
        print(f"PASS n={self.n}")
        sys.exit(0)


def banner(n: int, what: str) -> None:
    print(f"char2/verify_n{n}.py: certificate for the degree-{n} characteristic-2 circuit")
    print(what)
