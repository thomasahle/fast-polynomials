#!/usr/bin/env python3
"""Certificate for the degree-7 characteristic-2 circuits (4 products).

Two degree-7 circuits are displayed in the paper, and both are certified here.

Part A -- the former ChainHash degree-7 finalizer (``septic7_64`` of both
benchmark framework headers; the circuit cited for the k = 7 row in
sections/experiments.tex and CIRCUITS[7] of website/js/char2.js):
    y = x (x + c0),  z = (x + c1)(y + c2),  t = z (z + c3),  u = (x + c4)(y + t + c5),  P = u + c6.
Implementation: tools/bench/chainhash/verify7.py (kept in place, executed here
by path): sympy over GF(2)[c_0..c_6][X], the coefficient table, the coordinate
change q(c)/c(q), the row table (two Frobenius pivots q_1^2, q_3^2), the
decoder composed with the rows, a GF(2^64) round trip (seed 1, 2000 x 3) and
exhaustive runs over GF(2), GF(4), GF(8).

Part B -- the "4 products, degree 7" circuit displayed at the top of
sections/appendix_polynomials.tex, whose gate t differs:
    y = x (x + a0),  z = (x + a1)(y + a2),  t = (x + y + z + a3)(x + y + z),  u = (x + a4)(y + t + a5),  P = u + a6,
with the explicit inverse of Lemma lem:first-char2-circuit-inverse (two square
roots b = p5^(1/2), c = (...)^(1/2)).  Checked here directly with sympy:
the coefficient table, the two displayed intermediate expansions, and
decode(encode(a)) = a in GF(2)[a_0..a_6] with the roots as Frobenius pivots.

Both decoders take square roots, so both statements are for perfect fields of
characteristic 2 (every finite GF(2^k)).  Each part ends with a GF(2^64) round
trip with a stated seed and count.

Run from the repository root:  python3 -m char2.verify_n7
"""

from __future__ import annotations

from .verify_common import (
    REPO,
    Circuit,
    FieldRing,
    G,
    Report,
    audit_chainhash_output,
    banner,
    eval_circuit,
    eval_wires,
    field64,
    gf2_ring,
    indent,
    padd,
    pmul,
    print_circuit,
    roundtrip,
    run_script_by_path,
)

SCRIPT = REPO / "tools" / "bench" / "chainhash" / "verify7.py"

SPEC_A = Circuit(
    7,
    (
        G("y", ["x"], None, ["x"], 0),
        G("z", ["x"], 1, ["y"], 2),
        G("t", ["z"], None, ["z"], 3),
        G("u", ["x"], 4, ["y", "t"], 5),
    ),
    (("u",), 6),
    keyname="c",
)

SPEC_B = Circuit(
    7,
    (
        G("y", ["x"], None, ["x"], 0),
        G("z", ["x"], 1, ["y"], 2),
        G("t", ["x", "y", "z"], 3, ["x", "y", "z"], None),
        G("u", ["x"], 4, ["y", "t"], 5),
    ),
    (("u",), 6),
)

DECODER_A = """\
Decoder A (tools/bench/chainhash/verify7.py, eq:ph:chain7-*; P = X^7 + sum e_i X^i):
  q(c) = (c4, c0 + c1, c3, c2 + c0 c1, c1, c5, c6);  c(q) = (q1 + q4, q4, q3 + q1 q4 + q4^2, q2, q0, q5, q6)
  rows: e6 = q0,  e5 = q1^2,  e4 = q2 + q0 q1^2,  e3 = q3^2 + q2 q1 + q2 q0 + 1,
        e2 = q4 + q2 q3 + q1 + q0 (q3^2 + q2 q1 + 1),  e1 = q5 + delta^2 + q2 delta + q0 (q2 q3 + q1 + q4),
        e0 = q6 + q0 (delta^2 + q2 delta + q5),  delta = q4 (q3 + q1 q4 + q4^2)
  decoder: q0 = e6,  q1 = e5^(1/2),  q2 = e4 + q0 q1^2,  q3 = (e3 + q2 q1 + q2 q0 + 1)^(1/2),
           q4 = e2 + q2 q3 + q1 + q0 (q3^2 + q2 q1 + 1),  q5 = e1 + delta^2 + q2 delta + q0 (q2 q3 + q1 + q4),
           q6 = e0 + q0 (delta^2 + q2 delta + q5),  then c = c(q).   Two Frobenius pivots (rows X^5, X^3)."""

DECODER_B = """\
Decoder B (Lemma lem:first-char2-circuit-inverse; P = x^7 + sum p_j x^j):
  a4 = p6
  b  = p5^(1/2)                                  [Frobenius pivot; b = 1 + a0 + a1]
  a3 = p4 + a4 p5
  c  = (p3 + a3 b + 1 + a4 a3)^(1/2)             [Frobenius pivot; c = 1 + a0 + a2 + a0 a1]
  a0 = p2 + a3 c + a4 (c^2 + a3 b + 1)
  a1 = b + 1 + a0
  a2 = c + 1 + a0 + a0 a1
  d  = a1 a2
  a5 = p1 + d^2 + a3 d + a4 (a3 c + a0)
  a6 = p0 + a4 (d^2 + a3 d + a5)
  behind it: x + y + z = x^3 + b x^2 + c x + d,  t = (x+y+z)^2 + a3 (x+y+z),
  y + t + a5 = x^6 + b^2 x^4 + a3 x^3 + (c^2 + a3 b + 1) x^2 + (a3 c + a0) x + (d^2 + a3 d + a5)."""


def decode_b(p, R, truth=None):
    """Lemma lem:first-char2-circuit-inverse literally; p = [p0, .., p6] -> [a0, .., a6]."""
    add, mul, one, zero = R.add, R.mul, R.one, R.zero

    def xsum(*xs):
        out = zero
        for x in xs:
            out = add(out, x)
        return out

    hint_b = hint_c = None
    if truth is not None:
        t0, t1, t2 = truth[0], truth[1], truth[2]
        hint_b = one + t0 + t1
        hint_c = one + t0 + t2 + t0 * t1
    a4 = p[6]
    b = R.root(p[5], 1, hint_b)
    a3 = add(p[4], mul(a4, p[5]))
    c = R.root(xsum(p[3], mul(a3, b), one, mul(a4, a3)), 1, hint_c)
    a0 = xsum(p[2], mul(a3, c), mul(a4, xsum(mul(c, c), mul(a3, b), one)))
    a1 = xsum(b, one, a0)
    a2 = xsum(c, one, a0, mul(a0, a1))
    d = mul(a1, a2)
    d2 = mul(d, d)
    a5 = xsum(p[1], d2, mul(a3, d), mul(a4, add(mul(a3, c), a0)))
    a6 = add(p[0], mul(a4, xsum(d2, mul(a3, d), a5)))
    return [a0, a1, a2, a3, a4, a5, a6]


def main() -> None:
    rep = Report(7)
    banner(
        7,
        "Part A: the former ChainHash degree-7 finalizer septic7_64 (sections/experiments.tex, k = 7 row; "
        "= CIRCUITS[7] of website/js/char2.js), implementation tools/bench/chainhash/verify7.py.\n"
        "Part B: the '4 products, degree 7' display of sections/appendix_polynomials.tex "
        "(gate t = (x+y+z+a3)(x+y+z) instead of t = z(z+a3)) with the inverse of Lemma "
        "lem:first-char2-circuit-inverse.\nBoth decoders use two square roots: perfect fields of characteristic 2.",
    )

    rep.section("Part A: circuit and decoder")
    print_circuit(SPEC_A, "septic7_64 = verify7.py = char2.js CIRCUITS[7]")
    print(DECODER_A)
    rep.section("Part A: tools/bench/chainhash/verify7.py (sympy over GF(2)[c][X] and GF(2)[q]; own GF(2^64) round trip; exhaustive GF(2), GF(4), GF(8))")
    holder: dict = {}

    def run_script() -> None:
        holder["ns"], holder["text"] = run_script_by_path(SCRIPT)

    rep.run("verify7.py ran to completion", run_script)
    text = holder.get("text", "")
    print(indent(text))
    problems = audit_chainhash_output(text)
    rep.check("verify7.py: coefficient table, coordinate change, row table, decoder composition, round trips all clean", not problems, "; ".join(problems))
    rep.check("verify7.py: circuit is monic of degree 7", "degree of f: 7  e7 = 1" in text)
    rep.check("verify7.py: the two Frobenius pivots are squares (e5 == q1^2, e3 + ... == q3^2)", "e5 == q1^2: True" in text and "== q3^2: True" in text)
    F = field64()
    R = FieldRing(F)
    if "ns" in holder:
        decode = holder["ns"]["decode"]
        sqrt = lambda v: F.root_pow2(v, 1)  # noqa: E731
        rep.section("Part A: numeric round trip (gate list above evaluated here, inverted by verify7.py's decode)")
        roundtrip(SPEC_A, lambda cc: decode(list(cc), F.mul, sqrt), R, seed=7, count=2000, report=rep)

    rep.section("Part B: the appendix_polynomials.tex display and Lemma lem:first-char2-circuit-inverse")
    rep.check("gate list matches the appendix display '4 products, degree 7' (h = 4, 12 XORs)", print_circuit(SPEC_B, "appendix_polynomials.tex, '4 products, degree 7'", (4, 12)))
    print(DECODER_B)
    S, a = gf2_ring([f"a{i}" for i in range(7)])
    one = S.one
    a0, a1, a2, a3, a4, a5, a6 = a
    p = eval_circuit(SPEC_B, a, S)
    rep.check("circuit output is monic of degree 7", len(p) == 8 and p[7] == one)
    b = one + a0 + a1
    c = one + a0 + a2 + a0 * a1
    d = a1 * a2
    wires = eval_wires(SPEC_B, a, S)
    x, y, z, t = wires["x"], wires["y"], wires["z"], wires["t"]
    xyz = padd(S, padd(S, x, y), z)
    rep.check("x + y + z = x^3 + b x^2 + c x + d", xyz == [d, c, b, one])
    rep.check("t = (x+y+z)^2 + a3 (x+y+z)", t == padd(S, pmul(S, xyz, xyz), pmul(S, [a3], xyz)))
    sextic = [d * d + a3 * d + a5, a3 * c + a0, c * c + a3 * b + one, a3, b * b, S.zero, one]
    rep.check("y + t + a5 = x^6 + b^2 x^4 + a3 x^3 + (c^2 + a3 b + 1) x^2 + (a3 c + a0) x + (d^2 + a3 d + a5)", padd(S, padd(S, y, t), [a5]) == sextic)
    table = {
        6: a4,
        5: b * b,
        4: a3 + a4 * b * b,
        3: c * c + a3 * b + one + a4 * a3,
        2: a3 * c + a0 + a4 * (c * c + a3 * b + one),
        1: d * d + a3 * d + a5 + a4 * (a3 * c + a0),
        0: a4 * (d * d + a3 * d + a5) + a6,
    }
    rep.check("coefficient table p6..p0 of the lemma", all(p[j] == table[j] for j in range(7)))
    rep.check(
        "decode(encode(a)) = a in GF(2)[a0,...,a6] (composed identity; b, c as Frobenius pivots)",
        decode_b(p[:7], S, truth=a) == a and len(S.root_checks) == 2 and all(S.root_checks),
    )
    rep.section("Part B: numeric round trip (square roots by x -> x^(2^63))")
    roundtrip(SPEC_B, lambda cc: decode_b(cc, R), R, seed=7, count=2000, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
