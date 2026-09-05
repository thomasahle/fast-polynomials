#!/usr/bin/env python3
"""Certificate for the degree-9 characteristic-2 circuit (5 products).

Circuit: the degree-9 row of display (A.0) in sections/appendix_polynomials.tex
(the alternative with an explicit inverse); the same gate list is CIRCUITS[9] of
website/js/char2.js and ``_eval_n9`` of char2/worked_examples.py.
Decoder: Lemma lem:char2-small-staircase-butterfly, equations (9.1)-(9.3):
five unit-slope top rows, the linear constant block (9.2), then four unit
pivots below the explicit baseline B (the circuit at a_5 = .. = a_8 = 0).

What is checked (run from the repository root as ``python3 -m char2.verify_n9``):
  * the circuit expands to a monic degree-9 polynomial;
  * every displayed identity of (9.1)-(9.3) holds literally in GF(2)[a_0..a_8]
    (sympy, ring GF(2)[a0,...,a8]);
  * decode(encode(a)) = a as a composed identity in GF(2)[a_0..a_8] and
    encode(decode(c)) = c in GF(2)[c_0..c_8], so the coefficient map is a
    polynomial bijection over every field of characteristic 2;
  * a numeric GF(2^64) round trip with a stated seed and count.
"""

from __future__ import annotations

from .verify_common import (
    Circuit,
    FieldRing,
    G,
    Report,
    banner,
    eval_circuit,
    field64,
    gf2_ring,
    print_circuit,
    roundtrip,
)

SPEC = Circuit(
    9,
    (
        G("y", ["x"], None, ["x"], 0),
        G("z", ["x"], None, ["y"], 1),
        G("t", ["y", "z"], 2, ["z"], 3),
        G("u", ["x", "z"], 4, ["t"], 5),
        G("v", ["y"], 6, ["z"], 7),
    ),
    (("u", "v"), 8),
)

DECODER = """\
Decoder (Lemma lem:char2-small-staircase-butterfly; P = x^9 + sum c_j x^j):
  (9.1)  a0 = c8 + 1
         a1 = c7 + 1 + a0 + a0^2
         r  = c6 + 1 + a0^2 + a0^3                          (= a2 + a3 + a4)
         s  = c5 + 1 + a0^2 + a0^3 + a0^2 a1 + a1^2         (= a3 + a4)
         q  = c4 + a0^2 + a0^2 r + a0 a1^2 + a1 + a1^2      (= a2 + a3)
  (9.2)  a2 = r + s,  a3 = q + a2,  a4 = s + a3
         B  = the circuit at (a0, .., a4, 0, 0, 0, 0), b_j = [x^j] B
  (9.3)  h  = c3 + b3                                       (= a5 + a6)
         a7 = c2 + b2 + a0 h
         a5 = c1 + b1 + a1 h + a0 a7
         a6 = h + a5
         a8 = c0 + b0 + a4 a5 + a6 a7
  Every step has unit slope: no root, division or field-size assumption."""


def decode9(c, R):
    """(9.1)-(9.3) literally; c = [c0, .., c8] -> [a0, .., a8]."""
    add, mul, one, zero = R.add, R.mul, R.one, R.zero

    def xsum(*xs):
        out = zero
        for x in xs:
            out = add(out, x)
        return out

    a0 = add(c[8], one)
    a0_2 = mul(a0, a0)
    a0_3 = mul(a0_2, a0)
    a1 = xsum(c[7], one, a0, a0_2)
    a1_2 = mul(a1, a1)
    r = xsum(c[6], one, a0_2, a0_3)
    s = xsum(c[5], one, a0_2, a0_3, mul(a0_2, a1), a1_2)
    q = xsum(c[4], a0_2, mul(a0_2, r), mul(a0, a1_2), a1, a1_2)
    a2 = add(r, s)
    a3 = add(q, a2)
    a4 = add(s, a3)
    B = eval_circuit(SPEC, [a0, a1, a2, a3, a4, zero, zero, zero, zero], R)
    h = add(c[3], B[3])
    a7 = xsum(c[2], B[2], mul(a0, h))
    a5 = xsum(c[1], B[1], mul(a1, h), mul(a0, a7))
    a6 = add(h, a5)
    a8 = xsum(c[0], B[0], mul(a4, a5), mul(a6, a7))
    return [a0, a1, a2, a3, a4, a5, a6, a7, a8]


def main() -> None:
    rep = Report(9)
    banner(
        9,
        "Circuit: degree-9 row of display (A.0), sections/appendix_polynomials.tex "
        "(= CIRCUITS[9] of website/js/char2.js).  Decoder: (9.1)-(9.3) of Lemma "
        "lem:char2-small-staircase-butterfly, unit pivots only (every characteristic-2 field).",
    )
    rep.check("gate list matches the appendix display (A.0) and char2.js CIRCUITS[9]", print_circuit(SPEC, "appendix (A.0), degree 9", (4, 12)))
    print(DECODER)

    rep.section("Symbolic certificate in GF(2)[a0,...,a8] (sympy)")
    S, a = gf2_ring([f"a{i}" for i in range(9)])
    c = eval_circuit(SPEC, a, S)
    rep.check("circuit output is monic of degree 9", len(c) == 10 and c[9] == S.one)
    one = S.one
    a0, a1, a2, a3, a4, a5, a6, a7, a8 = a
    r_true, s_true, q_true = a2 + a3 + a4, a3 + a4, a2 + a3
    rep.check("(9.1) a0 = c8 + 1", c[8] + one == a0)
    rep.check("(9.1) a1 = c7 + 1 + a0 + a0^2", c[7] + one + a0 + a0**2 == a1)
    rep.check("(9.1) r = c6 + 1 + a0^2 + a0^3 equals a2 + a3 + a4", c[6] + one + a0**2 + a0**3 == r_true)
    rep.check(
        "(9.1) s = c5 + 1 + a0^2 + a0^3 + a0^2 a1 + a1^2 equals a3 + a4",
        c[5] + one + a0**2 + a0**3 + a0**2 * a1 + a1**2 == s_true,
    )
    rep.check(
        "(9.1) q = c4 + a0^2 + a0^2 r + a0 a1^2 + a1 + a1^2 equals a2 + a3",
        c[4] + a0**2 + a0**2 * r_true + a0 * a1**2 + a1 + a1**2 == q_true,
    )
    rep.check("(9.2) inverts the constant block", [r_true + s_true, q_true + (r_true + s_true), s_true + (q_true + r_true + s_true)] == [a2, a3, a4])
    B = eval_circuit(SPEC, [a0, a1, a2, a3, a4, S.zero, S.zero, S.zero, S.zero], S)
    h = a5 + a6
    rep.check("row 3 minus baseline = a5 + a6", c[3] + B[3] == h)
    rep.check("row 2 minus baseline = a7 + a0 (a5 + a6)", c[2] + B[2] == a7 + a0 * h)
    rep.check("row 1 minus baseline = a5 + a1 (a5 + a6) + a0 a7", c[1] + B[1] == a5 + a1 * h + a0 * a7)
    rep.check("row 0 minus baseline = a8 + a4 a5 + a6 a7", c[0] + B[0] == a8 + a4 * a5 + a6 * a7)
    rep.check("decode(encode(a)) = a in GF(2)[a0,...,a8] (composed identity)", decode9(c[:9], S) == a)

    S2, cs = gf2_ring([f"c{i}" for i in range(9)])
    keys = decode9(cs, S2)
    back = eval_circuit(SPEC, keys, S2)
    rep.check("encode(decode(c)) = c in GF(2)[c0,...,c8] (free coefficients; output monic)", back[:9] == cs and back[9] == S2.one)

    rep.section("Numeric round trip")
    F = field64()
    R = FieldRing(F)
    roundtrip(SPEC, lambda cc: decode9(cc, R), R, seed=9, count=500, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
