#!/usr/bin/env python3
"""Certificate for the degree-11 characteristic-2 circuit (6 products).

Circuit: the degree-11 row of display (A.0) in sections/appendix_polynomials.tex
(the alternative with an explicit inverse).  NOTE: this is NOT the degree-11
circuit of website/js/char2.js (CIRCUITS[11] there is a different, square-first
circuit with a unit-pivot decoder), and not the benchmarked "6 products,
degree 11" search candidate shown above (A.0); the appendix's explicit inverse
is for the (A.0) row certified here.
Decoder: Lemma lem:char2-small-staircase-butterfly, equations (11.1)-(11.4):
three unit top rows, two inverse-Frobenius steps (11.2) (so the field must be
perfect, e.g. every finite GF(2^k)), one baseline pivot for a_6, and the
cancellation (11.3) whose rows give (11.4).

What is checked (run from the repository root as ``python3 -m char2.verify_n11``):
  * the circuit expands to a monic degree-11 polynomial;
  * rows (11.1), the two squares behind (11.2), the baseline pivot for a_6,
    the identity (11.3) and the pivots (11.4) hold literally in
    GF(2)[a_0..a_10] (sympy);
  * decode(encode(a)) = a as a composed identity in GF(2)[a_0..a_10], where
    each square root is the symbolic Frobenius pivot "radicand == root^2";
  * a numeric GF(2^64) round trip (both directions) with a stated seed and count.
"""

from __future__ import annotations

from .verify_common import (
    Circuit,
    FieldRing,
    G,
    Report,
    banner,
    eval_circuit,
    eval_wires,
    field64,
    gf2_ring,
    padd,
    peq,
    pmul,
    print_circuit,
    roundtrip,
)

SPEC = Circuit(
    11,
    (
        G("y", ["x"], None, ["x"], 0),
        G("z", ["y"], 1, ["x", "y"], 2),
        G("t", ["x"], None, ["y"], 3),
        G("u", ["t"], 4, ["z"], 5),
        G("v", ["x", "y", "t", "u"], 6, ["z", "t"], 7),
        G("w", ["t"], 8, ["y", "u"], 9),
    ),
    (("v", "w"), 10),
)

DECODER = """\
Decoder (Lemma lem:char2-small-staircase-butterfly; P = x^11 + sum c_j x^j):
         a0 = c10,  a3 = c9 + 1,  a4 = c8 + a0
         K7 = 1 + a0^2 + a0^4 + a3
         K6 = 1 + a0 + a0^3 + a0^5 + a4
         K5 = a0 + a0^2 + a0^4 a3 + a0^2 a3 + a3
  (11.1) c7 = K7 + s^2 + h,  c6 = K6 + a0 s^2 + (a0+1) h,
         c5 = K5 + a0^2 (s^2 + h) + s + a1^2 + a3 s^2 + s h + a3 h,
         with s = a1 + a2 and h = a5 + a7 + a8
  (11.2) r  = c7 + K7
         h  = c6 + K6 + a0 r
         s  = (r + h)^(1/2)                                     [Frobenius pivot]
         a1 = (c5 + K5 + a0^2 r + s + a3 s^2 + s h + a3 h)^(1/2) [Frobenius pivot]
         a2 = s + a1
         B0 = the circuit at (a5,a6,a7,a8,a9,a10) = (0,0,0,h,0,0);  a6 = c4 + [x^4] B0
         B  = the circuit at (a5,a6,a7,a8,a9,a10) = (0,a6,0,h,0,0);  d_j = c_j + [x^j] B
  (11.3) P + B = kappa (t + a4) + a5 y + a7 (x + t + a6) + a9 (t + a8) + a10,
         kappa = a5 (h + a5),  a8 = h + a5 + a7
  (11.4) a5 = d2 + a0 d3,  kappa = a5 (h + a5),  a7 = d1 + a3 d3 + a0 a5,
         a9 = d3 + kappa + a7,  a8 = h + a5 + a7,  a10 = d0 + kappa a4 + a7 a6 + a9 a8
  The only non-polynomial steps are the two square roots in (11.2): unique over a perfect field."""


def decode11(c, R, truth=None):
    """(11.1)-(11.4) literally; c = [c0, .., c10] -> [a0, .., a10].

    Over a finite field ``R.root`` is the unique square root; symbolically
    (``truth`` = the key symbols) it checks radicand == root^2 and returns the root.
    """
    add, mul, one, zero = R.add, R.mul, R.one, R.zero

    def xsum(*xs):
        out = zero
        for x in xs:
            out = add(out, x)
        return out

    a0 = c[10]
    a3 = add(c[9], one)
    a4 = add(c[8], a0)
    a0_2 = mul(a0, a0)
    a0_3 = mul(a0_2, a0)
    a0_4 = mul(a0_2, a0_2)
    a0_5 = mul(a0_4, a0)
    K7 = xsum(one, a0_2, a0_4, a3)
    K6 = xsum(one, a0, a0_3, a0_5, a4)
    K5 = xsum(a0, a0_2, mul(a0_4, a3), mul(a0_2, a3), a3)
    r = add(c[7], K7)
    h = xsum(c[6], K6, mul(a0, r))
    s = R.root(add(r, h), 1, None if truth is None else truth[1] + truth[2])
    s2 = mul(s, s)
    a1 = R.root(xsum(c[5], K5, mul(a0_2, r), s, mul(a3, s2), mul(s, h), mul(a3, h)), 1, None if truth is None else truth[1])
    a2 = add(s, a1)
    B0 = eval_circuit(SPEC, [a0, a1, a2, a3, a4, zero, zero, zero, h, zero, zero], R)
    a6 = add(c[4], B0[4])
    B = eval_circuit(SPEC, [a0, a1, a2, a3, a4, zero, a6, zero, h, zero, zero], R)
    d = [add(c[j], B[j]) for j in range(4)]
    a5 = add(d[2], mul(a0, d[3]))
    kappa = mul(a5, add(h, a5))
    a7 = xsum(d[1], mul(a3, d[3]), mul(a0, a5))
    a9 = xsum(d[3], kappa, a7)
    a8 = xsum(h, a5, a7)
    a10 = xsum(d[0], mul(kappa, a4), mul(a7, a6), mul(a9, a8))
    return [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]


def main() -> None:
    rep = Report(11)
    banner(
        11,
        "Circuit: degree-11 row of display (A.0), sections/appendix_polynomials.tex.  "
        "Decoder: (11.1)-(11.4) of Lemma lem:char2-small-staircase-butterfly; two Frobenius "
        "square roots, hence every perfect field of characteristic 2 (all finite GF(2^k)).\n"
        "NOTE: website/js/char2.js CIRCUITS[11] is a different degree-11 circuit (not certified here).",
    )
    rep.check("gate list matches the appendix display (A.0)", print_circuit(SPEC, "appendix (A.0), degree 11", (4, 18)))
    print(DECODER)

    rep.section("Symbolic certificate in GF(2)[a0,...,a10] (sympy)")
    S, a = gf2_ring([f"a{i}" for i in range(11)])
    one, zero = S.one, S.zero
    c = eval_circuit(SPEC, a, S)
    rep.check("circuit output is monic of degree 11", len(c) == 12 and c[11] == one)
    a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 = a
    s, h = a1 + a2, a5 + a7 + a8
    rep.check("a0 = c10, a3 = c9 + 1, a4 = c8 + a0", [c[10], c[9] + one, c[8] + a0] == [a0, a3, a4])
    K7 = one + a0**2 + a0**4 + a3
    K6 = one + a0 + a0**3 + a0**5 + a4
    K5 = a0 + a0**2 + a0**4 * a3 + a0**2 * a3 + a3
    rep.check("(11.1) c7 = K7 + s^2 + h", c[7] == K7 + s**2 + h)
    rep.check("(11.1) c6 = K6 + a0 s^2 + (a0 + 1) h", c[6] == K6 + a0 * s**2 + (a0 + one) * h)
    rep.check(
        "(11.1) c5 = K5 + a0^2 (s^2 + h) + s + a1^2 + a3 s^2 + s h + a3 h",
        c[5] == K5 + a0**2 * (s**2 + h) + s + a1**2 + a3 * s**2 + s * h + a3 * h,
    )
    r = c[7] + K7
    h_dec = c[6] + K6 + a0 * r
    rep.check("(11.2) h = c6 + K6 + a0 r recovers a5 + a7 + a8", h_dec == h)
    rep.check("(11.2) r + h = s^2 (square root pivot for s = a1 + a2)", r + h_dec == s**2)
    rep.check(
        "(11.2) c5 + K5 + a0^2 r + s + a3 s^2 + s h + a3 h = a1^2 (square root pivot for a1)",
        c[5] + K5 + a0**2 * r + s + a3 * s**2 + s * h + a3 * h == a1**2,
    )
    B0 = eval_circuit(SPEC, [a0, a1, a2, a3, a4, zero, zero, zero, h, zero, zero], S)
    rep.check("a6 = c4 + [x^4] B0", c[4] + B0[4] == a6)
    B = eval_circuit(SPEC, [a0, a1, a2, a3, a4, zero, a6, zero, h, zero, zero], S)
    wires = eval_wires(SPEC, a, S)
    t, y, x = wires["t"], wires["y"], wires["x"]
    kappa = a5 * (h + a5)
    rhs = [zero]
    for scalar, poly in ((kappa, padd(S, t, [a4])), (a5, y), (a7, padd(S, padd(S, x, t), [a6])), (a9, padd(S, t, [a8])), (a10, [one])):
        rhs = padd(S, rhs, pmul(S, [scalar], poly))
    lhs = padd(S, c, B)
    rep.check("(11.3) P + B = kappa (t + a4) + a5 y + a7 (x + t + a6) + a9 (t + a8) + a10", peq(S, lhs, rhs))
    d = [c[j] + B[j] for j in range(4)]
    rep.check("(11.4) a5 = d2 + a0 d3", d[2] + a0 * d[3] == a5)
    rep.check("(11.4) a7 = d1 + a3 d3 + a0 a5", d[1] + a3 * d[3] + a0 * a5 == a7)
    rep.check("(11.4) a9 = d3 + kappa + a7", d[3] + kappa + a7 == a9)
    rep.check("(11.4) a8 = h + a5 + a7", h + a5 + a7 == a8)
    rep.check("(11.4) a10 = d0 + kappa a4 + a7 a6 + a9 a8", d[0] + kappa * a4 + a7 * a6 + a9 * a8 == a10)
    rep.check(
        "decode(encode(a)) = a in GF(2)[a0,...,a10] (composed identity; roots as Frobenius pivots)",
        decode11(c[:11], S, truth=a) == a and len(S.root_checks) == 2 and all(S.root_checks),
    )

    rep.section("Numeric round trip (square roots by x -> x^(2^63))")
    F = field64()
    R = FieldRing(F)
    roundtrip(SPEC, lambda cc: decode11(cc, R), R, seed=11, count=500, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
