#!/usr/bin/env python3
"""Certificate for the degree-13 characteristic-2 circuit (7 products).

Circuit: the degree-13 row of display (A.0) in sections/appendix_polynomials.tex
(the alternative with an explicit inverse); the same gate list is CIRCUITS[13]
of website/js/char2.js and ``_eval_n13`` of char2/worked_examples.py (whose
closed-form GF(4) decoder is char2/decode_n13.py).
Decoder: Lemma lem:char2-degree13-inverse, the unitriangular certificate
(13.1)-(13.5): linear key coordinates q (13.1), row order d (13.2), baselines
K_i (13.3), and the unit pivots [x^{d_i}] P = q_i + K_i(q_0..q_{i-1}) (13.4).

What is checked (run from the repository root as ``python3 -m char2.verify_n13``):
  * the circuit expands to a monic degree-13 polynomial;
  * all thirteen unit-pivot identities (13.4) in GF(2)[q_0..q_12] (sympy): row
    d_i minus q_i involves only q_0..q_{i-1};
  * the three displayed rows, the coordinate change (13.1) and its inverse,
    the cancellation identity (13.6) and its instantiation in the circuit;
  * decode(encode(a)) = a as a composed identity in GF(2)[q_0..q_12] with the
    generic baseline decoder (13.4)/(13.3);
  * a numeric GF(2^64) round trip with a stated seed and count.
"""

from __future__ import annotations

from .verify_common import (
    Circuit,
    FieldRing,
    G,
    Report,
    banner,
    decode_unit_pivots,
    eval_circuit,
    eval_wires,
    field64,
    gf2_ring,
    padd,
    pcoeff,
    pmul,
    print_circuit,
    roundtrip,
    uses_only,
)

SPEC = Circuit(
    13,
    (
        G("y", ["x"], None, ["x"], None),
        G("z", ["x", "y"], 12, ["y"], 11),
        G("w", ["y", "z"], 10, ["z"], 9),
        G("v", ["y", "z"], 8, ["w"], 7),
        G("u", ["z", "v"], 6, ["x"], 5),
        G("t", ["x", "y"], 4, ["x"], 3),
        G("s", ["w", "t"], 2, ["y"], 1),
    ),
    (("u", "v", "s"), 0),
)

# (13.2): row d_i carries pivot q_i.
ROWS = [12, 11, 10, 7, 6, 9, 8, 5, 4, 3, 1, 2, 0]
# (13.1): q = (a5, a11+a12, a12, a9, a8, a10, a1, a7, a3, a4, a6, a2, a0).
Q_OF_A = ["a5", "a11 + a12", "a12", "a9", "a8", "a10", "a1", "a7", "a3", "a4", "a6", "a2", "a0"]

DECODER = """\
Decoder (Lemma lem:char2-degree13-inverse; P = x^13 + sum c_j x^j):
  (13.1) q = (a5, a11 + a12, a12, a9, a8, a10, a1, a7, a3, a4, a6, a2, a0);
         inverse: a5 = q0, a11 = q1 + q2, a12 = q2, a9 = q3, a8 = q4, a10 = q5, a1 = q6,
                  a7 = q7, a3 = q8, a4 = q9, a6 = q10, a2 = q11, a0 = q12
  (13.2) rows d = (12, 11, 10, 7, 6, 9, 8, 5, 4, 3, 1, 2, 0)
  (13.3) K_i(q_0..q_{i-1}) = [x^{d_i}] P(q_0, .., q_{i-1}, 0, .., 0)
  (13.4) [x^{d_i}] P = q_i + K_i(q_0..q_{i-1}),  0 <= i <= 12   (unit pivots)
  decoder: q_i = c_{d_i} + K_i(q_0..q_{i-1}) for i = 0..12, then the inverse of (13.1).
  Unit pivots only: valid over every field of characteristic 2."""


def keys_from_q(Q, R):
    add = R.add
    a = [R.zero] * 13
    a[5] = Q[0]
    a[11] = add(Q[1], Q[2])
    a[12] = Q[2]
    a[9] = Q[3]
    a[8] = Q[4]
    a[10] = Q[5]
    a[1] = Q[6]
    a[7] = Q[7]
    a[3] = Q[8]
    a[4] = Q[9]
    a[6] = Q[10]
    a[2] = Q[11]
    a[0] = Q[12]
    return a


def q_from_keys(a, R):
    return [a[5], R.add(a[11], a[12]), a[12], a[9], a[8], a[10], a[1], a[7], a[3], a[4], a[6], a[2], a[0]]


def decode13(c, R):
    return decode_unit_pivots(SPEC, keys_from_q, c, R, rows=ROWS)


def main() -> None:
    rep = Report(13)
    banner(
        13,
        "Circuit: degree-13 row of display (A.0), sections/appendix_polynomials.tex "
        "(= CIRCUITS[13] of website/js/char2.js).  Decoder: unitriangular certificate "
        "(13.1)-(13.5) of Lemma lem:char2-degree13-inverse, unit pivots only (every characteristic-2 field).",
    )
    rep.check("gate list matches the appendix display (A.0) and char2.js CIRCUITS[13]", print_circuit(SPEC, "appendix (A.0), degree 13", (5, 21)))
    print(DECODER)

    rep.section("Symbolic certificate in GF(2)[q0,...,q12] (sympy)")
    S, q = gf2_ring([f"q{i}" for i in range(13)])
    one = S.one
    a = keys_from_q(q, S)
    rep.check("(13.1) coordinate change and its inverse are mutually inverse", q_from_keys(a, S) == q)
    c = eval_circuit(SPEC, a, S)
    rep.check("circuit output is monic of degree 13", len(c) == 14 and c[13] == one)
    print("  pivot table (row d_i : pivot q_i = key expression, |K_i| monomials):")
    all_unit = True
    for i, row in enumerate(ROWS):
        K = c[row] + q[i]
        unit = uses_only(K, q[:i], q)
        all_unit &= unit
        print(f"    row {row:2d} : q{i:<2d} = {Q_OF_A[i]:<9}  K_{i} has {len(K.terms()):4d} monomials" + ("" if unit else "   <-- uses a current/later coordinate"))
    rep.check("(13.4) all thirteen rows are unit pivots: [x^{d_i}] P + q_i involves only q_0..q_{i-1}", all_unit)
    rep.check("[x^12] P = q0", c[12] == q[0])
    rep.check("[x^11] P = q0 + q1", c[11] == q[0] + q[1])
    rep.check("[x^10] P = 1 + q0 + q0 q1 + q2", c[10] == one + q[0] + q[0] * q[1] + q[2])

    # (13.6) as a generic identity, and its instantiation A = z + y, B = z + a9, R = x + a5 + 1, S = y + a1.
    T, (A, B, Rg, Sg, E, ell, p, t) = gf2_ring(["A", "B", "R", "S", "E", "l", "p", "t"])

    def Fpt(pp, tt):
        Wp = (A + pp) * B
        Vt = (A + tt) * (Wp + ell)
        return Rg * Vt + Sg * Wp + E

    rep.check(
        "(13.6) F_{p,t} + F_{0,0} = (p + t) R A B + p t R B + t R l + p S B",
        Fpt(p, t) + Fpt(T.zero, T.zero) == (p + t) * Rg * A * B + p * t * Rg * B + t * Rg * ell + p * Sg * B,
    )
    Sa, aa = gf2_ring([f"a{i}" for i in range(13)])
    wires = eval_wires(SPEC, aa, Sa)
    x, y, z, w, v, tt = (wires[k] for k in ("x", "y", "z", "w", "v", "t"))
    A_c = padd(Sa, z, y)
    B_c = padd(Sa, z, [aa[9]])
    R_c = padd(Sa, x, [aa[5] + Sa.one])
    S_c = padd(Sa, y, [aa[1]])
    rep.check("w = (A + a10) B and v = (A + a8)(w + a7) with A = z + y, B = z + a9", w == pmul(Sa, padd(Sa, A_c, [aa[10]]), B_c) and v == pmul(Sa, padd(Sa, A_c, [aa[8]]), padd(Sa, w, [aa[7]])))
    E_c = padd(Sa, padd(Sa, pmul(Sa, padd(Sa, x, [aa[5]]), padd(Sa, z, [aa[6]])), pmul(Sa, S_c, padd(Sa, tt, [aa[2]]))), [aa[0]])
    P_c = eval_circuit(SPEC, aa, Sa)
    rep.check("P = R v + S w + E with R = x + a5 + 1, S = y + a1, E = (x + a5)(z + a6) + (y + a1)(t + a2) + a0", P_c == padd(Sa, padd(Sa, pmul(Sa, R_c, v), pmul(Sa, S_c, w)), E_c))
    rep.check("[x^6] (R A B) = 1 and [x^6] (S B) = 1 (the a10 terms of row 6 cancel)", pcoeff(Sa, pmul(Sa, pmul(Sa, R_c, A_c), B_c), 6) == Sa.one and pcoeff(Sa, pmul(Sa, S_c, B_c), 6) == Sa.one)

    rep.check("decode(encode(a)) = a in GF(2)[q0,...,q12] (generic baseline decoder, composed identity)", decode13(c[:13], S) == a)

    rep.section("Numeric round trip")
    F = field64()
    R = FieldRing(F)
    roundtrip(SPEC, lambda cc: decode13(cc, R), R, seed=13, count=200, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
