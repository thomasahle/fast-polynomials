#!/usr/bin/env python3
"""Certificate for the degree-23 characteristic-2 circuit (12 products).

Circuit: "12 products, degree 23" of sections/appendix_polynomials.tex; the
same gate list is CIRCUITS[23] of website/js/char2.js (whose wire n is our f).
Decoder: Lemma lem:char2-degree23-inverse -- polynomial coordinates
(A.35)-(A.36) with inverse (A.37)-(A.38) (a19 = q14 + H(a), H = row 8 of the
circuit at a19 = 0), baselines (A.39), the eighteen unit pivots (A.40) for
rows 22..5 and row 0, the four-row block (A.43) with its explicit solution
(A.44), and the descending recurrence (A.45).  No root is taken: valid over
every field of characteristic 2.

Implementation: char2/verify_n23_unitriangular_symbolic.py (kept in place;
``certify()``): in GF(2)[q_0..q_22][x] it verifies the inverse (A.37)-(A.38)
by substitution, the unit pivots of (A.40) for rows 22 down to 5 (including
c8 = q14), the block rows (A.43) with their solution (A.44), and the unit
slope of q22 in row 0.  This wrapper additionally checks the six displayed
rows (A.41) on that script's symbolic output, checks that the gate list and
a(q) below agree numerically with the script, and runs a GF(2^64) round trip
with the decoder (A.45) transcribed literally (unit pivots, block solve, q22).

Run from the repository root:  python3 -m char2.verify_n23
"""

from __future__ import annotations

import random

from .verify_common import (
    Circuit,
    FieldRing,
    G,
    Report,
    banner,
    compile_f2poly,
    eval_circuit,
    eval_compiled,
    field64,
    pcoeff,
    print_circuit,
    roundtrip,
)

SPEC = Circuit(
    23,
    (
        G("y", ["x"], None, ["x"], None),
        G("z", ["y"], 0, ["x", "y"], 1),
        G("t", ["x"], 2, ["z"], 3),
        G("u", ["y", "z", "t"], 4, ["z", "t"], 5),
        G("v", ["x"], 6, ["y", "z"], 7),
        G("w", ["x", "y", "z"], 8, ["y", "v"], 9),
        G("s", ["z"], 10, ["v"], 11),
        G("r", ["x", "t"], 12, ["u"], 13),
        G("g", ["z", "t"], 14, ["x", "u"], 15),
        G("l", ["x"], 16, ["z", "v"], 17),
        G("m", ["x", "y", "z"], 18, ["x", "y", "z", "w", "s", "g", "l"], 19),
        G("f", ["z"], 20, ["u", "m"], 21),
    ),
    (("y", "v", "w", "s", "r", "g", "f"), 22),
)

DECODER = """\
Decoder (Lemma lem:char2-degree23-inverse; P = x^23 + sum c_j x^j):
  (A.37) a0 = q2, a1 = q1 + q2, a2 = q0, a3 = q3 + q5 + q6, a4 = q4 + q5 + q6 + q7, a5 = q16, a6 = q8,
         a7 = q11 + q7 q16 + q16^2 + q20, a12 = q15 + q16, a13 = q17 + q18, a14 = q7 + q16, a15 = q20,
         a16 = q18, a17 = q21, a18 = q5, a20 = q6, a21 = q19, a22 = q22
  (A.38) rho = (q0 + q8)(q7 q16 + q16^2 + q20) + q7 q16 + q16^2,  gamma = q0 + q3 + q5 + q6 + q8 + q9 + q11 + 1,
         alpha = gamma + q7^2,  beta = q7 gamma + 1;
         a11 = q13 + q16^4 + alpha q16^2 + beta q16 + q20^2 + gamma q20 + q18 + q21
         a10 = q12 + rho + q16 + a11 + a12
         a9  = q10 + rho + a11 + q18 + q20
         a8  = q9 + q7 q16 + q16^2 + a10 + q18 + q20
         a19 = q14 + H(a),  H(a) = [x^8] P(a | a19 = 0)
  (A.39) K_i(q_0..q_{i-1}) = [x^{22-i}] P(a(q_0, .., q_{i-1}, 0, .., 0))   (0 <= i <= 17 and i = 22)
  (A.40) c_{22-i} = q_i + K_i(q_0..q_{i-1}); in particular c8 = q14   (pivot table (A.42): row 22-i carries q_i)
  (A.43) rows 4, 3, 2, 1 as a block: kappa_j = [x^j] P(a(q_0..q_17, 0, .., 0)),  e_j = c_j + kappa_j,
         e4 = (q0 + q8 + 1) q18 + q19,  e3 = (q0 + q8) q18 + q19,
         e2 = (q1 (q0 + q8 + 1) + q8) q18 + q1 q19 + q20,  e1 = T q18 + q2 q19 + (q8 + q18 + 1) q20 + q21,
         T = q0 q2 + q2 q8 + q2 + q3 + q5 + q6 + q7 q16 + q11 + q16^2 + 1
  (A.44) q18 = e4 + e3,  q19 = e3 + (q0 + q8) q18,  q20 = e2 + (q1 (q0 + q8 + 1) + q8) q18 + q1 q19,
         q21 = e1 + T q18 + q2 q19 + (q8 + q18 + 1) q20
  (A.45) decoder: q_i = c_{22-i} + K_i (i = 0..17), then (A.44), then q22 = c0 + K_22; finally a = a(q).
  Unit pivots and a determinant-1 block: valid over every field of characteristic 2."""


def keys_from_q(Q, R):
    """(A.37)-(A.38), with a19 = q14 + [x^8] P(a | a19 = 0)."""
    m, add, zero, one = R.mul, R.add, R.zero, R.one

    def s(*xs):
        out = zero
        for x in xs:
            out = add(out, x)
        return out

    q = Q
    a = [zero] * 23
    a[0] = q[2]
    a[1] = add(q[1], q[2])
    a[2] = q[0]
    a[3] = s(q[3], q[5], q[6])
    a[4] = s(q[4], q[5], q[6], q[7])
    a[5] = q[16]
    a[6] = q[8]
    q16sq = m(q[16], q[16])
    w = s(m(q[7], q[16]), q16sq, q[20])
    a[7] = add(q[11], w)
    a[12] = add(q[15], q[16])
    a[13] = add(q[17], q[18])
    a[14] = add(q[7], q[16])
    a[15] = q[20]
    a[16] = q[18]
    a[17] = q[21]
    a[18] = q[5]
    a[20] = q[6]
    a[21] = q[19]
    a[22] = q[22]
    rho = s(m(add(q[0], q[8]), w), m(q[7], q[16]), q16sq)
    gamma = s(q[0], q[3], q[5], q[6], q[8], q[9], q[11], one)
    alpha = add(gamma, m(q[7], q[7]))
    beta = add(m(q[7], gamma), one)
    a[11] = s(q[13], m(q16sq, q16sq), m(alpha, q16sq), m(beta, q[16]), m(q[20], q[20]), m(gamma, q[20]), q[18], q[21])
    a[10] = s(q[12], rho, q[16], a[11], a[12])
    a[9] = s(q[10], rho, a[11], q[18], q[20])
    a[8] = s(q[9], m(q[7], q[16]), q16sq, a[10], q[18], q[20])
    a[19] = zero
    a[19] = add(q[14], pcoeff(R, eval_circuit(SPEC, a, R), 8))
    return a


def decode23(c, R):
    """(A.45) literally: unit pivots for rows 22..5, the block (A.44), then row 0."""
    m, add, zero, one = R.mul, R.add, R.zero, R.one

    def s(*xs):
        out = zero
        for x in xs:
            out = add(out, x)
        return out

    q = [zero] * 23
    for i in range(18):
        base = eval_circuit(SPEC, keys_from_q(q, R), R)
        q[i] = add(c[22 - i], pcoeff(R, base, 22 - i))
    base = eval_circuit(SPEC, keys_from_q(q, R), R)  # q18 = .. = q22 = 0: the kappa_j
    e = {j: add(c[j], pcoeff(R, base, j)) for j in (4, 3, 2, 1)}
    q[18] = add(e[4], e[3])
    q[19] = add(e[3], m(add(q[0], q[8]), q[18]))
    q[20] = s(e[2], m(add(m(q[1], s(q[0], q[8], one)), q[8]), q[18]), m(q[1], q[19]))
    T = s(m(q[0], q[2]), m(q[2], q[8]), q[2], q[3], q[5], q[6], m(q[7], q[16]), q[11], m(q[16], q[16]), one)
    q[21] = s(e[1], m(T, q[18]), m(q[2], q[19]), m(s(q[8], q[18], one), q[20]))
    base = eval_circuit(SPEC, keys_from_q(q, R), R)
    q[22] = add(c[0], pcoeff(R, base, 0))
    return keys_from_q(q, R)


def main() -> None:
    rep = Report(23)
    banner(
        23,
        "Circuit: '12 products, degree 23' of sections/appendix_polynomials.tex (= CIRCUITS[23] of website/js/char2.js).  "
        "Decoder: (A.35)-(A.45) of Lemma lem:char2-degree23-inverse, unit pivots and one determinant-1 block.\n"
        "Implementation: char2/verify_n23_unitriangular_symbolic.py (imports tools/char2_inverse_finder.py).",
    )
    rep.check("gate list matches the appendix display and char2.js CIRCUITS[23]", print_circuit(SPEC, "appendix '12 products, degree 23'", (7, 50)))
    print(DECODER)

    rep.section("char2/verify_n23_unitriangular_symbolic.py: exact certificate in GF(2)[q0,...,q22][x]")
    from . import verify_n23_unitriangular_symbolic as sym

    holder: dict = {}

    def run_sym() -> None:
        holder["res"] = sym.certify()

    rep.run("certify(): inverse (A.37)-(A.38), eighteen unit pivots (rows 22..5, c8 = q14), block (A.43)/(A.44), unit slope of q22 in row 0", run_sym)
    res = holder.get("res")
    if res is not None:
        q, p = res["q"], res["p"]
        one = sym.ONE
        expected = {
            22: q[0],
            21: one + q[0] + q[1] + q[0] ** 2,
            20: one + q[1] + q[2] + q[0] * q[1] + q[0] ** 3,
            19: q[1] + q[2] + q[3] + q[0] * q[2] + q[1] * q[2] + q[2] ** 2 + q[0] ** 3 + q[0] ** 2 * q[1],
            18: q[1] + q[2] + q[4] + q[0] ** 2 + q[0] * q[1] + q[0] * q[3] + q[1] * q[2] + q[2] ** 2 + q[0] ** 3
            + q[0] ** 2 * q[1] + q[0] ** 2 * q[2] + q[0] * q[1] * q[2] + q[0] * q[2] ** 2 + q[0] ** 3 * q[1],
            17: q[1] + q[2] + q[5] + q[0] * q[2] + q[1] * q[2] + q[2] ** 2 + q[0] ** 3 + q[0] ** 2 * q[2] + q[0] ** 2 * q[3]
            + q[0] ** 3 * q[2] + q[0] ** 2 * q[1] * q[2] + q[0] ** 2 * q[2] ** 2,
        }
        rep.check("(A.41) the six displayed rows c22..c17", all(p.coeff(j) == expected[j] for j in expected))

    rep.section("Consistency of this gate list and a(q) with the symbolic script (numeric, GF(2^64))")
    F = field64()
    R = FieldRing(F)
    if res is not None:
        compiled_a = [compile_f2poly(expr) for expr in res["a"]]
        compiled_p = [compile_f2poly(res["p"].coeff(j)) for j in range(24)]
        rng = random.Random(2300)
        same_keys = same_coeffs = True
        for _ in range(3):
            Qv = [rng.getrandbits(64) for _ in range(23)]
            env = {f"q{i}": Qv[i] for i in range(23)}
            keys = keys_from_q(Qv, R)
            same_keys &= keys == [eval_compiled(ca, env, R) for ca in compiled_a]
            same_coeffs &= eval_circuit(SPEC, keys, R) == [eval_compiled(cp, env, R) for cp in compiled_p]
        rep.check("a(q) of (A.37)-(A.38) equals the script's inverse at 3 random points", same_keys)
        rep.check("the circuit printed above equals the script's symbolic P at 3 random points", same_coeffs)

    rep.section("Numeric round trip with the decoder (A.45)")
    roundtrip(SPEC, lambda cc: decode23(cc, R), R, seed=23, count=10, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
