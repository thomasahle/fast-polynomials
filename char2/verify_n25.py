#!/usr/bin/env python3
"""Certificate for the degree-25 characteristic-2 circuit (13 products).

Circuit: "13 products, degree 25" of sections/appendix_polynomials.tex; the
same gate list is CIRCUITS[25] of website/js/char2.js (whose wires h, j, n are
our d, k, f).
Decoder: Lemma lem:char2-degree25-inverse -- the pivot table (A.46) (row 24-i
carries the key a_{p_i}), the chain of twenty-four elementary substitutions
a_{p_i} = q_i + tau_i (A.47)-(A.48) with the short tails (A.49), the
unitriangular identities (A.50) and the descending recurrence (A.52) followed
by back-substitution through the chain.  No root is taken: valid over every
field of characteristic 2.

Implementation: char2/verify_n25_unitriangular_symbolic.py (kept in place;
``certify()``): in GF(2)[a_0..a_24][x] it performs the twenty-four
substitutions, checking at each step that the named row is affine in a_{p_i}
with slope 1, that tau_i is free of a_{p_i}, and that the row then reads
q_i + K_i(q_0..q_{i-1}); then all twenty-four identities (A.50) and the unit
slope of a24 in row 0.  This wrapper checks the displayed tails (A.49), the
monomial counts of the seven long tails, the six displayed rows (A.51), then
builds the numeric a(q) by back-substituting the certified tails and runs a
GF(2^64) round trip with the recurrence (A.52).

Run from the repository root:  python3 -m char2.verify_n25
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
    decode_unit_pivots,
    eval_circuit,
    eval_compiled,
    f2poly_text,
    field64,
    print_circuit,
    roundtrip,
)

SPEC = Circuit(
    25,
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
        G("d", ["y", "z", "t"], 18, ["x", "y", "z", "u", "v", "w", "r"], 19),
        G("k", ["x", "y", "t"], 20, ["l"], 21),
        G("f", ["x", "t", "u", "s", "r", "g", "l", "d", "k"], 22, ["t"], 23),
    ),
    (("y", "z", "u", "l", "f"), 24),
)

PIVOTS = [2, 0, 1, 3, 4, 12, 6, 5, 23, 7, 9, 13, 8, 17, 10, 11, 15, 19, 21, 22, 18, 16, 14, 20]
LONG_TAIL_SIZES = {13: 71, 14: 215, 15: 339, 16: 212, 17: 245, 18: 359, 19: 4652}
LATE_KEYS = {14, 15, 16, 18, 19, 20, 21}

DECODER = """\
Decoder (Lemma lem:char2-degree25-inverse; P = x^25 + sum c_j x^j):
  (A.46) row 24-i carries the key a_{p_i}, p = (2, 0, 1, 3, 4, 12, 6, 5, 23, 7, 9, 13,
                                                  8, 17, 10, 11, 15, 19, 21, 22, 18, 16, 14, 20), and a24 in row 0
  (A.47) a_{p_i} = q_i + tau_i, tau_i in F2[q_0..q_{i-1}, a_{p_{i+1}}..a_{p_23}] (i = 0..23), q24 = a24
  (A.48) after the first i substitutions, [P]_{24-i} = a_{p_i} + tau_i + K_i(q_0..q_{i-1})
  (A.49) tau_0 = tau_2 = tau_3 = tau_6 = tau_7 = tau_8 = tau_21 = tau_22 = tau_23 = 0, tau_1 = a1, tau_5 = a23,
         tau_4 = a5 + a12 + a18 + a23, tau_9 = a8 + a13 + a14 + a16 + (q4 + q5 + q7) a18 + a18^2,
         tau_10 = (q0 + q6)(a13 + a14 + (q4 + q5 + q7) a18 + a18^2) + a14,
         tau_11 = (q0 + q6) a16 + (q0 + q4 + q5 + q6 + q7 + 1) a18 + a18^2 + a14,
         tau_12 = (q4 + q5 + q7) a18 + a18^2 + a14 + a16, tau_20 = (q0 + q6 + 1) a16;
         tau_13..tau_19 have 71, 215, 339, 212, 245, 359, 4652 monomials (later keys among a14,a15,a16,a18,a19,a20,a21)
  (A.50) c_{24-i} = q_i + K_i(q_0..q_{i-1}), 0 <= i <= 24, K_i = [x^{24-i}] P(a(q_0, .., q_{i-1}, 0, .., 0))
  (A.52) decoder: q_i = c_{24-i} + K_i(q_0..q_{i-1}) for i = 0..24, then back-substitution
         a_{p_i} = q_i + tau_i in the order i = 23, 22, .., 0 and a24 = q24.
  Unit pivots only: valid over every field of characteristic 2."""


def make_keys_from_q(tails):
    """a(q) by back-substitution through the certified tails (variables q<i>, b<j> = a_j)."""
    compiled = [compile_f2poly(tail) for tail in tails]

    def keys_from_q(Q, R):
        a = [R.zero] * 25
        a[24] = Q[24]
        env = {f"q{i}": Q[i] for i in range(24)}
        for i in range(23, -1, -1):
            j = PIVOTS[i]
            a[j] = R.add(Q[i], eval_compiled(compiled[i], env, R))
            env[f"b{j}"] = a[j]
        return a

    return keys_from_q


def main() -> None:
    rep = Report(25)
    banner(
        25,
        "Circuit: '13 products, degree 25' of sections/appendix_polynomials.tex (= CIRCUITS[25] of website/js/char2.js).  "
        "Decoder: the 24-step chain (A.46)-(A.52) of Lemma lem:char2-degree25-inverse, unit pivots only.\n"
        "Implementation: char2/verify_n25_unitriangular_symbolic.py (exact polynomial certificate; no search).",
    )
    rep.check("gate list matches the appendix display and char2.js CIRCUITS[25]", print_circuit(SPEC, "appendix '13 products, degree 25'", (7, 59)))
    print(DECODER)

    rep.section("char2/verify_n25_unitriangular_symbolic.py: the 24 elementary substitutions in GF(2)[a0,...,a24][x]")
    from . import verify_n25_unitriangular_symbolic as sym

    F2Poly = sym.F2Poly

    holder: dict = {}

    def run_sym() -> None:
        holder["res"] = sym.certify(verbose=True)

    rep.run("certify(): every row 24-i affine in a_{p_i} with slope 1, tau_i free of a_{p_i}, row = q_i + K_i, all 24 identities (A.50), unit slope of a24", run_sym)
    res = holder.get("res")
    if res is not None:
        rep.check("pivot order equals the table (A.46)", res["pivot_order"] == PIVOTS)
        tails = res["tails"]
        q = [F2Poly.var(f"q{i}") for i in range(24)]
        b = [F2Poly.var(f"b{j}") for j in range(24)]
        one = sym.ONE
        expected = {i: sym.ZERO for i in (0, 2, 3, 6, 7, 8, 21, 22, 23)}
        expected[1] = b[1]
        expected[5] = b[23]
        expected[4] = b[5] + b[12] + b[18] + b[23]
        q457 = q[4] + q[5] + q[7]
        expected[9] = b[8] + b[13] + b[14] + b[16] + q457 * b[18] + b[18] ** 2
        expected[10] = (q[0] + q[6]) * (b[13] + b[14] + q457 * b[18] + b[18] ** 2) + b[14]
        expected[11] = (q[0] + q[6]) * b[16] + (q[0] + q[4] + q[5] + q[6] + q[7] + one) * b[18] + b[18] ** 2 + b[14]
        expected[12] = q457 * b[18] + b[18] ** 2 + b[14] + b[16]
        expected[20] = (q[0] + q[6] + one) * b[16]
        rep.check("(A.49) the seventeen displayed tails are exact", all(tails[i] == expected[i] for i in expected))
        print("    displayed tails:")
        for i in sorted(expected):
            print(f"      tau_{i:<2d} = {f2poly_text(tails[i])}")
        rep.check("tau_13..tau_19 have 71, 215, 339, 212, 245, 359, 4652 monomials", all(len(tails[i].t) == LONG_TAIL_SIZES[i] for i in LONG_TAIL_SIZES))
        later_ok = all({int(v[1:]) for v in tails[i].variables() if v.startswith("b")} <= LATE_KEYS for i in LONG_TAIL_SIZES)
        rep.check("their later keys lie among a14, a15, a16, a18, a19, a20, a21", later_ok)
        qq, p = res["q"], res["p_final"]
        rows = {
            24: qq[0],
            23: qq[0] + qq[1],
            22: qq[0] + qq[2] + qq[0] * qq[1],
            21: one + qq[0] + qq[2] + qq[3] + qq[0] ** 2 + qq[0] * qq[1] + qq[0] * qq[2] + qq[1] * qq[2] + qq[2] ** 2 + qq[0] ** 4,
            20: qq[0] + qq[2] + qq[4] + qq[0] * qq[1] + qq[0] * qq[3] + qq[1] * qq[2] + qq[2] ** 2 + qq[0] ** 3
            + qq[0] * qq[1] * qq[2] + qq[0] * qq[2] ** 2 + qq[0] ** 5,
            19: one + qq[2] + qq[3] + qq[5] + qq[0] ** 2 + qq[0] * qq[1] + qq[0] * qq[2] + qq[1] * qq[2] + qq[2] ** 2 + qq[0] ** 3
            + qq[0] ** 2 * qq[1] + qq[0] ** 4 + qq[0] ** 4 * qq[1] + qq[0] ** 5,
        }
        rep.check("(A.51) the six displayed rows c24..c19", all(p.coeff(j) == rows[j] for j in rows))

    rep.section("Numeric a(q) by back-substitution through the certified tails, and its consistency with the script (GF(2^64))")
    F = field64()
    R = FieldRing(F)
    if res is not None:
        keys_from_q = make_keys_from_q(res["tails"])
        compiled_a = [compile_f2poly(expr) for expr in res["a"]]
        rng = random.Random(2500)
        same = True
        for _ in range(2):
            Qv = [rng.getrandbits(64) for _ in range(25)]
            env = {f"q{i}": Qv[i] for i in range(24)}
            env["a24"] = Qv[24]
            same &= keys_from_q(Qv, R) == [eval_compiled(ca, env, R) for ca in compiled_a]
        rep.check("back-substituted a(q) equals the script's fully substituted keys at 2 random points", same)

        rep.section("Numeric round trip with the recurrence (A.52)")
        roundtrip(SPEC, lambda cc: decode_unit_pivots(SPEC, keys_from_q, cc, R), R, seed=25, count=3, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
