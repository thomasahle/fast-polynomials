#!/usr/bin/env python3
"""Certificate for the degree-21 characteristic-2 circuit (11 products).

Circuit: "11 products, degree 21" of sections/appendix_polynomials.tex; the
same gate list is CIRCUITS[21] of website/js/char2.js.
Decoder: Lemma lem:char2-degree21-inverse -- polynomial coordinates
(A.26)-(A.27) with inverse (A.28)-(A.29), baselines (A.30), the twenty-one unit
pivots (A.31) with the pivot table (A.33) (row 20-i carries q_i), and the
descending recurrence (A.34).  No root is taken: valid over every field of
characteristic 2.

Implementation: char2/verify_n21_unitriangular_symbolic.py (kept in place).
Importing it runs the exact certificate in GF(2)[q_0..q_20][x]: the coordinate
inverse, the gate degrees, all twenty-one identities (A.31), the eight
displayed rows (A.32), 39 XORs and height 5; its ``main()`` adds the exhaustive
GF(2) diagnostic.  This wrapper checks that the gate list and (A.28)-(A.29)
agree numerically with the script and runs a GF(2^64) round trip with (A.34).

Run from the repository root:  python3 -m char2.verify_n21
"""

from __future__ import annotations

import importlib
import random

from .verify_common import (
    Circuit,
    FieldRing,
    G,
    Report,
    banner,
    decode_unit_pivots,
    eval_circuit,
    eval_mpoly,
    field64,
    print_circuit,
    roundtrip,
)

SPEC = Circuit(
    21,
    (
        G("y", ["x"], None, ["x"], None),
        G("z", ["y"], 0, ["x", "y"], 1),
        G("t", ["x"], 2, ["z"], 3),
        G("u", ["y", "t"], 4, ["z", "t"], 5),
        G("v", ["x", "z"], 6, ["z"], 7),
        G("w", ["x", "y", "z"], 8, ["y", "v"], 9),
        G("s", ["x"], 10, ["y"], 11),
        G("r", ["x"], 12, ["y"], 13),
        G("q", ["v"], 14, ["t", "v", "s"], 15),
        G("l", ["s"], 16, ["u", "w", "q"], 17),
        G("m", ["t", "s"], 18, ["z", "u", "w", "q"], 19),
    ),
    (("m", "z", "r", "l"), 20),
)

DECODER = """\
Decoder (Lemma lem:char2-degree21-inverse; P = x^21 + sum c_j x^j):
  (A.28) a0 = q2, a1 = q1 + q2, a2 = q0, a3 = q3, a4 = q12 + q14, a5 = q14, a6 = q9, a7 = q6 + q8 + q3 + q9,
         a8 = q13, a9 = q11 + q12 + q14, a10 = q5, a11 = q8, a12 = q18, a13 = q19, a14 = q10 + q12,
         a16 = q4 + q16, a17 = q17, a18 = q16, a19 = q15, a20 = q20
  (A.29) a15 = q7 + q8 + q8^2 + q0 q8 + q5 q8 + q10 + q12 + q13 + q3^2 + q3
  (A.30) K_i(q_0..q_{i-1}) = [x^{20-i}] P(a(q_0, .., q_{i-1}, 0, .., 0))
  (A.31) c_{20-i} = q_i + K_i(q_0..q_{i-1}),  0 <= i <= 20   (pivot table (A.33): row 20-i carries q_i)
  (A.34) decoder: q_i = c_{20-i} + K_i(q_0..q_{i-1}) for i = 0..20, then a = a(q) by (A.28)-(A.29).
  Unit pivots only: valid over every field of characteristic 2."""


def keys_from_q(Q, R):
    m = R.mul

    def s(*xs):
        out = R.zero
        for x in xs:
            out = R.add(out, x)
        return out

    return [
        Q[2],
        s(Q[1], Q[2]),
        Q[0],
        Q[3],
        s(Q[12], Q[14]),
        Q[14],
        Q[9],
        s(Q[6], Q[8], Q[3], Q[9]),
        Q[13],
        s(Q[11], Q[12], Q[14]),
        Q[5],
        Q[8],
        Q[18],
        Q[19],
        s(Q[10], Q[12]),
        s(Q[7], Q[8], m(Q[8], Q[8]), m(Q[0], Q[8]), m(Q[5], Q[8]), Q[10], Q[12], Q[13], m(Q[3], Q[3]), Q[3]),
        s(Q[4], Q[16]),
        Q[17],
        Q[16],
        Q[15],
        Q[20],
    ]


def decode21(c, R):
    return decode_unit_pivots(SPEC, keys_from_q, c, R)


def main() -> None:
    rep = Report(21)
    banner(
        21,
        "Circuit: '11 products, degree 21' of sections/appendix_polynomials.tex (= CIRCUITS[21] of website/js/char2.js).  "
        "Decoder: (A.26)-(A.34) of Lemma lem:char2-degree21-inverse, unit pivots only.\n"
        "Implementation: char2/verify_n21_unitriangular_symbolic.py.",
    )
    rep.check("gate list matches the appendix display and char2.js CIRCUITS[21]", print_circuit(SPEC, "appendix '11 products, degree 21'", (5, 39)))
    print(DECODER)

    rep.section("char2/verify_n21_unitriangular_symbolic.py: exact certificate in GF(2)[q0,...,q20][x] (runs at import), then main()")
    holder: dict = {}

    def load() -> None:
        holder["mod"] = importlib.import_module("char2.verify_n21_unitriangular_symbolic")

    rep.run("module-level certificate: inverse (A.28)-(A.29), gate degrees, all twenty-one unit pivots (A.31), displayed rows (A.32), 39 XORs, height 5", load)
    mod = holder.get("mod")
    if mod is not None:
        rep.run("main(): report and exhaustive GF(2) diagnostic (2^20 key words)", mod.main)
        print("    K_i monomial counts:", mod.term_counts)

    rep.section("Consistency of this gate list and a(q) with the symbolic script (numeric, GF(2^64))")
    F = field64()
    R = FieldRing(F)
    if mod is not None:
        rng = random.Random(2100)
        same_keys = same_coeffs = True
        for _ in range(5):
            Qv = [rng.getrandbits(64) for _ in range(21)]
            keys = keys_from_q(Qv, R)
            same_keys &= keys == [eval_mpoly(mod.a[i], Qv, R) for i in range(21)]
            same_coeffs &= eval_circuit(SPEC, keys, R) == [eval_mpoly(mod.c[j], Qv, R) for j in range(22)]
        rep.check("a(q) of (A.28)-(A.29) equals the script's inverse at 5 random points", same_keys)
        rep.check("the circuit printed above equals the script's symbolic P at 5 random points", same_coeffs)

    rep.section("Numeric round trip with the recurrence (A.34)")
    roundtrip(SPEC, lambda cc: decode21(cc, R), R, seed=21, count=20, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
