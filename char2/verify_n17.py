#!/usr/bin/env python3
"""Certificate for the degree-17 characteristic-2 circuit (9 products).

Circuit: "9 products, degree 17" of sections/appendix_polynomials.tex; the same
gate list is CIRCUITS[17] of website/js/char2.js.
Decoder: Lemma lem:char2-degree17-inverse -- normalized gate coordinates (A.8)
with the polynomial inverse (A.9)-(A.10), the coordinate change (A.11)-(A.12)
to z_1..z_17, and the seventeen row identities (A.13) whose pivots are unit
except the three Frobenius pivots z_3^2 (row 13), z_8^2 (row 9) and z_9^4
(row 8); hence a bijection over every perfect field of characteristic 2 (all
finite GF(2^k)).

Implementation: char2/verify_n17_uniform_symbolic.py (kept in place): its
``main()`` rebuilds the circuit from the z-coordinates in GF(2)[z_1..z_17]
(char2/symexpr.py) and expands all seventeen identities of (A.13) exactly.
The numeric decoder is char2/decode_n17_uniform.py (the same pivot loop with
2^t-th roots in the field).  This wrapper checks that the gate list printed
below agrees with that decoder's circuit and runs a GF(2^64) round trip.

Run from the repository root:  python3 -m char2.verify_n17
"""

from __future__ import annotations

import importlib
import random

from .decode_n17_uniform import decode_n17_coeffs, eval_n17
from .verify_common import (
    Circuit,
    FieldRing,
    G,
    Report,
    banner,
    eval_circuit,
    field64,
    print_circuit,
    roundtrip,
)

SPEC = Circuit(
    17,
    (
        G("y", ["x"], None, ["x"], 0),
        G("z", ["x"], 1, ["x", "y"], 2),
        G("t", ["y"], 3, ["x", "y"], 4),
        G("u", ["y", "z"], 5, ["z", "t"], 6),
        G("v", ["x", "z"], 7, ["x", "z", "t", "u"], 8),
        G("h", ["y"], 9, ["x"], None),
        G("j", ["y"], 10, ["x"], 11),
        G("l", ["t"], 12, ["h"], 13),
        G("w", ["x", "u"], 14, ["u", "v"], 15),
    ),
    (("j", "l", "w"), 16),
)

DECODER = """\
Decoder (Lemma lem:char2-degree17-inverse; P = x^17 + sum c_d x^d, [f]_i = [x^i] f):
  (A.8)  q0 = [y]_1, (q1,q2) = ([z]_2,[z]_1), (q3,q4) = ([t]_2,[t]_1), (q5,q6) = ([u]_4,[u]_3),
         (q7,q8) = ([v]_7,[v]_3), q9 = [h]_1, (q10,q11) = ([j]_2,[j]_1), (q12,q13) = ([l]_4,[l]_3),
         (q14,q15) = ([w]_10,[w]_7), q16 = a16
  (A.9)  a0 = q0; a1 = q1 + q0 + 1, a2 = q2 + (q0+1) a1; sigma = q3 + q0^2 + q0, a3 = q4 + q0 sigma, a4 = sigma + a3
  (A.10) for G = (A + alpha)(B + beta), A, B known and monic, deg A < deg B:
         alpha = [G]_{deg B} + [AB]_{deg B},  beta = [G]_{deg A} + [AB + alpha B]_{deg A}   (gates u, v, j, l, w); a9 = q9
  (A.11) s = q0 + q3, r = q5 + q7, e = q4 + q5^2 + q5
  (A.12) (z1..z17) = (q1, q2, s, r, q0, e, q14, q6, q5, q15, q8, q9, q12, q13, q10, q11, q16)
  (A.13) row d_i of P minus the same row of the circuit at z_i = .. = z_17 = 0 equals
           i : 1  2  3    4  5  6  7  8    9    10 11 12 13 14 15 16 17
         d_i : 16 15 13   14 12 11 10 9    8    7  6  5  4  3  2  1  0
         piv : z1 z2 z3^2 z4 z5 z6 z7 z8^2 z9^4 z10 ...            z17
  decoder: z_i = (c_{d_i} + [P_i]_{d_i})^(1/2^e_i) in the order i = 1..17, then (A.9)-(A.12).
  Three Frobenius pivots: unique roots over a perfect field (every finite GF(2^k))."""


def main() -> None:
    rep = Report(17)
    banner(
        17,
        "Circuit: '9 products, degree 17' of sections/appendix_polynomials.tex (= CIRCUITS[17] of website/js/char2.js).  "
        "Decoder: (A.8)-(A.13) of Lemma lem:char2-degree17-inverse; three Frobenius pivots (perfect fields).\n"
        "Implementation: char2/verify_n17_uniform_symbolic.py (symbolic), char2/decode_n17_uniform.py (numeric).",
    )
    rep.check("gate list matches the appendix display and char2.js CIRCUITS[17]", print_circuit(SPEC, "appendix '9 products, degree 17'", (5, 29)))
    print(DECODER)

    rep.section("char2/verify_n17_uniform_symbolic.py: exact identities (A.13) in GF(2)[z1,...,z17]")
    mod = importlib.import_module("char2.verify_n17_uniform_symbolic")
    rep.run("all seventeen triangular identities (A.13) with the pivot exponents 1,1,2,1,1,1,1,2,4,1,...,1 and the gate-by-gate inverse (A.9)-(A.10)", mod.main)

    rep.section("Consistency of this gate list with char2/decode_n17_uniform.py, and numeric round trip")
    F = field64()
    R = FieldRing(F)
    rng = random.Random(1700)
    same = True
    for _ in range(5):
        keys = [rng.getrandbits(64) for _ in range(17)]
        same &= eval_circuit(SPEC, keys, R) == eval_n17(keys, F=F)
    rep.check("the circuit printed above equals decode_n17_uniform.eval_n17 at 5 random key vectors", same)
    roundtrip(SPEC, lambda cc: decode_n17_coeffs(cc, F=F), R, seed=17, count=20, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
