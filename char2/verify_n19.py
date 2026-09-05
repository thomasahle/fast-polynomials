#!/usr/bin/env python3
"""Certificate for the degree-19 characteristic-2 circuit (10 products).

Circuit: "10 products, degree 19" of sections/appendix_polynomials.tex; the
same gate list is CIRCUITS[19] of website/js/char2.js.
Decoder: Lemma lem:char2-degree19-inverse -- polynomial coordinates (A.15) with
inverse (A.16); the cubic-shell structure P = S C + r + a18 with the fixed top
signature (A.19) of C, the shell top (A.20), monic division by S, the thirteen
inner unit pivots (A.22)/(A.23) and the low tail (A.25).  Flattened, this is
the descending unit-pivot recurrence q_i = c_{18-i} + K_i(q_0..q_{i-1}) on the
rows of P, which is what the symbolic script certifies for all nineteen rows.
No root is taken: valid over every field of characteristic 2.

Implementation: char2/verify_n19_unitriangular_symbolic.py (kept in place).
Importing it runs the exact certificate in GF(2)[q_0..q_18][x]: the
coordinate inverse, the gate degrees, the signature (A.19), the thirteen
inner identities (A.22) and the nineteen row identities; its ``main()`` adds
the exhaustive GF(2) diagnostic.  This wrapper checks the displayed rows
(A.20), that the gate list and (A.16) agree numerically with the script, and
runs a GF(2^64) round trip.

Run from the repository root:  python3 -m char2.verify_n19
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
    19,
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
    ),
    (("r", "l"), 18),
)

DECODER = """\
Decoder (Lemma lem:char2-degree19-inverse; P = x^19 + sum c_j x^j):
  (A.16) a0 = q5, a1 = q4 + q5, a2 = q3, a3 = q8, a4 = q12 + q14, a5 = q14, a6 = q9, a7 = q6 + q8 + q9,
         a8 = q13, a9 = q11 + q12 + q14, a10 = q0, a11 = q1, a12 = q16, a13 = q17, a14 = q10 + q12,
         a15 = q7 + q10 + q12 + q13 + q8^2 + q8, a16 = q2, a17 = q15, a18 = q18
  (A.17) S = s + a16 = x^3 + q0 x^2 + q1 x + (q0 q1 + q2),  C = u + w + q + a17,  P = S C + r + a18
  (A.19) [C]_16 = 1, [C]_15 = [C]_14 = 0, [C]_13 = 1 (cubic-shell invariant)
  (A.20) q0 = c18,  q1 = c17,  q2 = c16 + q0 q1 + 1;  then rows 19..3 of P are those of S C:
         monic division by S recovers C
  (A.22) [C]_{15-i} = q_i + B_i(q_0..q_{i-1}), 3 <= i <= 15  (pivot table (A.23): C-row 15-i carries q_i)
  (A.25) P + S C = r + a18 = x^3 + q16 x^2 + q17 x + (q16 q17 + q18): rows 2, 1, 0 give q16, q17, q18
  flattened form (certified for all nineteen rows of P): q_i = c_{18-i} + K_i(q_0..q_{i-1}), i = 0..18,
         K_i = [x^{18-i}] P(a(q_0..q_{i-1}, 0, .., 0));  then a = a(q).
  Unit pivots only: valid over every field of characteristic 2."""


def keys_from_q(Q, R):
    def s(*xs):
        out = R.zero
        for x in xs:
            out = R.add(out, x)
        return out

    return [
        Q[5],
        s(Q[4], Q[5]),
        Q[3],
        Q[8],
        s(Q[12], Q[14]),
        Q[14],
        Q[9],
        s(Q[6], Q[8], Q[9]),
        Q[13],
        s(Q[11], Q[12], Q[14]),
        Q[0],
        Q[1],
        Q[16],
        Q[17],
        s(Q[10], Q[12]),
        s(Q[7], Q[10], Q[12], Q[13], R.mul(Q[8], Q[8]), Q[8]),
        Q[2],
        Q[15],
        Q[18],
    ]


def decode19(c, R):
    return decode_unit_pivots(SPEC, keys_from_q, c, R)


def main() -> None:
    rep = Report(19)
    banner(
        19,
        "Circuit: '10 products, degree 19' of sections/appendix_polynomials.tex (= CIRCUITS[19] of website/js/char2.js).  "
        "Decoder: (A.15)-(A.25) of Lemma lem:char2-degree19-inverse, unit pivots only.\n"
        "Implementation: char2/verify_n19_unitriangular_symbolic.py.",
    )
    rep.check("gate list matches the appendix display and char2.js CIRCUITS[19]", print_circuit(SPEC, "appendix '10 products, degree 19'", (5, 31)))
    print(DECODER)

    rep.section("char2/verify_n19_unitriangular_symbolic.py: exact certificate in GF(2)[q0,...,q18][x] (runs at import), then main()")
    holder: dict = {}

    def load() -> None:
        holder["mod"] = importlib.import_module("char2.verify_n19_unitriangular_symbolic")

    rep.run("module-level certificate: inverse (A.16), gate degrees, signature (A.19), inner pivots (A.22), all nineteen row pivots, 31 XORs, height 5", load)
    mod = holder.get("mod")
    if mod is not None:
        Q, c, ONE = mod.Q, mod.c, mod.ONE
        rep.check("(A.20) c18 = q0, c17 = q1, c16 = q2 + q0 q1 + 1", c[18] == Q[0] and c[17] == Q[1] and c[16] == Q[2] + Q[0] * Q[1] + ONE)
        rep.run("main(): report and exhaustive GF(2) diagnostic (2^18 key words)", mod.main)
        print("    K_i monomial counts:", mod.term_counts)

    rep.section("Consistency of this gate list and a(q) with the symbolic script (numeric, GF(2^64))")
    F = field64()
    R = FieldRing(F)
    if mod is not None:
        rng = random.Random(1900)
        same_keys = same_coeffs = True
        for _ in range(5):
            Qv = [rng.getrandbits(64) for _ in range(19)]
            keys = keys_from_q(Qv, R)
            same_keys &= keys == [eval_mpoly(mod.a[i], Qv, R) for i in range(19)]
            same_coeffs &= eval_circuit(SPEC, keys, R) == [eval_mpoly(mod.c[j], Qv, R) for j in range(20)]
        rep.check("a(q) of (A.16) equals the script's inverse at 5 random points", same_keys)
        rep.check("the circuit printed above equals the script's symbolic P at 5 random points", same_coeffs)

    rep.section("Numeric round trip with the flattened recurrence")
    roundtrip(SPEC, lambda cc: decode19(cc, R), R, seed=19, count=20, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
