#!/usr/bin/env python3
"""Certificate for the degree-15 characteristic-2 circuit (8 products).

Circuit: "8 products, degree 15" of sections/appendix_polynomials.tex (the
square-first circuit y = x^2, ..., P = w + s + r + a14); the same gate list is
CIRCUITS[15] of website/js/char2.js.  (char2/decode_n15_fastpoly.py and
char2/test_n15_uniform_symbolic.py concern an earlier, different degree-15
circuit that is not displayed in the paper.)
Decoder: Lemma lem:char2-degree15-inverse -- the linear coordinates (A.1)/(A.2),
the baselines (A.3) and the fifteen unit pivots (A.4) with pivot table (A.5);
the decoder is the descending recurrence (A.7).  No root is taken: valid over
every field of characteristic 2.

Implementation: char2/verify_n15_unitriangular_symbolic.py (kept in place).
Importing it runs the exact certificate in GF(2)[q_0..q_14][x] (all fifteen
identities of (A.4), gate degrees, XOR count, height); its ``main()`` adds the
exhaustive GF(2) diagnostic.  This wrapper checks that the gate list printed
below and the coordinates (A.2) agree numerically with that script's symbolic
circuit and inverse, then runs a GF(2^64) round trip with the recurrence (A.7).

Run from the repository root:  python3 -m char2.verify_n15
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
    15,
    (
        G("y", ["x"], None, ["x"], None),
        G("z", ["y"], 0, ["x", "y"], 1),
        G("t", ["x"], 2, ["z"], 3),
        G("u", ["y", "t"], 4, ["z", "t"], 5),
        G("v", ["x", "z"], 6, ["z"], 7),
        G("w", ["x", "y", "z"], 8, ["y", "v"], 9),
        G("s", ["z"], 10, ["v"], 11),
        G("r", ["t"], 12, ["u"], 13),
    ),
    (("w", "s", "r"), 14),
)

DECODER = """\
Decoder (Lemma lem:char2-degree15-inverse; P = x^15 + sum c_j x^j):
  (A.1)/(A.2) linear coordinates, inverse a(q):
      a0 = q2, a1 = q1 + q2, a2 = q0, a3 = q3, a4 = q4 + q5 + q7, a5 = q5, a6 = q8 + q11, a7 = q11,
      a8 = q6 + q12 + q13, a9 = q13, a10 = q12 + q13, a11 = q10 + q13, a12 = q7, a13 = q9, a14 = q14
  (A.3) K_i(q_0..q_{i-1}) = [x^{14-i}] P(a(q_0, .., q_{i-1}, 0, .., 0))
  (A.4) c_{14-i} = q_i + K_i(q_0..q_{i-1}),  0 <= i <= 14;  pivot table (A.5): row 14-i carries q_i
        (branches r, r, r, r, r, r, w+s, r, w+s, r, w+s, w+s, w+s, w+s, out)
  (A.7) decoder: q_i = c_{14-i} + K_i(q_0..q_{i-1}) for i = 0..14, then a = a(q).
  Unit pivots only: valid over every field of characteristic 2."""


def keys_from_q(Q, R):
    add = R.add
    return [
        Q[2],
        add(Q[1], Q[2]),
        Q[0],
        Q[3],
        add(add(Q[4], Q[5]), Q[7]),
        Q[5],
        add(Q[8], Q[11]),
        Q[11],
        add(add(Q[6], Q[12]), Q[13]),
        Q[13],
        add(Q[12], Q[13]),
        add(Q[10], Q[13]),
        Q[7],
        Q[9],
        Q[14],
    ]


def decode15(c, R):
    return decode_unit_pivots(SPEC, keys_from_q, c, R)


def main() -> None:
    rep = Report(15)
    banner(
        15,
        "Circuit: '8 products, degree 15' of sections/appendix_polynomials.tex (= CIRCUITS[15] of website/js/char2.js).  "
        "Decoder: unitriangular certificate (A.1)-(A.7) of Lemma lem:char2-degree15-inverse, unit pivots only.\n"
        "Implementation: char2/verify_n15_unitriangular_symbolic.py.",
    )
    rep.check("gate list matches the appendix display and char2.js CIRCUITS[15]", print_circuit(SPEC, "appendix '8 products, degree 15'", (5, 24)))
    print(DECODER)

    rep.section("char2/verify_n15_unitriangular_symbolic.py: exact certificate in GF(2)[q0,...,q14][x] (runs at import), then main()")
    holder: dict = {}

    def load() -> None:
        holder["mod"] = importlib.import_module("char2.verify_n15_unitriangular_symbolic")

    rep.run("module-level certificate: coordinate inverse, gate degrees, all fifteen unit pivots (A.4), 24 XORs, height 5", load)
    mod = holder.get("mod")
    if mod is not None:
        print("    gate degrees 2, 4, 5, 10, 8, 12, 12, 15; products 8; polynomial XORs 24; height 5 (asserted by the script)")
        print("    K_i monomial counts:", mod.term_counts)

        def exhaustive() -> None:  # the script's __main__ diagnostic (not the proof)
            images = {mod.evaluate_over_gf2(key_word) & ((1 << 15) - 1) for key_word in range(1 << 15)}
            assert len(images) == 1 << 15

        rep.run("exhaustive GF(2) diagnostic of the script: 2^15 key words give 2^15 distinct coefficient vectors", exhaustive)

    rep.section("Consistency of this gate list and a(q) with the symbolic script (numeric, GF(2^64))")
    F = field64()
    R = FieldRing(F)
    if mod is not None:
        rng = random.Random(1500)
        same_keys = same_coeffs = True
        for _ in range(5):
            Q = [rng.getrandbits(64) for _ in range(15)]
            keys = keys_from_q(Q, R)
            same_keys &= keys == [eval_mpoly(mod.a[i], Q, R) for i in range(15)]
            same_coeffs &= eval_circuit(SPEC, keys, R) == [eval_mpoly(mod.c[j], Q, R) for j in range(16)]
        rep.check("a(q) of (A.2) equals the script's inverse at 5 random points", same_keys)
        rep.check("the circuit printed above equals the script's symbolic P at 5 random points", same_coeffs)

    rep.section("Numeric round trip with the recurrence (A.7)")
    roundtrip(SPEC, lambda cc: decode15(cc, R), R, seed=15, count=50, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
