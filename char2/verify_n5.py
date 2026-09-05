#!/usr/bin/env python3
"""Certificate for the degree-5 characteristic-2 circuit (3 products): the ChainHash finalizer.

Circuit: eq:ph:chain5 of sections/appendix_chainhash.tex (Lemma lem:ph:chain,
``chx_finalize<5>`` of the ChainHash implementation); the same gate list is
CIRCUITS[5] of website/js/char2.js (the universal square-first head y, z, t of
the certified degree-15/19/21 family).
Decoder: eq:ph:chain5-q/cq (linear coordinates), eq:ph:chain5-rows (five unit
pivots) and eq:ph:chain5-decoder; no root is taken, so the coefficient map is a
polynomial bijection over every field of characteristic 2.

Implementation: tools/bench/chainhash/verify5.py (kept in place, executed here
by path).  It expands the circuit over GF(2)[c_0..c_4][X] with sympy, checks the
coefficient table, the coordinate change and its inverse, the row table with
its unit pivots, decode(rows(q)) = q in GF(2)[q_0..q_4] and rows(decode(e)) = e
in GF(2)[e_0..e_4], then a GF(2^64) round trip (seed 1, 2000 x 3) and
exhaustive runs over GF(2), GF(4), GF(8).  This wrapper reads every verdict it
prints, and adds a second GF(2^64) round trip that evaluates the gate list
printed below and inverts it with verify5.py's ``decode``.

Run from the repository root:  python3 -m char2.verify_n5
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
    field64,
    indent,
    print_circuit,
    roundtrip,
    run_script_by_path,
)

SCRIPT = REPO / "tools" / "bench" / "chainhash" / "verify5.py"

SPEC = Circuit(
    5,
    (
        G("y", ["x"], None, ["x"], None),
        G("z", ["y"], 0, ["x", "y"], 1),
        G("t", ["x"], 2, ["z"], 3),
    ),
    (("t",), 4),
    keyname="c",
)

DECODER = """\
Decoder (Lemma lem:ph:chain, f_c = X^5 + sum e_i X^i):
  eq:ph:chain5-q   q(c) = (c2, c0 + c1, c0, c3, c4);   eq:ph:chain5-cq  c(q) = (q2, q1 + q2, q0, q3, q4)
  eq:ph:chain5-rows  e4 = q0 + 1,  e3 = q1 + q0,  e2 = q2 + q0 q1,
                     e1 = q3 + delta + q0 q2,  e0 = q4 + q0 (delta + q3),  delta = q2 (q1 + q2)
  eq:ph:chain5-decoder  q0 = e4 + 1,  q1 = e3 + q0,  q2 = e2 + q0 q1,
                        q3 = e1 + delta + q0 q2,  q4 = e0 + q0 (delta + q3),  then c = c(q)
  Every pivot is the identity: no Frobenius root, valid over every field of characteristic 2."""


def main() -> None:
    rep = Report(5)
    banner(
        5,
        "Circuit: eq:ph:chain5 of sections/appendix_chainhash.tex (ChainHash finalizer chx_finalize<5>; "
        "= CIRCUITS[5] of website/js/char2.js).  Decoder: eq:ph:chain5-decoder, unit pivots only.\n"
        f"Implementation: {SCRIPT.relative_to(REPO)} (executed by path).",
    )
    print_circuit(SPEC, "appendix_chainhash.tex eq:ph:chain5", output_name="f_c")
    print(DECODER)

    rep.section("tools/bench/chainhash/verify5.py (sympy over GF(2)[c][X], GF(2)[q], GF(2)[e]; own GF(2^64) round trip; exhaustive GF(2), GF(4), GF(8))")
    holder: dict = {}

    def run_script() -> None:
        holder["ns"], holder["text"] = run_script_by_path(SCRIPT)

    rep.run("verify5.py ran to completion", run_script)
    text = holder.get("text", "")
    print(indent(text))
    problems = audit_chainhash_output(text)
    rep.check("verify5.py: coefficient table, coordinate change, row table, unit pivots, both compositions, round trips all clean", not problems, "; ".join(problems))
    rep.check("verify5.py: circuit is monic of degree 5", "degree of f: 5  e5 = 1" in text)

    rep.section("Numeric round trip: gate list above evaluated here, inverted by verify5.py's decode")
    if "ns" in holder:
        F = field64()
        R = FieldRing(F)
        decode = holder["ns"]["decode"]
        roundtrip(SPEC, lambda cc: decode(list(cc), F.mul), R, seed=5, count=2000, report=rep)
    rep.finish()


if __name__ == "__main__":
    main()
