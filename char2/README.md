# char2 experiments

## Certificate scripts (one per characteristic-2 construction)

Every circuit of the paper's characteristic-2 lane has one certificate script
`char2/verify_n<k>.py`, k = 5, 7, ..., 25, with the same interface: run from
the repository root as `python3 -m char2.verify_n<k>` (no arguments).  Each
prints the gate list it certifies (and which display it is), the explicit
decoder, the symbolic certificate (decode(encode(a)) = a over GF(2)[keys]
and/or the unit-pivot table, exact polynomial identities, never a
finite-field or Jacobian test), then a numeric GF(2^64) round trip
(modulus x^64+x^4+x^3+x+1) with a stated seed and count in both directions,
and ends with a single line `PASS n=<k>` or `FAIL n=<k>: ...` (exit code
0/1).  Shared plumbing (the field, a ring adapter that runs the same decoder
symbolically and numerically, the gate-list evaluator, the generic top-down
unit-pivot decoder `q_i = c_row(i) + K_i(q_0..q_{i-1})`) lives in
`char2/verify_common.py`.  The older symbolic scripts remain the
implementation and are imported by the wrappers.

| degree | script | circuit source | what is certified | runtime |
|---|---|---|---|---|
| 5 | `verify_n5.py` (runs `tools/bench/chainhash/verify5.py` by path) | `appendix_chainhash.tex` eq:ph:chain5, the ChainHash finalizer `chx_finalize<5>`; = website `CIRCUITS[5]` | coefficient table over F2[c][X]; coordinate change q(c)/c(q); five unit-pivot rows; decode∘rows = id in F2[q], rows∘decode = id in F2[e]; exhaustive GF(2), GF(4), GF(8); GF(2^64) round trips (verify5.py: seed 1, 2000×3; wrapper: seed 5, 2000+2000 through the printed gate list). Every characteristic-2 field. | 1.4 s |
| 7 | `verify_n7.py` (part A runs `tools/bench/chainhash/verify7.py` by path; part B is self-contained sympy) | A: `septic7_64`, the former degree-7 finalizer (`experiments.tex`, k = 7 row; = website `CIRCUITS[7]`), t = z(z+c3). B: the "4 products, degree 7" display of `appendix_polynomials.tex`, t = (x+y+z+a3)(x+y+z), Lemma `lem:first-char2-circuit-inverse` | A: coefficient table, q(c)/c(q), row table with Frobenius pivots q1², q3², decoder∘rows = id in F2[q]; exhaustive GF(2), GF(4), GF(8); GF(2^64) (seed 1, 2000×3; seed 7, 2000+2000). B: coefficient table p6..p0, the two displayed expansions, decode∘encode = id in F2[a0..a6] with b, c as Frobenius pivots; GF(2^64) seed 7, 2000+2000. Perfect fields. | 35 s (the exhaustive GF(8) run of verify7.py) |
| 9 | `verify_n9.py` | (A.0) degree-9 row of `appendix_polynomials.tex`; = website `CIRCUITS[9]`, `worked_examples._eval_n9` | (9.1)-(9.3) as identities in F2[a0..a8]; decode∘encode = id in F2[a]; encode∘decode = id in F2[c0..c8]; GF(2^64) seed 9, 500+500. Every characteristic-2 field. | 0.8 s |
| 11 | `verify_n11.py` | (A.0) degree-11 row of `appendix_polynomials.tex` (**not** website `CIRCUITS[11]`, which is a different circuit) | rows (11.1), the two squares behind (11.2), the a6 baseline pivot, identity (11.3), pivots (11.4), decode∘encode = id in F2[a0..a10] with the roots as Frobenius pivots; GF(2^64) seed 11, 500+500. Perfect fields. | 2.1 s |
| 13 | `verify_n13.py` | (A.0) degree-13 row of `appendix_polynomials.tex`; = website `CIRCUITS[13]`, `worked_examples._eval_n13` (`decode_n13.py` is its closed-form GF(4) decoder) | thirteen unit pivots (13.4) in F2[q0..q12], the three displayed rows, (13.1) and its inverse, (13.6) and its instantiation (R, S, A, B, E), decode∘encode = id in F2[q] with the generic baseline decoder; GF(2^64) seed 13, 200+200. Every characteristic-2 field. | 2.4 s |
| 15 | `verify_n15.py` (implementation `verify_n15_unitriangular_symbolic.py`) | "8 products, degree 15"; = website `CIRCUITS[15]` (`decode_n15_fastpoly.py` / `test_n15_uniform_symbolic.py` concern an earlier circuit that is not displayed) | inverse (A.2), fifteen unit pivots (A.4) in F2[q0..q14][x], 24 XORs, height 5, exhaustive GF(2) diagnostic; the printed gate list and a(q) agree numerically with the script's symbolic circuit; GF(2^64) seed 15, 50+50 with the recurrence (A.7). Every characteristic-2 field. | 1.5 s |
| 17 | `verify_n17.py` (implementation `verify_n17_uniform_symbolic.py`; numeric decoder `decode_n17_uniform.py`) | "9 products, degree 17"; = website `CIRCUITS[17]` | all seventeen identities (A.13) in F2[z1..z17] with pivot exponents 1,1,2,1,1,1,1,2,4,1,...; gate-by-gate inverse (A.9)-(A.10); the printed gate list equals `eval_n17`; GF(2^64) seed 17, 20+20. Perfect fields. | 1.6 s |
| 19 | `verify_n19.py` (implementation `verify_n19_unitriangular_symbolic.py`) | "10 products, degree 19"; = website `CIRCUITS[19]` | inverse (A.16), signature (A.19), inner pivots (A.22), all nineteen row pivots in F2[q0..q18][x], displayed rows (A.20), 31 XORs, height 5, exhaustive GF(2) (2^18); numeric consistency with the script; GF(2^64) seed 19, 20+20. Every characteristic-2 field. | 2.4 s |
| 21 | `verify_n21.py` (implementation `verify_n21_unitriangular_symbolic.py`) | "11 products, degree 21"; = website `CIRCUITS[21]` | inverse (A.28)-(A.29), twenty-one unit pivots (A.31), displayed rows (A.32), 39 XORs, height 5, exhaustive GF(2) (2^20); numeric consistency; GF(2^64) seed 21, 20+20 with (A.34). Every characteristic-2 field. | 8.3 s |
| 23 | `verify_n23.py` (implementation `verify_n23_unitriangular_symbolic.py`, `certify()`) | "12 products, degree 23"; = website `CIRCUITS[23]` (its wire n is our f) | inverse (A.37)-(A.38) by substitution, eighteen unit pivots (rows 22..5, c8 = q14), block (A.43)/(A.44), q22 in row 0, displayed rows (A.41); numeric consistency; GF(2^64) seed 23, 10+10 with the decoder (A.45) transcribed literally. Every characteristic-2 field. | 1.8 s |
| 25 | `verify_n25.py` (implementation `verify_n25_unitriangular_symbolic.py`, `certify()`) | "13 products, degree 25"; = website `CIRCUITS[25]` (its wires h, j, n are our d, k, f) | the 24 elementary substitutions in F2[a0..a24][x] (slope-1 rows, tails free of the pivot, all 24 identities (A.50), a24 in row 0), pivot order (A.46), the seventeen displayed tails (A.49), the long-tail monomial counts 71, ..., 4652 and their later keys, displayed rows (A.51); a(q) by back-substitution through the tails equals the script's; GF(2^64) seed 25, 3+3 with (A.52). Every characteristic-2 field. | 13.6 s |

Runtimes: Apple M2 Pro, Python 3.14, sympy 1.14, one process each.
Cross-check notes: the degree-7 and degree-11 gate lists of `website/js/char2.js`
are not the ones `appendix_polynomials.tex` displays (degree 7: the website and
`verify7.py` use t = z(z+c3), the appendix t = (x+y+z+a3)(x+y+z), both certified
in `verify_n7.py`; degree 11: the website carries a different square-first
circuit, only the appendix (A.0) row is certified here).  All other degrees
match the appendix and the website gate for gate.


Scratchpad for **characteristic 2** constructions aiming for the exact `⌊n/2⌋+1` multiplication bound.

## Current proof frontier

Section 70 of `better_bounds/char2_static_patterns.md` gives a closed
degree-by-degree common-constant pair recurrence: degree `d` carries `2d-2`
coordinates in `d-1` products, with a root-free inverse by one boundary pivot
and monic division.  Its exact generic degree-six identity audit is:

- `python3 -B char2/verify_common_constant_pair.py`

The remaining endpoint is one boundary coordinate: converting this joint
state into the punctured Artin--Schreier pair must expose the deferred common
constant as a variable leading coefficient.

The constrained two-crown endpoint considered in Section 71 is explicitly
noninjective.  Its exact symbolic expansion and `D=4` collision certificate
are checked by:

- `python3 -B char2/audit_constrained_two_crown_cell.py`

Section 63 of `better_bounds/char2_static_patterns.md` gives a second closed
dyadic object: a globally decodable three-surface state of degree `D` with
`D-1` coordinates in `D/2` products.  Its doubling step has an exact
monic-division decoder and linear addition count.  The identity-level audit
of the generic `D=8 -> 16` step is:

- `python3 -B char2/verify_state63_transition.py`

This still is not a single-output family.  The literal one-product cap and
the small affine-mask cap classes are noninjective already at `D=8`; the
remaining problem is a genuinely nonlinear lossless cap, followed by
non-dyadic transport.

Section 55 of `better_bounds/char2_static_patterns.md` now gives a closed,
field-uniform dyadic **joint carrier** recursion.  A degree-`D` pair with
`D-2` coordinates in `D/2` products is doubled by absorbing a monic
zero-constant peeled `Q_{D-1}` into one factor; monic division and one unit
coefficient pivot recover every old and fresh coordinate.  The construction
has `5D/4+4 log_2(D)-8` polynomial XORs and height `log_2 D`.

This is not yet the requested single-output `(2n-1,n)` family.  The remaining
proof problem is a lossless cap from the joint carrier (followed by a
non-dyadic transport).  The obvious one-product affine cap is already false at
the first recursive level, so it is not listed below as a candidate.

## How to run

- Exhaustive GF(4) bijection tests for a candidate family live in the scripts here (see `search_n9.py` etc).
- The worked examples from the prompt (n=9 and n=11) are checked in `worked_examples.py`:
  - `python3 -B -m char2.worked_examples`
  - Also includes an n=13 worked example: `python3 -B -m char2.worked_examples --n 13`
- Explicit decoder (coeffs -> params) for the n=13 example over GF(4):
  - `python3 -B -m char2.decode_n13`

- Symbolic proof checks for the identities baked into the `n=63` top-window decoder:
  - `python3 -B -m char2.test_mersenne_identities`
  - `python3 -B -m char2.test_mersenne_identities_v2`
- Deterministically print the same identities (from the circuit description, no search):
  - `python3 -B -m char2.derive_mersenne_identities`
- Symbolic proof checks for the anchored-doubling lemmas and ladder top-window propagation:
  - `python3 -B -m char2.test_anchor_lemmas`
  - `python3 -B -m char2.test_ladder_topwindow`
- GF(4) sanity for the proof-driven stage decoders:
  - `python3 -B -m char2.test_mersenne_decoder_n31`
  - `python3 -B -m char2.test_mersenne_decoder_n63_v2`

- Degree-15 / 8-multiplication circuit (the search harness remains useful for
  diagnostics):
  - `python3 -B -m char2.try_n15 --only "fast_poly found" --samples 200000 --seed 0`
- Explicit, search-free decoder over arbitrary finite binary extensions.  Its
  only non-unit pivot is one inverse Frobenius square; the runner checks the
  transcription over GF(2), GF(4), GF(8), GF(16), and GF(256):
  - `python3 -B -m char2.decode_n15_fastpoly`
- Exact symbolic checks of the decoder's displayed pivots in
  `F2[a0,...,a14]` (not a finite-field search):
  - `python3 -B -m char2.test_n15_uniform_symbolic`
- Explicit decoder for the uniform degree-17 / 9-multiplication circuit:
  - `python3 -B -m char2.decode_n17_uniform`
- Exact polynomial-ring audit of all seventeen degree-17 pivots (not a
  finite-field or Jacobian test):
  - `python3 -B -m char2.verify_n17_uniform_symbolic`
- Exact unitriangular audit of the square-first degree-15 alternative.  This
  proves a polynomial inverse over every characteristic-two field (the bundled
  exhaustive `F_2` run is only a diagnostic):
  - `python3 -B -m char2.verify_n15_unitriangular_symbolic`

- Exact unitriangular audit of the square-first degree-19 circuit (ten
  products, 31 polynomial XORs, height five), including its polynomial change
  of coordinates and an independent exhaustive `F_2` diagnostic:

  - `python3 -B -m char2.verify_n19_unitriangular_symbolic`
- Exact unitriangular audit of the square-first degree-21 circuit (eleven
  products, 39 polynomial XORs, height five).  The symbolic identities prove
  a polynomial inverse over every characteristic-two field; the exhaustive
  `F_2` pass remains only an independent diagnostic:

  - `python3 -B -m char2.verify_n21_unitriangular_symbolic`
- Exact rejection of the natural degree-23 third-rung continuation over
  `GF(4)`: the script evaluates the formal coefficient Jacobian at a fixed
  explicit key and verifies rank `22` (so this is a valid disproof of that
  candidate, although Jacobian rank could never prove a survivor):

  - `python3 -B -m char2.audit_n23_alternate_tag7_gf4`
- Rejection audits for the tempting post-`n=21` and normalized-pair caps:
  the quartic-tag lift has binary full-rank candidates but an explicit
  rank-22 `GF(4)` witness; the keyed Artin--Schreier cap, normalized quadratic
  cell, and crossed punctured lift have exact small-field collisions.  These
  scripts are diagnostics, not ingredients in a proof:

  - `python3 -B -m char2.audit_n23_quartic_tag_lift_gf4`
  - `python3 -B -m char2.audit_keyed_artin_schreier_cap`
  - `python3 -B -m char2.audit_normalized_quadratic_cell`
  - `python3 -B -m char2.audit_crossed_punctured_lift --max-L 3`
- Exact `GF(2)` collision replays for the rejected two- and three-surface
  carrier recurrences discussed in Section 51 of the design notes:

  - `python3 -B -m char2.audit_carrier_transfer_collisions`
- Exact polynomial-identity audit of the complementary-tag carrier cell.  It
  verifies the root-free *conditional* decoder used in Section 48 of the
  design notes:

  - `python3 -B -m char2.verify_complementary_crown_cell`
- Exact rejection of that cell as a global recurrence on the natural
  degree-`(8,4)` carrier/tag base (an explicit `F_2` collision, not merely a
  Jacobian-rank diagnostic):

  - `python3 -B -m char2.audit_complementary_crown_iteration`
- Exact diagnostic for the normalized consecutive-pair theorem in Section 50
  of the design notes (the proof itself is the displayed reverse monic-
  division recurrence):

  - `python3 -B -m char2.audit_normalized_consecutive_pair`
- Exact rejection of the naive degree-23 rail lift (the script verifies an
  explicit collision over `F_2`; its Jacobian ranks are supplementary
  diagnostics and this is not a general nonexistence proof):
  - `python3 -B -m char2.audit_n23_extension`
- Exact causal audits for the two fixed-scalar degree-15 alternatives:
  - `python3 -B -m char2.verify_parametric_n15_symbolic`
- Exact audit of the structurally useful square-first degree-17 alternative:
  - `python3 -B -m char2.verify_n17_square_first_symbolic`

## Field-generic sanity

- Tiny GF(2^k) field implementation and Frobenius-root sanity:
  - `python3 -B -m char2.test_gf2k`
- Gap-tuned even-step gadget (algebra + decoder window) sanity over GF(16):
  - `python3 -B -m char2.test_gap_tuned_gadget`
- The proof-driven `n=31`/`n=63` *stage decoders* also validate over GF(16):
  - `python3 -B -m char2.test_mersenne_decoder_gf16`
  - `python3 -B -m char2.test_mersenne_decoder_gf16_v2`
- Generic top-window peeling sanity (incl. the top-half of `t_{2^m-1}` for m=2..6):
  - `python3 -B -m char2.test_mersenne_peel`
