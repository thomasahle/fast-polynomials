# FastPoly formalization roadmap

Goal: formalize `sections/constructions.tex` (as repaired — the LaTeX-side fixes are owned by
the Codex agent; this library tracks the *fixed* proofs, in particular the
coefficient-triangular formulation of `lem:Rk2l`).

**Scope (2026-09-05).** Formalization obligations come from claims in the current
manuscript reachable from `main.tex`, together with the lemmas needed to prove
them. Retired constructions and old roadmap entries are not independent targets.
The binary known-powers construction is now the only version in the paper and Lean.
Its complete height bound is `thm:construction-height`: `2⌈log₂ n⌉+4` for
odd degrees and `+5` for the even lift. The historical fill-defined Mersenne
family, scalar-head compiler, their certificates, and the standalone
`Sequential*` depth files have been removed. The canonical decoder is
`peel_correct`, its row certificate is `peel_unitriangular`, and the
count ledger now reads the actual `peelCircuit` gates. Generic fill/head
certificates remain as ingredients of the current odd-degree construction.

Validation (2026-09-05): `nice -n 10 lake build FastPoly` passed (2001 jobs).
The canonical decoder, row certificate, gate-count formulas, and both final height
theorems were also axiom-audited: only `propext`, `Classical.choice`, and `Quot.sound`.
The revised manuscript compiles and its changed algorithm/figure pages were rendered
and inspected. Removed proof files have a local recovery archive at
`/tmp/fastpoly-linear-depth.TrACLg/legacy-proofs.tar.gz`.

## General degree-six lower-bound release integration (2026-09-05)

- `LowerBound/General/Main.lean` is now imported by the umbrella, alongside
  `LowerBoundChar2/Sharpness.lean`. The default CI build therefore covers both.
- `no_rationalInverse_general` quantifies over the general three-gate display:
  sixteen fixed circuit constants and any affine six-parameter/seven-slot map.
  The first-gate gauge correction, quadratic slot map, singular/transversal
  cases, and degenerate first gates are proved, not assumed as normalization.
- The README and coverage appendix point to this entry point instead of only
  the older normal-form theorem. Its axiom audit reports exactly `propext`,
  `Classical.choice`, and `Quot.sound` (the sharpness theorem has the same list).
- Characteristic-two website decoder ports for odd degrees 5–25 are complete.
  The distinct worked appendix degree11 circuit now has its own completed
  inverse; website coverage is not used as evidence for that circuit.
  Hashing and numerical-stability appendix results are excluded by
  Thomas's explicit request; they must not be described as Lean-checked.

## Characteristic-two decoder ports (2026-09-05)

Proof requirement (Thomas): every recovery or realization result must give
the explicit decoder. A bijection must check both `decode (encode keys) = keys`
and `encode (decode rows) = rows`; a realization/surjectivity claim must give
the corresponding explicit right inverse. Coefficient and degree identities
only support checking those formulas. Neither abstract bijectivity nor a
generic solver replaces the inverse. This applies to all decoder ports,
not just the larger degrees.

- `Examples/Char2Degree5/7/9/11/13/15.lean` certify the website's literal
  shared circuits. Every file proves its exact multiplication count, an
  explicit coefficient decoder for every monic polynomial, and bijective
  evaluation of the normalized-coordinate family at distinct points.
- `Examples/Char2Triangular.lean` proves both directions of the actual
  recursive back-substitution algorithm. `Char2Frobenius.lean` supplies the
  square-root pivots; only degree 7 among these completed bases needs
  `[PerfectRing F 2]`. This is not a finite-field enumeration proof.
- `Examples/ExplicitEvaluationInverse.lean` exposes the Lagrange interpolation
  formula as a named decoder, with both compositions and an explicit evaluation
  equivalence. The generic finite-family wrapper and the older degree-seven
  wrapper now use this interface instead of an unnamed local interpolation
  witness. Its isolated build passed in 3.2s with a 20,000-heartbeat cap.
- `Examples/Char2Construction.lean` connects coefficient vectors to arbitrary
  monic polynomials and proves the one-product even lift using the same
  `Cost.Circuit` syntax. `Examples/Char2Finite.lean` packages all degrees
  5–25 with exactly `n/2+1` products and is imported by the umbrella.
  It also exposes `degree19/degree20` (10/11 products) and
  `degree21/degree22` (11/12 products) and `degree23/degree24` (12/13 products).
  `degree25` uses 13 products and its explicit raw-key inverse. The even
  bases use the one-product lift. The perfect-field assumption is needed
  for degrees7/17 and their even lifts, not degree25.
- The older degree-5–15 normalized-family certificates do not by themselves
  assert that every original raw gate-offset vector is uniquely decoded.
  Their arbitrary-polynomial realization theorem is proved; a stronger
  raw-key-bijection claim needs its own bridge. Degrees17,19,21,23 and25 now have
  those bridges as well, as detailed below.
  The existing `Char2SmallInverses.lean` still supplies the raw-key degree-9
  theorem for the paper's displayed circuit.
- `tools/gen_char2_lean.py` replays the existing explicit coordinate changes
  and emits kernel-checked coefficient/ring proofs for the completed small
  degrees. Symbolic replay (`--stats`) succeeds through degree 25, but expanded
  Lean source generation is disabled above degree 15: those drafts were too
  slow and have been archived outside the source tree. The completed larger
  ports follow the supplied verifiers' named inverse steps instead.
- `Examples/Char2DecoderSteps.lean` supplies a unit pivot, a dependent block,
  and an explicit self-inverse coordinate update with compositional
  independence lemmas. This is the primitive used by degree 25's supplied
  24-step shear certificate, not a proof of those 24 circuit-specific rows.
- `Examples/Char2CoefficientShear/Char2CoefficientShearTransport` express
  a correction as two coefficient reads of the named circuit (pivot zeroed,
  then future coordinates zeroed), with both inverse compositions and
  preservation of supplied higher, lower, and same-row unit columns.
  `Char2CoefficientAction/Char2PivotAction` transport an explicitly supplied
  coupled update through these shears. Its earlier-coordinate corrections
  disappear by the normalized coefficient equations; a singleton-support
  action is proved to be the literal coordinate translation. No expanded
  correction polynomial, generic solver, or circuit search is used.
- `Examples/Char2Degree23Terminal.lean` ports the degree-23 verifier's four-row
  terminal block, in both directions, including the known row corrections.
  `Char2Degree23RowEight.lean` proves the actual circuit's row-eight unit
  pivot: its slope is a product of monic quartics. Its `exitEquiv` combines
  the row-eight and final constant-offset decoders and checks both inverse
  compositions against the actual circuit rows, with other offsets fixed.
  Both modules keep the earlier
  quantities opaque and use local rewrites/cancellation, not ring expansion.
  All three new modules have a 20,000-heartbeat limit and are in the umbrella.
  Degree23's preceding scalar pivots and the bridge from circuit coefficients
  to these terminal equations are now checked, as detailed below. Full construction coverage is
  now 5–25.
- `Examples/Char2UpdateTriangular.lean` constructs the explicit recursive inverse
  from single-coordinate update identities. It proves independence from future
  coordinates by finite resets, then checks both back-substitution compositions.
  The named circuit baseline is never expanded; the direct check used 1.66s
  user CPU with a 20,000-heartbeat cap.
- `Examples/Char2Degree19Shell/Crown.lean` certify the outer cubic decoder
  against the actual existing circuit: read the shell, divide by its monic
  cubic (including the row-three boundary correction), then read the low
  offsets. The crown's fixed top-row signature follows from named square gates.
  `Char2Degree19Coordinates.lean` checks the supplied key-coordinate inverse in
  both directions. The inner crown's thirteen unit pivots are now checked in
  `Char2Degree19InnerTail/Simple/Changes/ZChanges/Direct/Seam`, by finite changes
  to named gates and degree bounds on the corrections, without expanding any
  coefficient baseline.
- `Examples/Char2Degree19Targets.lean` proves that the explicit outer decoder of
  every monic degree-19 target has the required crown signature (degree 16,
  rows 15/14/13 equal to 0/0/1), using monic division and four-term convolution.
  This also checks the outer decoder's existence direction for arbitrary
  targets. The module builds under the same 20,000-heartbeat cap (7.4s).
- `Examples/Char2Degree19KeyUpdates/InnerInverse.lean` connect all thirteen
  supplied coordinate changes to those raw-gate differences. The actual inner
  decoder is prefix back-substitution, with both compositions checked.
  `Char2Degree19Realization.lean` assembles it with the outer monic-division
  inverse and proves `decodePolynomial_correct` for every monic degree-19
  target. `Char2Degree19Program.lean` identifies the same polynomial with the
  literal ten-product program; `construction` packages the explicit right
  inverse and counted circuit. All new degree-19 declarations use the reduced
  20,000-heartbeat cap.
- `Examples/Char2Degree19Bijection.lean` also proves recovery of the original
  nineteen raw keys, not just normalized coordinates. It packages the actual
  low-coefficient map and its explicit decoder as `coefficientEquiv`, with both
  compositions. `evaluationEquiv` composes that inverse with named Lagrange
  interpolation; it works over every characteristic-two field. The module
  checked in 1.0s under the same heartbeat cap.
- `Examples/Char2Degree23Coordinates/Keys.lean` check both directions of the
  complete supplied key-coordinate change, including the circuit-dependent
  row-eight shear. The row-eight and constant-offset circuit bridge is an
  ingredient of the completed full degree23 inverse and counted realization
  described below; these components are checked and imported by the umbrella.
- `Examples/Char2Degree21Coordinates/Frame/Pivots/Leading/KeyUpdates/Inverse`
  check all twenty-one single-coordinate differences and the actual prefix
  decoder, including both compositions on the original raw offsets.
  `Char2Degree21Program` checks the same eleven-product circuit using named
  gate environments and one evaluation equation per bind tail, avoiding a
  whole-circuit reduction. `Char2Degree21Realization` connects that exact
  program and inverse to every monic degree-21 target and gives the explicit
  Lagrange-then-circuit evaluation equivalence. All keep the unchanged
  20,000-heartbeat cap. The degree-22 lift is exposed in `Char2Finite`.
- `Examples/Char2UnequalOffsets`, `Char2Degree17QuadraticOffsets`,
  `Char2Degree17Wires`, and `Char2Degree17GateCoordinates` check the existing
  degree-17 gate hierarchy and its explicit raw-offset/gate-coordinate inverse
  in both directions. The completed output coefficient inverse is below.
  `Char2PivotUpdates` now supplies checked explicit prefix back-substitution
  with specified zero-preserving scalar inverses, including Frobenius pivots.
  The further `Char2RecoveredProductUpdates` and
  `Char2Degree17TriangularCoordinates` modules individually check the exact
  two-row product-update identities and the supplied S/R/E change plus
  permutation, including its composition with the raw-key inverse. They are
  now imported, together with the subsequent circuit-specific output pivots.
  `Char2Degree17TerminalFrame/TerminalPivots` subsequently pass individual
  checks for seven actual normalized-output unit differences (rows10,7,4,3,2,1,0)
  and higher-row invariance. `EllPerturbation/Q9Pivot` and
  `SexticCancellation/Q8Pivot` add the actual row-five and row-six pivots,
  respectively: nine of seventeen normalized pivots are now checked.
  `Char2Degree17HighFrame` proves the reduced high output is `A²B+A*S6`
  above row ten, with all other wires in a named degree-ten correction.
  `HighSignature/RRow/LeadingInverse` additionally check the actual leading
  four-row inverse, including both compositions and the swapped row order.
  `Q0Pivot/EPivot` add rows12/11; `LowWindows/Q6Pivot` check the actual
  row-nine square pivot and its explicit inverse Frobenius. `Q5Pivot` adds
  the row-eight fourth-power pivot, using only local scalar cancellation
  with the earlier tail kept named. `Rows/Inverse` assemble all seventeen
  steps and prove both inverse compositions on the original raw keys.
  `Program/Realization` connect the exact nine-product circuit to every
  monic degree17 target and the explicit interpolation-then-decoding
  evaluation inverse. Every declaration keeps the20k heartbeat cap.
  These modules are checked and imported; `degree18` is the10M even lift.
- `Examples/Char2Degree23Frame` checks monicity of the actual named gates and
  degree-23 output. `Char2Degree23Cancellations/HighFrame` also individually
  check the shared-wire cancellations (degrees9→7 and15→14) and split the
  output into its five-factor degree-23 part and a monic degree-15 remainder
  (8.1s/2.2s module builds). Both auxiliary modules are now imported. This is
  structural support for the completed full degree23 inverse below.
  `HighDifference/HighPivots`, `SeamDifference/SeamPivots`, and `HighKeys`
  check and transport the first eight pivots to the supplied normalized keys
  (rows22–15). `MiddleFrame/MiddlePivots/MiddleCoordinates/MiddleKeys`
  check six more actual normalized pivots (rows14–9), keeping `W=w+s`
  and `v` named and bounding the row-eight correction separately.
  `LowFrame/LowKeys/TerminalRows` add normalized coordinates14,17,19,22:
  row eight, row five, the adapted terminal row-three pivot, and the final
  constant. Coordinate19 preserves the earlier row-four-plus-row-three sum.
  `FifteenKeys/SixteenKeys/EighteenKeys/TwentyKeys/TwentyOne` finish all
  twenty-three normalized pivots. Their named wire changes remove an
  explicitly computed row-eight scalar and retain the supplied low slope.
  `Char2MonicPivotPeel` explicitly recovers a monic-column scalar from its
  top coefficient. `Char2Degree23NormalizedPeel` uses that solve to remove
  the already-installed row-eight column, without expanding its baseline.
  `Rows/RowUpdates/Inverse` assemble the full prefix decoder in the supplied
  row-four-plus-row-three order, prove both compositions, and compose with
  the explicit key inverse to cover the original raw offsets.
  `Program/Realization` connect the literal twelve-product circuit to every
  monic degree23 target and supply the interpolation-then-decoding evaluation
  inverse. All are checked and imported at the unchanged20k heartbeat cap.
  `Char2Finite.degree23/degree24` expose the12M construction and its13M lift.
- `Examples/Char2Degree25Frame/HighFrame` check the existing thirteen-product
  circuit's named wires, monicity, and five-quintic high frame, with a monic
  degree20 remainder. `HighDifference/HighPivots`, `SeamFrame`, and
  `RowEighteen/RowSeventeen/RowSixteen/RowFifteen/RowFourteen/RowThirteen/RowTwelve`
  check the first thirteen supplied raw shifts, at rows24 through12, with
  explicit monic slopes and no whole-output expansion. `Program` checks the
  literal13-product gate/bind ledger. `PrefixCoordinates/PrefixPivots` check
  the first nine partial coordinate substitutions and their unit columns.
  `MiddleCoordinates` composes the next four explicit shears, with both
  raw-key inverse compositions. `MiddleFrame/HighKeys/MiddleKeys` transport
  all thirteen unit columns through that exact partial map: the first nine
  use a named degree15 correction bound; the other four use exact raw-key
  identities. `RowEleven/RowsTenNine/RowEight/RowsSevenSixFive` check the next
  seven raw directions (rows11–5), including their exact coupled changes,
  and the constant row. `LowerRawKeys/CoupledLowerKeys` transport them to the
  partial middle map. `LowerCoordinates/LowerActions/TailCoordinates` then
  normalize coordinates13–19 by explicit coefficient shears and conjugate
  the supplied coupled updates through them. The final partial map has
  **twenty nonconstant unit columns (rows24–5), plus the constant column**,
  both raw-key inverse compositions, and the actual output/key bridge.
  `TwentyWires/Bounds`, `TwentyOneWires/Bounds`, `TwentyTwoWires/Bounds`
  supply exact final-direction differences bounded by degree11.
  `LateScalars/LateKeys/LatePeel` transport these through the seven existing
  coefficient shears, reducing their differences to degree4. The generic
  `Char2CoefficientDegreePeel` proves each single-row reduction; named
  branch equations and locally opaque circuit families keep elaboration bounded.
  `TerminalHead/HeadChange/RemainderUnit/TerminalUnits` identify the explicit
  degree4/3/2 head remainders modulo the fixed monic quintic. `TailRowEleven`
  preserves the recovered row11; `RowElevenRead/TerminalOne` use it to read
  the final raw a17 correction and certify the linear remainder for row1.
  `Coordinates` applies the final row4 shear and supplies **all25 unit
  columns**. `Char2CoefficientInverse` assembles explicit descending-prefix
  decoding with both compositions. `Inverse` connects it to ordinary
  coefficients of the actual raw circuit; `Realization` supplies arbitrary
  monic targets, the literal13-product program, and explicit evaluation
  inversion via interpolation. All these helpers are checked and imported
  at the unchanged20k heartbeat cap. No perfect-field assumption is used
  by degree25. The existing exact symbolic verifier
  `char2/verify_n25_unitriangular_symbolic.py` was rerun: all24 supplied
  nonconstant pivots and the final scalar passed over GF(2)[keys]. This run
  did not include the wrapper's numerical round-trip tests.
- `Examples/Char2Degree15FastCore/Tail/Leading/Inverse/Program/Realization`
  now replace the old expanded degree-15 certificate on the main import path.
  The same eight-product circuit and supplied linear key formulas are retained.
  The proof cancels the shared `w+s` branch before reading rows, verifies all
  fifteen named-wire differences, and uses explicit prefix back-substitution
  with both compositions. The program bridge uses named gate/bind-tail steps;
  the realization covers every monic target, with a displayed evaluation
  inverse. Every new declaration keeps the20k heartbeat cap. The old generated
  `Char2Degree15.lean` is an unimported reference, retained without changing
  generator compatibility; it is no longer a prerequisite of `Char2Finite`.
- `Examples/Char2Degree11FastCore/Signature/Changes/Units/Inverse/Program/Realization`
  similarly replace the generated degree11 certificate on the active path.
  They retain the original six-product circuit and supplied normalized key
  formulas. The final `B*J` product stays opaque: its small named-wire
  differences give eleven unit pivots and an explicit prefix inverse with
  both compositions. Arbitrary-monic realization and the explicit evaluation
  inverse are checked. Each declaration keeps the20k heartbeat cap. The old
  `Char2Degree11.lean` remains an unchanged, unimported reference.
- Eight `Char2Degree13Fast*` modules likewise replace the generated degree13
  proof on the active path. They preserve its seven products and exact
  coordinate variant (`a4=q8+q9`). All thirteen named-wire pivots, the
  nonmonotone row permutation and both prefix inverse compositions are
  checked, together with arbitrary-monic realization and the explicit
  evaluation inverse. The final two products remain opaque; only small
  coefficient windows are read. The old generated13 file is untouched and
  unimported. This retains the previous normalized-coordinate scope; it
  does not assert an additional original-raw-key bijection for degree13.

### Retained appendix circuits: exact raw-key inverses (2026-09-06)

- The degree11 circuit of display (A.0) is **not** the square-first website
  circuit. `Char2PaperDegree11Core/Top` prove its six named products,
  monicity and exact rows10–5 using the cancellation of the two final
  branches and small coefficient windows. `HeadInverse` supplies the two
  inverse-Frobenius operations of (11.2), with both compositions.
  `Tail/TailInverse` prove the displayed butterfly identity (11.3), the
  a6 baseline pivot, and the four explicit inverse formulas (11.4).
  `Coordinates/CoefficientFrame/Inverse` connect those exact formulas to
  the original eleven raw keys and ordinary circuit coefficients, in both
  directions. `Program/Realization` connect them to the literal six-product
  circuit, arbitrary monic targets and explicit interpolation/evaluation
  inversion. This completes the degree11 half of
  `lem:char2-small-staircase-butterfly` over perfect characteristic-two fields.
  No full circuit expansion or increased20k heartbeat limit is used.
- `Char2PaperDegree13Inverse` supplies the missing raw-key bridge for
  `lem:char2-degree13-inverse`. The printed coordinates and Fast13's
  coordinates differ only by the explicitly displayed earlier-coordinate
  shear `q9 += q8`. Both linear key-map compositions are checked; each
  named raw gate is identified with the existing Fast13 circuit. The
  resulting coefficient inverse and interpolation/evaluation inverse
  check both compositions on the original thirteen raw keys, over every
  characteristic-two field. Both completed modules are umbrella imports.

Latest integration check: `nice -n 10 lake build FastPoly FastPoly.LowerBound.Main
FastPoly.LowerBound.General.Main FastPoly.LowerBound.General.Transport` passed
with **2215 jobs** after integrating the retained appendix degree11 and
degree13 raw-key inverses (12.85s wall, 1.78s user CPU, 2.81s system CPU;
dependencies already built). Their additional26-declaration axiom audit
passes with only `propext`, `Classical.choice`, and `Quot.sound`, and no
`sorryAx`; the final theorem signatures have no undischarged pivot hypotheses.
The preceding degree25/dispatcher integration passed at2204jobs
(5.98s wall, 1.70s user CPU, 2.04s system CPU; dependencies prebuilt).
Full website construction coverage is **5–25**. Its additional23-declaration complete-inverse axiom audit
passes with only `propext`, `Classical.choice`, and `Quot.sound`, and no
`sorryAx`. The checked degree25 construction requires only a field of
characteristic two; the uniform dispatcher retains the perfect-field
assumption required by degrees7/17.
The preceding twenty-column integration passed at2179jobs (16.07s wall).
Its additional24-declaration axiom audit passes with only
`propext`, `Classical.choice`, and `Quot.sound`, and no `sorryAx`.
The preceding thirteen-column integration passed at2166jobs (11.47s wall);
its additional ten-declaration axiom audit passed with only the same three
standard axioms and no `sorryAx`.
The preceding degree17 integration passed at2156jobs (14.59s wall) and
extended the contiguous dispatcher through degree24.
The preceding fast13/degree23 integration passed at2144jobs (13.94s wall).
The degree17 integration's additional20-declaration axiom audit passes with
only `propext`, `Classical.choice`, and `Quot.sound`, and no `sorryAx`.
The preceding degree11 integration passed at2111jobs (17.12s wall).
The preceding degree15 integration passed at2084jobs (30.14s wall), and
the degree21/22 integration passed at2075jobs
(104.85s wall, 7.12s user CPU, 20.77s system CPU on the loaded machine).
Rebuilding the older generated degree-15
coefficient certificate previously took123s of an integration critical path;
it has now been removed from the active import path in favor of the checked
named-wire inverse. The integrated import graph is checked; unimported drafts
may remain in flight. No new commit pin is asserted here.
The twenty-one audited new inverse/constructor/evaluation declarations report
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
An additional nineteen-declaration audit after the degree21 integration
(coefficient/evaluation inverses, program realization, even lift, degree17
gate inverse, and new generic helpers) has the same clean result.
The next twenty-declaration audit, covering the fast degree15 realization
and batched degree17/23 helpers, is clean as well. An isolated direct recheck
of `Char2Degree15FastInverse.lean` passed in8.30s wall /3.55s user CPU /1.81s
system CPU; its prerequisites were already compiled, so this is not a
clean-build timing for the entire six-module replacement.
An additional twenty-five-declaration audit covering fast11's two inverse
compositions, circuit count and realization, plus the new degree17/23 pivot
and peel declarations (including the normalized middle pivots and their
row-eight transport), is clean: only the same three standard axioms occur.

Validation: `nice -n 10 lake build FastPoly` passed with 2036 jobs after this
integration. Axiom audits of `Char2Finite.monic_evaluation`, the degree-15
program decoder and evaluation bijection, and `Construction.evenLift` report
only `propext`, `Classical.choice`, and `Quot.sound`. The six completed generated
sources also pass `tools/gen_char2_lean.py DEGREE --check` against the current
website. The generator's pure polynomial algebra is in
`tools/char2_polynomial.py`; it has no private research-tool dependency.

Staged-inverse validation: all three new modules passed at the reduced
heartbeat limit. Lake reported 2.1 s for the degree-23 terminal block and 3.1 s
for its row-eight bridge (dependencies already available; not a clean-build
timing). The Python degree-23 and degree-25 verifiers now use the same small
public algebra helper, rather than the unpublished inverse-search module.
Both verifier scripts passed unchanged mathematical assertions (23: 0.18 s;
25: 7.11 s). After adding the staged components, `lake build FastPoly` passed
at 2040 jobs. Axiom audits of the two block inverse directions and the row-eight
inverse directions are clean (only the standard Lean axioms; no `sorryAx`).

## Same-polynomial paper capstone (2026-09-04)

- `Cost/Additions/Decoded.lean` strengthens the odd master induction so one semantic
  pair simultaneously has the explicit coefficient decoder, the logarithmic-height
  realization, and an addition-certified realization.  The two circuits may use the
  paper's different arrangements, but their four output polynomials are identical.
- `Cost/Additions/DecodedPolynomial.lean` completes that pair, handles the affine,
  quadratic, and septic bases, and preserves the common polynomial through the even
  lift.  `decodedAdditionPolynomial_exists` covers every positive admissible degree.
- `PaperMain.lean` now projects both advertised arrangements from this common witness;
  `MainArrangementsChecked.of_charZero` and `.of_charP` therefore close the former
  same-polynomial packaging gap.  The umbrella build is green, and `#print axioms`
  reports only `propext`, `Classical.choice`, and `Quot.sound`.

**Construction-family boundary.**  `Recover/`, `Polynomial/LowJet.lean`, the circuit
syntax in `Cost/Circuit*.lean`, and the arbitrary finite-output
`Cost.MultiplicationProgram` / `Cost.MultiplicationRealization` packages are
characteristic independent.  The four-output
`JointPair*` and quadratic/quartic `RealizedOddGadget` wrappers specialize those generic
layers to the present family.  The current `Section4/`--`Section6/` recursion is the
large-characteristic family and owns its admissibility hypotheses.  A later
construction over `F_{2^k}` should be added as a sibling family with its own payload
wrapper and dispatch, consuming the same recovery, low-jet, and generic circuit
interfaces; it must not be encoded as exceptional branches inside the present `T`
recursion.

Uniformity is obtained by free specialization, not by a pointwise `∀θ, ∃ circuit`
statement.  `Cost/CircuitNaturality.lean` proves that evaluation commutes with every
base-algebra homomorphism, and `Cost/PolynomialCircuitNaturality.lean` specializes the
same fixed joint program from free indeterminates to arbitrary parameter values.
`Cost/FreeSpecialization.lean` supplies the public finite-key form: choose the program
once at `MvPolynomial (Fin n) R`, extend `Fin n` keys by zero to the internal `Nat`
labels, and specialize the same syntax to every target algebra.  This avoids both the
wrong quantifier order and an unnecessary infinite-variable automorphism statement.
`Cost/PolynomialProgram.lean` then supplies the characteristic-neutral final combine,
even lift, and degree-one/two endpoints; `Cost/SepticProgram.lean` is the literal
four-product, ten-addition degree-seven endpoint.  Its generic `ofOutputs` combiner
selects any two positions of any finite payload; `ofJointPair` is only the current
four-output wrapper.  For an even target `n`, certify the odd source directly in the
same ambient `MvPolynomial (Fin n) R` environment before applying `evenLift`, so the
fresh final coordinate is never introduced by an unproved change of free ring.

Semantics: relative visible algebras `𝒱(K, Φ, G, t)` (`Recover/Context.lean`); proofs via
scalar/block triangular certificates (`Recover/Filtered.lean`); coefficient identities via
the top-window calculus (`Polynomial/`). Statements are over an abstract `[Algebra R A]`;
the free instantiation `A = R[α]` (MvPolynomial) is what makes them non-vacuous and is where
provenance of the known context is proved.

**Final-invariant correction (audit 2026-08-27).**  Algebraic splittability alone is
automatic for a decodable monic family via the canonical coefficient split.  The paper's
actual induction invariant is therefore a *realized compatible package*: the explicit pair,
its unconditional compatibility certificate, recorded `H₂`/`H₄` wires, and one
fixed `Cost.JointPairProgram` whose evaluator produces those four polynomials for every
parameter environment and whose own syntax has the claimed multiplication count.
`Cost.JointPairRealization` is a useful pointwise composition helper, while
`Cost.PairCost` is only the legacy numerical shadow; neither alone expresses the public
uniform invariant.  `Main.lean` must assemble the fixed program in the same strong
induction; it must not state the structural and numerical existence results independently
and then silently identify their witnesses.
Degree `7` is only an exception to the three-product joint realization, not to algebraic
splittability.

**Addition-realization correction (audit 2026-08-28).**  The recurrence relations in
`Cost/Additions/` formalize the manuscript's optimized schedules, but they are not yet
gate-count predicates on the literal programs returned by `Main`.  This distinction is
substantive for the shared `T` bases and finite outer arrangements:
the generic shared even and odd `tCircuit` bases have 6 rather than 5 and 17 rather
than 15 additions, and the present degree-27 program has 46 rather than 43.  The
manuscript schedules save those gates by carrying the scalar tower shift through both shared bases and forming
`F₂ = F₁ + kρ`, and a finite degree-27 tower peephole that constructs `H₂` before
`H₂+α₂₅` instead of recovering it afterward.  `Cost/RetainedShiftTCircuit.lean`
now supplies the two optimized shared-base circuits, their exact literal counts, and
semantic equivalence to the existing definitions whenever the retained-shift equation
holds; `Cost/ShiftedPowerTowerCircuit.lean` supplies the generic two-product,
eight-addition shifted tower; and `Cost/RealizationP27Optimized.lean` installs both
peepholes into the already-certified degree-27 continuation, proving the same four
outputs with exactly 13 products and 43 additions.  The remaining compiler work is to
select the optimized siblings in the generic realized programs.  The stateful part is
now isolated in `Cost/RetainedShiftTCompiler.lean`: its fuelled compiler changes only
the two shared-base branches, carries the scalar side wire through the level-one
even-to-level-two call, preserves the ordinary `tCircuitF` semantics and multiplication
count, and proves the exact saved-addition recurrence (one at a shared even base and two
at a shared odd base).  `Cost/RetainedShiftTInstantiate.lean` is the gate-free generic
call-site adapter: it designates any existing producer wire as the scalar side input and
preserves the complete local pair.  Completing that adapter's result from the ordinary
compiler to `Tpair` awaits only the public arbitrary-source form of `eval_tCircuit`; no
caller needs a sentinel parameter index.  A public addition theorem must use optimized
semantic siblings with
explicit decoders and prove a bound on
`program.additions` for the same fixed existential program; it must not pair
`PairAddCost` with an unrelated realization.

## Complete-polynomial height + general char-2 lower bound (2026-09-02)

- `HeightFinal.lean` — the final clause of `thm:construction-height` and
  `thm:construction-count` in one package, `RealizedPolynomial R θ n m D` (monic
  degree-`n`, `V`-relative decoder of the block `θ 0 … θ (n-1)`, one fixed
  `Cost.PolynomialProgram R m`, `multDepth ≤ D`): `odd_polynomial_height`
  (`(n-1)/2 + 1` products, height `≤ 2⌈log₂ n⌉ + 4`, from `odd_realizable_pairs'`
  through `PolynomialProgram.ofJointPair` + `multDepth_ofOutputs_le`),
  `septic_polynomial_height` (`4`, `≤ 4`), `RealizedPolynomial.evenLift`
  (`P = x·Q + θ n`: `+1` product, `+1` height, decoder = coefficient shift),
  `polynomial_height` (every `n ≥ 3`: `⌊n/2⌋ + 1` products, height
  `≤ 2⌈log₂ n⌉ + 4 + (n+1) % 2` — the even lift's product is NOT absorbed since
  `⌈log₂(n-1)⌉ = ⌈log₂ n⌉` for even `n ≥ 4`), `linear_/quadratic_polynomial_height`,
  and the `n`-admissible entry points `polynomial_height_of_admissible/_of_charZero/
  _of_charP` (bridge `Admissible.intCast_units`).
- `LowerBoundChar2/General.lean` — `thm:char2-lower` WITHOUT the affine hypothesis
  (the paper's fibre-counting proof): `no_surjective_eval` (`1 < n`,
  `2n ≤ |F|`, `CharP F 2`: `∃ X` injective with `E_X : F^{2n+1} → F^{2n}` not
  surjective), `no_construction_general` (any preprocessing map `Λ → Slots`),
  `no_construction'` (re-derives `no_construction`).  Ingredients: `gauge_injective`
  (free action), `gauge_gauge`/`transl_gauge` (group law, commutation — recorded, not
  needed), `card_fibre_eq_of_le` (pure counting), `eval_eq_iff_gauge` (fibres =
  orbits), `card_coincide_eq_pow` (`|𝒜| = Q^{n+1}` via `Fix π`),
  `card_coincide_mem` (`|𝒜| ∈ {0, Q^{2n}, Q^{2n+1}}`), `pow_succ_not_mem`.  Both new
  files are in the umbrella (`LowerBoundChar2.General` transitively brings the whole
  affine development into `lake build FastPoly`).

## Semantic-cost integration + batch-3 (2026-08-28): the master carries its circuit

- **`odd_realizable_pairs` upgraded**: the detached `Cost.PairCost` conjunct is
  replaced by `∃ prog : Cost.JointPairProgram R ((n-1)/2), prog.RealizesAt θ T₁ T₂ H₂ H₄`
  — the fixed base-ring straight-line program itself, carried branch-wise
  (`Three/Crown/Fifteen/TwentySeven/ThirtyOne.realized`, `eightThreeFromGadget`,
  `eightSevenRealized` + `RealizedOddGadget.dispatch/relative`).  The `BarredGadgets`
  hypothesis is GONE from the master: the realized dispatch internally uses the
  schedule-faithful `barQ` circuits.  The `8k+7` fresh block is reparameterized to the
  counted `(s, d)` sum/difference form (ring-bridge to the `(a, b)` shadow via
  `IsUnit 2`; decode stays integral), aligning Main's witness with the 6-addition
  ledger body.  Kernel note: branch witnesses go through the generic `joint_exists`
  so structure projections are checked once on a variable, not by unfolding each
  concrete circuit inside the master's term (fixes a kernel deterministic timeout).
- **New endpoints**: `odd_realizable_pairs_free` (the certificate at
  `Cost.freeParameterEnv`) and `odd_realizable_pairs_uniform_family` (one fixed
  program realizes the specialized pair and powers for every key over every
  `R'`-algebra, via `realizesFiniteFamily_of_free`).
- **Batch-3 refactors applied** (8 drafted groups, 165 patches, all green):
  `descend_on_finset` engine (Recover ×4 + engine in Context), PerturbedT shared
  prelude, Rk2lTriMaster htower/hconv/descent dedupe, T.lean `*_good` sextet +
  `eE*_top` quadruplet + sublead triplets, Induction.lean shell/schedule/monic-root
  collapses (+`coeff_combined_mem`/`coeff_add_C_mem` engines), FillRec/FillCert
  step-setup and band-lemma dedupe, monic-quadratic alias canonicalization
  (Main/SpecialCases/Septic), `square_gadget_mem` reproved via the relative
  CausalShell engine, Unitriangular engine adoption.  Umbrella: 1957 jobs, zero
  sorries.

## Quality pass (2026-08-28): survey-driven dedupe, batches 1–2 applied

A 29-agent read-only survey produced 126 verified findings (full detail with
apply-plans: `notes/refactor_survey_2026-08-28.json`).  Applied:

- **New canonical engines**: `coeff_combined_zero_left`, `mem_of_natCast_mul_mem`,
  `update_last`/`update_ne` (version-compat shims) in `Recover/Context.lean`;
  `slot_mem_sup_adjoin_Ico`/`known_mem_sup_adjoin` in `Recover/Triangular.lean`;
  `isUnit_two_of_cast` in `CertEngines.lean`; `BarredGadgets.mono` in `Dispatch.lean`;
  `crownH4t_good`/`crownHp_good`/`crownHp_sd`/`crownHp_coeff_mem` in
  `FourKPlusOne.lean`; `coeff_X_mul_of_pos` in `Polynomial/CausalShell.lean`;
  `Rpair_combined_coeff_mem` in `SlotSurj.lean`; `monic_add_low` moved to its
  canonical home `Polynomial/TopWindow.lean`.
- **Call-site collapses**: 10× `hcomb0`, 6× IsUnit-2 derivation, 5× `hbar`
  weakening, 4× `hXmul`, 15× `hsd` lambda, 6× crown monic/degree block,
  2× crown tower block, 40× `Function.update` shim, 3× ~35-line Rpair-combined
  membership block.
- **Dead code removed** (zero consumers, not paper-named): `mem_visible`,
  `Vis_mono_known/window`, `Vis_sup_le/eq_self`, `sub_mem_of_mem_shiftW`,
  `shift_pivot_windowed`, `mem_sup_adjoin_absorb`, `coeff_mem_smul`,
  `mersSlotF_succ`, `Rk2l_top_boundary` (paper tag moved onto the sharpened
  `Rk2l_top_two`).
- **Unused hypotheses dropped**: `odd_deg_facts` (hpar, hk), `odd_rest_mem`
  (hHt, hdHt, hind₁, hind₂), `odd_pivot_low` (hHt, hdHt, hKt, h2),
  `add_block_cert`/`sq_cert_supp` (heD), `sp_cert` (hHm), `fillSlot_windows`
  (hin, hq, hqh) with the induced trims of `fillStep_supp₂`/`fillStep_pivot_top`.
- **Kept deliberately** (Lean-dead but formalize *named* paper lemmas):
  `discharge_side_information`, `extractable_via_derivable`, `ScalarShift.lean`
  (`lem:scalar-shift-square`), `square_gadget_mem` (`lem:square-gadget`),
  Triangular's `concatenation` section (`lem:triangular-block-concatenation`),
  the cubic unitriangular base and the `Admissible` API.
- **Deferred to a future pass** (verified, plans in the JSON): the descending-fuel
  induction engine (`descend_on_finset`, 5 sites), the PerturbedT ~50-line prelude
  ×3, Rk2lTriMaster descent-packaging ×9 branches and `htower'` ×3, the T.lean
  `*_good` sextet, `eE*_top` quadruplet, Induction.lean shell/schedule collapses,
  FillRec/FillCert step-setup dedupe, the monic-quadratic canonicalization
  (Main/SpecialCases/crownH2 aliasing), and the tree-wide band-arithmetic and
  sup-adjoin adoption (~70 sites).  Umbrella after the pass: 1916 jobs, zero
  sorries.

The addition analysis is now split along its mathematical dependency chain:
`Cost/Additions/T.lean` contains the primitive and shared-`T` recurrences,
`Cost/Additions/Gadgets.lean` contains auxiliary-gadget ledgers, and
`Cost/Additions/Final.lean` contains the pair and complete-polynomial bounds.
`Cost/Additions.lean` remains a compatibility import and exposes the unchanged API.

## Appendix A (2026-08-28): optimized circuits formalized; (17,9) added and certified

- `Examples/OptimizedCircuits.lean` — the original eleven optimized-candidate
  circuits (six characteristic-2, five large-prime) as wire-level definitions with
  monic/degree lemmas over any nontrivial commutative ring, via a small `Circuit` monic-degree
  calculus (`md_mul`/`md_add_low`/`ndb_*`); plus the reduced-key `(17, 9)` chain.
- `Examples/Chain17Bridge.lean` — the `(17, 9)` entry added to `A.2` is CERTIFIED:
  `Chain17.eq_master` (the displayed chain equals the combined crown `T_{4,4}` pair
  under the integral key change `bof`; layered ring proof, `tpair_eq` by `rfl`),
  `Chain17.decodable` (inherited from `fourk_decodable`), `Chain17.bof_surjective`
  (given `IsUnit 2`).  Derivation sympy-validated; emitted by the new
  `tools/polychain.py chain 17 --reduced` (unit-triangular key normalization added to
  the tool, selftest n ≤ 120 green, full-matrix fallback for the ±-pair gates).
- `Examples/Char2Inverse.lean` — **`lem:first-char2-circuit-inverse`** in full: the
  `2·J` normal-form witness over any ring, the paper's square-root recovery chain
  (`decode_coeffMap` / `coeffMap_decode` over a perfect field of characteristic 2),
  bijective monic degree-7 interpolation (Lagrange), and the composed bijection
  `circuit_eval_bijective : F⁷ → F⁷`.  This is a certified finite appendix
  example, not the future all-degree `F_{2^k}` construction family.
- **Historical characteristic-two small-base boundary (2026-08-28):** the appendix and
  `better_bounds/CHAR2_SMALL_BASES.md` now give explicit inverses for the worked
  degree-`7`, `9`, `11`, and `13` circuits.  The inverse for degree `7` is the only
  one of these formalized at that snapshot.  The degree-`9`, `11`, and `13`
  definitions in `Examples/OptimizedCircuits.lean` are the older search candidates,
  not the worked circuits now displayed in the appendix; their monicity/degree
  theorems remain valid but are not recovery theorems. The three worked
  inverses are now completed in `Char2SmallInverses`, `Char2PaperDegree11*`,
  and `Char2PaperDegree13Inverse`, respectively; see the current status above.
- `sections/appendix_polynomials.tex` — the `(17, 9)` block added to `A.2` with the
  provenance note.  Umbrella: 1916 jobs, zero sorries.

## Main assembly (2026-08-27): master induction sealed; dedicated barred endpoint green

- `Section6/GadgetDecoders.lean` — `q4k1_decodable` (V-relative `Q_{4k+1}` decoder with
  the `crownH4` byproduct clause, via `Tpair_compatiblePair` at context `V` +
  `x_alpha_mem` + `Rk2l_extract`), `q4k1_good`, `q_odd_degree_decodable'` (V-relative
  form), `fourk_decodable` (pair-level `4k+1` decoder); crown coeff-mem helpers in
  `FourKPlusOne.lean`; `CausalPair.coeff_mem_of_le` in `Recover/Context.lean`.
- `Section6/Dispatch.lean` — `BarredGadgets` interface Prop (degree-capped) and
  `odd_gadget_dispatch` (`lem:odd-gadgets-H2H4`): `d ∈ {1,3,7}` affine/Mersenne bases,
  `d ≡ 1 (4)` crown, `d ≡ 3 (8)` known-powers `l = 2` (fillChain level-1 identity),
  `d ≡ 7 (8)` delegated to `BarredGadgets`.  Exactly `d` fresh parameters per gadget.
- `Main.lean` — **`odd_realizable_pairs`** (`thm:odd-realizable-pairs`, structural
  half): strong induction, seven branches (base 3, crown `4k+1`, specials `15/27/31`
  via `P15`/`P27Full`/`P31Full`, and the two difference-of-squares steps through
  `eightk3_*`/`eightk7_*` with `Θ`-sets = θ-blocks ∪ recorded-power coefficient
  ranges).  Invariant: `CompatiblePair ⊥` at degree `n-1` + exact `n`-parameter
  decoder + recorded `H₂` (and `H₄` for `n ≥ 5`) in every coefficient-closed
  subalgebra.  Plus **`odd_coefficient_map_bijective`** (`cor:all-odd-decodable`
  coverage form) through Codex's `coefficient_aeval_bijective_of_monic_decodable`.
- **Dedicated `BarredGadgets` discharge complete**
  (`Examples/{BarQGeneral,BarredGadgets}.lean`,
  `barredGadgets_of_admissible`): `m=1` uses the optimized finite degree-15 decoder;
  `m≥2` uses the manuscript's `barQ_{8m+7}` circuit.  Its explicit relative decoder
  follows the top scalar pivots, determinant-`-m²` block, two boundary pivots, affine
  transport of `Rk2l_triangular`, and six low pivots.  The older recursive
  `barredGadgets_of_adm` in `Main.lean` is algebraically valid but costs one extra
  product per barred slot; it must be replaced by the dedicated endpoint in the
  schedule-faithful exact-count wrapper.
- **Fixed joint program attached**: `odd_realizable_pairs` now chooses one
  `Cost.JointPairProgram R ((n-1)/2)` in the same branch that constructs and decodes
  the pair.  `odd_realizable_pairs_free` instantiates that induction at the canonical
  free environment, and `odd_realizable_pairs_uniform_family` specializes the same
  fixed syntax to every finite key vector.  Thus the program precedes the keys in the
  quantifier order; the former detached `PairCost` conclusion is no longer part of the
  master invariant.  The unconditional algebraic endpoints
  `odd_realizable_pairs'`, `odd_coefficient_map_bijective`, and
  `monic_coefficient_map_bijective` still need only `n`-admissibility.
- **Full coverage endpoint** (`thm:construction-count`, coverage clause):
  `even_lift_bijective` (`P = x·Q + c₀` with the fresh constant as last coordinate),
  `septic_good` (new, in `Examples/Septic.lean`), and `monic_coefficient_map_bijective`
  — for EVERY `n ≥ 1`: affine (`n=1`), quadratic (`n=2`), septic (`n=7`), odd master
  (`n ≥ 3` odd, `≠ 7`), even lift of the odd master (`n ≥ 4` even, `≠ 8`), and even
  lift of the septic (`n = 8`).  Every monic degree-`n` coefficient vector is a unique
  instance of a decodable family.  Umbrella: 1714 jobs, zero sorries.

## Status

The table below is the authoritative live status.  The detailed audit in
**`notes/lean_remaining_work.md`** records the 2026-08-26 starting point and proof
obligations, but its per-file statuses are historical and must not override this table.

| Paper item | Lean | Status |
|---|---|---|
| visible algebra, transport, monotonicity | `Recover/Context.lean` | ✅ |
| `def:compatible-pair` | `Recover/Context.lean` `CompatiblePair` | ✅ |
| scalar triangular recovery | `Recover/Filtered.lean` `mem_obsAlg_of_scalarCert` | ✅ |
| block recovery (constant and known-coefficient matrices, explicit inverse/adjugate) | `Recover/Filtered.lean` `mem_of_blockCert`; `Recover/KnownBlock.lean` `mem_of_known_blockCert`, `mem_of_known_blockCert_of_det` | ✅ |
| top-window calculus (`lem:monic-cauchy-transport`, formerly local "R-Cauchy") | `Polynomial/TopWindow.lean` `coeff_mul_monic` | ✅ causal row and top-two specializations |
| `lem:peel-monic-factor`, `lem:monic-from-power(-boundary)`, `lem:monic-division`, `lem:square-gadget(-boundary)`, `lem:scalar-shift-square` | `Polynomial/` | ✅ |
| Additivity, Multiplicativity, square closure, `lem:x-alpha-extraction`, base pairs | `Recover/`; known-shift clause currently `Examples/P27Full.lean` | ✅ (both ordinary extraction and the full-window, already-known-shift descent) |
| `def:coefficient-triangular`, `lem:triangular-shift` | `Recover/Triangular.lean` | ✅ |
| `lem:triangular-implies-compatible` (compatibility half) | `Recover/Triangular.lean` `CoeffTriangular.toCompatiblePair` | ✅ |
| `lem:triangular-block-concatenation` (NEW in final tex) | `Recover/Triangular.lean` `adjoin_Ico_glue`, `side_data_absorb` | ✅ (glue lemmas; packaged form on demand) |
| `d`-admissibility predicate + monotonicity (NEW) | `FastPoly/Admissible.lean` `Admissible`, `admissible_of_charZero/charP` | ✅ |
| fill construction, `lem:fill-correctness` (all levels) | `Section4/FillTwo,Fill,FillRec` `fill_correct` | ✅ |
| `Q_{2^k-1}` defs + monic/degree + decodability | `Section4/Peeled.lean` `peel`, `peel_monic`, `peel_correct` | ✅ |
| `lem:Q-unitriangular` (slot induction, unit-pivot `CoeffTriangular` form) | `Section4/PeeledCert.lean`, `Section5/SlotSurj.lean` | ✅ `peel_unitriangular` for every level, fill-chain certificates, and slot surjectivity used by the complete `Rk2l_triangular` master |
| `T_{k,2^l}` definitions + fuel irrelevance | `Section5/T.lean` `TF`, `Tpair`, `TF_succ`, `TF_fuel` | ✅ (restructured; named branch components) |
| `T` structural layer (monic/degree `k·2^l`, all four branches) | `Section5/T.lean` `TF_good`, `Tpair_good`, `Rpair`, `Tpair_eq_pow_add_R` | ✅ (scalar-difference conditionality enters at `Rk2l`, not here) |
| `lem:Rk2l` (three stage tables, `lem:odd-T-cubic-loss`, R-top-two invariants inside the induction) | `Section5/Rk2l.lean` + `Rk2lTri*.lean`; `Section5/UBinomial.lean` `mul_pow_split`, `natDegree_uTail_le` | ✅ **COMPLETE — `Rk2l_triangular` (master, `Rk2lTriMaster.lean`) + `Rk2l_deg` + `Rk2l_lead` + `Rk2l_top_two`** (formerly: prerequisites ✅ incl. even-branch `R-top-two-even` COMPLETE (`Section5/Rk2lEven.lean`: `Rpair_even_fst/snd`, `eE1/eE2_top`, `even_sum_top/deg`, `Rpair_even_top`); odd branch: `R-odd-block-exp`, `oG₁/oG₂`-tops, `uPrincipal_top` (all ✅, `Rk2lOdd.lean`), `U`-binomial engine ✅ (`UBinomial.lean`); `R-top-two-odd` assembly (`odd_sum_top`, `Rpair_odd_top`) + shared-base decompositions + `Rpair_oddbase_top` (hsd consumer) ✅; master `Rk2l_deg` ✅ (`Section5/Rk2l.lean`, in umbrella); `Rk2l_lead` (γ_k form) ✅; σ-value lemmas ✅; `Rk2l_top_boundary` ✅ (freeze set source-complete); stage tables symbolically validated at (4,2), (5,2)-base, (3,3) incl. the low-block permutation (`tools/mers_slot_table.py`); design in `notes/rk2l_lean_design.md`) |
| `lem:Rk2l-leading-coeff`, `lem:Rk2l-top-boundary` (all four coefficients) | `Section5/Rk2l.lean`, `Section5/Rk2lTriMaster.lean` | ✅ `Rk2l_lead` and `Rk2l_top_two`; the latter uses only top-two tower data and feeds the barred seam decoder |
| `lem:causal-perturbed-T` (NEW) | `Section5/PerturbedT.lean` | ✅ **COMPLETE — `Tpair_compatiblePair` (Rk2l ∘ triangular-implies-compatible), `perturbed_Q_vis` (Q-coefficient pivots, slope M), `perturbed_delta_vis` (δ-row), `causal_perturbed_T` (compatible pair on `range (N - r)`; low rows from `Rk2l_triangular` at `Vis`-context `Vd`, high rows causal via the binomial split)** |
| `lem:4k+1-splittable`, `lem:Q4k+1-from-H2` (H₄-byproduct clause) | `Section5/{FourKPlusOne,QFourKOne}.lean`, `Section6/GadgetDecoders.lean` | ✅ unconditional compatible crown plus the five explicit V-relative decoder pivots and recorded quartic byproduct |
| `Q_{2^{l+1}k+(2^l-1)}` + `lem:Q-odd-degree-with-powers` (NEW) | `Section6/QOddDegree.lean` | ✅ **COMPLETE — `q_odd_degree_decodable`: every parameter block (fill-two, per-level fill data, Mersenne perturbation `β`, scalar `δ`, full inner `T`-block `α`) recovered from output coefficients + given powers; composes `fill_correct` ∘ `causal_perturbed_T` ∘ `peel_correct` ∘ `Rk2l_extract`** |
| unified `lem:barQ8k+7` for `k ≥ 1` (4×4 block, det `−k²`); optimized `k=1` base | `Examples/{BarredPivot,BarQ15,BarQGeneral,BarredGadgets}.lean` | ✅ finite `k=1` decoder + general `k≥2` circuit, exact reflection/top and boundary jets, explicit determinant block, affine triangular remainder transport, low pivots, and final V-relative `BarredGadgets` adapter |
| `𝒬_d` dispatch + `lem:odd-gadgets-H2H4` (NEW) | `Section6/Dispatch.lean`; `Examples/BarredGadgets.lean` | ✅ every residue class, including the dedicated barred endpoint, is implemented and consumed by `Main.lean` |
| `lem:8k+3-splittable`, `lem:8k+7-splittable` (conditional forms, −1 boundary constants) | `Section6/Induction.lean` | ✅ both compatibility and V-relative decodability halves; recorded powers are reconstructed before either gadget decoder is invoked |
| `lem:base-three-compatible` (NEW) | `Section6/SpecialCases.lean` `base_three_compatible` | ✅ (verified) |
| special cases 15/27/31 | `Examples/{P15,P27,P27Composition,P27Full,P31,P31Full}.lean` + `Section6/SpecialCases.lean` | ✅ `P15` full explicit decoder; reusable relative square-shell engine; `P31` complete actual construction (outer `-1,+1,-1` shells, recovery of the shared `H₂,H₄` tower, then explicit discharge of `barQ₁₅`, `Q₇`, `Q₃`); `P27` complete actual construction (five `q4k1` crown pivots, quartic byproduct, known-shift pair descent, eight-row triangular remainder decode, then explicit `Q₇,Q₃` discharge) |
| realized-compatible package: explicit pair, **byproduct fields (H₂, H₄)**, unconditional compatibility, and an actual shared fixed program | `Cost/{Circuit,MultiplicationProgram,PolynomialCircuit,FreeSpecialization,Realization*,OddGadget*}.lean`, `Main.lean`, `Instantiation.lean` | ✅ the master carries one branch-faithful `JointPairProgram`; free specialization gives one fixed syntax before all finite key environments |
| final odd theorem (excluding only the optimal degree-7 pair), plus all-degree decodable coverage | `Main.lean` | ✅ algebraic compatible-pair and bijective-coverage endpoints for every `n≥1`, plus `odd_realizable_pairs_uniform_family` with the exact `(n-1)/2`-product fixed program |
| `lem:polynomial-left-inverse-automorphism` (NEW; mathlib Noetherian argument) | `Automorphism.lean` | ✅ explicit adjoin-to-surjectivity argument + stabilized-kernel proof that a surjective Noetherian algebra endomorphism is injective; packaged as `MvPolynomial.algEquivOfDecodable` |
| free instantiation `A = MvPolynomial (Fin n) F`, provenance | `Instantiation.lean`, `Main.lean` | ✅ visible-algebra decoder specialized to free coordinates; coefficient substitution is bijective and packaged as a polynomial automorphism |
| cost model + `lem:fill-Q-count` + `lem:T-multiplication-count` + `lem:odd-gadgets-count` + `thm:construction-count` (+ even-degree lift, degrees 1-2) | `Cost/{Model,Counts,Gadgets,Final,Circuit,MultiplicationProgram,PolynomialProgram,SepticProgram,Realization*}.lean`, `Main.lean` | ✅ exact numerical recurrences, actual branch circuits, and the fixed `(n-1)/2`-product program carried by the master and specialized uniformly |
| addition accounting: exact share-aware recurrences, uniform `Aₙ ≤ 2n`, and `Aₙ ≤ 5n/4 + 6⌈log₂ n⌉² + 1` | `Cost/Additions/{T,Gadgets,Final}.lean`, compatibility import `Cost/Additions.lean`, `Cost/{PeeledCircuit,RetainedShiftTCircuit,RetainedShiftTCompiler,RetainedShiftTInstantiate,ShiftedPowerTowerCircuit,RealizationP27Optimized,PolynomialProgram,SepticProgram}.lean`, `Examples/SepticAdditions.lean` | ✅ symbolic bounds, literal ten-addition septic, one-addition final/even lifts, six-addition `8k+7` shell, binary known-powers compiler, exact retained-shift compiler, and a fixed degree-27 program with 13 products/43 additions; ✅ same-program capstone `Cost.construction_additions_checked` (`Cost/Additions/Realization.lean`, 2026-09-02): for every `n ≥ 1` one fixed `PolynomialProgram` with `≤ ⌊n/2⌋+1` products realizes its degree-`n` polynomial and its literal `additions` satisfy `≤ 2n` and `4·a ≤ 5n+24⌈log₂n⌉²+4`; built from `additionJointPairRealization_exists` (residue dispatch of the master) and `additionPolynomialRealization_exists`; standard axioms only; the program is the optimized schedule, not the master's height-optimal one |

| peeled known-powers gadget and complete logarithmic-height construction (`thm:construction-height`) | `Section4/Peeled.lean`, `Height/PeeledCircuit.lean`, `Main.lean`, `HeightFinal.lean`, `PaperMain.lean` | ✅ gadget decoder and ledger; the master carries the height bound, and the complete polynomial has height at most `2⌈log₂ n⌉+4` for odd `n` and `2⌈log₂ n⌉+5` for even `n`. No historical compiler work is needed for this result. |

## Conventions

- **Explicit decoding only** (repo rule, see `AGENTS.md`): every recovery proof exhibits
  the decoding expression (pivot/peel/division/block-inverse). No search, no `decide`,
  no solver black boxes; `omega`/`ring`/closed `simp only` sets are the only automation.

- New files import narrowly; keep `Mathlib.Tactic` out of the core files.
- Coefficient identities of concrete circuits (septic pattern): prove one `_eq` expansion by
  `simp only [map_*]; ring`, then extract with
  `simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]; norm_num`.
  These statements can be generated by `tools/` sympy scripts — do not hand-compute them.
- The old developments (`CompatiblePairs/`, `old_codex_lean/`) are reference material only;
  never imported. Salvage map: see the audit in the session notes.
