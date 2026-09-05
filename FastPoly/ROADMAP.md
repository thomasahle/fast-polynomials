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
- **Characteristic-two small-base boundary:** the appendix and
  `better_bounds/CHAR2_SMALL_BASES.md` now give explicit inverses for the worked
  degree-`7`, `9`, `11`, and `13` circuits.  The inverse for degree `7` is the only
  one of these presently formalized in Lean.  The degree-`9`, `11`, and `13`
  definitions in `Examples/OptimizedCircuits.lean` are the older search candidates,
  not the worked circuits now displayed in the appendix; their monicity/degree
  theorems remain valid but are not recovery theorems.  Formalizing the three worked
  inverses in a fresh `Examples/Char2SmallBases.lean` is pending; use filtered
  scalar/block certificates, not the expanded GF(4) decoder.
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
