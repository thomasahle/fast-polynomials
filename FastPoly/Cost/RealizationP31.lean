import FastPoly.Cost.PeeledCircuit
import FastPoly.Cost.PowerTowerCircuit
import FastPoly.Examples.P31Full
import FastPoly.Height.RealizationDepth

/-!
# Semantic realization of the degree-31 cost base

This file compiles the manuscript's exceptional degree-31 pair into one shared
arithmetic DAG.  Its multiplication budget is visible in five pieces:

* the common quadratic--quartic tower uses two products;
* the barred degree-15 block uses seven products;
* the Mersenne degree-7 and degree-3 blocks use three and one products;
* the two outer differences of squares use one product each.

Thus the complete circuit uses exactly `2 + 7 + 3 + 1 + 2 = 15`
multiplications.  The construction and all identities are over an arbitrary
commutative base ring; the characteristic assumptions needed by the decoder do
not enter the realization.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace ThirtyOne

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private def x : Circuit R PolyInput 1 := Circuit.polyX
private def a (i : ℕ) : Circuit R PolyInput 1 := Circuit.polyParameter i

/-! ## The shared quadratic--quartic tower -/

/-- Output order `(H₂,H₄,H₄,0)`.  The final two wires provide the
shifted-power and source labels expected by the reusable Mersenne compiler. -/
def tower : Circuit R PolyInput 4 :=
  Circuit.quadraticQuarticUnshifted x (a 7) (a 6) (a 5) (a 4)

@[simp] theorem eval_tower_zero (θ : ℕ → A) :
    (tower (R := R)).eval (polyEnv θ) 0 = FastPoly.P31Full.H2 θ := by
  rw [tower, Circuit.eval_quadraticQuarticUnshifted_zero]
  simp only [x, a, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.P31Full.H2, FastPoly.P15.H2]

@[simp] theorem eval_tower_one (θ : ℕ → A) :
    (tower (R := R)).eval (polyEnv θ) 1 = FastPoly.P31Full.H4 θ := by
  rw [tower, Circuit.eval_quadraticQuarticUnshifted_one]
  simp only [x, a, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.P31Full.H4,
    FastPoly.P15.H4, FastPoly.P15.H2]
  ring

@[simp] theorem eval_tower_two (θ : ℕ → A) :
    (tower (R := R)).eval (polyEnv θ) 2 = FastPoly.P31Full.H4 θ := by
  rw [tower, Circuit.eval_quadraticQuarticUnshifted_two]
  simp only [x, a, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.P31Full.H4, FastPoly.P15.H4, FastPoly.P15.H2]
  ring

@[simp] theorem eval_tower_three (θ : ℕ → A) :
    (tower (R := R)).eval (polyEnv θ) 3 = 0 := by
  rw [tower, Circuit.eval_quadraticQuarticUnshifted_three]

private theorem H2_eq_barH2 (θ : ℕ → A) :
    FastPoly.P31Full.H2 θ = FastPoly.BarQ15.H2 (θ 6) (θ 7) := by
  change FastPoly.P15.H2 θ = FastPoly.BarQ15.H2 (θ 6) (θ 7)
  rw [FastPoly.P15.H2_eq]
  simp only [FastPoly.BarQ15.H2, pow_one]

private theorem H4_eq_barH4 (θ : ℕ → A) :
    FastPoly.P31Full.H4 θ =
      FastPoly.BarQ15.H4 (FastPoly.P15.h0 θ) (FastPoly.P15.h1 θ)
        (FastPoly.P15.h2 θ) (FastPoly.P15.h3 θ) := by
  change FastPoly.P15.H4 θ =
    FastPoly.BarQ15.H4 (FastPoly.P15.h0 θ) (FastPoly.P15.h1 θ)
      (FastPoly.P15.h2 θ) (FastPoly.P15.h3 θ)
  rw [FastPoly.P15.H4_eq]
  simp only [FastPoly.BarQ15.H4, pow_one]

/-! ## The seven-product barred block -/

private abbrev TowerEnv := Sum PolyInput (Fin 4)
private abbrev SeedEnv := Sum TowerEnv (Fin 2)
private abbrev MiddleEnv := Sum SeedEnv (Fin 2)
private abbrev ColumnEnv := Sum MiddleEnv (Fin 2)

/-- First barred layer, in output order `(H₈,Q₃)`. -/
private def barSeed : Circuit R TowerEnv 2 :=
  let h₂ := Circuit.rightInput (R := R) (ι := PolyInput) (0 : Fin 4)
  let h₄ := Circuit.rightInput (R := R) (ι := PolyInput) (1 : Fin 4)
  let old (p : Circuit R PolyInput 1) : Circuit R TowerEnv 1 := p.liftLeft
  let h₈ := .add
    (.mul (.add h₄ (.add (old x) (old (a 17))))
      (.add h₄ (.add h₂ (old (a 18)))))
    (old (a 16))
  let q₃ := .add
    (.mul (.add (old x) (old (a 25))) (.add h₂ (old (a 24))))
    (old (a 23))
  .fork h₈ q₃

/-- Second barred layer, in output order `(U₀,V₀)`. -/
private def barMiddle : Circuit R SeedEnv 2 :=
  let h₈ := Circuit.rightInput (R := R) (ι := TowerEnv) (0 : Fin 2)
  let q₃ := Circuit.rightInput (R := R) (ι := TowerEnv) (1 : Fin 2)
  let h₄ := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 2) (1 : Fin 4)
  let oldest (p : Circuit R PolyInput 1) : Circuit R SeedEnv 1 := p.liftLeft.liftLeft
  let u₀ := .add (.mul (.add h₄ (oldest (a 29))) h₈) q₃
  let v₀ := .add
    (.mul (.add h₄ (oldest (a 30))) (.add h₈ (oldest (a 19))))
    (oldest (a 22))
  .fork u₀ v₀

/-- Third barred layer, in output order `(C₁,C₂)`. -/
private def barColumns : Circuit R MiddleEnv 2 :=
  let u₀ := Circuit.rightInput (R := R) (ι := SeedEnv) (0 : Fin 2)
  let v₀ := Circuit.rightInput (R := R) (ι := SeedEnv) (1 : Fin 2)
  let h₂ := Circuit.grandOutput (R := R) (ι := PolyInput)
    (n := 2) (o := 2) (0 : Fin 4)
  let oldest (p : Circuit R PolyInput 1) : Circuit R MiddleEnv 1 :=
    p.liftLeft.liftLeft.liftLeft
  let c₁ := .add (.mul (.add h₂ (oldest (a 27))) u₀) (oldest (a 21))
  let c₂ := .add (.mul (.add h₂ (oldest (a 28))) v₀) (oldest (a 20))
  .fork c₁ c₂

/-- Final barred layer, `(x+b₀)C₁+C₂`. -/
private def barFinish : Circuit R ColumnEnv 1 :=
  let c₁ := Circuit.rightInput (R := R) (ι := MiddleEnv) (0 : Fin 2)
  let c₂ := Circuit.rightInput (R := R) (ι := MiddleEnv) (1 : Fin 2)
  let oldest (p : Circuit R PolyInput 1) : Circuit R ColumnEnv 1 :=
    p.liftLeft.liftLeft.liftLeft.liftLeft
  .add (.mul (.add (oldest x) (oldest (a 26))) c₁) c₂

/-- The complete barred degree-15 block, consuming the already shared `H₂,H₄`
wires and introducing no duplicate tower computation. -/
private def barCircuit : Circuit R TowerEnv 1 :=
  .bind barSeed <| .bind barMiddle <| .bind barColumns barFinish

private noncomputable def towerEnv (θ : ℕ → A) : TowerEnv → A[X] :=
  Sum.elim (polyEnv θ) ((tower (R := R)).eval (polyEnv θ))

private noncomputable def seedEnv (θ : ℕ → A) : SeedEnv → A[X] :=
  Sum.elim (towerEnv (R := R) θ) ((barSeed (R := R)).eval (towerEnv (R := R) θ))

private noncomputable def middleEnv (θ : ℕ → A) : MiddleEnv → A[X] :=
  Sum.elim (seedEnv (R := R) θ) ((barMiddle (R := R)).eval (seedEnv (R := R) θ))

private noncomputable def columnEnv (θ : ℕ → A) : ColumnEnv → A[X] :=
  Sum.elim (middleEnv (R := R) θ)
    ((barColumns (R := R)).eval (middleEnv (R := R) θ))

private theorem eval_barSeed_zero (θ : ℕ → A) :
    (barSeed (R := R)).eval (towerEnv (R := R) θ) 0 =
      FastPoly.BarQ15.H8 (θ 6) (θ 7) (FastPoly.P15.h0 θ)
        (FastPoly.P15.h1 θ) (FastPoly.P15.h2 θ) (FastPoly.P15.h3 θ)
        (fun t => θ (16 + t)) := by
  rw [barSeed, Circuit.eval_fork_zero, towerEnv]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_rightInput,
    Circuit.eval_liftLeft, eval_tower_zero, eval_tower_one, x, a, Circuit.eval_polyX,
    Circuit.eval_polyParameter, FastPoly.BarQ15.H8, FastPoly.BarQ15.u,
    FastPoly.BarQ15.v, FastPoly.BarQ15.w, H2_eq_barH2, H4_eq_barH4]

private theorem eval_barSeed_one (θ : ℕ → A) :
    (barSeed (R := R)).eval (towerEnv (R := R) θ) 1 =
      FastPoly.BarQ15.Q3 (θ 6) (θ 7) (fun t => θ (16 + t)) := by
  rw [barSeed, Circuit.eval_fork_one, towerEnv]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_rightInput,
    Circuit.eval_liftLeft, eval_tower_zero, x, a, Circuit.eval_polyX,
    Circuit.eval_polyParameter,
    FastPoly.BarQ15.Q3, FastPoly.BarQ15.a, H2_eq_barH2]

private theorem eval_barMiddle_zero (θ : ℕ → A) :
    (barMiddle (R := R)).eval (seedEnv (R := R) θ) 0 =
      FastPoly.BarQ15.U0 (θ 6) (θ 7) (FastPoly.P15.h0 θ)
        (FastPoly.P15.h1 θ) (FastPoly.P15.h2 θ) (FastPoly.P15.h3 θ)
        (fun t => θ (16 + t)) := by
  rw [barMiddle, Circuit.eval_fork_zero, seedEnv]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_rightInput]
  rw [eval_barSeed_zero, eval_barSeed_one, towerEnv]
  simp only [Circuit.eval_priorOutput, Circuit.eval_liftLeft, eval_tower_one,
    a, Circuit.eval_polyParameter,
    FastPoly.BarQ15.U0, FastPoly.BarQ15.b, H4_eq_barH4]

private theorem eval_barMiddle_one (θ : ℕ → A) :
    (barMiddle (R := R)).eval (seedEnv (R := R) θ) 1 =
      FastPoly.BarQ15.V0 (θ 6) (θ 7) (FastPoly.P15.h0 θ)
        (FastPoly.P15.h1 θ) (FastPoly.P15.h2 θ) (FastPoly.P15.h3 θ)
        (fun t => θ (16 + t)) := by
  rw [barMiddle, Circuit.eval_fork_one, seedEnv]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_rightInput]
  rw [eval_barSeed_zero, towerEnv]
  simp only [Circuit.eval_priorOutput, Circuit.eval_liftLeft, eval_tower_one,
    a, Circuit.eval_polyParameter, FastPoly.BarQ15.V0,
    FastPoly.BarQ15.b, FastPoly.BarQ15.rho, FastPoly.BarQ15.a, H4_eq_barH4]

private theorem eval_barColumns_zero (θ : ℕ → A) :
    (barColumns (R := R)).eval (middleEnv (R := R) θ) 0 =
      FastPoly.BarQ15.C1 (θ 6) (θ 7) (FastPoly.P15.h0 θ)
        (FastPoly.P15.h1 θ) (FastPoly.P15.h2 θ) (FastPoly.P15.h3 θ)
        (fun t => θ (16 + t)) := by
  rw [barColumns, Circuit.eval_fork_zero, middleEnv]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_rightInput]
  rw [eval_barMiddle_zero, seedEnv, towerEnv]
  simp only [Circuit.eval_grandOutput, Circuit.eval_liftLeft, eval_tower_zero,
    a, Circuit.eval_polyParameter, FastPoly.BarQ15.C1,
    FastPoly.BarQ15.b, FastPoly.BarQ15.a, H2_eq_barH2]

private theorem eval_barColumns_one (θ : ℕ → A) :
    (barColumns (R := R)).eval (middleEnv (R := R) θ) 1 =
      FastPoly.BarQ15.C2 (θ 6) (θ 7) (FastPoly.P15.h0 θ)
        (FastPoly.P15.h1 θ) (FastPoly.P15.h2 θ) (FastPoly.P15.h3 θ)
        (fun t => θ (16 + t)) := by
  rw [barColumns, Circuit.eval_fork_one, middleEnv]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_rightInput]
  rw [eval_barMiddle_one, seedEnv, towerEnv]
  simp only [Circuit.eval_grandOutput, Circuit.eval_liftLeft, eval_tower_zero,
    a, Circuit.eval_polyParameter, FastPoly.BarQ15.C2,
    FastPoly.BarQ15.b, FastPoly.BarQ15.a, H2_eq_barH2]

private theorem eval_barFinish (θ : ℕ → A) :
    (barFinish (R := R)).eval (columnEnv (R := R) θ) 0 =
      FastPoly.P31Full.A15 θ := by
  rw [barFinish, columnEnv]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_rightInput]
  rw [eval_barColumns_zero, eval_barColumns_one, middleEnv, seedEnv, towerEnv]
  simp only [Circuit.eval_liftLeft, x, a,
    Circuit.eval_polyX, Circuit.eval_polyParameter, FastPoly.P31Full.A15,
    FastPoly.BarQ15.barQ15, FastPoly.BarQ15.b]

private theorem eval_barCircuit (θ : ℕ → A) :
    (barCircuit (R := R)).eval (towerEnv (R := R) θ) 0 =
      FastPoly.P31Full.A15 θ := by
  rw [barCircuit, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [seedEnv, middleEnv, columnEnv] using eval_barFinish (R := R) θ

/-! ## The two ordinary Mersenne blocks -/

/-- Common tower wiring for both `Q₇` and `Q₃`; only the parameter offset differs. -/
private def mersWiring (offset : ℕ) : ConstructionWiring 4 where
  power i := if i = 1 then .inr 0 else if i = 2 then .inr 1 else .inr 3
  shiftedPower := .inr 2
  parameter i := offset + i
  source _ := .inr 3

private def bCircuit : Circuit R TowerEnv 1 :=
  (peelCircuit (R := R) 3).instantiateConstruction (mersWiring 8)

private def cCircuit : Circuit R TowerEnv 1 :=
  (peelCircuit (R := R) 2).instantiateConstruction (mersWiring 1)

private theorem eval_mersWiring_power (θ : ℕ → A) (offset : ℕ) :
    (mersWiring offset).powerValues θ ((tower (R := R)).eval (polyEnv θ)) =
      FastPoly.P31Full.Hp θ := by
  funext i
  by_cases h1 : i = 1
  · subst i
    simp only [ConstructionWiring.powerValues, mersWiring, if_pos, Sum.elim_inr,
      eval_tower_zero, FastPoly.P31Full.Hp]
  · by_cases h2 : i = 2
    · subst i
      simp only [ConstructionWiring.powerValues, mersWiring, h1, if_false,
        if_pos, Sum.elim_inr, eval_tower_one, FastPoly.P31Full.Hp]
    · simp only [ConstructionWiring.powerValues, mersWiring, h1, h2,
        if_false, Sum.elim_inr, eval_tower_three, FastPoly.P31Full.Hp]

private theorem eval_bCircuit (θ : ℕ → A) :
    (bCircuit (R := R)).eval (towerEnv (R := R) θ) 0 =
      FastPoly.P31Full.B7 θ := by
  rw [bCircuit, towerEnv, Circuit.eval_instantiateConstruction,
    eval_mersWiring_power]
  simp only [ConstructionWiring.shiftedValue,
    mersWiring, Sum.elim_inr, eval_tower_two,
    FastPoly.P31Full.B7]
  exact eval_peelCircuit (R := R) (FastPoly.P31Full.Hp θ)
    (FastPoly.P31Full.H4 θ) (fun i => θ (8 + i)) (fun _ => 0) 3

private theorem eval_cCircuit (θ : ℕ → A) :
    (cCircuit (R := R)).eval (towerEnv (R := R) θ) 0 =
      FastPoly.P31Full.C3 θ := by
  rw [cCircuit, towerEnv, Circuit.eval_instantiateConstruction,
    eval_mersWiring_power]
  simp only [ConstructionWiring.shiftedValue,
    mersWiring, Sum.elim_inr, eval_tower_two,
    FastPoly.P31Full.C3]
  exact eval_peelCircuit (R := R) (FastPoly.P31Full.Hp θ)
    (FastPoly.P31Full.H4 θ) (fun i => θ (1 + i)) (fun _ => 0) 2

/-! ## Bind all inner blocks once, then form the two outer shells -/

/-- Output order `(A₁₅,B₇,C₃)`. -/
private def innerBlocks : Circuit R TowerEnv 3 :=
  .fork barCircuit (.fork bCircuit cCircuit)

private theorem eval_innerBlocks_zero (θ : ℕ → A) :
    (innerBlocks (R := R)).eval (towerEnv (R := R) θ) 0 =
      FastPoly.P31Full.A15 θ := by
  rw [innerBlocks, Circuit.eval_triple_zero, eval_barCircuit]

private theorem eval_innerBlocks_one (θ : ℕ → A) :
    (innerBlocks (R := R)).eval (towerEnv (R := R) θ) 1 =
      FastPoly.P31Full.B7 θ := by
  rw [innerBlocks, Circuit.eval_triple_one, eval_bCircuit]

private theorem eval_innerBlocks_two (θ : ℕ → A) :
    (innerBlocks (R := R)).eval (towerEnv (R := R) θ) 2 =
      FastPoly.P31Full.C3 θ := by
  rw [innerBlocks, Circuit.eval_triple_two, eval_cCircuit]

private abbrev InnerEnv := Sum TowerEnv (Fin 3)

/-- The two one-product outer differences of squares, together with the retained
quadratic and quartic byproducts. -/
private def outerCircuit : Circuit R InnerEnv 4 :=
  let A₁₅ := Circuit.rightInput (R := R) (ι := TowerEnv) (0 : Fin 3)
  let B₇ := Circuit.rightInput (R := R) (ι := TowerEnv) (1 : Fin 3)
  let C₃ := Circuit.rightInput (R := R) (ι := TowerEnv) (2 : Fin 3)
  let H₂ := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 3) (0 : Fin 4)
  let H₄ := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 3) (1 : Fin 4)
  let oldest (p : Circuit R PolyInput 1) : Circuit R InnerEnv 1 := p.liftLeft.liftLeft
  let T₁ := Circuit.diffSquareAdd A₁₅ B₇ C₃
  let T₂ := Circuit.diffSquareAdd (.add A₁₅ (oldest (a 15))) H₄
    (oldest (a 0))
  Circuit.pairWithPowers T₁ T₂ H₂ H₄

private noncomputable def innerEnv (θ : ℕ → A) : InnerEnv → A[X] :=
  Sum.elim (towerEnv (R := R) θ)
    ((innerBlocks (R := R)).eval (towerEnv (R := R) θ))

private theorem eval_outer_zero (θ : ℕ → A) :
    (outerCircuit (R := R)).eval (innerEnv (R := R) θ) 0 =
      FastPoly.P31Full.T1 θ := by
  rw [outerCircuit, Circuit.eval_pairWithPowers_zero, innerEnv]
  simp only [Circuit.eval_diffSquareAdd, Circuit.eval_rightInput]
  rw [eval_innerBlocks_zero, eval_innerBlocks_one, eval_innerBlocks_two]
  simp only [FastPoly.P31Full.T1, FastPoly.P31.T1, pow_two]
  ring

private theorem eval_outer_one (θ : ℕ → A) :
    (outerCircuit (R := R)).eval (innerEnv (R := R) θ) 1 =
      FastPoly.P31Full.T2 θ := by
  rw [outerCircuit, Circuit.eval_pairWithPowers_one, innerEnv]
  simp only [Circuit.eval_diffSquareAdd, Circuit.eval_add,
    Circuit.eval_rightInput, Circuit.eval_liftLeft]
  rw [eval_innerBlocks_zero, towerEnv]
  simp only [Circuit.eval_priorOutput, Circuit.eval_liftLeft,
    eval_tower_one, a, Circuit.eval_polyParameter,
    FastPoly.P31Full.T2, FastPoly.P31.T2, pow_two]
  ring

private theorem eval_outer_two (θ : ℕ → A) :
    (outerCircuit (R := R)).eval (innerEnv (R := R) θ) 2 =
      FastPoly.P31Full.H2 θ := by
  rw [outerCircuit, Circuit.eval_pairWithPowers_two, innerEnv, towerEnv,
    Circuit.eval_priorOutput, eval_tower_zero]

private theorem eval_outer_three (θ : ℕ → A) :
    (outerCircuit (R := R)).eval (innerEnv (R := R) θ) 3 =
      FastPoly.P31Full.H4 θ := by
  rw [outerCircuit, Circuit.eval_pairWithPowers_three, innerEnv, towerEnv,
    Circuit.eval_priorOutput, eval_tower_one]

/-! ## Full realization and exact multiplication count -/

/-- Full circuit in output order `(T¹₃₁,T²₃₁,H₂,H₄)`. -/
def circuit : Circuit R PolyInput 4 :=
  .bind tower <| .bind innerBlocks outerCircuit

@[simp] theorem tower_multiplications :
    (tower (R := R)).gates.multiplications = 2 := by
  rw [tower, Circuit.gates_quadraticQuarticUnshifted_multiplications]
  rfl

@[simp] theorem tower_additions :
    (tower (R := R)).gates.additions = 6 := by
  rw [tower, Circuit.gates_quadraticQuarticUnshifted_additions]
  rfl

omit [CommRing R] in
@[simp] theorem barSeed_multiplications :
    (barSeed (R := R)).gates.multiplications = 2 := by
  rfl

omit [CommRing R] in
@[simp] theorem barSeed_additions :
    (barSeed (R := R)).gates.additions = 8 := by
  rfl

omit [CommRing R] in
@[simp] theorem barMiddle_multiplications :
    (barMiddle (R := R)).gates.multiplications = 2 := by
  rfl

omit [CommRing R] in
@[simp] theorem barMiddle_additions :
    (barMiddle (R := R)).gates.additions = 5 := by
  rfl

omit [CommRing R] in
@[simp] theorem barColumns_multiplications :
    (barColumns (R := R)).gates.multiplications = 2 := by
  rfl

omit [CommRing R] in
@[simp] theorem barColumns_additions :
    (barColumns (R := R)).gates.additions = 4 := by
  rfl

omit [CommRing R] in
@[simp] theorem barFinish_multiplications :
    (barFinish (R := R)).gates.multiplications = 1 := by
  rfl

omit [CommRing R] in
@[simp] theorem barFinish_additions :
    (barFinish (R := R)).gates.additions = 2 := by
  rfl

omit [CommRing R] in
@[simp] theorem barCircuit_multiplications :
    (barCircuit (R := R)).gates.multiplications = 7 := by
  simp only [barCircuit, Circuit.gates_bind, GateCount.add_multiplications,
    barSeed_multiplications, barMiddle_multiplications,
    barColumns_multiplications, barFinish_multiplications]

omit [CommRing R] in
@[simp] theorem barCircuit_additions :
    (barCircuit (R := R)).gates.additions = 19 := by
  simp only [barCircuit, Circuit.gates_bind, GateCount.add_additions,
    barSeed_additions, barMiddle_additions, barColumns_additions,
    barFinish_additions]

omit [CommRing R] in
@[simp] theorem bCircuit_multiplications :
    (bCircuit (R := R)).gates.multiplications = 3 := by
  rw [bCircuit, Circuit.gates_instantiateConstruction,
    gates_peelCircuit_multiplications (R := R) 3 (by omega)]
  norm_num

omit [CommRing R] in
@[simp] theorem bCircuit_additions :
    (bCircuit (R := R)).gates.additions = 8 := by
  rw [bCircuit, Circuit.gates_instantiateConstruction]
  rfl

omit [CommRing R] in
@[simp] theorem cCircuit_multiplications :
    (cCircuit (R := R)).gates.multiplications = 1 := by
  rw [cCircuit, Circuit.gates_instantiateConstruction,
    gates_peelCircuit_multiplications (R := R) 2 (by omega)]
  norm_num

omit [CommRing R] in
@[simp] theorem cCircuit_additions :
    (cCircuit (R := R)).gates.additions = 3 := by
  rw [cCircuit, Circuit.gates_instantiateConstruction]
  rfl

omit [CommRing R] in
@[simp] theorem innerBlocks_multiplications :
    (innerBlocks (R := R)).gates.multiplications = 11 := by
  simp only [innerBlocks, Circuit.gates_fork, GateCount.add_multiplications,
    barCircuit_multiplications, bCircuit_multiplications,
    cCircuit_multiplications]

omit [CommRing R] in
@[simp] theorem innerBlocks_additions :
    (innerBlocks (R := R)).gates.additions = 30 := by
  simp only [innerBlocks, Circuit.gates_fork, GateCount.add_additions,
    barCircuit_additions, bCircuit_additions, cCircuit_additions]

omit [CommRing R] in
@[simp] theorem outerCircuit_multiplications :
    (outerCircuit (R := R)).gates.multiplications = 2 := by
  simp only [outerCircuit, Circuit.gates_pairWithPowers,
    GateCount.add_multiplications, Circuit.gates_diffSquareAdd_multiplications,
    Circuit.gates, Circuit.gates_rightInput, Circuit.gates_priorOutput,
    Circuit.gates_liftLeft, a, Circuit.polyParameter, Circuit.gates_input,
    GateCount.zero_multiplications, GateCount.adds_multiplications]

omit [CommRing R] in
@[simp] theorem outerCircuit_additions :
    (outerCircuit (R := R)).gates.additions = 7 := by
  simp only [outerCircuit, Circuit.gates_pairWithPowers,
    GateCount.add_additions, Circuit.gates_diffSquareAdd_additions,
    Circuit.gates, Circuit.gates_rightInput, Circuit.gates_priorOutput,
    Circuit.gates_liftLeft, a, Circuit.polyParameter, Circuit.gates_input,
    GateCount.zero_additions, GateCount.adds_additions]

/-- Exact count for the actual shared degree-31 circuit. -/
theorem circuit_multiplications :
    (circuit (R := R)).gates.multiplications = 15 := by
  simp only [circuit, Circuit.gates_bind, GateCount.add_multiplications,
    tower_multiplications, innerBlocks_multiplications,
    outerCircuit_multiplications]

/-- Exact addition count of the same shared degree-31 circuit. -/
theorem circuit_additions :
    (circuit (R := R)).gates.additions = 43 := by
  simp only [circuit, Circuit.gates_bind, GateCount.add_additions,
    tower_additions, innerBlocks_additions, outerCircuit_additions]

theorem eval_circuit_zero (θ : ℕ → A) :
    (circuit (R := R)).eval (polyEnv θ) 0 = FastPoly.P31Full.T1 θ := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [towerEnv, innerEnv] using eval_outer_zero (R := R) θ

theorem eval_circuit_one (θ : ℕ → A) :
    (circuit (R := R)).eval (polyEnv θ) 1 = FastPoly.P31Full.T2 θ := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [towerEnv, innerEnv] using eval_outer_one (R := R) θ

theorem eval_circuit_two (θ : ℕ → A) :
    (circuit (R := R)).eval (polyEnv θ) 2 = FastPoly.P31Full.H2 θ := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [towerEnv, innerEnv] using eval_outer_two (R := R) θ

theorem eval_circuit_three (θ : ℕ → A) :
    (circuit (R := R)).eval (polyEnv θ) 3 = FastPoly.P31Full.H4 θ := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [towerEnv, innerEnv] using eval_outer_three (R := R) θ

/-- Height ledger of the degree-31 circuit: each inner block is bounded by its own
product count over the depth-two tower, and the two outer shells add one level. -/
theorem multDepth_circuit_le :
    ((circuit (R := R)).multDepth (fun _ => 0) 0 ≤ 2 * Nat.clog 2 31 + 3) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 1 ≤ 2 * Nat.clog 2 31 + 3) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 2 ≤ 1) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 3 ≤ 2) := by
  obtain ⟨ht0, ht1, ht2, ht3⟩ := Height.multDepth_quadraticQuarticUnshifted_le
    (x (R := R)) (a 7) (a 6) (a 5) (a 4) (fun _ => 0) rfl rfl rfl rfl rfl
  rw [show Circuit.quadraticQuarticUnshifted (x (R := R)) (a 7) (a 6) (a 5) (a 4)
      = tower from rfl] at ht0 ht1 ht2 ht3
  have henv : ∀ i, (Sum.elim (fun _ : PolyInput => (0 : ℕ))
      ((tower (R := R)).multDepth (fun _ => 0))) i ≤ 2 := by
    intro i
    rcases i with i | i
    · exact Nat.zero_le 2
    · match i with
      | 0 => exact ht0.trans (by omega)
      | 1 => exact ht1
      | 2 => exact ht2
      | 3 => exact ht3.trans (by omega)
  have hbar := Circuit.multDepth_le_multiplications (barCircuit (R := R))
    (d := 2) henv 0
  rw [barCircuit_multiplications] at hbar
  have hb := Circuit.multDepth_le_multiplications (bCircuit (R := R))
    (d := 2) henv 0
  rw [bCircuit_multiplications] at hb
  have hcc := Circuit.multDepth_le_multiplications (cCircuit (R := R))
    (d := 2) henv 0
  rw [cCircuit_multiplications] at hcc
  have hc : 4 ≤ Nat.clog 2 31 := by
    have h16 := Height.clog_two_sixteen
    have hmono := Nat.clog_mono_right 2 (show (16 : ℕ) ≤ 31 by omega)
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, outerCircuit, innerBlocks,
      Circuit.pairWithPowers, Circuit.multDepth_fork, Fin.addCases_left,
      Fin.addCases_right, Height.multDepth_diffSquareAdd,
      Circuit.multDepth_rightInput, Circuit.priorOutput, Circuit.multDepth_input,
      Sum.elim_inl,
      Sum.elim_inr,
      show (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) from rfl,
      show (1 : Fin 3) = Fin.natAdd 1 (Fin.castAdd 1 (0 : Fin 1)) from rfl,
      show (2 : Fin 3) = Fin.natAdd 1 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    omega
  · rw [show (1 : Fin 4) = Fin.castAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, outerCircuit, innerBlocks,
      Circuit.pairWithPowers, Circuit.multDepth_fork, Fin.addCases_left,
      Fin.addCases_right, Height.multDepth_diffSquareAdd,
      Circuit.multDepth_rightInput, Circuit.priorOutput,
      Circuit.multDepth_add, Circuit.multDepth_liftLeft, Sum.elim_inl,
      Sum.elim_inr, a, Circuit.polyParameter, Circuit.input,
      Circuit.multDepth_wire,
      show (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) from rfl]
    omega
  · rw [show (2 : Fin 4) = Fin.natAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, outerCircuit,
      Circuit.pairWithPowers, Circuit.multDepth_fork, Fin.addCases_left,
      Fin.addCases_right, Circuit.priorOutput, Circuit.multDepth_input,
      Sum.elim_inl, Sum.elim_inr]
    exact ht0
  · rw [show (3 : Fin 4) = Fin.natAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, outerCircuit,
      Circuit.pairWithPowers, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.priorOutput, Circuit.multDepth_input,
      Sum.elim_inl, Sum.elim_inr]
    exact ht1

/-- Exact joint realization of the manuscript's degree-31 witness. -/
def realized (θ : ℕ → A) :
    JointPairRealization (R := R) θ
      (FastPoly.P31Full.T1 θ) (FastPoly.P31Full.T2 θ)
      (FastPoly.P31Full.H2 θ) (FastPoly.P31Full.H4 θ) 15 where
  circuit := circuit
  eval₁ := eval_circuit_zero θ
  eval₂ := eval_circuit_one θ
  evalH₂ := eval_circuit_two θ
  evalH₄ := eval_circuit_three θ
  multiplication_count := circuit_multiplications

theorem realizable (θ : ℕ → A) :
    JointPairRealizable (R := R) θ
      (FastPoly.P31Full.T1 θ) (FastPoly.P31Full.T2 θ)
      (FastPoly.P31Full.H2 θ) (FastPoly.P31Full.H4 θ) 15 :=
  ⟨realized θ⟩

end ThirtyOne

end FastPoly.Cost
