import FastPoly.Cost.PeeledCircuit
import FastPoly.Cost.PowerTowerCircuit
import FastPoly.Cost.TCircuitCount
import FastPoly.Examples.P27Full
import FastPoly.Height.RealizationDepth

/-!
# Semantic realization of the degree-27 cost base

The degree-27 construction has four genuinely shared layers:

* a two-product quadratic--quartic tower;
* the four-product `T_{3,4}` pair and the one-product crown producing `Q₁₃`;
* the one- and three-product Mersenne gadgets `Q₃` and `Q₇`;
* two one-product difference-of-squares shells producing the final pair.

Each layer below is introduced by `Circuit.bind`.  Thus the exact count belongs to the
same DAG that outputs `P27Full.T1`, `P27Full.T2`, and their shared quadratic and quartic
byproducts.  All semantic identities are commutative-ring identities; no characteristic
or unit hypothesis occurs in this file.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace TwentySeven

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private def x : Circuit R PolyInput 1 := Circuit.polyX
private def a (i : ℕ) : Circuit R PolyInput 1 := Circuit.polyParameter i

/-! ## The shared quadratic--quartic tower -/

/-- The crown uses `H₂+θ₂₅`, while the final pair records the unshifted `H₂`.
This producer computes the shifted quadratic directly and derives both quartics from it.
Its output order is `(H₂+θ₂₅,H₄,H₄+θ₂₄,0)`. -/
private def shiftedTower : Circuit R PolyInput 4 :=
  Circuit.quadraticQuartic x (a 3) (.add (a 2) (a 25)) (a 23) (a 22) (a 24)

/-- Output order `(H₂,H₂+θ₂₅,H₄,H₄+θ₂₄,0)`.  Recovering the unshifted quadratic is
an addition, so retaining both wires costs no multiplication. -/
def tower : Circuit R PolyInput 5 :=
  .bind shiftedTower <|
    let h₂s := Circuit.rightInput (R := R) (ι := PolyInput) (0 : Fin 4)
    let h₄ := Circuit.rightInput (R := R) (ι := PolyInput) (1 : Fin 4)
    let h₄s := Circuit.rightInput (R := R) (ι := PolyInput) (2 : Fin 4)
    let zero := Circuit.rightInput (R := R) (ι := PolyInput) (3 : Fin 4)
    let old (p : Circuit R PolyInput 1) := p.liftLeft
    .fork
      (Circuit.pairWithPowers (.sub h₂s (old (a 25))) h₂s h₄ h₄s)
      zero

private theorem H2_coeff_one (theta : ℕ → A) :
    (FastPoly.P27Full.H2 theta).coeff 1 = theta 3 := by
  change (FastPoly.crownH2 (theta 3) (theta 2)).coeff 1 = theta 3
  exact FastPoly.crownH2_coeff_one

private theorem H2_coeff_zero (theta : ℕ → A) :
    (FastPoly.P27Full.H2 theta).coeff 0 = theta 2 := by
  change (FastPoly.crownH2 (theta 3) (theta 2)).coeff 0 = theta 2
  exact FastPoly.crownH2_coeff_zero

@[simp] private theorem eval_shiftedTower_zero (theta : ℕ → A) :
    (shiftedTower (R := R)).eval (polyEnv theta) 0 =
      FastPoly.crownH2 ((FastPoly.P27Full.H2 theta).coeff 1)
        ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25) := by
  rw [shiftedTower, Circuit.eval_quadraticQuartic_zero]
  simp only [x, a, Circuit.eval_add, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.crownH2, H2_coeff_one, H2_coeff_zero, map_add]

@[simp] private theorem eval_shiftedTower_one (theta : ℕ → A) :
    (shiftedTower (R := R)).eval (polyEnv theta) 1 = FastPoly.P27Full.H4 theta := by
  rw [shiftedTower, Circuit.eval_quadraticQuartic_one]
  simp only [x, a, Circuit.eval_add, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.P27Full.H4, FastPoly.crownH4, FastPoly.crownH2,
    H2_coeff_one, H2_coeff_zero, map_add]

@[simp] private theorem eval_shiftedTower_two (theta : ℕ → A) :
    (shiftedTower (R := R)).eval (polyEnv theta) 2 =
      FastPoly.P27Full.H4 theta + C (theta 24) := by
  rw [shiftedTower, Circuit.eval_quadraticQuartic_two]
  simp only [x, a, Circuit.eval_add, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.P27Full.H4, FastPoly.crownH4, FastPoly.crownH2,
    H2_coeff_one, H2_coeff_zero, map_add]

@[simp] private theorem eval_shiftedTower_three (theta : ℕ → A) :
    (shiftedTower (R := R)).eval (polyEnv theta) 3 = 0 := by
  rw [shiftedTower, Circuit.eval_quadraticQuartic_three]

@[simp] theorem eval_tower_zero (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 0 = FastPoly.P27Full.H2 theta := by
  rw [tower, Circuit.eval_bind]
  change (shiftedTower (R := R)).eval (polyEnv theta) 0 - C (theta 25) = _
  rw [eval_shiftedTower_zero]
  rw [H2_coeff_one, H2_coeff_zero]
  simp only [FastPoly.crownH2, FastPoly.P27Full.H2,
    FastPoly.P27Composition.H2, FastPoly.P27.H2, map_add]
  ring

@[simp] theorem eval_tower_one (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 1 =
      FastPoly.crownH2 ((FastPoly.P27Full.H2 theta).coeff 1)
        ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25) := by
  rw [tower, Circuit.eval_bind]
  change (shiftedTower (R := R)).eval (polyEnv theta) 0 = _
  exact eval_shiftedTower_zero theta

@[simp] theorem eval_tower_two (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 2 = FastPoly.P27Full.H4 theta := by
  rw [tower, Circuit.eval_bind]
  change (shiftedTower (R := R)).eval (polyEnv theta) 1 = _
  exact eval_shiftedTower_one theta

@[simp] theorem eval_tower_three (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 3 =
      FastPoly.P27Full.H4 theta + C (theta 24) := by
  rw [tower, Circuit.eval_bind]
  change (shiftedTower (R := R)).eval (polyEnv theta) 2 = _
  exact eval_shiftedTower_two theta

@[simp] theorem eval_tower_four (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 4 = 0 := by
  rw [tower, Circuit.eval_bind]
  change (shiftedTower (R := R)).eval (polyEnv theta) 3 = 0
  exact eval_shiftedTower_three theta

/-! ## The degree-13 crown -/

/-- Wire the shared tower into the local `T_{3,4}` compiler. -/
def tWiring : ConstructionWiring 5 where
  power i := if i = 1 then .inr 1 else if i = 2 then .inr 2 else .inl .variable
  shiftedPower := .inr 3
  parameter i := 14 + i
  source _ := .inr 4

private def tLocal : Circuit R (Sum PolyInput (Fin 5)) 2 :=
  (tCircuit (R := R) 3 2).instantiateConstruction tWiring

private noncomputable def towerEnv (theta : ℕ → A) : Sum PolyInput (Fin 5) → A[X] :=
  Sum.elim (polyEnv theta) ((tower (R := R)).eval (polyEnv theta))

theorem eval_tWiring_power (theta : ℕ → A) :
    tWiring.powerValues theta ((tower (R := R)).eval (polyEnv theta)) =
      FastPoly.crownHp ((FastPoly.P27Full.H2 theta).coeff 1)
        ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25)
        (theta 23) (theta 22) := by
  funext i
  by_cases h1 : i = 1
  · subst i
    simp only [ConstructionWiring.powerValues, tWiring, if_pos, Sum.elim_inr,
      eval_tower_one, FastPoly.crownHp_one]
  · by_cases h2 : i = 2
    · subst i
      simp only [ConstructionWiring.powerValues, tWiring, h1, if_false, if_pos,
        Sum.elim_inr, eval_tower_two, FastPoly.crownHp_two]
      unfold FastPoly.P27Full.H4 FastPoly.crownH4
      ring
    · simp only [ConstructionWiring.powerValues, tWiring, h1, h2, if_false,
        Sum.elim_inl, polyEnv_variable, FastPoly.crownHp]

theorem eval_tLocal (theta : ℕ → A) :
    ((tLocal (R := R)).eval (towerEnv (R := R) theta) 0,
      (tLocal (R := R)).eval (towerEnv (R := R) theta) 1) =
      FastPoly.Tpair
        (FastPoly.crownHp ((FastPoly.P27Full.H2 theta).coeff 1)
          ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25)
          (theta 23) (theta 22))
        (FastPoly.P27Full.H4 theta + C (theta 24)) 3 2
        (fun i => theta (14 + i)) := by
  rw [tLocal, towerEnv, Circuit.eval_instantiateConstruction, eval_tWiring_power]
  simp only [ConstructionWiring.shiftedValue, tWiring, Sum.elim_inr,
    eval_tower_three]
  exact eval_tCircuit (R := R)
    (FastPoly.crownHp ((FastPoly.P27Full.H2 theta).coeff 1)
      ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25)
      (theta 23) (theta 22))
    (FastPoly.P27Full.H4 theta + C (theta 24))
    (fun i => theta (14 + i)) 3 2

@[simp] private theorem eval_tLocal_zero (theta : ℕ → A) :
    (tLocal (R := R)).eval (towerEnv (R := R) theta) 0 =
      (FastPoly.Tpair
        (FastPoly.crownHp ((FastPoly.P27Full.H2 theta).coeff 1)
          ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25)
          (theta 23) (theta 22))
        (FastPoly.P27Full.H4 theta + C (theta 24)) 3 2
        (fun i => theta (14 + i))).1 := by
  exact congrArg Prod.fst (eval_tLocal (R := R) theta)

@[simp] private theorem eval_tLocal_one (theta : ℕ → A) :
    (tLocal (R := R)).eval (towerEnv (R := R) theta) 1 =
      (FastPoly.Tpair
        (FastPoly.crownHp ((FastPoly.P27Full.H2 theta).coeff 1)
          ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25)
          (theta 23) (theta 22))
        (FastPoly.P27Full.H4 theta + C (theta 24)) 3 2
        (fun i => theta (14 + i))).2 := by
  exact congrArg Prod.snd (eval_tLocal (R := R) theta)

private abbrev TFinishEnv := Sum (Sum PolyInput (Fin 5)) (Fin 2)

/-- Multiply the first `T_{3,4}` component by `X+θ₂₆`, add the second component,
and retain the two advertised powers.  Output order is `(Q₁₃,H₂,H₄,0)`. -/
private def tFinish : Circuit R TFinishEnv 4 :=
  let t₁ := Circuit.rightInput (R := R) (ι := Sum PolyInput (Fin 5)) (0 : Fin 2)
  let t₂ := Circuit.rightInput (R := R) (ι := Sum PolyInput (Fin 5)) (1 : Fin 2)
  let h₂ := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 2) (0 : Fin 5)
  let h₄ := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 2) (2 : Fin 5)
  let zero := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 2) (4 : Fin 5)
  let old (p : Circuit R PolyInput 1) : Circuit R TFinishEnv 1 := p.liftLeft.liftLeft
  let q₁₃ := .add (.mul (.add (old x) (old (a 26))) t₁) t₂
  Circuit.pairWithPowers q₁₃ h₂ h₄ zero

private noncomputable def tFinishEnv (theta : ℕ → A) : TFinishEnv → A[X] :=
  Sum.elim (towerEnv (R := R) theta)
    ((tLocal (R := R)).eval (towerEnv (R := R) theta))

@[simp] theorem eval_tFinish_zero (theta : ℕ → A) :
    (tFinish (R := R)).eval (tFinishEnv (R := R) theta) 0 =
      FastPoly.P27Full.A13 theta := by
  change (X + C (theta 26)) *
      (tLocal (R := R)).eval (towerEnv (R := R) theta) 0 +
      (tLocal (R := R)).eval (towerEnv (R := R) theta) 1 = _
  rw [eval_tLocal_zero, eval_tLocal_one]
  rfl

@[simp] theorem eval_tFinish_one (theta : ℕ → A) :
    (tFinish (R := R)).eval (tFinishEnv (R := R) theta) 1 =
      FastPoly.P27Full.H2 theta := by
  simp only [tFinish, Circuit.eval_pairWithPowers_one,
    tFinishEnv, towerEnv, Circuit.eval_priorOutput, eval_tower_zero]

@[simp] theorem eval_tFinish_two (theta : ℕ → A) :
    (tFinish (R := R)).eval (tFinishEnv (R := R) theta) 2 =
      FastPoly.P27Full.H4 theta := by
  simp only [tFinish, Circuit.eval_pairWithPowers_two,
    tFinishEnv, towerEnv, Circuit.eval_priorOutput, eval_tower_two]

@[simp] theorem eval_tFinish_three (theta : ℕ → A) :
    (tFinish (R := R)).eval (tFinishEnv (R := R) theta) 3 = 0 := by
  simp only [tFinish, Circuit.eval_pairWithPowers_three,
    tFinishEnv, towerEnv, Circuit.eval_priorOutput, eval_tower_four]

/-- Shared producer in output order `(Q₁₃,H₂,H₄,0)`. -/
def a13Circuit : Circuit R PolyInput 4 :=
  .bind tower (.bind tLocal tFinish)

@[simp] theorem eval_a13Circuit_zero (theta : ℕ → A) :
    (a13Circuit (R := R)).eval (polyEnv theta) 0 = FastPoly.P27Full.A13 theta := by
  rw [a13Circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [towerEnv, tFinishEnv] using eval_tFinish_zero (R := R) theta

@[simp] theorem eval_a13Circuit_one (theta : ℕ → A) :
    (a13Circuit (R := R)).eval (polyEnv theta) 1 = FastPoly.P27Full.H2 theta := by
  rw [a13Circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [towerEnv, tFinishEnv] using eval_tFinish_one (R := R) theta

@[simp] theorem eval_a13Circuit_two (theta : ℕ → A) :
    (a13Circuit (R := R)).eval (polyEnv theta) 2 = FastPoly.P27Full.H4 theta := by
  rw [a13Circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [towerEnv, tFinishEnv] using eval_tFinish_two (R := R) theta

@[simp] theorem eval_a13Circuit_three (theta : ℕ → A) :
    (a13Circuit (R := R)).eval (polyEnv theta) 3 = 0 := by
  rw [a13Circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [towerEnv, tFinishEnv] using eval_tFinish_three (R := R) theta

/-! ## The `Q₃` and `Q₇` blocks -/

/-- Both Mersenne gadgets use the retained unshifted tower. -/
def mersWiring (offset : ℕ) : ConstructionWiring 4 where
  power i := if i = 1 then .inr 1 else if i = 2 then .inr 2 else .inr 3
  shiftedPower := .inr 2
  parameter i := offset + i
  source _ := .inr 3

private def q3Circuit : Circuit R (Sum PolyInput (Fin 4)) 1 :=
  (peelCircuit (R := R) 2).instantiateConstruction (mersWiring 4)

private def q7Circuit : Circuit R (Sum PolyInput (Fin 4)) 1 :=
  (peelCircuit (R := R) 3).instantiateConstruction (mersWiring 7)

private noncomputable def a13Env (theta : ℕ → A) : Sum PolyInput (Fin 4) → A[X] :=
  Sum.elim (polyEnv theta) ((a13Circuit (R := R)).eval (polyEnv theta))

theorem eval_mersWiring_power (theta : ℕ → A) (offset : ℕ) :
    (mersWiring offset).powerValues theta
        ((a13Circuit (R := R)).eval (polyEnv theta)) =
      FastPoly.P27Composition.Hp theta (FastPoly.P27Full.H4 theta) := by
  funext i
  by_cases h1 : i = 1
  · subst i
    simp only [ConstructionWiring.powerValues, mersWiring, if_pos, Sum.elim_inr,
      eval_a13Circuit_one, FastPoly.P27Composition.Hp]
  · by_cases h2 : i = 2
    · subst i
      simp only [ConstructionWiring.powerValues, mersWiring, h1, if_false, if_pos,
        Sum.elim_inr, eval_a13Circuit_two, FastPoly.P27Composition.Hp]
    · simp only [ConstructionWiring.powerValues, mersWiring, h1, h2, if_false,
        Sum.elim_inr, eval_a13Circuit_three, FastPoly.P27Composition.Hp]

@[simp] theorem eval_q3Circuit (theta : ℕ → A) :
    (q3Circuit (R := R)).eval (a13Env (R := R) theta) 0 =
      FastPoly.P27Full.B3 theta := by
  rw [q3Circuit, a13Env, Circuit.eval_instantiateConstruction,
    eval_mersWiring_power (R := R) theta 4]
  simp only [ConstructionWiring.shiftedValue, mersWiring, Sum.elim_inr,
    eval_a13Circuit_two]
  exact eval_peelCircuit (R := R)
    (FastPoly.P27Composition.Hp theta (FastPoly.P27Full.H4 theta))
    (FastPoly.P27Full.H4 theta) (fun i => theta (4 + i)) (fun _ => 0) 2

@[simp] theorem eval_q7Circuit (theta : ℕ → A) :
    (q7Circuit (R := R)).eval (a13Env (R := R) theta) 0 =
      FastPoly.P27Full.C7 theta := by
  rw [q7Circuit, a13Env, Circuit.eval_instantiateConstruction,
    eval_mersWiring_power (R := R) theta 7]
  simp only [ConstructionWiring.shiftedValue, mersWiring, Sum.elim_inr,
    eval_a13Circuit_two]
  exact eval_peelCircuit (R := R)
    (FastPoly.P27Composition.Hp theta (FastPoly.P27Full.H4 theta))
    (FastPoly.P27Full.H4 theta) (fun i => theta (7 + i)) (fun _ => 0) 3

/-- Bundle `Q₁₃,Q₃,Q₇` with the retained powers.  Output order is
`(Q₁₃,Q₃,Q₇,H₂,H₄)`. -/
private def blocksBody : Circuit R (Sum PolyInput (Fin 4)) 5 :=
  let q₁₃ := Circuit.rightInput (R := R) (ι := PolyInput) (0 : Fin 4)
  let h₂ := Circuit.rightInput (R := R) (ι := PolyInput) (1 : Fin 4)
  let h₄ := Circuit.rightInput (R := R) (ι := PolyInput) (2 : Fin 4)
  .fork (Circuit.pairWithPowers q₁₃ q3Circuit q7Circuit h₂) h₄

/-- All three inner blocks and both recorded powers, sharing the crown prefix. -/
def blocksCircuit : Circuit R PolyInput 5 :=
  .bind a13Circuit blocksBody

private theorem eval_fourFork_zero {ι : Type*} (left : Circuit R ι 4)
    (right : Circuit R ι 1) (input : ι → A) :
    (Circuit.fork left right).eval input 0 = left.eval input 0 := by
  rfl

private theorem eval_fourFork_one {ι : Type*} (left : Circuit R ι 4)
    (right : Circuit R ι 1) (input : ι → A) :
    (Circuit.fork left right).eval input 1 = left.eval input 1 := by
  rfl

private theorem eval_fourFork_two {ι : Type*} (left : Circuit R ι 4)
    (right : Circuit R ι 1) (input : ι → A) :
    (Circuit.fork left right).eval input 2 = left.eval input 2 := by
  rfl

private theorem eval_fourFork_three {ι : Type*} (left : Circuit R ι 4)
    (right : Circuit R ι 1) (input : ι → A) :
    (Circuit.fork left right).eval input 3 = left.eval input 3 := by
  rfl

private theorem eval_fourFork_four {ι : Type*} (left : Circuit R ι 4)
    (right : Circuit R ι 1) (input : ι → A) :
    (Circuit.fork left right).eval input 4 = right.eval input 0 := by
  rfl

private theorem eval_blocksBody_zero (theta : ℕ → A) :
    (blocksBody (R := R)).eval (a13Env (R := R) theta) 0 =
      FastPoly.P27Full.A13 theta := by
  rw [blocksBody, eval_fourFork_zero, Circuit.eval_pairWithPowers_zero,
    a13Env, Circuit.eval_rightInput, eval_a13Circuit_zero]

private theorem eval_blocksBody_one (theta : ℕ → A) :
    (blocksBody (R := R)).eval (a13Env (R := R) theta) 1 =
      FastPoly.P27Full.B3 theta := by
  rw [blocksBody, eval_fourFork_one, Circuit.eval_pairWithPowers_one,
    eval_q3Circuit]

private theorem eval_blocksBody_two (theta : ℕ → A) :
    (blocksBody (R := R)).eval (a13Env (R := R) theta) 2 =
      FastPoly.P27Full.C7 theta := by
  rw [blocksBody, eval_fourFork_two, Circuit.eval_pairWithPowers_two,
    eval_q7Circuit]

private theorem eval_blocksBody_three (theta : ℕ → A) :
    (blocksBody (R := R)).eval (a13Env (R := R) theta) 3 =
      FastPoly.P27Full.H2 theta := by
  rw [blocksBody, eval_fourFork_three, Circuit.eval_pairWithPowers_three,
    a13Env, Circuit.eval_rightInput, eval_a13Circuit_one]

private theorem eval_blocksBody_four (theta : ℕ → A) :
    (blocksBody (R := R)).eval (a13Env (R := R) theta) 4 =
      FastPoly.P27Full.H4 theta := by
  rw [blocksBody, eval_fourFork_four, a13Env, Circuit.eval_rightInput,
    eval_a13Circuit_two]

@[simp] theorem eval_blocksCircuit_zero (theta : ℕ → A) :
    (blocksCircuit (R := R)).eval (polyEnv theta) 0 = FastPoly.P27Full.A13 theta := by
  rw [blocksCircuit, Circuit.eval_bind]
  simpa only [a13Env] using eval_blocksBody_zero (R := R) theta

@[simp] theorem eval_blocksCircuit_one (theta : ℕ → A) :
    (blocksCircuit (R := R)).eval (polyEnv theta) 1 = FastPoly.P27Full.B3 theta := by
  rw [blocksCircuit, Circuit.eval_bind]
  simpa only [a13Env] using eval_blocksBody_one (R := R) theta

@[simp] theorem eval_blocksCircuit_two (theta : ℕ → A) :
    (blocksCircuit (R := R)).eval (polyEnv theta) 2 = FastPoly.P27Full.C7 theta := by
  rw [blocksCircuit, Circuit.eval_bind]
  simpa only [a13Env] using eval_blocksBody_two (R := R) theta

@[simp] theorem eval_blocksCircuit_three (theta : ℕ → A) :
    (blocksCircuit (R := R)).eval (polyEnv theta) 3 = FastPoly.P27Full.H2 theta := by
  rw [blocksCircuit, Circuit.eval_bind]
  simpa only [a13Env] using eval_blocksBody_three (R := R) theta

@[simp] theorem eval_blocksCircuit_four (theta : ℕ → A) :
    (blocksCircuit (R := R)).eval (polyEnv theta) 4 = FastPoly.P27Full.H4 theta := by
  rw [blocksCircuit, Circuit.eval_bind]
  simpa only [a13Env] using eval_blocksBody_four (R := R) theta

/-! ## The two outer square shells -/

private abbrev ShellEnv := Sum PolyInput (Fin 5)
private abbrev FinishEnv := Sum ShellEnv (Fin 1)

/-- First shell: `Q₁₃²-Q₃²+θ₁`. -/
private def firstShell : Circuit R ShellEnv 1 :=
  let q₁₃ := Circuit.rightInput (R := R) (ι := PolyInput) (0 : Fin 5)
  let q₃ := Circuit.rightInput (R := R) (ι := PolyInput) (1 : Fin 5)
  let old (p : Circuit R PolyInput 1) : Circuit R ShellEnv 1 := p.liftLeft
  Circuit.diffSquareAdd q₁₃ q₃ (old (a 1))

/-- Second shell: add `Q₇²-H₂²+θ₀` and expose the retained powers. -/
private def finish : Circuit R FinishEnv 4 :=
  let t₁ := Circuit.rightInput (R := R) (ι := ShellEnv) (0 : Fin 1)
  let q₇ := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 1) (2 : Fin 5)
  let h₂ := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 1) (3 : Fin 5)
  let h₄ := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 1) (4 : Fin 5)
  let old (p : Circuit R PolyInput 1) : Circuit R FinishEnv 1 := p.liftLeft.liftLeft
  let extra := Circuit.diffSquareAdd q₇ h₂ (old (a 0))
  Circuit.pairWithPowers t₁ (.add t₁ extra) h₂ h₄

/-- Full circuit in output order `(T¹₂₇,T²₂₇,H₂,H₄)`. -/
def circuit : Circuit R PolyInput 4 :=
  .bind blocksCircuit (.bind firstShell finish)

private noncomputable def blocksEnv (theta : ℕ → A) : ShellEnv → A[X] :=
  Sum.elim (polyEnv theta) ((blocksCircuit (R := R)).eval (polyEnv theta))

private noncomputable def finishEnv (theta : ℕ → A) : FinishEnv → A[X] :=
  Sum.elim (blocksEnv (R := R) theta)
    ((firstShell (R := R)).eval (blocksEnv (R := R) theta))

@[simp] theorem eval_firstShell (theta : ℕ → A) :
    (firstShell (R := R)).eval (blocksEnv (R := R) theta) 0 =
      FastPoly.P27Full.T1 theta := by
  simp only [firstShell, Circuit.eval_diffSquareAdd, Circuit.eval_rightInput,
    Circuit.eval_liftLeft, blocksEnv, a, Circuit.eval_polyParameter,
    eval_blocksCircuit_zero, eval_blocksCircuit_one,
    FastPoly.P27Full.T1, FastPoly.P27Composition.T1, FastPoly.P27.T1, pow_two]
  ring

@[simp] theorem eval_finish_zero (theta : ℕ → A) :
    (finish (R := R)).eval (finishEnv (R := R) theta) 0 =
      FastPoly.P27Full.T1 theta := by
  rw [finish, Circuit.eval_pairWithPowers_zero, finishEnv,
    Circuit.eval_rightInput, eval_firstShell]

@[simp] theorem eval_finish_one (theta : ℕ → A) :
    (finish (R := R)).eval (finishEnv (R := R) theta) 1 =
      FastPoly.P27Full.T2 theta := by
  rw [finish, Circuit.eval_pairWithPowers_one, Circuit.eval_add, finishEnv,
    Circuit.eval_rightInput, Circuit.eval_diffSquareAdd]
  rw [eval_firstShell, blocksEnv]
  simp only [Circuit.eval_priorOutput, Circuit.eval_liftLeft,
    a, Circuit.eval_polyParameter]
  rw [eval_blocksCircuit_two, eval_blocksCircuit_three]
  simp only [
    FastPoly.P27Full.T2, FastPoly.P27Composition.T2, FastPoly.P27.T2,
    FastPoly.P27Full.T1, FastPoly.P27Composition.T1, FastPoly.P27.T1, pow_two]
  ring

@[simp] theorem eval_finish_two (theta : ℕ → A) :
    (finish (R := R)).eval (finishEnv (R := R) theta) 2 =
      FastPoly.P27Full.H2 theta := by
  rw [finish, Circuit.eval_pairWithPowers_two, finishEnv, blocksEnv,
    Circuit.eval_priorOutput, eval_blocksCircuit_three]

@[simp] theorem eval_finish_three (theta : ℕ → A) :
    (finish (R := R)).eval (finishEnv (R := R) theta) 3 =
      FastPoly.P27Full.H4 theta := by
  rw [finish, Circuit.eval_pairWithPowers_three, finishEnv, blocksEnv,
    Circuit.eval_priorOutput, eval_blocksCircuit_four]

theorem eval_circuit_zero (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 0 = FastPoly.P27Full.T1 theta := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [blocksEnv, finishEnv] using eval_finish_zero (R := R) theta

theorem eval_circuit_one (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 1 = FastPoly.P27Full.T2 theta := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [blocksEnv, finishEnv] using eval_finish_one (R := R) theta

theorem eval_circuit_two (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 2 = FastPoly.P27Full.H2 theta := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [blocksEnv, finishEnv] using eval_finish_two (R := R) theta

theorem eval_circuit_three (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 3 = FastPoly.P27Full.H4 theta := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [blocksEnv, finishEnv] using eval_finish_three (R := R) theta

/-! ## Exact multiplication count -/

@[simp] private theorem shiftedTower_multiplications :
    (shiftedTower (R := R)).gates.multiplications = 2 := by
  rw [shiftedTower, Circuit.gates_quadraticQuartic_multiplications]
  simp only [x, a, Circuit.polyX, Circuit.polyParameter, Circuit.gates_input,
    Circuit.gates, GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications]

@[simp] theorem tower_multiplications :
    (tower (R := R)).gates.multiplications = 2 := by
  simp only [tower, Circuit.gates_bind, GateCount.add_multiplications,
    shiftedTower_multiplications, Circuit.gates_pairWithPowers,
    Circuit.gates_rightInput, Circuit.gates_liftLeft,
    Circuit.gates, GateCount.zero_multiplications, GateCount.adds_multiplications,
    a, Circuit.polyParameter, Circuit.gates_input]

@[simp] private theorem tLocal_multiplications :
    (tLocal (R := R)).gates.multiplications = 4 := by
  rw [tLocal, Circuit.gates_instantiateConstruction,
    gates_tCircuit_multiplications 3 2 (by exact ⟨by omega, by omega⟩)]
  norm_num

omit [CommRing R] in
@[simp] private theorem tFinish_multiplications :
    (tFinish (R := R)).gates.multiplications = 1 := by
  simp only [tFinish, Circuit.gates_pairWithPowers, GateCount.add_multiplications,
    Circuit.gates, GateCount.adds_multiplications, GateCount.muls_multiplications,
    GateCount.zero_multiplications, Circuit.gates_rightInput,
    Circuit.gates_priorOutput, Circuit.gates_liftLeft,
    x, a, Circuit.polyX, Circuit.polyParameter, Circuit.gates_input]

@[simp] theorem a13Circuit_multiplications :
    (a13Circuit (R := R)).gates.multiplications = 7 := by
  simp only [a13Circuit, Circuit.gates_bind, GateCount.add_multiplications,
    tower_multiplications, tLocal_multiplications, tFinish_multiplications]

omit [CommRing R] in
@[simp] private theorem q3Circuit_multiplications :
    (q3Circuit (R := R)).gates.multiplications = 1 := by
  rw [q3Circuit, Circuit.gates_instantiateConstruction,
    gates_peelCircuit_multiplications (R := R) 2 (by omega)]
  norm_num

omit [CommRing R] in
@[simp] private theorem q7Circuit_multiplications :
    (q7Circuit (R := R)).gates.multiplications = 3 := by
  rw [q7Circuit, Circuit.gates_instantiateConstruction,
    gates_peelCircuit_multiplications (R := R) 3 (by omega)]
  norm_num

omit [CommRing R] in
@[simp] private theorem blocksBody_multiplications :
    (blocksBody (R := R)).gates.multiplications = 4 := by
  simp only [blocksBody, Circuit.gates_fork, Circuit.gates_pairWithPowers,
    GateCount.add_multiplications, Circuit.gates_rightInput,
    GateCount.zero_multiplications, q3Circuit_multiplications,
    q7Circuit_multiplications]

@[simp] theorem blocksCircuit_multiplications :
    (blocksCircuit (R := R)).gates.multiplications = 11 := by
  simp only [blocksCircuit, Circuit.gates_bind, GateCount.add_multiplications,
    a13Circuit_multiplications, blocksBody_multiplications]

omit [CommRing R] in
@[simp] private theorem firstShell_multiplications :
    (firstShell (R := R)).gates.multiplications = 1 := by
  simp only [firstShell, Circuit.gates_diffSquareAdd_multiplications,
    Circuit.gates_rightInput, Circuit.gates_liftLeft, a,
    Circuit.polyParameter, Circuit.gates_input, GateCount.zero_multiplications,
    Nat.zero_add, Nat.add_zero]

omit [CommRing R] in
@[simp] private theorem finish_multiplications :
    (finish (R := R)).gates.multiplications = 1 := by
  simp only [finish, Circuit.gates_pairWithPowers, GateCount.add_multiplications,
    Circuit.gates, GateCount.adds_multiplications, GateCount.zero_multiplications,
    Circuit.gates_rightInput, Circuit.gates_priorOutput,
    Circuit.gates_diffSquareAdd_multiplications, Circuit.gates_liftLeft,
    a, Circuit.polyParameter, Circuit.gates_input]

/-- Exact multiplication count of the actual degree-27 circuit. -/
theorem circuit_multiplications :
    (circuit (R := R)).gates.multiplications = 13 := by
  simp only [circuit, Circuit.gates_bind, GateCount.add_multiplications,
    blocksCircuit_multiplications, firstShell_multiplications,
    finish_multiplications]

/-- Height ledger of the degree-27 circuit: thirteen products in total, exactly the
`2⌈log₂27⌉+3` budget, with the recorded powers at the tower depths `(1,2)`. -/
theorem multDepth_circuit_le :
    ((circuit (R := R)).multDepth (fun _ => 0) 0 ≤ 2 * Nat.clog 2 27 + 3) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 1 ≤ 2 * Nat.clog 2 27 + 3) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 2 ≤ 1) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 3 ≤ 2) := by
  obtain ⟨hs0, hs1, hs2, hs3⟩ := Height.multDepth_quadraticQuartic_le
    (x (R := R)) (a 3) (.add (a 2) (a 25)) (a 23) (a 22) (a 24) (fun _ => 0)
    rfl rfl (by simp [a, Circuit.polyParameter, Circuit.input]) rfl rfl rfl
  rw [show Circuit.quadraticQuartic (x (R := R)) (a 3) (.add (a 2) (a 25)) (a 23)
      (a 22) (a 24) = shiftedTower from rfl] at hs0 hs1 hs2 hs3
  have hm : ∀ j, (circuit (R := R)).multDepth (fun _ => 0) j ≤ 13 := by
    intro j
    have h := Circuit.multDepth_le_multiplications (circuit (R := R))
      (env := fun _ => 0) (d := 0) (fun _ => le_rfl) j
    rwa [circuit_multiplications, Nat.add_zero] at h
  have hc : 5 ≤ Nat.clog 2 27 := by
    have h17 := Height.clog_two_seventeen
    have hmono := Nat.clog_mono_right 2 (show (17 : ℕ) ≤ 27 by omega)
    omega
  refine ⟨(hm 0).trans (by omega), (hm 1).trans (by omega), ?_, ?_⟩
  · rw [show (2 : Fin 4) = Fin.natAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, finish, blocksCircuit, blocksBody,
      a13Circuit, tFinish, tower, Circuit.pairWithPowers, Circuit.multDepth_fork,
      Fin.addCases_left, Fin.addCases_right, Circuit.priorOutput,
      Circuit.multDepth_rightInput,
      Circuit.multDepth_sub, Circuit.multDepth_liftLeft, Sum.elim_inl,
      Sum.elim_inr, a, Circuit.polyParameter, Circuit.input,
      Circuit.multDepth_wire,
      show (3 : Fin 5) = Fin.castAdd 1 (Fin.natAdd 2 (Fin.natAdd 1 (0 : Fin 1)))
        from rfl,
      show (1 : Fin 4) = Fin.castAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl,
      show (0 : Fin 5) = Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (0 : Fin 1)))
        from rfl]
    omega
  · rw [show (3 : Fin 4) = Fin.natAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, finish, blocksCircuit, blocksBody,
      a13Circuit, tFinish, tower, Circuit.pairWithPowers, Circuit.multDepth_fork,
      Fin.addCases_left, Fin.addCases_right, Circuit.priorOutput,
      Circuit.multDepth_rightInput,
      Circuit.multDepth_sub, Circuit.multDepth_liftLeft, Sum.elim_inl,
      Sum.elim_inr, a, Circuit.polyParameter, Circuit.input,
      Circuit.multDepth_wire,
      show (4 : Fin 5) = Fin.natAdd 4 (0 : Fin 1) from rfl,
      show (2 : Fin 4) = Fin.natAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl,
      show (2 : Fin 5) = Fin.castAdd 1 (Fin.natAdd 2 (Fin.castAdd 1 (0 : Fin 1)))
        from rfl]
    omega

/-- Exact joint realization of the manuscript's degree-27 witness. -/
def realized (theta : ℕ → A) :
    JointPairRealization (R := R) theta
      (FastPoly.P27Full.T1 theta) (FastPoly.P27Full.T2 theta)
      (FastPoly.P27Full.H2 theta) (FastPoly.P27Full.H4 theta) 13 where
  circuit := circuit
  eval₁ := eval_circuit_zero theta
  eval₂ := eval_circuit_one theta
  evalH₂ := eval_circuit_two theta
  evalH₄ := eval_circuit_three theta
  multiplication_count := circuit_multiplications

theorem realizable (theta : ℕ → A) :
    JointPairRealizable (R := R) theta
      (FastPoly.P27Full.T1 theta) (FastPoly.P27Full.T2 theta)
      (FastPoly.P27Full.H2 theta) (FastPoly.P27Full.H4 theta) 13 :=
  ⟨realized theta⟩

end TwentySeven

end FastPoly.Cost
