import FastPoly.Cost.CircuitPeephole
import FastPoly.Cost.RetainedShiftTCircuit
import FastPoly.Cost.ShiftedPowerTowerCircuit
import FastPoly.Cost.RealizationP27

/-!
# Addition-optimal realization of the degree-27 base

The decoder-facing continuation is exactly the already-certified degree-27 circuit.
Only its first two shared producers are replaced: the quadratic/quartic tower retains
the unshifted quadratic, and the `T_{3,4}` base retains the scalar quartic shift.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace TwentySevenOptimized

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private def x : Circuit R PolyInput 1 := Circuit.polyX
private def a (i : ℕ) : Circuit R PolyInput 1 := Circuit.polyParameter i

/-- Output order `(H₂,H₂+θ₂₅,H₄,H₄+θ₂₄,0)`. -/
def tower : Circuit R PolyInput 5 :=
  Circuit.quadraticShiftQuartic x (a 3) (a 2) (a 25) (a 23) (a 22) (a 24)

private theorem H2_coeff_one (theta : ℕ → A) :
    (FastPoly.P27Full.H2 theta).coeff 1 = theta 3 := by
  change (FastPoly.crownH2 (theta 3) (theta 2)).coeff 1 = theta 3
  exact FastPoly.crownH2_coeff_one

private theorem H2_coeff_zero (theta : ℕ → A) :
    (FastPoly.P27Full.H2 theta).coeff 0 = theta 2 := by
  change (FastPoly.crownH2 (theta 3) (theta 2)).coeff 0 = theta 2
  exact FastPoly.crownH2_coeff_zero

@[simp] theorem eval_tower_zero (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 0 = FastPoly.P27Full.H2 theta := by
  rw [tower, Circuit.eval_quadraticShiftQuartic_zero]
  rfl

@[simp] theorem eval_tower_one (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 1 =
      FastPoly.crownH2 ((FastPoly.P27Full.H2 theta).coeff 1)
        ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25) := by
  rw [tower, Circuit.eval_quadraticShiftQuartic_one]
  rw [H2_coeff_one, H2_coeff_zero]
  simp only [x, a, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.crownH2, map_add]
  ring

@[simp] theorem eval_tower_two (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 2 = FastPoly.P27Full.H4 theta := by
  rw [tower, Circuit.eval_quadraticShiftQuartic_two]
  simp only [x, a, Circuit.eval_polyX, Circuit.eval_polyParameter]
  rw [← H2_coeff_one theta, ← H2_coeff_zero theta]
  simp only [FastPoly.P27Full.H4, FastPoly.crownH4, FastPoly.crownH2, map_add]
  ring

@[simp] theorem eval_tower_three (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 3 =
      FastPoly.P27Full.H4 theta + C (theta 24) := by
  rw [tower, Circuit.eval_quadraticShiftQuartic_three]
  simp only [x, a, Circuit.eval_polyX, Circuit.eval_polyParameter]
  rw [← H2_coeff_one theta, ← H2_coeff_zero theta]
  simp only [FastPoly.P27Full.H4, FastPoly.crownH4, FastPoly.crownH2, map_add]
  ring

@[simp] theorem eval_tower_four (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) 4 = 0 := by
  rw [tower, Circuit.eval_quadraticShiftQuartic_four]

theorem eval_tower_eq_old (theta : ℕ → A) :
    (tower (R := R)).eval (polyEnv theta) =
      (TwentySeven.tower (R := R)).eval (polyEnv theta) := by
  funext i
  by_cases h₀ : i = 0
  · subst i
    rw [eval_tower_zero, TwentySeven.eval_tower_zero]
  by_cases h₁ : i = 1
  · subst i
    rw [eval_tower_one, TwentySeven.eval_tower_one]
  by_cases h₂ : i = 2
  · subst i
    rw [eval_tower_two, TwentySeven.eval_tower_two]
  by_cases h₃ : i = 3
  · subst i
    rw [eval_tower_three, TwentySeven.eval_tower_three]
  have h₄ : i = 4 := Fin.ext (by omega)
  subst i
  rw [eval_tower_four, TwentySeven.eval_tower_four]

private def rhoLocal : Circuit R ConstructionInput 1 :=
  Circuit.constructionParameter 10

/-- Optimized local `T_{3,4}` producer, wired to the five tower outputs. -/
def tLocal : Circuit R (Sum PolyInput (Fin 5)) 2 :=
  (RetainedShiftT.oddBaseTCircuit 3 rhoLocal).instantiateConstruction
    TwentySeven.tWiring

private noncomputable def towerEnv (theta : ℕ → A) :
    Sum PolyInput (Fin 5) → A[X] :=
  Sum.elim (polyEnv theta) ((tower (R := R)).eval (polyEnv theta))

theorem eval_tLocal (theta : ℕ → A) :
    ((tLocal (R := R)).eval (towerEnv (R := R) theta) 0,
      (tLocal (R := R)).eval (towerEnv (R := R) theta) 1) =
      FastPoly.Tpair
        (FastPoly.crownHp ((FastPoly.P27Full.H2 theta).coeff 1)
          ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25)
          (theta 23) (theta 22))
        (FastPoly.P27Full.H4 theta + C (theta 24)) 3 2
        (fun i => theta (14 + i)) := by
  rw [tLocal, towerEnv, Circuit.eval_instantiateConstruction]
  let localEnv : ConstructionInput → A[X] :=
    constructionEnv
      (TwentySeven.tWiring.powerValues theta
        ((tower (R := R)).eval (polyEnv theta)))
      (TwentySeven.tWiring.shiftedValue theta
        ((tower (R := R)).eval (polyEnv theta)))
      (fun i => theta (TwentySeven.tWiring.parameter i))
      (TwentySeven.tWiring.sourceValues theta
        ((tower (R := R)).eval (polyEnv theta)))
  have hshift : localEnv .shiftedPower =
      localEnv (.power 2) + (rhoLocal (R := R)).eval localEnv 0 := by
    simp only [localEnv, constructionEnv_shiftedPower, constructionEnv_power,
      rhoLocal, Circuit.eval_constructionParameter,
      TwentySeven.tWiring, ConstructionWiring.shiftedValue,
      ConstructionWiring.powerValues]
    simp only [show (2 : ℕ) ≠ 1 by omega, if_false, if_true, Sum.elim_inr]
    rw [eval_tower_two, eval_tower_three]
  have hsame := RetainedShiftT.eval_oddBaseTCircuit_eq_tCircuit
    (R := R) (A := A) 3 (by omega) (by omega) (rhoLocal (R := R)) localEnv hshift
  change
    ((RetainedShiftT.oddBaseTCircuit 3 (rhoLocal (R := R))).eval localEnv 0,
      (RetainedShiftT.oddBaseTCircuit 3 (rhoLocal (R := R))).eval localEnv 1) = _
  rw [hsame]
  dsimp only [localEnv]
  rw [eval_tower_eq_old theta]
  rw [TwentySeven.eval_tWiring_power (R := R) theta]
  simp only [ConstructionWiring.shiftedValue, TwentySeven.tWiring, Sum.elim_inr,
    TwentySeven.eval_tower_three]
  exact eval_tCircuit (R := R)
    (FastPoly.crownHp ((FastPoly.P27Full.H2 theta).coeff 1)
      ((FastPoly.P27Full.H2 theta).coeff 0 + theta 25)
      (theta 23) (theta 22))
    (FastPoly.P27Full.H4 theta + C (theta 24))
    (fun i => theta (14 + i)) 3 2

/-- Replace only the tower and local `T` producer; retain the certified crown finish. -/
def a13Circuit : Circuit R PolyInput 4 :=
  Circuit.replaceFirstTwoProducers tower tLocal (TwentySeven.a13Circuit (R := R))

theorem eval_a13Circuit_eq_old (theta : ℕ → A) :
    (a13Circuit (R := R)).eval (polyEnv theta) =
      (TwentySeven.a13Circuit (R := R)).eval (polyEnv theta) := by
  rw [a13Circuit, TwentySeven.a13Circuit]
  apply Circuit.eval_replaceFirstTwoProducers_eq_bind_bind_two
  · exact eval_tower_eq_old theta
  · exact (eval_tLocal (R := R) theta).trans
      (TwentySeven.eval_tLocal (R := R) theta).symm

/-- Replace the `Q₁₃` producer and retain the existing `Q₃,Q₇` continuation. -/
def blocksCircuit : Circuit R PolyInput 5 :=
  Circuit.replaceTopProducer a13Circuit (TwentySeven.blocksCircuit (R := R))

theorem eval_blocksCircuit_eq_old (theta : ℕ → A) :
    (blocksCircuit (R := R)).eval (polyEnv theta) =
      (TwentySeven.blocksCircuit (R := R)).eval (polyEnv theta) := by
  rw [blocksCircuit, TwentySeven.blocksCircuit]
  apply Circuit.eval_replaceTopProducer_eq_bind
  exact eval_a13Circuit_eq_old theta

/-- The full optimized degree-27 joint circuit. -/
def circuit : Circuit R PolyInput 4 :=
  Circuit.replaceTopProducer blocksCircuit (TwentySeven.circuit (R := R))

theorem eval_circuit_eq_old (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) =
      (TwentySeven.circuit (R := R)).eval (polyEnv theta) := by
  rw [circuit, TwentySeven.circuit]
  apply Circuit.eval_replaceTopProducer_eq_bind
  exact eval_blocksCircuit_eq_old theta

theorem eval_circuit_zero (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 0 = FastPoly.P27Full.T1 theta := by
  rw [eval_circuit_eq_old, TwentySeven.eval_circuit_zero]

theorem eval_circuit_one (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 1 = FastPoly.P27Full.T2 theta := by
  rw [eval_circuit_eq_old, TwentySeven.eval_circuit_one]

theorem eval_circuit_two (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 2 = FastPoly.P27Full.H2 theta := by
  rw [eval_circuit_eq_old, TwentySeven.eval_circuit_two]

theorem eval_circuit_three (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 3 = FastPoly.P27Full.H4 theta := by
  rw [eval_circuit_eq_old, TwentySeven.eval_circuit_three]

/-- Exact counts of the same circuit whose semantics are proved above. -/
@[simp] theorem tower_multiplications :
    (tower (R := R)).gates.multiplications = 2 := by
  rw [tower, Circuit.gates_quadraticShiftQuartic_multiplications]
  rfl

@[simp] theorem tower_additions :
    (tower (R := R)).gates.additions = 8 := by
  rw [tower, Circuit.gates_quadraticShiftQuartic_additions]
  rfl

@[simp] theorem tLocal_multiplications :
    (tLocal (R := R)).gates.multiplications = 4 := by
  rw [tLocal, Circuit.gates_instantiateConstruction,
    RetainedShiftT.oddBaseTCircuit_multiplications]
  rfl

@[simp] theorem tLocal_additions :
    (tLocal (R := R)).gates.additions = 15 := by
  rw [tLocal, Circuit.gates_instantiateConstruction,
    RetainedShiftT.oddBaseTCircuit_additions]
  rfl

@[simp] theorem a13Circuit_multiplications :
    (a13Circuit (R := R)).gates.multiplications = 7 := by
  rw [a13Circuit, TwentySeven.a13Circuit,
    Circuit.gates_replaceFirstTwoProducers_bind_bind]
  simp only [GateCount.add_multiplications, tower_multiplications,
    tLocal_multiplications]
  rfl

@[simp] theorem a13Circuit_additions :
    (a13Circuit (R := R)).gates.additions = 25 := by
  rw [a13Circuit, TwentySeven.a13Circuit,
    Circuit.gates_replaceFirstTwoProducers_bind_bind]
  simp only [GateCount.add_additions, tower_additions, tLocal_additions]
  rfl

@[simp] theorem blocksCircuit_multiplications :
    (blocksCircuit (R := R)).gates.multiplications = 11 := by
  rw [blocksCircuit, TwentySeven.blocksCircuit,
    Circuit.gates_replaceTopProducer_bind]
  simp only [GateCount.add_multiplications, a13Circuit_multiplications]
  rfl

@[simp] theorem blocksCircuit_additions :
    (blocksCircuit (R := R)).gates.additions = 36 := by
  rw [blocksCircuit, TwentySeven.blocksCircuit,
    Circuit.gates_replaceTopProducer_bind]
  simp only [GateCount.add_additions, a13Circuit_additions]
  rfl

theorem circuit_multiplications :
    (circuit (R := R)).gates.multiplications = 13 := by
  rw [circuit, TwentySeven.circuit, Circuit.gates_replaceTopProducer_bind]
  simp only [GateCount.add_multiplications, blocksCircuit_multiplications]
  rfl

theorem circuit_additions :
    (circuit (R := R)).gates.additions = 43 := by
  rw [circuit, TwentySeven.circuit, Circuit.gates_replaceTopProducer_bind]
  simp only [GateCount.add_additions, blocksCircuit_additions]
  rfl

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

end TwentySevenOptimized

end FastPoly.Cost
