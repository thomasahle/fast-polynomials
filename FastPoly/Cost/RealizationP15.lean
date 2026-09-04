import FastPoly.Cost.MersenneCircuitCount
import FastPoly.Cost.PowerTowerCircuit
import FastPoly.Examples.P15
import FastPoly.Height.RealizationDepth

/-!
# Semantic realization of the degree-15 cost base

This is the fused seven-product circuit from the manuscript.  The quadratic and
quartic tower costs two products, `Q₇` costs three given that shared tower, and each of
the two outer difference-of-squares shells costs one.  All four advertised outputs are
wires of this single DAG.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace Fifteen

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private def x : Circuit R PolyInput 1 := Circuit.polyX
private def a (i : ℕ) : Circuit R PolyInput 1 := Circuit.polyParameter i

/-- Output order `(H₂,H₄,H₄,0)`; the repeated quartic is a convenient shifted-power
wire for the local Mersenne compiler. -/
def tower : Circuit R PolyInput 4 :=
  Circuit.quadraticQuarticUnshifted x (a 7) (a 6) (a 5) (a 4)

def qWiring : ConstructionWiring 4 where
  power i := if i = 1 then .inr 0 else if i = 2 then .inr 1 else .inr 3
  shiftedPower := .inr 2
  parameter i := 8 + i
  source _ := .inr 3

private def qCircuit : Circuit R (Sum PolyInput (Fin 4)) 1 :=
  (peelCircuit (R := R) 3).instantiateConstruction qWiring

private abbrev QEnv := Sum PolyInput (Fin 4)
private abbrev ShellEnv := Sum QEnv (Fin 1)
private abbrev FinishEnv := Sum ShellEnv (Fin 1)

/-- The first outer shell, `Q₇²-(H₂+α₃)²+α₁`. -/
private def firstShell : Circuit R ShellEnv 1 :=
  let q := Circuit.rightInput (R := R) (ι := QEnv) (0 : Fin 1)
  let h₂ := Circuit.priorOutput (R := R) (ι := PolyInput) (n := 1) (0 : Fin 4)
  let old (p : Circuit R PolyInput 1) : Circuit R ShellEnv 1 := p.liftLeft.liftLeft
  Circuit.diffSquareAdd q (.add h₂ (old (a 3))) (old (a 1))

/-- The second shell adds `H₄²-(H₂+α₂)²+α₀`, then exposes the shared powers. -/
private def finish : Circuit R FinishEnv 4 :=
  let t₁ := Circuit.rightInput (R := R) (ι := ShellEnv) (0 : Fin 1)
  let h₂ := Circuit.grandOutput (R := R) (ι := PolyInput)
    (n := 1) (o := 1) (0 : Fin 4)
  let h₄ := Circuit.grandOutput (R := R) (ι := PolyInput)
    (n := 1) (o := 1) (1 : Fin 4)
  let oldest (p : Circuit R PolyInput 1) : Circuit R FinishEnv 1 :=
    p.liftLeft.liftLeft.liftLeft
  let extra := Circuit.diffSquareAdd h₄ (.add h₂ (oldest (a 2))) (oldest (a 0))
  Circuit.pairWithPowers t₁ (.add t₁ extra) h₂ h₄

/-- Full circuit in output order `(T¹₁₅,T²₁₅,H₂,H₄)`. -/
def circuit : Circuit R PolyInput 4 :=
  .bind tower (.bind qCircuit (.bind firstShell finish))

@[simp] theorem eval_tower_zero (θ : ℕ → A) :
    (tower (R := R)).eval (polyEnv θ) 0 = FastPoly.P15.H2 θ := by
  rw [tower, Circuit.eval_quadraticQuarticUnshifted_zero]
  simp only [x, a, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.P15.H2]

@[simp] theorem eval_tower_one (θ : ℕ → A) :
    (tower (R := R)).eval (polyEnv θ) 1 = FastPoly.P15.H4 θ := by
  rw [tower, Circuit.eval_quadraticQuarticUnshifted_one]
  simp only [x, a, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.P15.H4, FastPoly.P15.H2]
  ring

@[simp] theorem eval_tower_two (θ : ℕ → A) :
    (tower (R := R)).eval (polyEnv θ) 2 = FastPoly.P15.H4 θ := by
  rw [tower, Circuit.eval_quadraticQuarticUnshifted_two]
  simp only [x, a, Circuit.eval_polyX, Circuit.eval_polyParameter,
    FastPoly.P15.H4, FastPoly.P15.H2]
  ring

@[simp] theorem eval_tower_three (θ : ℕ → A) :
    (tower (R := R)).eval (polyEnv θ) 3 = 0 := by
  rw [tower, Circuit.eval_quadraticQuarticUnshifted_three]

theorem eval_qWiring_power (θ : ℕ → A) :
    qWiring.powerValues θ ((tower (R := R)).eval (polyEnv θ)) =
      FastPoly.P15.Hp θ := by
  funext i
  by_cases h1 : i = 1
  · subst i
    simp only [ConstructionWiring.powerValues, qWiring, if_pos, Sum.elim_inr,
      eval_tower_zero, FastPoly.P15.Hp]
  · by_cases h2 : i = 2
    · subst i
      simp only [ConstructionWiring.powerValues, qWiring, h1, if_false, if_pos,
        Sum.elim_inr, eval_tower_one, FastPoly.P15.Hp]
    · simp only [ConstructionWiring.powerValues, qWiring, h1, h2, if_false,
        Sum.elim_inr, eval_tower_three, FastPoly.P15.Hp]

theorem eval_qCircuit (θ : ℕ → A) :
    (qCircuit (R := R)).eval
        (Sum.elim (polyEnv θ) ((tower (R := R)).eval (polyEnv θ))) 0 =
      FastPoly.P15.Q7 θ := by
  rw [qCircuit, Circuit.eval_instantiateConstruction, eval_qWiring_power]
  simp only [ConstructionWiring.shiftedValue, qWiring, Sum.elim_inr, eval_tower_two]
  exact eval_peelCircuit (R := R) (FastPoly.P15.Hp θ) (FastPoly.P15.H4 θ)
    (fun i => θ (8 + i)) (fun _ => 0) 3

private noncomputable def qEnv (θ : ℕ → A) : QEnv → A[X] :=
  Sum.elim (polyEnv θ) ((tower (R := R)).eval (polyEnv θ))

private noncomputable def shellEnv (θ : ℕ → A) : ShellEnv → A[X] :=
  Sum.elim (qEnv (R := R) θ)
    ((qCircuit (R := R)).eval (qEnv (R := R) θ))

private noncomputable def finishEnv (θ : ℕ → A) : FinishEnv → A[X] :=
  Sum.elim (shellEnv (R := R) θ)
    ((firstShell (R := R)).eval (shellEnv (R := R) θ))

/-- Semantic equation for the first one-product shell. -/
theorem eval_firstShell (θ : ℕ → A) :
    (firstShell (R := R)).eval (shellEnv (R := R) θ) 0 =
      FastPoly.P15.T1 θ (FastPoly.P15.Q7 θ) := by
  simp only [firstShell, shellEnv, qEnv, Circuit.eval_diffSquareAdd,
    Circuit.eval_rightInput, Circuit.eval_add, Circuit.eval_priorOutput,
    Circuit.eval_liftLeft, eval_qCircuit, eval_tower_zero, a,
    Circuit.eval_polyParameter, FastPoly.P15.T1, FastPoly.P15.U, pow_two]
  ring

/-- Semantic equations for the four output wires of the final one-product shell. -/
theorem eval_finish_zero (θ : ℕ → A) :
    (finish (R := R)).eval (finishEnv (R := R) θ) 0 =
      FastPoly.P15.T1 θ (FastPoly.P15.Q7 θ) := by
  rw [finish, Circuit.eval_pairWithPowers_zero]
  rw [finishEnv, Circuit.eval_rightInput]
  exact eval_firstShell (R := R) θ

theorem eval_finish_one (θ : ℕ → A) :
    (finish (R := R)).eval (finishEnv (R := R) θ) 1 =
      FastPoly.P15.T2 θ (FastPoly.P15.Q7 θ) := by
  rw [finish, Circuit.eval_pairWithPowers_one, Circuit.eval_add]
  rw [finishEnv, Circuit.eval_rightInput, eval_firstShell]
  simp only [Circuit.eval_diffSquareAdd, Circuit.eval_grandOutput,
    Circuit.eval_add, Circuit.eval_liftLeft, shellEnv, qEnv,
    eval_tower_zero, eval_tower_one, a, Circuit.eval_polyParameter,
    FastPoly.P15.T2, FastPoly.P15.W, pow_two]
  ring

theorem eval_finish_two (θ : ℕ → A) :
    (finish (R := R)).eval (finishEnv (R := R) θ) 2 = FastPoly.P15.H2 θ := by
  simp only [finish, Circuit.eval_pairWithPowers_two, finishEnv, shellEnv, qEnv,
    Circuit.eval_grandOutput, eval_tower_zero]

theorem eval_finish_three (θ : ℕ → A) :
    (finish (R := R)).eval (finishEnv (R := R) θ) 3 = FastPoly.P15.H4 θ := by
  simp only [finish, Circuit.eval_pairWithPowers_three, finishEnv, shellEnv, qEnv,
    Circuit.eval_grandOutput, eval_tower_one]

theorem eval_circuit_zero (θ : ℕ → A) :
    (circuit (R := R)).eval (polyEnv θ) 0 =
      FastPoly.P15.T1 θ (FastPoly.P15.Q7 θ) := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [qEnv, shellEnv, finishEnv] using eval_finish_zero (R := R) θ

theorem eval_circuit_one (θ : ℕ → A) :
    (circuit (R := R)).eval (polyEnv θ) 1 =
      FastPoly.P15.T2 θ (FastPoly.P15.Q7 θ) := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [qEnv, shellEnv, finishEnv] using eval_finish_one (R := R) θ

theorem eval_circuit_two (θ : ℕ → A) :
    (circuit (R := R)).eval (polyEnv θ) 2 = FastPoly.P15.H2 θ := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [qEnv, shellEnv, finishEnv] using eval_finish_two (R := R) θ

theorem eval_circuit_three (θ : ℕ → A) :
    (circuit (R := R)).eval (polyEnv θ) 3 = FastPoly.P15.H4 θ := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_bind]
  simpa only [qEnv, shellEnv, finishEnv] using eval_finish_three (R := R) θ

@[simp] theorem tower_multiplications :
    (tower (R := R)).gates.multiplications = 2 := by
  rw [tower, Circuit.gates_quadraticQuarticUnshifted_multiplications]
  rfl

@[simp] theorem tower_additions :
    (tower (R := R)).gates.additions = 6 := by
  rw [tower, Circuit.gates_quadraticQuarticUnshifted_additions]
  rfl

omit [CommRing R] in
@[simp] theorem qCircuit_multiplications :
    (qCircuit (R := R)).gates.multiplications = 3 := by
  rw [qCircuit, Circuit.gates_instantiateConstruction,
    gates_peelCircuit_multiplications (R := R) 3 (by omega)]
  norm_num

omit [CommRing R] in
@[simp] theorem qCircuit_additions :
    (qCircuit (R := R)).gates.additions = 8 := by
  rw [qCircuit, Circuit.gates_instantiateConstruction]
  rfl

omit [CommRing R] in
@[simp] theorem firstShell_multiplications :
    (firstShell (R := R)).gates.multiplications = 1 := by
  simp only [firstShell, Circuit.gates_diffSquareAdd_multiplications,
    Circuit.gates_rightInput, Circuit.gates, GateCount.add_multiplications,
    GateCount.zero_multiplications, GateCount.adds_multiplications,
    Circuit.gates_priorOutput, Circuit.gates_liftLeft, a,
    Circuit.polyParameter, Circuit.gates_input]

omit [CommRing R] in
@[simp] theorem firstShell_additions :
    (firstShell (R := R)).gates.additions = 4 := by
  simp only [firstShell, Circuit.gates_diffSquareAdd_additions,
    Circuit.gates_rightInput, Circuit.gates, GateCount.add_additions,
    GateCount.zero_additions, GateCount.adds_additions,
    Circuit.gates_priorOutput,
    Circuit.gates_liftLeft, a, Circuit.polyParameter, Circuit.gates_input]

omit [CommRing R] in
@[simp] theorem finish_multiplications :
    (finish (R := R)).gates.multiplications = 1 := by
  simp only [finish, Circuit.gates_pairWithPowers, GateCount.add_multiplications,
    Circuit.gates_rightInput, Circuit.gates, GateCount.adds_multiplications,
    GateCount.zero_multiplications,
    Circuit.gates_diffSquareAdd_multiplications, Circuit.gates_grandOutput,
    Circuit.gates_liftLeft, a, Circuit.polyParameter, Circuit.gates_input]

omit [CommRing R] in
@[simp] theorem finish_additions :
    (finish (R := R)).gates.additions = 5 := by
  simp only [finish, Circuit.gates_pairWithPowers, GateCount.add_additions,
    Circuit.gates_rightInput, Circuit.gates, GateCount.zero_additions,
    GateCount.adds_additions,
    Circuit.gates_diffSquareAdd_additions, Circuit.gates_grandOutput,
    Circuit.gates_liftLeft, a, Circuit.polyParameter, Circuit.gates_input]

theorem circuit_multiplications :
    (circuit (R := R)).gates.multiplications = 7 := by
  simp only [circuit, Circuit.gates_bind, GateCount.add_multiplications,
    tower_multiplications, qCircuit_multiplications, firstShell_multiplications,
    finish_multiplications]

/-- Exact addition count of the same shared circuit certified below. -/
theorem circuit_additions :
    (circuit (R := R)).gates.additions = 23 := by
  simp only [circuit, Circuit.gates_bind, GateCount.add_additions,
    tower_additions, qCircuit_additions, firstShell_additions,
    finish_additions]

/-- Height ledger of the degree-15 circuit: seven products in total, so the pair
outputs clear `2⌈log₂15⌉+3` with room, while the recorded powers stay at the tower
depths `(1,2)`. -/
theorem multDepth_circuit_le :
    ((circuit (R := R)).multDepth (fun _ => 0) 0 ≤ 2 * Nat.clog 2 15 + 3) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 1 ≤ 2 * Nat.clog 2 15 + 3) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 2 ≤ 1) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 3 ≤ 2) := by
  obtain ⟨ht0, ht1, ht2, ht3⟩ := Height.multDepth_quadraticQuarticUnshifted_le
    (x (R := R)) (a 7) (a 6) (a 5) (a 4) (fun _ => 0) rfl rfl rfl rfl rfl
  rw [show Circuit.quadraticQuarticUnshifted (x (R := R)) (a 7) (a 6) (a 5) (a 4)
      = tower from rfl] at ht0 ht1 ht2 ht3
  have hm : ∀ j, (circuit (R := R)).multDepth (fun _ => 0) j ≤ 7 := by
    intro j
    have h := Circuit.multDepth_le_multiplications (circuit (R := R))
      (env := fun _ => 0) (d := 0) (fun _ => le_rfl) j
    rwa [circuit_multiplications, Nat.add_zero] at h
  have hc : 2 ≤ Nat.clog 2 15 := by
    have h4 := Height.clog_two_four
    have hmono := Nat.clog_mono_right 2 (show (4 : ℕ) ≤ 15 by omega)
    omega
  refine ⟨(hm 0).trans (by omega), (hm 1).trans (by omega), ?_, ?_⟩
  · rw [show (2 : Fin 4) = Fin.natAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, finish, Circuit.pairWithPowers,
      Circuit.multDepth_fork, Fin.addCases_left, Fin.addCases_right,
      Circuit.grandOutput, Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    exact ht0
  · rw [show (3 : Fin 4) = Fin.natAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, finish, Circuit.pairWithPowers,
      Circuit.multDepth_fork, Fin.addCases_right,
      Circuit.grandOutput, Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    exact ht1

/-- Exact joint realization of the manuscript's degree-15 witness. -/
def realized (θ : ℕ → A) :
    JointPairRealization (R := R) θ
      (FastPoly.P15.T1 θ (FastPoly.P15.Q7 θ))
      (FastPoly.P15.T2 θ (FastPoly.P15.Q7 θ))
      (FastPoly.P15.H2 θ) (FastPoly.P15.H4 θ) 7 where
  circuit := circuit
  eval₁ := eval_circuit_zero θ
  eval₂ := eval_circuit_one θ
  evalH₂ := eval_circuit_two θ
  evalH₄ := eval_circuit_three θ
  multiplication_count := circuit_multiplications

theorem realizable (θ : ℕ → A) :
    JointPairRealizable (R := R) θ
      (FastPoly.P15.T1 θ (FastPoly.P15.Q7 θ))
      (FastPoly.P15.T2 θ (FastPoly.P15.Q7 θ))
      (FastPoly.P15.H2 θ) (FastPoly.P15.H4 θ) 7 :=
  ⟨realized θ⟩

end Fifteen

end FastPoly.Cost
