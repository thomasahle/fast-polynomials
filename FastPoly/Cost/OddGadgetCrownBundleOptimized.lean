import FastPoly.Cost.OddGadgetCrownBundle
import FastPoly.Cost.RealizationCrownOptimized

/-!
# Retained-shift crown bundle for the `4k+1` odd gadget

The ordinary crown bundle already produces its quartic, its scalar-shifted quartic,
and the scalar shift itself.  This sibling sends that existing scalar wire through
the retained-shift `T` compiler.  The output polynomials and multiplication/depth
ledgers are unchanged, while the literal addition count is the selected gadget
ledger.
-/

namespace FastPoly.Cost.OddGadget

open Polynomial

universe u v

namespace Q4Optimized

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Relabel the local compiler to the crown tower, retaining `theta 4` as source zero. -/
def retainedLabel : ConstructionInput → Sum ConstructionInput (Fin 3)
  | .variable => .inl .variable
  | .power i => if i = 1 then .inr 0 else if i = 2 then .inr 1 else .inl .variable
  | .shiftedPower => .inr 2
  | .parameter i => .inl (.parameter (5 + i))
  | .source i => if i = 0 then .inl (.parameter 4) else .inl (.source i)

/-- The retained local `T_{k,4}` call. -/
def localCircuit (k : ℕ) : Circuit R (Sum ConstructionInput (Fin 3)) 2 :=
  (RetainedShiftT.compiler k 2).relabel retainedLabel

/-- Output zero is `Q_{4k+1}`; output one is the already-constructed quartic. -/
def circuit (k : ℕ) : Circuit R ConstructionInput 2 :=
  .bind q4Tower <|
    .bind (localCircuit k) <|
      let old (p : Circuit R ConstructionInput 1) := p.liftLeft.liftLeft
      let T₁ := Circuit.rightInput (R := R)
        (ι := Sum ConstructionInput (Fin 3)) (0 : Fin 2)
      let T₂ := Circuit.rightInput (R := R)
        (ι := Sum ConstructionInput (Fin 3)) (1 : Fin 2)
      let Q := .add (.mul (.add (old Circuit.constructionX)
        (old (Circuit.constructionParameter 0))) T₁) T₂
      let H₄ := Circuit.priorOutput (R := R) (ι := ConstructionInput)
        (n := 2) (1 : Fin 3)
      .fork Q H₄

/-- The retained local call evaluates to the same mathematical `Tpair`. -/
theorem eval_local [Nontrivial A] {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (theta : ℕ → A) (k : ℕ) :
    ((localCircuit (R := R) k).eval
        (Sum.elim (env H₂ H₄ theta)
          ((q4Tower (R := R)).eval (env H₂ H₄ theta))) 0,
      (localCircuit (R := R) k).eval
        (Sum.elim (env H₂ H₄ theta)
          ((q4Tower (R := R)).eval (env H₂ H₄ theta))) 1) =
      FastPoly.Tpair
        (FastPoly.crownHp (H₂.coeff 1) (H₂.coeff 0 + theta 1)
          (theta 2) (theta 3))
        (FastPoly.crownH4 (H₂.coeff 1) (H₂.coeff 0 + theta 1)
          (theta 2) (theta 3) + C (theta 4))
        k 2 (fun i => theta (5 + i)) := by
  let values := (q4Tower (R := R)).eval (env H₂ H₄ theta)
  let localEnv := Sum.elim (env H₂ H₄ theta) values ∘ retainedLabel
  have hshift : localEnv .shiftedPower =
      localEnv (.power 2) + localEnv (.source 0) := by
    simp only [localEnv, Function.comp_apply, retainedLabel, Sum.elim_inr]
    change (q4Tower (R := R)).eval (env H₂ H₄ theta) 2 =
      (q4Tower (R := R)).eval (env H₂ H₄ theta) 1 + C (theta 4)
    rw [eval_q4Tower_two, eval_q4Tower_one]
  have hH₂shift := FastPoly.crownH2_shift hH₂m hH₂d (theta 1)
  let source : Fin 2 → A[X] := fun i => localEnv (.source i)
  have henv : localEnv =
      constructionEnv
        (FastPoly.crownHp (H₂.coeff 1) (H₂.coeff 0 + theta 1)
          (theta 2) (theta 3))
        (FastPoly.crownH4 (H₂.coeff 1) (H₂.coeff 0 + theta 1)
          (theta 2) (theta 3) + C (theta 4))
        (fun i => theta (5 + i)) source := by
    funext input
    cases input with
    | «variable» => rfl
    | power i =>
        by_cases hi1 : i = 1
        · subst i
          simp only [localEnv, retainedLabel, if_pos, Function.comp_apply,
            Sum.elim_inr, constructionEnv_power, values, eval_q4Tower_zero,
            FastPoly.crownHp_one]
          exact hH₂shift
        · by_cases hi2 : i = 2
          · subst i
            simp only [localEnv, retainedLabel, hi1, if_false, if_pos,
              Function.comp_apply, Sum.elim_inr, constructionEnv_power, values,
              eval_q4Tower_one, FastPoly.crownHp_two, FastPoly.crownH4]
            rw [hH₂shift]
          · simp only [localEnv, retainedLabel, hi1, hi2, if_false,
              Function.comp_apply, Sum.elim_inl, constructionEnv_power,
              FastPoly.crownHp]
            rfl
    | shiftedPower =>
        simp only [localEnv, retainedLabel, Function.comp_apply, Sum.elim_inr,
          constructionEnv_shiftedPower, values, eval_q4Tower_two,
          FastPoly.crownH4]
        rw [hH₂shift]
    | parameter i => rfl
    | source i => rfl
  simp only [localCircuit, Circuit.eval_relabel]
  change ((RetainedShiftT.compiler (R := R) k 2).eval localEnv 0,
    (RetainedShiftT.compiler (R := R) k 2).eval localEnv 1) = _
  rw [RetainedShiftT.eval_compiler_eq k 2 localEnv
    (show ValidTCall k 2 from ⟨by omega, by omega⟩) hshift, henv]
  exact eval_tCircuit_with_source (R := R)
    (FastPoly.crownHp (H₂.coeff 1) (H₂.coeff 0 + theta 1)
      (theta 2) (theta 3))
    (FastPoly.crownH4 (H₂.coeff 1) (H₂.coeff 0 + theta 1)
      (theta 2) (theta 3) + C (theta 4))
    (fun i => theta (5 + i)) source k 2

@[simp] theorem eval_circuit_zero [Nontrivial A]
    {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (theta : ℕ → A) (k : ℕ) :
    (circuit (R := R) k).eval (env H₂ H₄ theta) 0 =
      q4BundleOutput H₂ theta k 0 := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  have hpair := eval_local (R := R) (H₄ := H₄) hH₂m hH₂d theta k
  have h₁ := congrArg Prod.fst hpair
  have h₂' := congrArg Prod.snd hpair
  dsimp only at h₁ h₂'
  simp only [env] at h₁ h₂'
  rw [Circuit.eval_fork]
  dsimp only
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_left]
  simp only [Circuit.eval_add, Circuit.eval_mul,
    Circuit.eval_liftLeft, Circuit.eval_rightInput,
    Circuit.eval_constructionX, Circuit.eval_constructionParameter,
    env, q4BundleOutput, FastPoly.q4k1]
  rw [show (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 from rfl]
  rw [twoOutputs_zero]
  rw [h₁, h₂']

@[simp] theorem eval_circuit_one [Nontrivial A]
    {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (theta : ℕ → A) (k : ℕ) :
    (circuit (R := R) k).eval (env H₂ H₄ theta) 1 =
      q4BundleOutput H₂ theta k 1 := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  rw [Circuit.eval_fork]
  dsimp only
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_right, Circuit.eval_priorOutput]
  change (q4Tower (R := R)).eval (env H₂ H₄ theta) 1 =
    FastPoly.crownH4 (H₂.coeff 1) (H₂.coeff 0 + theta 1) (theta 2) (theta 3)
  rw [eval_q4Tower_one, FastPoly.crownH4,
    ← FastPoly.crownH2_shift hH₂m hH₂d]

omit [CommRing R] in
@[simp] theorem q4Tower_additions :
    (q4Tower (R := R)).gates.additions = 6 := by
  rfl

/-- Literal additions in the optimized crown-bundle circuit. -/
theorem circuit_additions (k : ℕ) (hk : 1 ≤ k) :
    (circuit (R := R) k).gates.additions = tAdd (2 * k) 1 + 3 := by
  simp only [circuit, localCircuit, Circuit.gates_bind, Circuit.gates_relabel,
    Circuit.gates, Circuit.gates_liftLeft,
    Circuit.gates_rightInput, Circuit.gates_priorOutput,
    GateCount.add_additions, GateCount.zero_additions,
    GateCount.adds_additions, GateCount.muls_additions,
    q4Tower_additions, Circuit.gates_constructionX,
    Circuit.gates_constructionParameter]
  rw [RetainedShiftT.compiler_additions_eq_tAdd k 2
    (show ValidTCall k 2 from ⟨by omega, by omega⟩),
    tAdd_even_base k hk]
  omega

/-- Exact multiplication count of the optimized crown-bundle circuit. -/
theorem circuit_multiplications (k : ℕ) (hk : 1 ≤ k) :
    (circuit (R := R) k).gates.multiplications = 2 * k := by
  simp only [circuit, localCircuit, Circuit.gates_bind, Circuit.gates_relabel,
    Circuit.gates, Circuit.gates_liftLeft,
    Circuit.gates_rightInput, Circuit.gates_priorOutput,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    q4Tower_multiplications, Circuit.gates_constructionX,
    Circuit.gates_constructionParameter]
  rw [RetainedShiftT.compiler_multiplications,
    gates_tCircuit_multiplications k 2
      (show ValidTCall k 2 from ⟨by omega, by omega⟩)]
  omega

/-- The retained local call has the ordinary q4 local height bound. -/
theorem multDepth_localCircuit_le (k : ℕ) (j : Fin 2) :
    (localCircuit (R := R) k).multDepth
      (Sum.elim Height.gadgetDepthEnv
        ((q4Tower (R := R)).multDepth Height.gadgetDepthEnv)) j
      ≤ 2 * Nat.clog 2 k + 3 := by
  obtain ⟨h0, h1, h2⟩ := multDepth_q4Tower_le (R := R)
  let dT := (q4Tower (R := R)).multDepth Height.gadgetDepthEnv
  have henv : ∀ input,
      (Sum.elim Height.gadgetDepthEnv dT ∘ retainedLabel) input ≤
        Height.gadgetDepthEnv input := by
    intro input
    cases input with
    | «variable» => rfl
    | power i =>
        by_cases hi1 : i = 1
        · subst i
          simpa [dT, retainedLabel] using h0
        · by_cases hi2 : i = 2
          · subst i
            simpa [dT, retainedLabel] using h1
          · simp [retainedLabel, hi1, hi2, Height.gadgetDepthEnv,
              Height.gadgetDp]
    | shiftedPower => simpa [dT, retainedLabel] using h2
    | parameter i => rfl
    | source i =>
        by_cases hi : i = 0
        · subst i
          rfl
        · simp [retainedLabel, hi, Height.gadgetDepthEnv]
  rw [localCircuit, Circuit.multDepth_relabel]
  calc
    (RetainedShiftT.compiler (R := R) k 2).multDepth
        (Sum.elim Height.gadgetDepthEnv dT ∘ retainedLabel) j
        ≤ (RetainedShiftT.compiler (R := R) k 2).multDepth
          Height.gadgetDepthEnv j := Circuit.multDepth_mono _ henv j
    _ ≤ Height.tDB k k 2 := by
      simpa only [RetainedShiftT.compiler] using
        (CrownOptimized.multDepth_compilerF_two_le (R := R) k k j)
    _ ≤ 2 * Nat.clog 2 k + 3 := by
      have h := Height.tDB_le k k 2 (by omega)
      omega

/-- The optimized bundle preserves the ordinary bundle's two-output depth bound. -/
theorem multDepth_circuit_le (k : ℕ) (hk : 1 ≤ k) :
    ((circuit (R := R) k).multDepth Height.gadgetDepthEnv 0
        ≤ 2 * Nat.clog 2 (2 * (2 * k) + 1) + 1) ∧
      ((circuit (R := R) k).multDepth Height.gadgetDepthEnv 1 ≤ 2) := by
  have hT0 := multDepth_localCircuit_le (R := R) k 0
  have hT1 := multDepth_localCircuit_le (R := R) k 1
  have hc1 : Nat.clog 2 (2 * k) = Nat.clog 2 k + 1 :=
    Height.clog_two_double k hk
  have hc2 : Nat.clog 2 (2 * (2 * k)) = Nat.clog 2 (2 * k) + 1 :=
    Height.clog_two_double (2 * k) (by omega)
  have hc3 : Nat.clog 2 (2 * (2 * k)) ≤ Nat.clog 2 (2 * (2 * k) + 1) :=
    Nat.clog_mono_right 2 (by omega)
  constructor
  · rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Circuit.constructionX, Circuit.constructionParameter, Circuit.input,
      Circuit.multDepth_wire, Height.denv_variable,
      Height.denv_parameter]
    omega
  · rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.priorOutput, Circuit.multDepth_input]
    exact (multDepth_q4Tower_le (R := R)).2.1

/-- Drop-in optimized crown bundle with the same two semantic outputs. -/
def realized [Nontrivial A] {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    BundleRealization (R := R) H₂ H₄ theta (q4BundleOutput H₂ theta k) (2 * k) where
  circuit := circuit k
  eval_eq := by
    funext i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact eval_circuit_zero hH₂m hH₂d theta k
    · exact eval_circuit_one hH₂m hH₂d theta k
  multiplication_count := circuit_multiplications k hk

end Q4Optimized

end FastPoly.Cost.OddGadget
