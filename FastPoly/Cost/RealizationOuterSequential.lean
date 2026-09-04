import FastPoly.Cost.OddGadgetAfterBundle
import FastPoly.Cost.RealizationOuter
import FastPoly.Height.RealizationDepth

/-!
# Sequential realization of the `8k+3` outer step

Unlike the `8k+7` step, the two auxiliary gadgets here are not parallel: the first
produces a new quartic consumed by the second.  This module records that dependency in
the circuit syntax, binds every producer once, and returns the new quartic as the
recorded byproduct of the outer pair.
-/

namespace FastPoly.Cost.Outer

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private abbrev SourceInput := Sum PolyInput (Fin 4)
private abbrev BundleInput := Sum SourceInput (Fin 2)
private abbrev ThirdInput := Sum BundleInput (Fin 1)

private def oldParameter (i : ℕ) : Circuit R ThirdInput 1 :=
  (Circuit.polyParameter (R := R) i).liftLeft.liftLeft.liftLeft

/-- Final two-square shell after binding the source, `(S₂,H₄')`, and `S₃`. -/
def eightThreeSequentialBody (aIndex alphaIndex : ℕ) : Circuit R ThirdInput 4 :=
  let S₁ := Circuit.grandOutput (R := R) (ι := PolyInput)
    (n := 2) (o := 1) (0 : Fin 4)
  let St₁ := Circuit.grandOutput (R := R) (ι := PolyInput)
    (n := 2) (o := 1) (1 : Fin 4)
  let H₂ := Circuit.grandOutput (R := R) (ι := PolyInput)
    (n := 2) (o := 1) (2 : Fin 4)
  let S₂ := Circuit.priorOutput (R := R) (ι := SourceInput)
    (n := 1) (0 : Fin 2)
  let H₄' := Circuit.priorOutput (R := R) (ι := SourceInput)
    (n := 1) (1 : Fin 2)
  let S₃ := Circuit.rightInput (R := R) (ι := BundleInput) (0 : Fin 1)
  let T₁ := Circuit.diffSquareAdd S₂ S₁ S₃
  let T₂ := Circuit.diffSquareAdd (.add S₂ (oldParameter aIndex)) St₁
    (oldParameter alphaIndex)
  Circuit.pairWithPowers T₁ T₂ H₂ H₄'

/-- Bind the three producers in their true data-dependency order. -/
def eightThreeSequentialCircuit
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM)
    (aIndex alphaIndex : ℕ) : Circuit R PolyInput 4 :=
  .bind source.circuit <|
    .bind second.circuit <|
      .bind third.circuit (eightThreeSequentialBody aIndex alphaIndex)

private noncomputable def finalEnv
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) : ThirdInput → A[X] :=
  Sum.elim (OddGadget.bundleEnv source second)
    (third.circuit.eval (OddGadget.bundleEnv source second))

@[simp] private theorem eval_source_zero
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) :
    (Circuit.grandOutput (R := R) (ι := PolyInput) (n := 2) (o := 1)
      (0 : Fin 4)).eval (finalEnv source second third) 0 = S₁ := by
  rw [finalEnv]
  change source.circuit.eval (polyEnv θ) 0 = S₁
  exact source.eval₁

@[simp] private theorem eval_source_one
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) :
    (Circuit.grandOutput (R := R) (ι := PolyInput) (n := 2) (o := 1)
      (1 : Fin 4)).eval (finalEnv source second third) 0 = St₁ := by
  rw [finalEnv]
  change source.circuit.eval (polyEnv θ) 1 = St₁
  exact source.eval₂

@[simp] private theorem eval_source_two
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) :
    (Circuit.grandOutput (R := R) (ι := PolyInput) (n := 2) (o := 1)
      (2 : Fin 4)).eval (finalEnv source second third) 0 = H₂ := by
  rw [finalEnv]
  change source.circuit.eval (polyEnv θ) 2 = H₂
  exact source.evalH₂

@[simp] private theorem eval_second_zero
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) :
    (Circuit.priorOutput (R := R) (ι := SourceInput) (n := 1)
      (0 : Fin 2)).eval (finalEnv source second third) 0 = S₂ := by
  rw [finalEnv]
  change second.circuit.eval (OddGadget.sourceEnv source) 0 = S₂
  simpa only [twoOutputs_zero] using second.eval_at 0

@[simp] private theorem eval_second_one
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) :
    (Circuit.priorOutput (R := R) (ι := SourceInput) (n := 1)
      (1 : Fin 2)).eval (finalEnv source second third) 0 = H₄new := by
  rw [finalEnv]
  change second.circuit.eval (OddGadget.sourceEnv source) 1 = H₄new
  simpa only [twoOutputs_one] using second.eval_at 1

@[simp] private theorem eval_third
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) :
    (Circuit.rightInput (R := R) (ι := BundleInput) (0 : Fin 1)).eval
      (finalEnv source second third) 0 = S₃ := by
  rw [finalEnv]
  change third.circuit.eval (OddGadget.bundleEnv source second) 0 = S₃
  exact third.eval_at 0

@[simp] private theorem eval_oldParameter
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) (i : ℕ) :
    (oldParameter (R := R) i).eval (finalEnv source second third) 0 = C (θ i) := by
  rw [oldParameter, finalEnv]
  change (Circuit.polyParameter (R := R) i).eval (polyEnv θ) 0 = C (θ i)
  rfl

private theorem eval_body_zero
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) (aIndex alphaIndex : ℕ) :
    (eightThreeSequentialBody (R := R) aIndex alphaIndex).eval
      (finalEnv source second third) 0 = S₂ * S₂ - S₁ * S₁ + S₃ := by
  simp only [eightThreeSequentialBody, Circuit.eval_pairWithPowers_zero,
    Circuit.eval_diffSquareAdd, eval_second_zero, eval_source_zero, eval_third]
  ring

private theorem eval_body_one
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) (aIndex alphaIndex : ℕ) :
    (eightThreeSequentialBody (R := R) aIndex alphaIndex).eval
      (finalEnv source second third) 1 =
      (S₂ + C (θ aIndex)) * (S₂ + C (θ aIndex)) - St₁ * St₁ +
        C (θ alphaIndex) := by
  simp only [eightThreeSequentialBody, Circuit.eval_pairWithPowers_one,
    Circuit.eval_diffSquareAdd, Circuit.eval_add, eval_second_zero,
    eval_oldParameter, eval_source_one]
  ring

private theorem eval_body_two
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) (aIndex alphaIndex : ℕ) :
    (eightThreeSequentialBody (R := R) aIndex alphaIndex).eval
      (finalEnv source second third) 2 = H₂ := by
  simp only [eightThreeSequentialBody, Circuit.eval_pairWithPowers_two,
    eval_source_two]

private theorem eval_body_three
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM) (aIndex alphaIndex : ℕ) :
    (eightThreeSequentialBody (R := R) aIndex alphaIndex).eval
      (finalEnv source second third) 3 = H₄new := by
  simp only [eightThreeSequentialBody, Circuit.eval_pairWithPowers_three,
    eval_second_one]

omit [CommRing R] in
@[simp] theorem eightThreeSequentialBody_multiplications (aIndex alphaIndex : ℕ) :
    (eightThreeSequentialBody (R := R) aIndex alphaIndex).gates.multiplications = 2 := by
  rfl

/-- Height ledger of the sequential `8k+3` body. -/
theorem multDepth_eightThreeSequentialCircuit_le
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM)
    (aIndex alphaIndex : ℕ) (D d₂ d₃ : ℕ)
    (hs0 : source.circuit.multDepth (fun _ => 0) 0 ≤ D)
    (hs1 : source.circuit.multDepth (fun _ => 0) 1 ≤ D)
    (hs2 : source.circuit.multDepth (fun _ => 0) 2 ≤ 1)
    (h2c0 : second.circuit.multDepth (Sum.elim (fun _ : PolyInput => 0)
      (source.circuit.multDepth (fun _ => 0))) 0 ≤ d₂)
    (h2c1 : second.circuit.multDepth (Sum.elim (fun _ : PolyInput => 0)
      (source.circuit.multDepth (fun _ => 0))) 1 ≤ 2)
    (h3c : third.circuit.multDepth
      (Sum.elim (Sum.elim (fun _ : PolyInput => 0)
        (source.circuit.multDepth (fun _ => 0)))
        (second.circuit.multDepth (Sum.elim (fun _ : PolyInput => 0)
          (source.circuit.multDepth (fun _ => 0))))) 0 ≤ d₃) :
    ((eightThreeSequentialCircuit source second third aIndex alphaIndex).multDepth
        (fun _ => 0) 0 ≤ max (max d₂ D + 1) d₃) ∧
      ((eightThreeSequentialCircuit source second third aIndex
        alphaIndex).multDepth (fun _ => 0) 1 ≤ max (max d₂ D + 1) d₃) ∧
      ((eightThreeSequentialCircuit source second third aIndex
        alphaIndex).multDepth (fun _ => 0) 2 ≤ 1) ∧
      ((eightThreeSequentialCircuit source second third aIndex
        alphaIndex).multDepth (fun _ => 0) 3 ≤ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [eightThreeSequentialCircuit, Circuit.multDepth_bind,
      eightThreeSequentialBody, oldParameter, Circuit.pairWithPowers,
      Circuit.multDepth_fork, Fin.addCases_left,
      Height.multDepth_diffSquareAdd,
      Circuit.multDepth_rightInput,
      Circuit.grandOutput, Circuit.priorOutput,
      Circuit.polyParameter, Circuit.input, Circuit.multDepth_wire,
      Sum.elim_inl, Sum.elim_inr]
    omega
  · rw [show (1 : Fin 4) = Fin.castAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [eightThreeSequentialCircuit, Circuit.multDepth_bind,
      eightThreeSequentialBody, oldParameter, Circuit.pairWithPowers,
      Circuit.multDepth_fork, Fin.addCases_left, Fin.addCases_right,
      Height.multDepth_diffSquareAdd, Circuit.multDepth_add,
      Circuit.multDepth_liftLeft,
      Circuit.grandOutput, Circuit.priorOutput,
      Circuit.polyParameter, Circuit.input, Circuit.multDepth_wire,
      Sum.elim_inl, Sum.elim_inr]
    omega
  · rw [show (2 : Fin 4) = Fin.natAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [eightThreeSequentialCircuit, Circuit.multDepth_bind,
      eightThreeSequentialBody, Circuit.pairWithPowers, Circuit.multDepth_fork,
      Fin.addCases_left, Fin.addCases_right, Circuit.grandOutput,
      Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    exact hs2
  · rw [show (3 : Fin 4) = Fin.natAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [eightThreeSequentialCircuit, Circuit.multDepth_bind,
      eightThreeSequentialBody, Circuit.pairWithPowers, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.priorOutput,
      Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    exact h2c1

/-- Actual realization of the sequential `8k+3` step.  In particular, the returned
quartic is the first gadget's new byproduct, not the smaller source's old quartic. -/
def eightThreeSequentialRealized
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM)
    (aIndex alphaIndex : ℕ) :
    JointPairRealization (R := R) θ
      (S₂ * S₂ - S₁ * S₁ + S₃)
      ((S₂ + C (θ aIndex)) * (S₂ + C (θ aIndex)) - St₁ * St₁ +
        C (θ alphaIndex)) H₂ H₄new (sourceM + secondM + thirdM + 2) where
  circuit := eightThreeSequentialCircuit source second third aIndex alphaIndex
  eval₁ := by
    rw [eightThreeSequentialCircuit, Circuit.eval_bind, Circuit.eval_bind,
      Circuit.eval_bind]
    simpa only [OddGadget.sourceEnv, OddGadget.bundleEnv, finalEnv] using
      eval_body_zero source second third aIndex alphaIndex
  eval₂ := by
    rw [eightThreeSequentialCircuit, Circuit.eval_bind, Circuit.eval_bind,
      Circuit.eval_bind]
    simpa only [OddGadget.sourceEnv, OddGadget.bundleEnv, finalEnv] using
      eval_body_one source second third aIndex alphaIndex
  evalH₂ := by
    rw [eightThreeSequentialCircuit, Circuit.eval_bind, Circuit.eval_bind,
      Circuit.eval_bind]
    simpa only [OddGadget.sourceEnv, OddGadget.bundleEnv, finalEnv] using
      eval_body_two source second third aIndex alphaIndex
  evalH₄ := by
    rw [eightThreeSequentialCircuit, Circuit.eval_bind, Circuit.eval_bind,
      Circuit.eval_bind]
    simpa only [OddGadget.sourceEnv, OddGadget.bundleEnv, finalEnv] using
      eval_body_three source second third aIndex alphaIndex
  multiplication_count := by
    simp only [eightThreeSequentialCircuit, Circuit.gates_bind,
      GateCount.add_multiplications, source.multiplication_count,
      second.multiplication_count, third.multiplication_count,
      eightThreeSequentialBody_multiplications]
    omega

end FastPoly.Cost.Outer
