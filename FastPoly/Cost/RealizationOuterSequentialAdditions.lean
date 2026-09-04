import FastPoly.Cost.RealizationOuterSequential

/-!
# Addition ledger for the sequential `8k+3` outer step

The semantic constructor binds its three producers in their true dependency order.
This module records the corresponding exact addition count on that same literal
circuit: the binds merely add the producer ledgers, while the final two-square body
uses seven additions.
-/

namespace FastPoly.Cost.Outer

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

omit [CommRing R] in
/-- The literal final shell uses three additions for each difference of squares and
one more for the shifted center of the second shell. -/
@[simp] theorem eightThreeSequentialBody_additions (aIndex alphaIndex : ℕ) :
    (eightThreeSequentialBody (R := R) aIndex alphaIndex).gates.additions = 7 := by
  rfl

/-- Exact addition count after binding the source, crown bundle, and final gadget. -/
theorem eightThreeSequentialCircuit_additions
    {theta : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) theta S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM)
    (aIndex alphaIndex : ℕ) :
    (eightThreeSequentialCircuit source second third aIndex
      alphaIndex).gates.additions =
      source.circuit.gates.additions + second.circuit.gates.additions +
        third.circuit.gates.additions + 7 := by
  simp only [eightThreeSequentialCircuit, Circuit.gates_bind,
    GateCount.add_additions, eightThreeSequentialBody_additions]
  omega

/-- The realized wrapper exposes exactly the circuit counted above. -/
theorem eightThreeSequentialRealized_additions
    {theta : ℕ → A} {S₁ St₁ H₂ H₄old S₂ H₄new S₃ : A[X]}
    {sourceM secondM thirdM : ℕ}
    (source : JointPairRealization (R := R) theta S₁ St₁ H₂ H₄old sourceM)
    (second : MultiplicationRealization (R := R) (OddGadget.sourceEnv source)
      (twoOutputs S₂ H₄new) secondM)
    (third : MultiplicationRealization (R := R) (OddGadget.bundleEnv source second)
      (fun _ : Fin 1 => S₃) thirdM)
    (aIndex alphaIndex : ℕ) :
    (eightThreeSequentialRealized source second third aIndex
      alphaIndex).circuit.gates.additions =
      source.circuit.gates.additions + second.circuit.gates.additions +
        third.circuit.gates.additions + 7 :=
  eightThreeSequentialCircuit_additions source second third aIndex alphaIndex

end FastPoly.Cost.Outer
