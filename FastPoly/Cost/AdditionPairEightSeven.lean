import FastPoly.Cost.AdditionJointPairProgram
import FastPoly.Cost.OddGadgetRelativeAdditions
import FastPoly.Cost.RealizationOuter

/-!
# Same-program addition certificate for the recursive `8k+7` pair step

The numerical recursive ledger is attached here to the exact circuit used by the
existing semantic outer constructor.  A small pointwise wrapper keeps the
`RealizesAt` proof and addition certificate on one fixed `JointPairProgram`; public
uniformity can then specialize a wrapper built over the free parameter environment.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

/-- A fixed addition-certified pair program together with its semantics at one
parameter environment.  The program is selected before the `RealizesAt` field. -/
structure AdditionJointPairRealization (R : Type u) [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] (theta : ℕ → A)
    (T₁ T₂ H₂ H₄ : A[X]) (degree additions : ℕ) where
  certificate : AdditionJointPairProgram R degree additions
  realizesAt : certificate.program.RealizesAt theta T₁ T₂ H₂ H₄

namespace AdditionJointPairRealization

/-- Expose the certificate's fixed circuit as the pointwise realization required by
the semantic composition helpers. -/
def realization {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {degree additions : ℕ}
    (source : AdditionJointPairRealization R theta T₁ T₂ H₂ H₄
      degree additions) :
    JointPairRealization (R := R) theta T₁ T₂ H₂ H₄ ((degree - 1) / 2) where
  circuit := source.certificate.program.circuit
  eval₁ := source.realizesAt.1
  eval₂ := source.realizesAt.2.1
  evalH₂ := source.realizesAt.2.2.1
  evalH₄ := source.realizesAt.2.2.2
  multiplication_count := source.certificate.program.multiplication_count

/-- The pointwise view keeps the certificate's literal addition equality. -/
@[simp] theorem realization_additions
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {degree additions : ℕ}
    (source : AdditionJointPairRealization R theta T₁ T₂ H₂ H₄
      degree additions) :
    source.realization.circuit.gates.additions = additions :=
  source.certificate.addition_count

/-- Build the recursive `8k+7` certificate on the same literal shared circuit as
`Outer.eightSevenRealized`. -/
def eightSeven
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {k a g₁ g₂ : ℕ}
    (hk : 2 ≤ k) (hk3 : k ≠ 3)
    (source : AdditionJointPairRealization R theta T₁ T₂ H₂ H₄
      (2 * k + 1) a)
    (secondOffset thirdOffset sIndex dIndex : ℕ)
    (second : AdditionRealizedOddGadget (R := R) H₂ H₄
      (fun i => theta (secondOffset + i)) (2 * k + 1) g₁)
    (third : AdditionRealizedOddGadget (R := R) H₂ H₄
      (fun i => theta (thirdOffset + i)) (4 * k + 3) g₂) :
    AdditionJointPairRealization R theta
      (third.Q * third.Q - second.Q * second.Q + T₁)
      ((third.Q + second.Q + C (theta sIndex)) *
        (third.Q - second.Q + C (theta dIndex)) + T₂)
      H₂ H₄ (8 * k + 7) (a + g₁ + g₂ + 6) := by
  let sourceR := source.realization
  let secondR := RealizedOddGadget.relative sourceR second.toRealized
  let thirdR := RealizedOddGadget.relative sourceR third.toRealized
  let realized := Outer.eightSevenRealized sourceR secondR thirdR sIndex dIndex
  exact
    { certificate :=
        { program :=
            { circuit := realized.circuit
              multiplication_count := by
                rw [realized.multiplication_count]
                omega }
          addition_count := by
            change (Outer.eightSevenCircuit sourceR secondR thirdR sIndex
              dIndex).gates.additions = a + g₁ + g₂ + 6
            rw [Outer.eightSevenCircuit_additions]
            simp only [sourceR, secondR, thirdR, realization_additions,
              AdditionRealizedOddGadget.relative_additions]
          ledger := PairAddCost.eightKPlusSeven k a g₁ g₂ hk hk3
            source.certificate.ledger second.ledger third.ledger }
      realizesAt := ⟨realized.eval₁, realized.eval₂, realized.evalH₂,
        realized.evalH₄⟩ }

end AdditionJointPairRealization

end FastPoly.Cost
