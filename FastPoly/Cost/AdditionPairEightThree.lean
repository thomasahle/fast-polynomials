import FastPoly.Cost.AdditionPairEightSeven
import FastPoly.Cost.OddGadgetCrownBundleOptimized
import FastPoly.Cost.RealizationOuterSequentialAdditions

/-!
# Same-program addition certificate for the recursive `8k+3` pair step

The low slot differs genuinely at degree one.  There it is a scalar polynomial,
carried by a parameter wire with no arithmetic gates; treating it as the generic
affine degree-one gadget would spend one addition absent from the selected ledger.
For larger low slots, the ordinary addition-certified realized gadget supplies the
same interface.  The recursive constructor then uses the optimized retained-quartic
bundle and the literal seven-addition sequential outer shell.
-/

namespace FastPoly.Cost

open Polynomial Algebra

universe u v

/-- A decoder-facing low-slot polynomial whose literal circuit realizes the selected
`LowGadgetAddCost`.  Unlike an ordinary odd gadget, the scalar degree-one case need
only have degree at most one and a known top coefficient. -/
structure AdditionRealizedLowGadget {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (H₂ H₄ : A[X]) (theta : ℕ → A) (degree additions : ℕ) where
  Q : A[X]
  degree_le : Q.natDegree ≤ degree
  leading_mem : ∀ V : Subalgebra R A, Q.coeff degree ∈ V
  recover : ∀ V : Subalgebra R A,
    (∀ j, H₂.coeff j ∈ V) → (∀ j, H₄.coeff j ∈ V) →
      (∀ j, Q.coeff j ∈ V) → ∀ t, t < degree → theta t ∈ V
  realization : OddGadget.Realization (R := R) H₂ H₄ theta Q (degree / 2)
  addition_count : realization.circuit.gates.additions = additions
  ledger : LowGadgetAddCost degree additions

namespace AdditionRealizedLowGadget

/-- The exceptional low slot at degree one is the scalar itself.  Its constant
coefficient is the explicit decoder pivot and its parameter wire costs no gates. -/
noncomputable def scalar {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (H₂ H₄ : A[X]) (theta : ℕ → A) :
    AdditionRealizedLowGadget (R := R) H₂ H₄ theta 1 0 where
  Q := C (theta 0)
  degree_le := by simp
  leading_mem := by
    intro V
    simp
  recover := by
    intro V _ _ hQ t ht
    have ht0 : t = 0 := by omega
    subst t
    simpa using hQ 0
  realization :=
    { circuit := Circuit.constructionParameter 0
      eval_eq := rfl
      multiplication_count := rfl
      depth_le := by
        show Height.gadgetDepthEnv (.parameter 0) ≤ _
        simp }
  addition_count := rfl
  ledger := LowGadgetAddCost.one

/-- Every ordinary realized gadget of degree at least three is also a low-slot
object; only its stronger exact-degree and monicity fields are forgotten. -/
def ofGadget {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {H₂ H₄ : A[X]} {theta : ℕ → A} {degree additions : ℕ}
    (hdegree : 3 ≤ degree)
    (gadget : AdditionRealizedOddGadget (R := R) H₂ H₄ theta
      degree additions) :
    AdditionRealizedLowGadget (R := R) H₂ H₄ theta degree additions where
  Q := gadget.Q
  degree_le := le_of_eq gadget.natDegree
  leading_mem := by
    intro V
    have hlead := gadget.monic.coeff_natDegree
    rw [gadget.natDegree] at hlead
    rw [hlead]
    exact one_mem V
  recover := gadget.recover
  realization := gadget.realization
  addition_count := gadget.addition_count
  ledger := LowGadgetAddCost.ofGadget hdegree gadget.ledger

end AdditionRealizedLowGadget

namespace AdditionJointPairRealization

/-- Build the recursive `8k+3` certificate on the optimized retained-quartic bundle
and the existing true-order sequential outer circuit. -/
noncomputable def eightThree
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Nontrivial A]
    {theta : ℕ → A} {T₁ T₂ H₂ H₄old : A[X]} {k a g₂ : ℕ}
    (hk : 1 ≤ k) (hk3 : k ≠ 3)
    (source : AdditionJointPairRealization R theta T₁ T₂ H₂ H₄old
      (2 * k + 1) a)
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (secondOffset thirdOffset aIndex alphaIndex : ℕ)
    (third : AdditionRealizedLowGadget (R := R) H₂
      (OddGadget.q4BundleOutput H₂
        (fun i => theta (secondOffset + i)) k 1)
      (fun i => theta (thirdOffset + i)) (2 * k - 1) g₂) :
    AdditionJointPairRealization R theta
      ((OddGadget.q4BundleOutput H₂
          (fun i => theta (secondOffset + i)) k 0) *
        (OddGadget.q4BundleOutput H₂
          (fun i => theta (secondOffset + i)) k 0) - T₁ * T₁ + third.Q)
      (((OddGadget.q4BundleOutput H₂
          (fun i => theta (secondOffset + i)) k 0) + C (theta aIndex)) *
        ((OddGadget.q4BundleOutput H₂
          (fun i => theta (secondOffset + i)) k 0) + C (theta aIndex)) -
          T₂ * T₂ + C (theta alphaIndex))
      H₂
      (OddGadget.q4BundleOutput H₂
        (fun i => theta (secondOffset + i)) k 1)
      (8 * k + 3) (a + (tAdd (2 * k) 1 + 3) + g₂ + 7) := by
  let sourceR := source.realization
  let secondBundle := OddGadget.Q4Optimized.realized (R := R) (H₄ := H₄old)
    hH₂m hH₂d (fun i => theta (secondOffset + i)) k hk
  let secondR := OddGadget.BundleRealization.relative sourceR secondBundle
  let thirdR := OddGadget.Realization.afterBundle sourceR secondR
    third.realization
  let realized := Outer.eightThreeSequentialRealized sourceR secondR thirdR
    aIndex alphaIndex
  exact
    { certificate :=
        { program :=
            { circuit := realized.circuit
              multiplication_count := by
                rw [realized.multiplication_count]
                omega }
          addition_count := by
            change (Outer.eightThreeSequentialCircuit sourceR secondR thirdR
              aIndex alphaIndex).gates.additions =
                a + (tAdd (2 * k) 1 + 3) + g₂ + 7
            rw [Outer.eightThreeSequentialCircuit_additions]
            have hsource : sourceR.circuit.gates.additions = a := by
              exact realization_additions source
            have hsecond : secondR.circuit.gates.additions =
                tAdd (2 * k) 1 + 3 := by
              exact OddGadget.BundleRealization.relative_additions sourceR
                secondBundle (OddGadget.Q4Optimized.circuit_additions k hk)
            have hthird : thirdR.circuit.gates.additions = g₂ := by
              exact OddGadget.Realization.afterBundle_additions sourceR secondR
                third.realization third.addition_count
            rw [hsource, hsecond, hthird]
          ledger := PairAddCost.eightKPlusThree k a
            (tAdd (2 * k) 1 + 3) g₂ hk hk3 source.certificate.ledger
            (GadgetAddCost.fourKPlusOne k hk) third.ledger }
      realizesAt := ⟨realized.eval₁, realized.eval₂, realized.evalH₂,
        realized.evalH₄⟩ }

end AdditionJointPairRealization

end FastPoly.Cost
