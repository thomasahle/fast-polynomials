import FastPoly.Cost.AdditionPairEightThree
import FastPoly.Cost.RealizedOddGadgetAdditionDispatch

/-!
# Addition-certified dispatch for the low `8k+3` slot

The selected low-slot ledger has one exceptional branch: degree one is a scalar
polynomial carried by a zero-gate parameter wire.  Every larger positive odd degree
uses the ordinary addition-certified gadget dispatcher.  This module makes that split
at the decoder-facing circuit level rather than only in the numerical recurrence.
-/

namespace FastPoly.Cost.AdditionRealizedLowGadget

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

/-- Every positive odd low-slot degree has a canonical decoder-facing realization
whose selected `LowGadgetAddCost` is proved for its literal circuit. -/
theorem dispatch (degree : ℕ) (hdegree : 1 ≤ degree)
    (hodd : degree % 2 = 1)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ degree → IsUnit (((n : ℕ) : ℤ) : R))
    {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) (theta : ℕ → A) :
    ∃ additions, Nonempty
      (AdditionRealizedLowGadget (R := R) H₂ H₄ theta degree additions) := by
  rcases eq_or_ne degree 1 with rfl | hne
  · exact ⟨0, ⟨scalar H₂ H₄ theta⟩⟩
  · have hthree : 3 ≤ degree := by omega
    obtain ⟨additions, ⟨gadget⟩⟩ :=
      AdditionRealizedOddGadget.dispatch (R := R) degree hodd hadm
        hH₂m hH₂d hH₄m hH₄d theta
    exact ⟨additions, ⟨ofGadget hthree gadget⟩⟩

end FastPoly.Cost.AdditionRealizedLowGadget
