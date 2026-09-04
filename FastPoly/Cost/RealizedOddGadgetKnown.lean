import FastPoly.Cost.RealizedOddGadgetBasic
import FastPoly.Section6.Dispatch

/-!
# Realized known-powers odd gadget

This file is the sole bridge between the public algebraic `knownGadget` decoder and
the local semantic circuit normal form `OddGadget.knownValue`.  The bridge is a
definitional polynomial identity; the long decoder remains in `Section6.Dispatch` and
is not duplicated in the cost layer.
-/

namespace FastPoly.Cost

open Polynomial Algebra

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

namespace OddGadget

omit [Nontrivial A] in
/-- The circuit normal form and the decoder's named known-powers polynomial are the
same expression.  At level two the intervening fill chain has no nontrivial stage. -/
theorem knownValue_eq_knownGadget (H₂ H₄ : A[X]) (m : ℕ) (θ : ℕ → A) :
    knownValue H₂ H₄ m θ = FastPoly.knownGadget H₂ H₄ m θ := by
  rfl

end OddGadget

namespace RealizedOddGadget

/-- The `8m+3` known-powers branch, pairing its explicit decoder with the circuit that
computes the very same polynomial in `4m+1 = (8m+3)/2` multiplications. -/
noncomputable def known {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (hH₄m : H₄.Monic)
    (hH₄d : H₄.natDegree = 4) (m : ℕ) (hm : 1 ≤ m)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * m → IsUnit (((n : ℕ) : ℤ) : R))
    (θ : ℕ → A) :
    RealizedOddGadget (R := R) H₂ H₄ θ (8 * m + 3) := by
  obtain ⟨hQm, hQd⟩ := FastPoly.knownGadget_good
    hH₂m hH₂d hH₄m hH₄d hm θ
  exact
    { Q := FastPoly.knownGadget H₂ H₄ m θ
      monic := hQm
      natDegree := hQd
      recover := by
        intro V hH₂V hH₄V hQV
        exact FastPoly.knownGadget_decodable hm hadm hH₂m hH₂d hH₄m hH₄d
          θ V hH₂V hH₄V hQV
      realization := by
        simpa only [OddGadget.knownValue_eq_knownGadget,
          show (8 * m + 3) / 2 = 4 * m + 1 by omega] using
          OddGadget.knownRealized (R := R) H₂ H₄ θ m hm }

end RealizedOddGadget

end FastPoly.Cost
