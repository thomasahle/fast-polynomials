import FastPoly.Examples.Char2Degree23RowEight

/-!
# Removing a supplied monic pivot column by reading its top row

The scalar multiplying a monic column is recovered by the explicit coefficient
difference. When the row was already installed by the decoder, that scalar is
zero and only the strictly lower residual remains. In particular, this permits
degree23's row-eight correction to stay named instead of expanding its baseline.
-/

namespace FastPoly.Char2MonicPivotPeel

open Polynomial
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The unit-slope decoding expression for a supplied monic column. -/
def recover (P Q : R[X]) (n : ℕ) : R := Q.coeff n - P.coeff n

theorem recover_eq {P Q D low : R[X]} {k : R}
    (hD : IsMonicOfDegree D n) (hlow : low.natDegree < n)
    (hchange : Q = P + D * C k + low) : recover P Q n = k := by
  have hd : D.coeff n = 1 := by
    rw [← hD.natDegree_eq]
    exact hD.monic.coeff_natDegree
  have hz : low.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hlow
  rw [recover, hchange, coeff_add, coeff_add, coeff_mul_C, hd, one_mul, hz, add_zero]
  exact add_sub_cancel_left _ _

/-- The top row has already been decoded, so its column disappears exactly. -/
theorem peel {P Q D low : R[X]} {k : R}
    (hD : IsMonicOfDegree D n) (hlow : low.natDegree < n)
    (hchange : Q = P + D * C k + low) (hrow : Q.coeff n = P.coeff n) :
    Q = P + low := by
  have hk : k = 0 := by
    rw [← recover_eq hD hlow hchange, recover, hrow, sub_self]
  rw [hchange, hk, map_zero, mul_zero, add_zero]

section CharacteristicTwo

variable [CharP R 2]

private theorem change_from_difference (P Q d : R[X]) (h : Q + P = d) :
    Q = P + d := by
  rw [← h, ← add_assoc, add_comm P Q, CharTwo.add_cancel_right]

/-- Characteristic-two finite-difference form used by the circuit pivots. -/
theorem peel_difference {P Q D low : R[X]} {k : R}
    (hD : IsMonicOfDegree D n) (hlow : low.natDegree < n)
    (hchange : Q + P = D * C k + low) (hrow : Q.coeff n = P.coeff n) :
    Q = P + low := by
  have he : Q = P + D * C k + low := by
    rw [change_from_difference P Q _ hchange, add_assoc]
  exact peel hD hlow he hrow

end CharacteristicTwo

end FastPoly.Char2MonicPivotPeel
