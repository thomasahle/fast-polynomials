import FastPoly.Examples.Char2CoefficientShearTransport

/-! Descending degree bounds through the actual coefficient normalization.
The inverse explicitly installs a row from its known prefix. A later
coordinate change therefore has zero difference in that row; the supplied
unit column bounds the correction, leaving one fewer possible degree. -/
namespace FastPoly.Char2CoefficientDegreePeel

open Polynomial Char2CoefficientShear Char2CoefficientShearTransport
  Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] {n : ℕ}

private theorem difference_four (a b c d : R[X]) :
    d + c = (b + a) + ((d + b) + (c + a)) := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero,
    CharTwo.add_cancel_left, add_zero, zero_add]

theorem degree_after (f : (Fin n → R) → R[X]) (j k : Fin n) (m : ℕ)
    (hjk : j < k)
    (hj : ∀ (q : Fin n → R) (d : R), UnitDifference (f q) (f (increment q j d)) m d)
    (hk : ∀ (q : Fin n → R) (d : R), (f (increment q k d) + f q).natDegree ≤ m)
    (q : Fin n → R) (d : R) :
    (f (coordinateShear f j m (increment q k d)) +
      f (coordinateShear f j m q)).natDegree ≤ m - 1 := by
  have hd : (f (coordinateShear f j m (increment q k d)) +
      f (coordinateShear f j m q)).natDegree ≤ m := by
    rw [difference_four (f q) (f (increment q k d))
      (f (coordinateShear f j m q)) (f (coordinateShear f j m (increment q k d)))]
    exact natDegree_add_le_of_degree_le (hk q d)
      (natDegree_add_le_of_degree_le
        (shear_output_difference f j m hj (increment q k d))
        (shear_output_difference f j m hj q))
  have hu : ∀ (q : Fin n → R) (d : R),
      (f (Function.update q j (q j + d))).coeff m = (f q).coeff m + d := by
    intro q d
    have hp := (hj q d).pivot
    rw [coeff_add] at hp
    calc
      (f (Function.update q j (q j + d))).coeff m =
          ((f (Function.update q j (q j + d))).coeff m + (f q).coeff m) +
            (f q).coeff m := (CharTwo.add_cancel_right _ _).symm
      _ = d + (f q).coeff m := by rw [hp]
      _ = (f q).coeff m + d := add_comm _ _
  have hz : (f (coordinateShear f j m (increment q k d)) +
      f (coordinateShear f j m q)).coeff m = 0 := by
    rw [coeff_add, coefficient_normalized f j m hu, coefficient_normalized f j m hu]
    change (Function.update q k (q k + d) j + baseline f j m (Function.update q k (q k + d))) +
      (q j + baseline f j m q) = 0
    rw [Function.update_of_ne (ne_of_lt hjk), baseline_update f j m k hjk.le,
      CharTwo.add_self_eq_zero]
  exact natDegree_le_pred hd hz

end FastPoly.Char2CoefficientDegreePeel
