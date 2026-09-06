import FastPoly.Examples.Char2CoefficientShearTransport

/-! Lift a supplied lower-row action through an explicitly invertible
coefficient shear. The previous pivot correction disappears by its normalized
coefficient equation, without expanding the tail. -/

namespace FastPoly.Char2CoefficientAction

open Polynomial Char2CoefficientShear Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] {n : ℕ}

def lift (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
    (S : (Fin n → R) → R → (Fin n → R))
    (q : Fin n → R) (δ : R) : Fin n → R :=
  (coordinateShear f j m).symm (S (coordinateShear f j m q) δ)

variable (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
  (S : (Fin n → R) → R → (Fin n → R))

theorem shear_lift (q : Fin n → R) (δ : R) :
    coordinateShear f j m (lift f j m S q δ) =
      S (coordinateShear f j m q) δ :=
  (coordinateShear f j m).apply_symm_apply _

theorem lift_unit (r : ℕ)
    (hS : ∀ (q : Fin n → R) (δ : R), UnitDifference (f q) (f (S q δ)) r δ)
    (q : Fin n → R) (δ : R) :
    UnitDifference (f (coordinateShear f j m q))
      (f (coordinateShear f j m (lift f j m S q δ))) r δ := by
  rw [shear_lift]
  exact hS (coordinateShear f j m q) δ

theorem lift_other (q : Fin n → R) (δ : R) (k : Fin n) (hkj : k ≠ j) :
    lift f j m S q δ k = S (coordinateShear f j m q) δ k := by
  unfold lift
  rw [coordinateShear_symm_apply, Function.update_of_ne hkj]

theorem lift_before
    (hbefore : ∀ (q : Fin n → R) (δ : R) (k : Fin n), k < j → S q δ k = q k)
    (q : Fin n → R) (δ : R) (k : Fin n) (hkj : k < j) :
    lift f j m S q δ k = q k := by
  rw [lift_other f j m S q δ k (ne_of_lt hkj), hbefore _ _ k hkj,
    coordinateShear_apply, Function.update_of_ne (ne_of_lt hkj)]

theorem baseline_lift
    (hbefore : ∀ (q : Fin n → R) (δ : R) (k : Fin n), k < j → S q δ k = q k)
    (q : Fin n → R) (δ : R) :
    baseline f j m (lift f j m S q δ) = baseline f j m q :=
  baseline_congr f j m _ q (lift_before f j m S hbefore q δ)

/-- The unit coefficient equation forces preservation of the earlier pivot.
The only cancellation is of its shared, unexpanded prefix baseline. -/
theorem lift_pivot
    (hj : ∀ (q : Fin n → R) (δ : R),
      UnitDifference (f q) (f (Char2CoefficientShearTransport.increment q j δ)) m δ)
    (r : ℕ) (hrm : r < m)
    (hS : ∀ (q : Fin n → R) (δ : R), UnitDifference (f q) (f (S q δ)) r δ)
    (hbefore : ∀ (q : Fin n → R) (δ : R) (k : Fin n), k < j → S q δ k = q k)
    (q : Fin n → R) (δ : R) : lift f j m S q δ j = q j := by
  have hu : ∀ (a : Fin n → R) (d : R),
      (f (Function.update a j (a j + d))).coeff m = (f a).coeff m + d := by
    intro a d
    have hp := (hj a d).pivot
    rw [coeff_add] at hp
    calc
      (f (Function.update a j (a j + d))).coeff m =
          ((f (Function.update a j (a j + d))).coeff m + (f a).coeff m) +
            (f a).coeff m := (CharTwo.add_cancel_right _ _).symm
      _ = d + (f a).coeff m := by rw [hp]
      _ = (f a).coeff m + d := add_comm _ _
  have hd := hS (coordinateShear f j m q) δ
  have hz : (f (S (coordinateShear f j m q) δ) +
      f (coordinateShear f j m q)).coeff m = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.difference_degree.trans_lt hrm)
  rw [coeff_add] at hz
  have he := CharTwo.add_eq_zero.mp hz
  rw [← shear_lift f j m S q δ,
    coefficient_normalized f j m hu (lift f j m S q δ),
    coefficient_normalized f j m hu q,
    baseline_lift f j m S hbefore q δ] at he
  exact add_right_cancel he

/-- An arbitrary non-pivot coordinate preserved by the supplied action stays
unchanged after lifting it. -/
theorem lift_preserves (k : Fin n) (hkj : k ≠ j)
    (hk : ∀ (q : Fin n → R) (δ : R), S q δ k = q k)
    (q : Fin n → R) (δ : R) : lift f j m S q δ k = q k := by
  rw [lift_other f j m S q δ k hkj, hk,
    coordinateShear_apply, Function.update_of_ne hkj]

/-- The supplied future pivot still receives exactly the specified increment. -/
theorem lift_increments (k : Fin n) (hjk : j < k)
    (hk : ∀ (q : Fin n → R) (δ : R), S q δ k = q k + δ)
    (q : Fin n → R) (δ : R) : lift f j m S q δ k = q k + δ := by
  rw [lift_other f j m S q δ k (ne_of_gt hjk), hk,
    coordinateShear_apply, Function.update_of_ne (ne_of_gt hjk)]

end FastPoly.Char2CoefficientAction
