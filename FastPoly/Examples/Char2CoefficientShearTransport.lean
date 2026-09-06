import FastPoly.Examples.Char2CoefficientShear
import FastPoly.Examples.Char2Degree19InnerTail

/-! Unit differences transported through an explicit coefficient shear.
All corrections stay opaque; only their supplied degree bounds are used. -/

namespace FastPoly.Char2CoefficientShearTransport

open Polynomial Char2CoefficientShear Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] {n : ℕ}

abbrev increment (q : Fin n → R) (i : Fin n) (δ : R) : Fin n → R :=
  Function.update q i (q i + δ)

private theorem difference_four (a b c d : R[X]) :
    d + c = (b + a) + ((d + b) + (c + a)) := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

/-- Low corrections at both endpoints preserve a higher unit difference. -/
theorem two_sided_transport {a b c d : R[X]} {m r : ℕ} {δ : R}
    (hu : UnitDifference a b r δ) (hmr : m < r)
    (hc : (c + a).natDegree ≤ m) (hd : (d + b).natDegree ≤ m) :
    UnitDifference c d r δ := by
  have hl : ((d + b) + (c + a)).natDegree ≤ m :=
    natDegree_add_le_of_degree_le hd hc
  have hz : ((d + b) + (c + a)).coeff r = 0 :=
    coeff_eq_zero_of_natDegree_lt (hl.trans_lt hmr)
  constructor
  · rw [difference_four a b c d]
    exact natDegree_add_le_of_degree_le hu.difference_degree (hl.trans hmr.le)
  · rw [difference_four a b c d, coeff_add, hu.pivot, hz, add_zero]

variable (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
  (hj : ∀ (q : Fin n → R) (δ : R),
    UnitDifference (f q) (f (increment q j δ)) m δ)

include hj in
theorem shear_output_difference (q : Fin n → R) :
    (f (coordinateShear f j m q) + f q).natDegree ≤ m := by
  rw [coordinateShear_apply]
  exact (hj q (tail f j m q)).difference_degree

include hj in
/-- No relation between the input coordinate indices is required for this
higher-row transport: both endpoint corrections have degree at most `m`. -/
theorem high_unit (i : Fin n) (r : ℕ) (hmr : m < r)
    (hi : ∀ (q : Fin n → R) (δ : R),
      UnitDifference (f q) (f (increment q i δ)) r δ)
    (q : Fin n → R) (δ : R) :
    UnitDifference (f (coordinateShear f j m q))
      (f (coordinateShear f j m (increment q i δ))) r δ :=
  two_sided_transport (hi q δ) hmr
    (shear_output_difference f j m hj q)
    (shear_output_difference f j m hj (increment q i δ))

theorem zeroAt_increment (q : Fin n → R) (k : Fin n) (hjk : j < k) (δ : R) :
    zeroAt j (increment q k δ) = increment (zeroAt j q) k δ := by
  unfold zeroAt increment
  rw [Function.update_of_ne (ne_of_gt hjk)]
  exact Function.update_comm (ne_of_gt hjk) (q k + δ) 0 q

/-- A lower supplied pivot cannot alter the coefficient used in this tail. -/
theorem tail_increment (k : Fin n) (hjk : j < k) (r : ℕ) (hrm : r < m)
    (hk : ∀ (q : Fin n → R) (δ : R),
      UnitDifference (f q) (f (increment q k δ)) r δ)
    (q : Fin n → R) (δ : R) :
    tail f j m (increment q k δ) = tail f j m q := by
  have hd := hk (zeroAt j q) δ
  have hz : (f (increment (zeroAt j q) k δ) + f (zeroAt j q)).coeff m = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.difference_degree.trans_lt hrm)
  rw [coeff_add] at hz
  have he : (f (increment (zeroAt j q) k δ)).coeff m =
      (f (zeroAt j q)).coeff m := CharTwo.add_eq_zero.mp hz
  unfold tail
  rw [zeroAt_increment j q k hjk δ, he,
    baseline_update f j m k hjk.le]

/-- The explicit correction commutes with a later, lower unit update. -/
theorem shear_increment (k : Fin n) (hjk : j < k) (r : ℕ) (hrm : r < m)
    (hk : ∀ (q : Fin n → R) (δ : R),
      UnitDifference (f q) (f (increment q k δ)) r δ)
    (q : Fin n → R) (δ : R) :
    coordinateShear f j m (increment q k δ) =
      increment (coordinateShear f j m q) k δ := by
  rw [coordinateShear_apply, coordinateShear_apply,
    tail_increment f j m k hjk r hrm hk q δ]
  unfold increment
  rw [Function.update_of_ne (ne_of_lt hjk),
    Function.update_of_ne (ne_of_gt hjk)]
  exact Function.update_comm (ne_of_gt hjk) (q k + δ) (q j + tail f j m q) q

/-- A later lower unit pivot survives normalization with exactly the same
increment, not an inferred or searched inverse. -/
theorem low_unit (k : Fin n) (hjk : j < k) (r : ℕ) (hrm : r < m)
    (hk : ∀ (q : Fin n → R) (δ : R),
      UnitDifference (f q) (f (increment q k δ)) r δ)
    (q : Fin n → R) (δ : R) :
    UnitDifference (f (coordinateShear f j m q))
      (f (coordinateShear f j m (increment q k δ))) r δ := by
  rw [shear_increment f j m k hjk r hrm hk q δ]
  exact hk (coordinateShear f j m q) δ

/-- The correction ignores its own pivot, so translation of that pivot
commutes with the displayed shear as well. -/
theorem shear_increment_self (q : Fin n → R) (δ : R) :
    coordinateShear f j m (increment q j δ) =
      increment (coordinateShear f j m q) j δ := by
  have ht : tail f j m (increment q j δ) = tail f j m q :=
    tail_independent f j m q (q j + δ)
  rw [coordinateShear_apply, coordinateShear_apply, ht]
  unfold increment
  rw [Function.update_self, Function.update_self,
    Function.update_idem, Function.update_idem]
  rw [add_right_comm (q j) δ (tail f j m q)]

include hj in
/-- Normalizing the supplied pivot preserves its unit output difference. -/
theorem own_unit (q : Fin n → R) (δ : R) :
    UnitDifference (f (coordinateShear f j m q))
      (f (coordinateShear f j m (increment q j δ))) m δ := by
  rw [shear_increment_self f j m q δ]
  exact hj (coordinateShear f j m q) δ

end FastPoly.Char2CoefficientShearTransport
