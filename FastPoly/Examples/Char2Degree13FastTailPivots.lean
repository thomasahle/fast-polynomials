import FastPoly.Examples.Char2Degree13FastChanges
import FastPoly.Examples.Char2Degree13FastSignature

/-! Pivot rows and the exceptional zero rows of the nonmonotone tail.
Only two small product windows (degrees 5 by 4 at rows 7 and 6) are read.
All remaining earlier-row preservation uses the named slope's degree. -/

namespace FastPoly.Char2Degree13Fast

set_option maxHeartbeats 20000

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

/-- A three-term window, with all discarded coefficients individually bounded. -/
private theorem product54_coeff7 (p q : R[X])
    (hp : p.natDegree ≤ 5) (hq : q.natDegree ≤ 4) :
    (p * q).coeff 7 = p.coeff 3 * q.coeff 4 +
      p.coeff 4 * q.coeff 3 + p.coeff 5 * q.coeff 2 := by
  have hp6 : p.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (hp.trans_lt (by omega))
  have hp7 : p.coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (hp.trans_lt (by omega))
  have hq5 : q.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega))
  have hq6 : q.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega))
  have hq7 : q.coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega))
  rw [coeff_mul]
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub,
    hp6, hp7, hq5, hq6, hq7, zero_mul, mul_zero, zero_add, add_zero]

/-- The adjacent four-term window; no lower coefficient is requested. -/
private theorem product54_coeff6 (p q : R[X])
    (hp : p.natDegree ≤ 5) (hq : q.natDegree ≤ 4) :
    (p * q).coeff 6 = p.coeff 2 * q.coeff 4 + p.coeff 3 * q.coeff 3 +
      p.coeff 4 * q.coeff 2 + p.coeff 5 * q.coeff 1 := by
  have hp6 : p.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (hp.trans_lt (by omega))
  have hq5 : q.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega))
  have hq6 : q.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega))
  rw [coeff_mul]
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub,
    hp6, hq5, hq6, zero_mul, mul_zero, zero_add, add_zero]

private theorem coeff_add_C_pos (p : R[X]) (c : R) (i : ℕ) (hi : 0 < i) :
    (p + C c).coeff i = p.coeff i := by
  rw [coeff_add, coeff_C]
  simp only [ne_of_gt hi, ite_false, add_zero]

theorem coefficient_change_one (p p' slope : R[X]) (delta : R) (j : ℕ)
    (he : p' = p + C delta * slope) (hs : slope.coeff j = 1) :
    p'.coeff j = p.coeff j + delta := by
  rw [he, coeff_add, coeff_C_mul, hs, mul_one]

theorem coefficient_change_zero (p p' slope : R[X]) (delta : R) (j : ℕ)
    (he : p' = p + C delta * slope) (hs : slope.coeff j = 0) :
    p'.coeff j = p.coeff j := by
  rw [he, coeff_add, coeff_C_mul, hs, mul_zero, add_zero]

variable [Nontrivial R]

theorem slope3_monic (q : Keys R) : IsMonicOfDegree (slope3 q) 9 :=
  (cFactor_monic q).mul ((aFactor_monic q).add_right
    (Char2Degree15Fast.const_lt (q 5) 4 (by omega)))
theorem slope4_monic (q : Keys R) : IsMonicOfDegree (slope4 q) 9 :=
  (rFactor_monic q).mul ((w_monic q).add_right
    (Char2Degree15Fast.const_lt (q 7) 8 (by omega)))
theorem slope5_monic (q : Keys R) : IsMonicOfDegree (slope5 q) 9 :=
  (cFactor_monic q).mul (bFactor_monic q)
theorem slope6_monic (q : Keys R) : IsMonicOfDegree (slope6 q) 8 :=
  ((w_monic q).add_right ((t_monic q).natDegree_eq ▸ (by omega : 3 < 8))).add_right
    (Char2Degree15Fast.const_lt (q 11) 8 (by omega))
theorem slope7_monic (q : Keys R) : IsMonicOfDegree (slope7 q) 5 :=
  (rFactor_monic q).mul ((aFactor_monic q).add_right
    (Char2Degree15Fast.const_lt (q 4) 4 (by omega)))
theorem slope8_monic (q : Keys R) (delta : R) : IsMonicOfDegree (slope8 q delta) 4 :=
  (sFactor_monic q).mul (y_monic.add_right
    (Char2Degree15Fast.const_lt (q 9 + delta) 2 (by omega)))
theorem slope9_monic (q : Keys R) : IsMonicOfDegree (slope9 q) 3 :=
  (sFactor_monic q).mul (isMonicOfDegree_X_add_one (q 8))
theorem slope10_monic (q : Keys R) : IsMonicOfDegree (slope10 q) 1 :=
  isMonicOfDegree_X_add_one (q 0)
theorem slope11_monic (q : Keys R) : IsMonicOfDegree (slope11 q) 2 := sFactor_monic q

/-- q3 is read at row 7, despite its change also having degree 9. -/
theorem slope3_coeff7 (q : Keys R) : (slope3 q).coeff 7 = 1 := by
  have ha : IsMonicOfDegree (aFactor q + C (q 5)) 4 :=
    (aFactor_monic q).add_right (Char2Degree15Fast.const_lt (q 5) 4 (by omega))
  rw [slope3, product54_coeff7 _ _ (cFactor_monic q).natDegree_eq.le ha.natDegree_eq.le,
    coeff_add_C_pos _ _ 4 (by omega), coeff_add_C_pos _ _ 3 (by omega),
    coeff_add_C_pos _ _ 2 (by omega), cFactor_coeff3, cFactor_coeff4, cFactor_coeff5,
    aFactor_coeff4, aFactor_coeff3, aFactor_coeff2]
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem slope4_coeff7 (q : Keys R) : (slope4 q).coeff 7 = 0 := by
  rw [slope4, rFactor, add_mul, coeff_add, coeff_X_mul, coeff_C_mul,
    coeff_add_C_pos _ _ 6 (by omega), coeff_add_C_pos _ _ 7 (by omega),
    w_coeff6, w_coeff7, mul_zero, add_zero]

/-- q4 is read at row 6; the previously read row 7 is exactly unchanged. -/
theorem slope4_coeff6 (q : Keys R) : (slope4 q).coeff 6 = 1 := by
  rw [slope4, rFactor, add_mul, coeff_add, coeff_X_mul, coeff_C_mul,
    coeff_add_C_pos _ _ 5 (by omega), coeff_add_C_pos _ _ 6 (by omega),
    w_coeff5, w_coeff6, mul_zero, add_zero]

theorem slope5_coeff7 (q : Keys R) : (slope5 q).coeff 7 = 0 := by
  rw [slope5, product54_coeff7 _ _ (cFactor_monic q).natDegree_eq.le
    (bFactor_monic q).natDegree_eq.le, cFactor_coeff3, cFactor_coeff4, cFactor_coeff5,
    bFactor_coeff4, bFactor_coeff3, bFactor_coeff2]
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem slope5_coeff6 (q : Keys R) : (slope5 q).coeff 6 = 0 := by
  rw [slope5, product54_coeff6 _ _ (cFactor_monic q).natDegree_eq.le
    (bFactor_monic q).natDegree_eq.le, cFactor_coeff2, cFactor_coeff3,
    cFactor_coeff4, cFactor_coeff5, bFactor_coeff4, bFactor_coeff3,
    bFactor_coeff2, bFactor_coeff1]
  unfold c2
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem slope6_coeff7 (q : Keys R) : (slope6 q).coeff 7 = 0 := by
  have ht : (t q).coeff 7 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((t_monic q).natDegree_eq ▸ (by omega : 3 < 7))
  rw [slope6, coeff_add_C_pos _ _ 7 (by omega), coeff_add, w_coeff7, ht, add_zero]

theorem slope6_coeff6 (q : Keys R) : (slope6 q).coeff 6 = 0 := by
  have ht : (t q).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((t_monic q).natDegree_eq ▸ (by omega : 3 < 6))
  rw [slope6, coeff_add_C_pos _ _ 6 (by omega), coeff_add, w_coeff6, ht, add_zero]

theorem slope11_coeff1 (q : Keys R) : (slope11 q).coeff 1 = 0 := by
  norm_num only [slope11, sFactor, y, coeff_add, coeff_X_pow, coeff_C,
    ite_true, ite_false, add_zero, zero_add]

theorem coefficient_change_monic (p p' slope : R[X]) (delta : R) (n : ℕ)
    (he : p' = p + C delta * slope) (hs : IsMonicOfDegree slope n) :
    p'.coeff n = p.coeff n + delta := by
  have hr : slope.coeff n = 1 := by
    rw [← hs.natDegree_eq]
    exact hs.monic.coeff_natDegree
  exact coefficient_change_one p p' slope delta n he hr

theorem coefficient_change_above (p p' slope : R[X]) (delta : R) (n j : ℕ)
    (he : p' = p + C delta * slope) (hs : IsMonicOfDegree slope n) (hj : n < j) :
    p'.coeff j = p.coeff j := by
  have hd : slope.natDegree < j := hs.natDegree_eq ▸ hj
  have hz : slope.coeff j = 0 := coeff_eq_zero_of_natDegree_lt hd
  exact coefficient_change_zero p p' slope delta j he hz

theorem increment3_pivot (q : Keys R) (delta : R) :
    (output (increment q 3 delta)).coeff 7 = (output q).coeff 7 + delta :=
  coefficient_change_one (output q) (output (increment q 3 delta)) (slope3 q) delta 7
    (output_increment3 q delta) (slope3_coeff7 q)

theorem increment3_above (q : Keys R) (delta : R) (j : ℕ) (hj : 9 < j) :
    (output (increment q 3 delta)).coeff j = (output q).coeff j :=
  coefficient_change_above (output q) (output (increment q 3 delta)) (slope3 q) delta 9 j
    (output_increment3 q delta) (slope3_monic q) hj

theorem increment4_pivot (q : Keys R) (delta : R) :
    (output (increment q 4 delta)).coeff 6 = (output q).coeff 6 + delta :=
  coefficient_change_one (output q) (output (increment q 4 delta)) (slope4 q) delta 6
    (output_increment4 q delta) (slope4_coeff6 q)

theorem increment4_above (q : Keys R) (delta : R) (j : ℕ) (hj : 9 < j) :
    (output (increment q 4 delta)).coeff j = (output q).coeff j :=
  coefficient_change_above (output q) (output (increment q 4 delta)) (slope4 q) delta 9 j
    (output_increment4 q delta) (slope4_monic q) hj

theorem increment5_pivot (q : Keys R) (delta : R) :
    (output (increment q 5 delta)).coeff 9 = (output q).coeff 9 + delta :=
  coefficient_change_monic (output q) (output (increment q 5 delta)) (slope5 q) delta 9
    (output_increment5 q delta) (slope5_monic q)

theorem increment5_above (q : Keys R) (delta : R) (j : ℕ) (hj : 9 < j) :
    (output (increment q 5 delta)).coeff j = (output q).coeff j :=
  coefficient_change_above (output q) (output (increment q 5 delta)) (slope5 q) delta 9 j
    (output_increment5 q delta) (slope5_monic q) hj

theorem increment6_pivot (q : Keys R) (delta : R) :
    (output (increment q 6 delta)).coeff 8 = (output q).coeff 8 + delta :=
  coefficient_change_monic (output q) (output (increment q 6 delta)) (slope6 q) delta 8
    (output_increment6 q delta) (slope6_monic q)

theorem increment6_above (q : Keys R) (delta : R) (j : ℕ) (hj : 8 < j) :
    (output (increment q 6 delta)).coeff j = (output q).coeff j :=
  coefficient_change_above (output q) (output (increment q 6 delta)) (slope6 q) delta 8 j
    (output_increment6 q delta) (slope6_monic q) hj

theorem increment7_pivot (q : Keys R) (delta : R) :
    (output (increment q 7 delta)).coeff 5 = (output q).coeff 5 + delta :=
  coefficient_change_monic (output q) (output (increment q 7 delta)) (slope7 q) delta 5
    (output_increment7 q delta) (slope7_monic q)

theorem increment7_above (q : Keys R) (delta : R) (j : ℕ) (hj : 5 < j) :
    (output (increment q 7 delta)).coeff j = (output q).coeff j :=
  coefficient_change_above (output q) (output (increment q 7 delta)) (slope7 q) delta 5 j
    (output_increment7 q delta) (slope7_monic q) hj

theorem increment8_pivot (q : Keys R) (delta : R) :
    (output (increment q 8 delta)).coeff 4 = (output q).coeff 4 + delta :=
  coefficient_change_monic (output q) (output (increment q 8 delta)) (slope8 q delta) delta 4
    (output_increment8 q delta) (slope8_monic q delta)

theorem increment8_above (q : Keys R) (delta : R) (j : ℕ) (hj : 4 < j) :
    (output (increment q 8 delta)).coeff j = (output q).coeff j :=
  coefficient_change_above (output q) (output (increment q 8 delta)) (slope8 q delta) delta 4 j
    (output_increment8 q delta) (slope8_monic q delta) hj

theorem increment9_pivot (q : Keys R) (delta : R) :
    (output (increment q 9 delta)).coeff 3 = (output q).coeff 3 + delta :=
  coefficient_change_monic (output q) (output (increment q 9 delta)) (slope9 q) delta 3
    (output_increment9 q delta) (slope9_monic q)

theorem increment9_above (q : Keys R) (delta : R) (j : ℕ) (hj : 3 < j) :
    (output (increment q 9 delta)).coeff j = (output q).coeff j :=
  coefficient_change_above (output q) (output (increment q 9 delta)) (slope9 q) delta 3 j
    (output_increment9 q delta) (slope9_monic q) hj

theorem increment10_pivot (q : Keys R) (delta : R) :
    (output (increment q 10 delta)).coeff 1 = (output q).coeff 1 + delta :=
  coefficient_change_monic (output q) (output (increment q 10 delta)) (slope10 q) delta 1
    (output_increment10 q delta) (slope10_monic q)

theorem increment10_above (q : Keys R) (delta : R) (j : ℕ) (hj : 1 < j) :
    (output (increment q 10 delta)).coeff j = (output q).coeff j :=
  coefficient_change_above (output q) (output (increment q 10 delta)) (slope10 q) delta 1 j
    (output_increment10 q delta) (slope10_monic q) hj

theorem increment11_pivot (q : Keys R) (delta : R) :
    (output (increment q 11 delta)).coeff 2 = (output q).coeff 2 + delta :=
  coefficient_change_monic (output q) (output (increment q 11 delta)) (slope11 q) delta 2
    (output_increment11 q delta) (slope11_monic q)

theorem increment11_above (q : Keys R) (delta : R) (j : ℕ) (hj : 2 < j) :
    (output (increment q 11 delta)).coeff j = (output q).coeff j :=
  coefficient_change_above (output q) (output (increment q 11 delta)) (slope11 q) delta 2 j
    (output_increment11 q delta) (slope11_monic q) hj

theorem increment4_preserves7 (q : Keys R) (delta : R) :
    (output (increment q 4 delta)).coeff 7 = (output q).coeff 7 :=
  coefficient_change_zero (output q) (output (increment q 4 delta)) (slope4 q) delta 7
    (output_increment4 q delta) (slope4_coeff7 q)

theorem increment5_preserves7 (q : Keys R) (delta : R) :
    (output (increment q 5 delta)).coeff 7 = (output q).coeff 7 :=
  coefficient_change_zero (output q) (output (increment q 5 delta)) (slope5 q) delta 7
    (output_increment5 q delta) (slope5_coeff7 q)

theorem increment5_preserves6 (q : Keys R) (delta : R) :
    (output (increment q 5 delta)).coeff 6 = (output q).coeff 6 :=
  coefficient_change_zero (output q) (output (increment q 5 delta)) (slope5 q) delta 6
    (output_increment5 q delta) (slope5_coeff6 q)

theorem increment6_preserves7 (q : Keys R) (delta : R) :
    (output (increment q 6 delta)).coeff 7 = (output q).coeff 7 :=
  coefficient_change_zero (output q) (output (increment q 6 delta)) (slope6 q) delta 7
    (output_increment6 q delta) (slope6_coeff7 q)

theorem increment6_preserves6 (q : Keys R) (delta : R) :
    (output (increment q 6 delta)).coeff 6 = (output q).coeff 6 :=
  coefficient_change_zero (output q) (output (increment q 6 delta)) (slope6 q) delta 6
    (output_increment6 q delta) (slope6_coeff6 q)

theorem increment11_preserves1 (q : Keys R) (delta : R) :
    (output (increment q 11 delta)).coeff 1 = (output q).coeff 1 :=
  coefficient_change_zero (output q) (output (increment q 11 delta)) (slope11 q) delta 1
    (output_increment11 q delta) (slope11_coeff1 q)

theorem increment12_pivot (q : Keys R) (delta : R) :
    (output (increment q 12 delta)).coeff 0 = (output q).coeff 0 + delta := by
  rw [output_increment12, coeff_add, coeff_C_zero]

theorem increment12_above (q : Keys R) (delta : R) (j : ℕ) (hj : 0 < j) :
    (output (increment q 12 delta)).coeff j = (output q).coeff j := by
  rw [output_increment12]
  exact coeff_add_C_pos (output q) delta j hj

end FastPoly.Char2Degree13Fast

