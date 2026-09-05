import FastPoly.Examples.Char2Degree11FastChanges
import FastPoly.Examples.Char2Degree19InnerChanges

/-! All eleven supplied degree-eleven unit pivots from named wire changes.
The leading two pivots use a monic slope times J and a separately bounded
lower tail. The remaining nine pivots are direct products with named slopes.
No coefficient of B*J is expanded. -/

namespace FastPoly.Char2Degree11Fast

set_option maxHeartbeats 20000

open Polynomial Char2Degree19InnerTail Char2Degree19InnerChanges

variable {R : Type*} [CommRing R] [CharP R 2]

private theorem translated_left (x a b c d : R[X]) :
    (x + (a + d)) * b + c = ((x + a) * b + c) + d * b := by ring

private theorem translated_right (a y b c d : R[X]) :
    a * (y + (b + d)) + c = (a * (y + b) + c) + d * a := by ring

theorem B_increment0 (q : Keys R) (delta : R) :
    B (increment q 0 delta) = B q + C delta * (y + C (q 1)) := by
  change (X + C (q 0 + delta)) * (y + C (q 1)) + C (q 2) = _
  rw [map_add]
  exact translated_left X (C (q 0)) (y + C (q 1)) (C (q 2)) (C delta)

theorem B_increment1 (q : Keys R) (delta : R) :
    B (increment q 1 delta) = B q + C delta * (X + C (q 0)) := by
  change (X + C (q 0)) * (y + C (q 1 + delta)) + C (q 2) = _
  rw [map_add]
  exact translated_right (X + C (q 0)) y (C (q 1)) (C (q 2)) (C delta)

theorem B_increment2 (q : Keys R) (delta : R) :
    B (increment q 2 delta) = B q + C delta := by
  change u q + C (q 2 + delta) = _
  rw [map_add, ← add_assoc]
  rfl

private theorem paired_z_change (x y a b d : R[X]) :
    (y + (b + d)) * (x + y + (a + (b + d))) =
      (y + b) * (x + y + (a + b)) + d * (x + (a + d)) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem right_z_change (x y a b d : R[X]) :
    (y + b) * (x + y + ((a + d) + b)) =
      (y + b) * (x + y + (a + b)) + d * (y + b) := by ring

theorem z_increment8 (q : Keys R) (delta : R) :
    z (increment q 8 delta) = z q + C delta * (y + C (q 9)) := by
  change (y + C (q 9)) * (X + y + C ((q 8 + delta) + q 9)) = _
  unfold z
  simp only [map_add]
  exact right_z_change X y (C (q 8)) (C (q 9)) (C delta)

theorem z_increment9 (q : Keys R) (delta : R) :
    z (increment q 9 delta) = z q + C delta * (X + C (q 8 + delta)) := by
  change (y + C (q 9 + delta)) * (X + y + C (q 8 + (q 9 + delta))) = _
  unfold z
  simp only [map_add]
  exact paired_z_change X y (C (q 8)) (C (q 9)) (C delta)

private theorem assemble_J (z b j c d s : R[X]) :
    z + b * (j + d * s) + c = (z + b * j + c) + d * (b * s) := by ring

theorem output_from_J_change (q q' : Keys R) (delta : R) (slope : R[X])
    (hz : z q' = z q) (hb : B q' = B q)
    (hj : J q' = J q + C delta * slope) (hc : q' 10 = q 10) :
    output q' = output q + C delta * (B q * slope) := by
  rw [output_split q', hz, hb, hj, hc, output_split q]
  exact assemble_J ..

private theorem assemble_z (z b j c d s : R[X]) :
    (z + d * s) + b * j + c = (z + b * j + c) + d * s := by ac_rfl

theorem output_from_z_change (q q' : Keys R) (delta : R) (slope : R[X])
    (hz : z q' = z q + C delta * slope) (hb : B q' = B q)
    (hj : J q' = J q) (hc : q' 10 = q 10) :
    output q' = output q + C delta * slope := by
  rw [output_split q', hz, hb, hj, hc, output_split q]
  exact assemble_z ..

/-- Product difference with independent opaque wires, in characteristic two. -/
private theorem assemble_B (z b j j' c d s : R[X]) :
    z + (b + d * s) * j' + c =
      (z + b * j + c) + (d * (s * j) + (b + d * s) * (j' + j)) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem output_from_B_change (q q' : Keys R) (delta : R) (slope : R[X])
    (hz : z q' = z q) (hb : B q' = B q + C delta * slope)
    (hc : q' 10 = q 10) :
    output q' = output q +
      (C delta * (slope * J q) + B q' * (J q' + J q)) := by
  rw [output_split q', hz, hb, hc, output_split q]
  exact assemble_B ..

private theorem assemble_constant_B (z b j c d : R[X]) :
    z + (b + d) * j + c = (z + b * j + c) + d * j := by ring

theorem output_increment2 (q : Keys R) (delta : R) :
    output (increment q 2 delta) = output q + C delta * J q := by
  rw [output_split, B_increment2, J_increment2]
  change z q + (B q + C delta) * J q + C (q 10) = _
  rw [output_split]
  exact assemble_constant_B ..

theorem output_increment3 (q : Keys R) (delta : R) :
    output (increment q 3 delta) = output q + C delta * (B q * (slope3 q)) :=
  output_from_J_change q (increment q 3 delta) delta (slope3 q)
    rfl rfl (J_increment3 q delta) rfl

theorem output_increment4 (q : Keys R) (delta : R) :
    output (increment q 4 delta) = output q + C delta * (B q * (slope4 q)) :=
  output_from_J_change q (increment q 4 delta) delta (slope4 q)
    rfl rfl (J_increment4 q delta) rfl

theorem output_increment5 (q : Keys R) (delta : R) :
    output (increment q 5 delta) = output q + C delta * (B q * (slope5 q delta)) :=
  output_from_J_change q (increment q 5 delta) delta (slope5 q delta)
    rfl rfl (J_increment5 q delta) rfl

theorem output_increment6 (q : Keys R) (delta : R) :
    output (increment q 6 delta) = output q + C delta * (B q * (slope6 q)) :=
  output_from_J_change q (increment q 6 delta) delta (slope6 q)
    rfl rfl (J_increment6 q delta) rfl

theorem output_increment7 (q : Keys R) (delta : R) :
    output (increment q 7 delta) = output q + C delta * B q := by
  have h := output_from_J_change q (increment q 7 delta) delta 1
    rfl rfl (J_increment7 q delta) rfl
  simpa only [mul_one] using h

theorem output_increment8 (q : Keys R) (delta : R) :
    output (increment q 8 delta) = output q + C delta * (y + C (q 9)) :=
  output_from_z_change q (increment q 8 delta) delta (y + C (q 9))
    (z_increment8 q delta) rfl (J_increment8 q delta) rfl

theorem output_increment9 (q : Keys R) (delta : R) :
    output (increment q 9 delta) = output q + C delta * (X + C (q 8 + delta)) :=
  output_from_z_change q (increment q 9 delta) delta (X + C (q 8 + delta))
    (z_increment9 q delta) rfl (J_increment9 q delta) rfl

theorem output_increment10 (q : Keys R) (delta : R) :
    output (increment q 10 delta) = output q + C delta := by
  rw [output_split, J_increment10]
  change z q + B q * J q + C (q 10 + delta) = _
  rw [map_add, ← add_assoc]
  rfl

variable [Nontrivial R]

theorem slope3_monic (q : Keys R) : IsMonicOfDegree (slope3 q) 4 := by
  have h2 : (C (1 + q 0) * X ^ 2 : R[X]).natDegree < 4 :=
    (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  have h1 : (C (q 1) * X : R[X]).natDegree < 4 :=
    (Char2Degree15Fast.mul_bound (natDegree_C (q 1)).le natDegree_X_le).trans_lt (by omega)
  exact (((isMonicOfDegree_X_pow R 4).add_right h2).add_right h1).add_right
    (Char2Degree15Fast.const_lt (q 5 + q 0 * q 1) 4 (by omega))

theorem slope4_monic (q : Keys R) : IsMonicOfDegree (slope4 q) 3 := by
  have h2 : (C (1 + q 0) * X ^ 2 : R[X]).natDegree < 3 :=
    (natDegree_C_mul_X_pow_le _ _).trans_lt (by omega)
  have h1 : (C (q 1) * X : R[X]).natDegree < 3 :=
    (Char2Degree15Fast.mul_bound (natDegree_C (q 1)).le natDegree_X_le).trans_lt (by omega)
  exact (((isMonicOfDegree_X_pow R 3).add_right h2).add_right h1).add_right
    (Char2Degree15Fast.const_lt (q 5 + q 6 + q 0 * q 1) 3 (by omega))

theorem slope5_monic (q : Keys R) (delta : R) :
    IsMonicOfDegree (slope5 q delta) 2 :=
  (isMonicOfDegree_X_pow R 2).add_right
    (Char2Degree15Fast.const_lt (q 3 + q 4 + delta) 2 (by omega))

theorem slope6_monic (q : Keys R) : IsMonicOfDegree (slope6 q) 1 :=
  isMonicOfDegree_X_add_one (q 4)

/-- The lower product has degree at most 3+4=7, below both leading pivots. -/
theorem unit_from_B_change (q q' : Keys R) (delta : R) (slope : R[X]) (k : ℕ)
    (hs : IsMonicOfDegree slope k) (hz : z q' = z q)
    (hb : B q' = B q + C delta * slope) (hc : q' 10 = q 10) :
    UnitDifference (output q) (output q') (k + 8) delta := by
  have ht : (B q' * (J q' + J q)).natDegree ≤ 7 :=
    Char2Degree15Fast.mul_bound (B_monic q').natDegree_eq.le (J_difference_degree q q')
  exact unit_difference_of_lower (output q) (output q') (slope * J q)
    (B q' * (J q' + J q)) (k + 8) delta (hs.mul (J_monic q))
    (ht.trans_lt (by omega)) (output_from_B_change q q' delta slope hz hb hc)

theorem increment0_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 0 delta)) 10 delta :=
  unit_from_B_change q (increment q 0 delta) delta (y + C (q 1)) 2
    (y_monic.add_right (Char2Degree15Fast.const_lt (q 1) 2 (by omega)))
    rfl (B_increment0 q delta) rfl

theorem increment1_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 1 delta)) 9 delta :=
  unit_from_B_change q (increment q 1 delta) delta (X + C (q 0)) 1
    (isMonicOfDegree_X_add_one (q 0)) rfl (B_increment1 q delta) rfl

theorem increment2_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 2 delta)) 8 delta := by
  apply unit_difference_of_split (output q) (output (increment q 2 delta))
    (J q) 8 delta 0 (by omega) (J_monic q)
  rw [map_zero, add_zero, output_increment2]

theorem increment3_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 3 delta)) 7 delta := by
  apply unit_difference_of_split (output q) (output (increment q 3 delta))
    (B q * slope3 q) 7 delta 0 (by omega) ((B_monic q).mul (slope3_monic q))
  rw [map_zero, add_zero, output_increment3]

theorem increment4_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 4 delta)) 6 delta := by
  apply unit_difference_of_split (output q) (output (increment q 4 delta))
    (B q * slope4 q) 6 delta 0 (by omega) ((B_monic q).mul (slope4_monic q))
  rw [map_zero, add_zero, output_increment4]

theorem increment5_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 5 delta)) 5 delta := by
  apply unit_difference_of_split (output q) (output (increment q 5 delta))
    (B q * slope5 q delta) 5 delta 0 (by omega) ((B_monic q).mul (slope5_monic q delta))
  rw [map_zero, add_zero, output_increment5]

theorem increment6_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 6 delta)) 4 delta := by
  apply unit_difference_of_split (output q) (output (increment q 6 delta))
    (B q * slope6 q) 4 delta 0 (by omega) ((B_monic q).mul (slope6_monic q))
  rw [map_zero, add_zero, output_increment6]

theorem increment7_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 7 delta)) 3 delta := by
  apply unit_difference_of_split (output q) (output (increment q 7 delta))
    (B q) 3 delta 0 (by omega) (B_monic q)
  rw [map_zero, add_zero, output_increment7]

theorem increment8_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 8 delta)) 2 delta := by
  apply unit_difference_of_split (output q) (output (increment q 8 delta))
    (y + C (q 9)) 2 delta 0 (by omega) (y_monic.add_right (Char2Degree15Fast.const_lt (q 9) 2 (by omega)))
  rw [map_zero, add_zero, output_increment8]

theorem increment9_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 9 delta)) 1 delta := by
  apply unit_difference_of_split (output q) (output (increment q 9 delta))
    (X + C (q 8 + delta)) 1 delta 0 (by omega) (isMonicOfDegree_X_add_one (q 8 + delta))
  rw [map_zero, add_zero, output_increment9]

theorem increment10_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 10 delta)) 0 delta := by
  have he : output (increment q 10 delta) + output q = C delta := by
    rw [output_increment10, Char2Decoder.cancel_tail]
  constructor
  · rw [he, natDegree_C]
  · rw [he, coeff_C_zero]

end FastPoly.Char2Degree11Fast

