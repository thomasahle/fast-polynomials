import FastPoly.Examples.Char2Degree21Pivots

/-!
# The four leading degree-21 pivots

Only the change in the quintic outer factor reaches rows 20,19,18,17.
The already checked degree-19 crown differences bound all other changes,
and the whole remaining frame has degree at most nine. Thus no baseline
coefficient, or even the lower frame's exact change, needs expansion.
-/

namespace FastPoly.Char2Degree21Pivots

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Crown Char2Degree19InnerTail
  Char2Degree19InnerChanges Char2Degree21Frame

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

private theorem moving_degree {a b : ℕ → R} {j : ℕ}
    (hc : (crown b + crown a).natDegree ≤ j) (k : ℕ)
    (hj : 5 + j < k + 16) (hk : 9 < k + 16) :
    (A b * (crown b + crown a) + (tail b + tail a)).natDegree < k + 16 := by
  have hl : (A b * (crown b + crown a)).natDegree < k + 16 :=
    (natDegree_mul_le.trans (Nat.add_le_add (A_monic b).natDegree_eq.le hc)).trans_lt hj
  have ht : (tail b + tail a).natDegree < k + 16 :=
    (natDegree_add_le_of_degree_le (tail_degree b) (tail_degree a)).trans_lt hk
  exact (natDegree_add_le _ _).trans_lt (max_lt hl ht)

/-- The leading change comes only from the outer quintic factor. -/
theorem output_difference_moving (a b : ℕ → R) (slope : R[X]) (k j : ℕ)
    (delta : R) (hs : IsMonicOfDegree slope k)
    (ha : A b = A a + C delta * slope)
    (hc : (crown b + crown a).natDegree ≤ j)
    (hj : 5 + j < k + 16) (hk : 9 < k + 16) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output b) (k + 16) delta := by
  have heq : Char2Degree21Frame.output b + Char2Degree21Frame.output a =
      C delta * (slope * crown a) +
        (A b * (crown b + crown a) + (tail b + tail a)) := by
    rw [output_eq b, output_eq a, moving_frame, ha, cancel_tail, mul_assoc]
  apply unit_difference_of_lower _ _ _ _ (k + 16) delta (hs.mul (crown_monic a))
    (moving_degree hc k hj hk)
  calc
    Char2Degree21Frame.output b = Char2Degree21Frame.output a +
        (Char2Degree21Frame.output b + Char2Degree21Frame.output a) := by
      rw [← add_assoc, cancel_tail]
    _ = _ := by rw [heq]

private theorem degree_trans {p p' p'' : R[X]} {n : ℕ}
    (h : (p' + p).natDegree ≤ n) (h' : (p'' + p').natDegree ≤ n) :
    (p'' + p).natDegree ≤ n := by
  have heq : p'' + p = (p'' + p') + (p' + p) := by
    rw [add_assoc, CharTwo.add_cancel_left]
  rw [heq]
  exact natDegree_add_le_of_degree_le h' h

private theorem leading_increment (t c e d : R[X]) :
    (t + d) + c + e = (t + c + e) + d := by ac_rfl

theorem A_shift0 (a : ℕ → R) (delta : R) :
    A (shift0 a delta) = A a + C delta * (z a + C (a 3)) := by
  have ht : t (shift0 a delta) = t a + C delta * (z a + C (a 3)) :=
    Char2Degree19InnerDirect.t_shift3 a delta
  change t (shift0 a delta) + C (a 16) + C (a 18) = _
  rw [ht]
  exact leading_increment ..

theorem shift0_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift0 a delta)) 20 delta := by
  have hs : IsMonicOfDegree (z a + C (a 3)) 4 :=
    (z_monic a).add_right (C_lt _ 4 (by omega))
  have hc : (crown (shift0 a delta) + crown a).natDegree ≤ 12 := by
    apply degree_trans (Char2Degree19InnerDirect.shift3_unit a delta).difference_degree
    exact (Char2Degree19InnerSimple.shift7_unit
      (Char2Degree19InnerDirect.shift3 a delta) (delta * a 11)).difference_degree.trans (by omega)
  exact output_difference_moving a _ _ 4 12 delta hs (A_shift0 a delta) hc
    (by omega) (by omega)

theorem z_shift1 (a : ℕ → R) (delta : R) :
    z (shift1 a delta) = z a + C delta * (y + C (a 0)) := by
  change (y + C (a 0)) * (X + y + C (a 1 + delta)) =
    (y + C (a 0)) * (X + y + C (a 1)) + C delta * (y + C (a 0))
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]

private theorem product_right_increment (l z c d : R[X]) :
    l * ((z + d) + c) = l * (z + c) + l * d := by
  rw [add_right_comm z d c, mul_add]

/-- Only `z` changes among the inputs of `t`; the other frame offsets are fixed. -/
theorem A_change_z (a b : ℕ → R) (slope : R[X]) (delta : R)
    (hz : z b = z a + C delta * slope)
    (h2 : b 2 = a 2) (h3 : b 3 = a 3) (h16 : b 16 = a 16) (h18 : b 18 = a 18) :
    A b = A a + C delta * ((X + C (a 2)) * slope) := by
  change (X + C (b 2)) * (z b + C (b 3)) + C (b 16) + C (b 18) = _
  rw [h2, h3, h16, h18, hz, product_right_increment, leading_increment,
    mul_left_comm _ (C delta)]
  rfl

theorem shift1_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift1 a delta)) 19 delta := by
  have hs : IsMonicOfDegree ((X + C (a 2)) * (y + C (a 0))) 3 :=
    (isMonicOfDegree_X_add_one (a 2)).mul (y_monic.add_right (C_lt _ 2 (by omega)))
  exact output_difference_moving a _ _ 3 11 delta hs
    (A_change_z a _ _ delta (z_shift1 a delta) rfl rfl rfl rfl)
    (Char2Degree19InnerZChanges.shift4_unit a delta).difference_degree (by omega) (by omega)

private theorem low_sum_cancel (y x a b : R[X]) :
    (y + a) + (x + y + b) = x + a + b := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem z_shift2 (a : ℕ → R) (delta : R) :
    z (shift2 a delta) = z a + C delta * (X + C (a 0) + C (a 1) + C delta) := by
  change (y + C (a 0 + delta)) * (X + y + C (a 1 + delta)) = _
  rw [map_add, map_add, ← add_assoc, ← add_assoc, both_factors, low_sum_cancel,
    pow_two, add_assoc, ← mul_add]
  rfl

theorem shift2_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift2 a delta)) 18 delta := by
  have hl : IsMonicOfDegree ((X : R[X]) + C (a 0) + C (a 1) + C delta) 1 :=
    ((isMonicOfDegree_X_add_one (a 0)).add_right (C_lt _ 1 (by omega))).add_right
      (C_lt _ 1 (by omega))
  have hs : IsMonicOfDegree
      ((X + C (a 2)) * (X + C (a 0) + C (a 1) + C delta)) 2 :=
    (isMonicOfDegree_X_add_one (a 2)).mul hl
  exact output_difference_moving a _ _ 2 10 delta hs
    (A_change_z a _ _ delta (z_shift2 a delta) rfl rfl rfl rfl)
    (Char2Degree19InnerZChanges.shift5_unit a delta).difference_degree (by omega) (by omega)

theorem A_shift3 (a : ℕ → R) (delta : R) :
    A (shift3 a delta) = A a + C delta * (X + C (a 2)) := by
  have ht : t (shift3 a delta) = t a + C delta * (X + C (a 2)) :=
    Char2Degree19InnerSeam.t_shift8 a delta
  change t (shift3 a delta) + C (a 16) + C (a 18) = _
  rw [ht]
  exact leading_increment ..

theorem shift3_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift3 a delta)) 17 delta :=
  output_difference_moving a _ _ 1 7 delta (isMonicOfDegree_X_add_one (a 2))
    (A_shift3 a delta) (Char2Degree19InnerSeam.shift8_unit a delta).difference_degree
    (by omega) (by omega)

end FastPoly.Char2Degree21Pivots
