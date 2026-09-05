import FastPoly.Examples.Char2Degree21Frame
import FastPoly.Examples.Char2Degree19InnerSimple
import FastPoly.Examples.Char2Degree19InnerZChanges
import FastPoly.Examples.Char2Degree19InnerSeam

/-!
# Local unit differences for the existing degree-21 coordinates

The degree-19 crown is reused unchanged. Most rows are its checked unit
differences multiplied by the quintic outer factor; the six last rows are
single-product changes in the frame. No coefficient baseline is expanded.
-/

namespace FastPoly.Char2Degree21Pivots

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Crown Char2Degree19InnerTail
  Char2Degree21Frame

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

-- These names use the degree-21 normalized coordinate numbering.
def shift0 (a : ℕ → R) (delta : R) : ℕ → R :=
  Char2Degree19InnerSimple.shift7 (Char2Degree19InnerDirect.shift3 a delta) (delta * a 11)
abbrev shift1 := @Char2Degree19InnerZChanges.shift4
abbrev shift2 := @Char2Degree19InnerZChanges.shift5
abbrev shift3 := @Char2Degree19InnerSeam.shift8
def shift4 (a : ℕ → R) (delta : R) : ℕ → R
  | 16 => a 16 + delta
  | j => a j
def shift5 (a : ℕ → R) (delta : R) : ℕ → R
  | 10 => a 10 + delta
  | 15 => a 15 + delta * a 11
  | j => a j
abbrev shift6 := @Char2Degree19InnerChanges.shift6
abbrev shift7 := @Char2Degree19InnerSimple.shift7
def shift8 (a : ℕ → R) (delta : R) : ℕ → R
  | 7 => a 7 + delta
  | 11 => a 11 + delta
  | 15 => a 15 + (delta ^ 2 + delta * (1 + a 2 + a 10))
  | j => a j
abbrev shift9 := @Char2Degree19InnerChanges.shift9
abbrev shift10 := @Char2Degree19InnerSimple.shift10
abbrev shift11 := @Char2Degree19InnerSimple.shift11
abbrev shift12 := @Char2Degree19InnerTail.shift12
abbrev shift13 := @Char2Degree19InnerTail.shift13
abbrev shift14 := @Char2Degree19InnerTail.shift14
def shift15 (a : ℕ → R) (delta : R) : ℕ → R
  | 19 => a 19 + delta
  | j => a j
def shift16 (a : ℕ → R) (delta : R) : ℕ → R
  | 16 => a 16 + delta
  | 18 => a 18 + delta
  | j => a j
def shift17 (a : ℕ → R) (delta : R) : ℕ → R
  | 17 => a 17 + delta
  | j => a j
def shift18 (a : ℕ → R) (delta : R) : ℕ → R
  | 12 => a 12 + delta
  | j => a j
def shift19 (a : ℕ → R) (delta : R) : ℕ → R
  | 13 => a 13 + delta
  | j => a j
def shift20 (a : ℕ → R) (delta : R) : ℕ → R
  | 20 => a 20 + delta
  | j => a j

theorem shift6_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift6 a delta)) 14 delta :=
  output_difference_fixed (Char2Degree19InnerChanges.shift6_unit a delta) rfl rfl

theorem shift7_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift7 a delta)) 13 delta :=
  output_difference_fixed (Char2Degree19InnerSimple.shift7_unit a delta) rfl rfl

theorem shift9_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift9 a delta)) 11 delta :=
  output_difference_fixed (Char2Degree19InnerChanges.shift9_unit a delta) rfl rfl

theorem shift10_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift10 a delta)) 10 delta :=
  output_difference_fixed (Char2Degree19InnerSimple.shift10_unit a delta) rfl rfl

theorem shift11_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift11 a delta)) 9 delta :=
  output_difference_fixed (Char2Degree19InnerSimple.shift11_unit a delta) rfl rfl

theorem shift12_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift12 a delta)) 8 delta :=
  output_difference_fixed (Char2Degree19InnerTail.shift12_unit a delta) rfl rfl

theorem shift13_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift13 a delta)) 7 delta :=
  output_difference_fixed (Char2Degree19InnerTail.shift13_unit a delta) rfl rfl

theorem shift14_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift14 a delta)) 6 delta :=
  output_difference_fixed (Char2Degree19InnerTail.shift14_unit a delta) rfl rfl

private theorem add_wire_change (a b c d : R[X]) :
    a + (b + d) + c = (a + b + c) + d := by ac_rfl

private theorem compensate_constant (s y c a d : R[X]) :
    (s + d * (y + c)) + (a + d * c) = (s + a) + d * y := by
  rw [mul_add]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero]

theorem s_shift5 (a : ℕ → R) (delta : R) :
    s (shift5 a delta) = s a + C delta * (y + C (a 11)) := by
  change (X + C (a 10 + delta)) * (y + C (a 11)) = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

theorem compensated_shift5 (a : ℕ → R) (delta : R) :
    s (shift5 a delta) + C (shift5 a delta 15) =
      (s a + C (a 15)) + C delta * y := by
  change s (shift5 a delta) + C (a 15 + delta * a 11) = _
  rw [s_shift5, map_add, map_mul, compensate_constant]

private theorem last_factor_change (a t s c d : R[X]) :
    a * (t + ((s + c) + d)) = a * (t + s + c) + d * a := by
  rw [← add_assoc, mul_add, mul_comm a d, ← add_assoc t s c]

theorem crown_shift5 (a : ℕ → R) (delta : R) :
    crown (shift5 a delta) = crown a + C delta * (y * (v a + C (a 14))) := by
  have hq : q (shift5 a delta) = q a + C delta * (y * (v a + C (a 14))) := by
    change (v a + C (a 14)) *
      (t a + v a + s (shift5 a delta) + C (shift5 a delta 15)) = _
    rw [add_assoc (t a + v a), compensated_shift5, last_factor_change, mul_assoc]
    rfl
  have hu : u (shift5 a delta) = u a := rfl
  have hw : w (shift5 a delta) = w a := rfl
  have hc : shift5 a delta 17 = a 17 := rfl
  rw [crown, hu, hw, hq, hc]
  change u a + w a + (q a + C delta * (y * (v a + C (a 14)))) + C (a 17) = _
  exact add_wire_change ..

theorem tail_shift5 (a : ℕ → R) (delta : R) :
    tail (shift5 a delta) = tail a + (C delta * (y + C (a 11))) * D a := by
  have ht : T (shift5 a delta) = T a + C delta * (y + C (a 11)) := by
    change t a + s (shift5 a delta) + C (a 18) = _
    rw [s_shift5]
    exact add_wire_change ..
  change T (shift5 a delta) * D a + z a + r a + C (a 20) = _
  rw [ht, add_mul]
  change _ = (T a * D a + z a + r a + C (a 20)) + _
  ac_rfl

theorem shift5_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift5 a delta)) 15 delta := by
  have hs : IsMonicOfDegree (y * (v a + C (a 14))) 10 :=
    y_monic.mul ((v_monic a).add_right (C_lt _ 8 (by omega)))
  have hc : UnitDifference (crown a) (crown (shift5 a delta)) 10 delta := by
    rw [crown_shift5]
    exact difference_scaled delta hs
  have hdy : (C delta * (y + C (a 11))).natDegree ≤ 2 := by
    exact natDegree_mul_le.trans (by
      rw [natDegree_C, (y_monic.add_right (C_lt (a 11) 2 (by omega))).natDegree_eq])
  have hl : (tail (shift5 a delta) + tail a).natDegree < 15 := by
    rw [tail_shift5, cancel_tail]
    exact (natDegree_mul_le.trans
      (Nat.add_le_add hdy (D_monic a).natDegree_eq.le)).trans_lt (by omega)
  exact output_difference hc rfl hl

theorem s_shift8 (a : ℕ → R) (delta : R) :
    s (shift8 a delta) = s a + C delta * (X + C (a 10)) := by
  change (X + C (a 10)) * (y + C (a 11 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]
  rfl

private theorem seam_balance (t s a x b c d : R[X]) :
    t + (s + d * (x + c)) + (a + (d ^ 2 + d * (1 + b + c))) =
      (t + d * (x + b)) + s + (a + (d ^ 2 + d)) := by
  simp only [mul_add, mul_one]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem seam_second_factor (a : ℕ → R) (delta : R) :
    t (shift8 a delta) + s (shift8 a delta) + C (shift8 a delta 15) =
      t (Char2Degree19InnerSeam.shift8 a delta) +
        s (Char2Degree19InnerSeam.shift8 a delta) +
        C (Char2Degree19InnerSeam.shift8 a delta 15) := by
  change t a + s (shift8 a delta) + C (a 15 + (delta ^ 2 + delta * (1 + a 2 + a 10))) =
    t (Char2Degree19InnerSeam.shift8 a delta) + s a + C (a 15 + (delta ^ 2 + delta))
  rw [s_shift8, Char2Degree19InnerSeam.t_shift8]
  simp only [map_add, map_mul, map_pow, map_one]
  exact seam_balance (t a) (s a) (C (a 15)) X (C (a 2)) (C (a 10)) (C delta)

private theorem q_regroup (t v s c : R[X]) : t + v + s + c = v + (t + s + c) := by
  ac_rfl

theorem q_shift8_compare (a : ℕ → R) (delta : R) :
    q (shift8 a delta) = q (Char2Degree19InnerSeam.shift8 a delta) := by
  have hv : v (shift8 a delta) = v (Char2Degree19InnerSeam.shift8 a delta) := rfl
  change (v (shift8 a delta) + C (a 14)) *
      (t (shift8 a delta) + v (shift8 a delta) + s (shift8 a delta) + C (shift8 a delta 15)) =
    (v (Char2Degree19InnerSeam.shift8 a delta) + C (a 14)) *
      (t (Char2Degree19InnerSeam.shift8 a delta) + v (Char2Degree19InnerSeam.shift8 a delta) +
        s (Char2Degree19InnerSeam.shift8 a delta) + C (Char2Degree19InnerSeam.shift8 a delta 15))
  rw [q_regroup, q_regroup, seam_second_factor, hv]

private theorem one_wire_compare (u w q c d : R[X]) :
    (u + w + q + c) + ((u + d) + w + q + c) = d := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

/-- The old checked seam differs only by the small change to `u`. -/
theorem crown_shift8_compare (a : ℕ → R) (delta : R) :
    crown (shift8 a delta) + crown (Char2Degree19InnerSeam.shift8 a delta) =
      Char2Degree19InnerDirect.uCorrection a (C delta * Char2Degree19InnerSeam.linear a) := by
  have hu : u (Char2Degree19InnerSeam.shift8 a delta) = u a +
      Char2Degree19InnerDirect.uCorrection a (C delta * Char2Degree19InnerSeam.linear a) :=
    Char2Degree19InnerDirect.u_change_t a _ _ rfl
      (Char2Degree19InnerSeam.t_shift8 a delta) rfl rfl
  have hw : w (shift8 a delta) = w (Char2Degree19InnerSeam.shift8 a delta) := rfl
  change (u a + w (shift8 a delta) + q (shift8 a delta) + C (a 17)) +
    (u (Char2Degree19InnerSeam.shift8 a delta) + w (Char2Degree19InnerSeam.shift8 a delta) +
      q (Char2Degree19InnerSeam.shift8 a delta) + C (a 17)) = _
  rw [hw, q_shift8_compare, hu, one_wire_compare]

theorem tail_shift8 (a : ℕ → R) (delta : R) :
    tail (shift8 a delta) = tail a + (C delta * (X + C (a 10))) * D a := by
  have ht : T (shift8 a delta) = T a + C delta * (X + C (a 10)) := by
    change t a + s (shift8 a delta) + C (a 18) = _
    rw [s_shift8]
    exact add_wire_change ..
  change T (shift8 a delta) * D a + z a + r a + C (a 20) = _
  rw [ht, add_mul]
  change _ = (T a * D a + z a + r a + C (a 20)) + _
  ac_rfl

theorem shift8_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift8 a delta)) 12 delta := by
  have hl : (C delta * Char2Degree19InnerSeam.linear a).natDegree ≤ 1 := by
    exact natDegree_mul_le.trans (by
      rw [natDegree_C, Char2Degree19InnerSeam.linear,
        (isMonicOfDegree_X_add_one (a 2)).natDegree_eq])
  have hc : UnitDifference (crown a) (crown (shift8 a delta)) 7 delta := by
    apply difference_lower (Char2Degree19InnerSeam.shift8_unit a delta)
    rw [crown_shift8_compare]
    exact (Char2Degree19InnerDirect.uCorrection_degree a _ 1 (by omega) hl).trans_lt (by omega)
  have hdx : (C delta * (X + C (a 10))).natDegree ≤ 1 := by
    exact natDegree_mul_le.trans (by
      rw [natDegree_C, (isMonicOfDegree_X_add_one (a 10)).natDegree_eq])
  have ht : (tail (shift8 a delta) + tail a).natDegree < 12 := by
    rw [tail_shift8, cancel_tail]
    exact (natDegree_mul_le.trans
      (Nat.add_le_add hdx (D_monic a).natDegree_eq.le)).trans_lt (by omega)
  exact output_difference hc rfl ht

private theorem outside_change (a c b d : R[X]) :
    (a + d) * c + b = (a * c + b) + d * c := by
  rw [add_mul]
  ac_rfl

theorem output_shift4 (a : ℕ → R) (delta : R) :
    Char2Degree21Frame.output (shift4 a delta) =
      Char2Degree21Frame.output a + C delta * crown a := by
  have ha : A (shift4 a delta) = A a + C delta := by
    change t a + C (a 16 + delta) + C (a 18) =
      (t a + C (a 16) + C (a 18)) + C delta
    rw [map_add]
    ac_rfl
  have hc : crown (shift4 a delta) = crown a := rfl
  have ht : tail (shift4 a delta) = tail a := rfl
  rw [output_eq, ha, hc, ht, output_eq, outside_change]

theorem shift4_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift4 a delta)) 16 delta := by
  rw [output_shift4]
  exact difference_scaled delta (crown_monic a)

private theorem right_tail_change (t d z r c e : R[X]) :
    t * (d + e) + z + r + c = (t * d + z + r + c) + e * t := by
  rw [mul_add]
  simp only [add_assoc, add_comm, add_left_comm, mul_comm]

theorem output_shift15 (a : ℕ → R) (delta : R) :
    Char2Degree21Frame.output (shift15 a delta) =
      Char2Degree21Frame.output a + C delta * T a := by
  have hd : D (shift15 a delta) = D a + C delta := by
    change z a + C (a 19 + delta) + C (a 17) =
      (z a + C (a 19) + C (a 17)) + C delta
    rw [map_add]
    ac_rfl
  have ht : tail (shift15 a delta) = tail a + C delta * T a := by
    change T a * D (shift15 a delta) + z a + r a + C (a 20) = _
    rw [hd, right_tail_change]
    rfl
  have ha : A (shift15 a delta) = A a := rfl
  have hc : crown (shift15 a delta) = crown a := rfl
  rw [output_eq, ha, hc, ht, output_eq, add_assoc]

theorem shift15_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift15 a delta)) 5 delta := by
  rw [output_shift15]
  exact difference_scaled delta (T_monic a)

private theorem double_constant_cancel (t c d e : R[X]) :
    t + (c + e) + (d + e) = t + c + d := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero]

private theorem left_tail_change (t d z r c e : R[X]) :
    (t + e) * d + z + r + c = (t * d + z + r + c) + e * d := by
  rw [add_mul]
  ac_rfl

theorem output_shift16 (a : ℕ → R) (delta : R) :
    Char2Degree21Frame.output (shift16 a delta) =
      Char2Degree21Frame.output a + C delta * D a := by
  have ha : A (shift16 a delta) = A a := by
    change t a + C (a 16 + delta) + C (a 18 + delta) = _
    rw [map_add, map_add, double_constant_cancel]
    rfl
  have hT : T (shift16 a delta) = T a + C delta := by
    change t a + s a + C (a 18 + delta) = _
    rw [map_add, ← add_assoc]
    rfl
  have ht : tail (shift16 a delta) = tail a + C delta * D a := by
    change T (shift16 a delta) * D a + z a + r a + C (a 20) = _
    rw [hT, left_tail_change]
    rfl
  have hc : crown (shift16 a delta) = crown a := rfl
  rw [output_eq, ha, hc, ht, output_eq, add_assoc]

theorem shift16_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift16 a delta)) 4 delta := by
  rw [output_shift16]
  exact difference_scaled delta (D_monic a)

private theorem parallel_change (a c b t d : R[X]) :
    a * (c + d) + (b + d * t) = (a * c + b) + d * (a + t) := by
  rw [mul_add, mul_add]
  simp only [add_assoc, add_comm, add_left_comm, mul_comm]

private theorem frame_sum (t s c d : R[X]) :
    (t + c + d) + (t + s + d) = s + c := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero]

theorem output_shift17 (a : ℕ → R) (delta : R) :
    Char2Degree21Frame.output (shift17 a delta) =
      Char2Degree21Frame.output a + C delta * (s a + C (a 16)) := by
  have hc : crown (shift17 a delta) = crown a + C delta := by
    change u a + w a + q a + C (a 17 + delta) = _
    rw [map_add, ← add_assoc]
    rfl
  have hd : D (shift17 a delta) = D a + C delta := by
    change z a + C (a 19) + C (a 17 + delta) = _
    rw [map_add, ← add_assoc]
    rfl
  have ht : tail (shift17 a delta) = tail a + C delta * T a := by
    change T a * D (shift17 a delta) + z a + r a + C (a 20) = _
    rw [hd, right_tail_change]
    rfl
  have ha : A (shift17 a delta) = A a := rfl
  have hs : A a + T a = s a + C (a 16) := frame_sum ..
  rw [output_eq, ha, hc, ht, output_eq, parallel_change, hs]

theorem shift17_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift17 a delta)) 3 delta := by
  rw [output_shift17]
  exact difference_scaled delta ((s_monic a).add_right (C_lt _ 3 (by omega)))

theorem output_shift18 (a : ℕ → R) (delta : R) :
    Char2Degree21Frame.output (shift18 a delta) =
      Char2Degree21Frame.output a + C delta * (y + C (a 13)) := by
  have hr : r (shift18 a delta) = r a + C delta * (y + C (a 13)) := by
    change (X + C (a 12 + delta)) * (y + C (a 13)) = _
    rw [map_add, ← add_assoc, add_mul]
    rfl
  change m a + z a + r (shift18 a delta) + ell a + C (a 20) = _
  rw [hr]
  change m a + z a + (r a + C delta * (y + C (a 13))) + ell a + C (a 20) = _
  change _ = (m a + z a + r a + ell a + C (a 20)) + C delta * (y + C (a 13))
  ac_rfl

theorem shift18_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift18 a delta)) 2 delta := by
  rw [output_shift18]
  exact difference_scaled delta (y_monic.add_right (C_lt _ 2 (by omega)))

theorem output_shift19 (a : ℕ → R) (delta : R) :
    Char2Degree21Frame.output (shift19 a delta) =
      Char2Degree21Frame.output a + C delta * (X + C (a 12)) := by
  have hr : r (shift19 a delta) = r a + C delta * (X + C (a 12)) := by
    change (X + C (a 12)) * (y + C (a 13 + delta)) = _
    rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]
    rfl
  change m a + z a + r (shift19 a delta) + ell a + C (a 20) = _
  rw [hr]
  change _ = (m a + z a + r a + ell a + C (a 20)) + C delta * (X + C (a 12))
  ac_rfl

theorem shift19_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift19 a delta)) 1 delta := by
  rw [output_shift19]
  exact difference_scaled delta (isMonicOfDegree_X_add_one (a 12))

theorem output_shift20 (a : ℕ → R) (delta : R) :
    Char2Degree21Frame.output (shift20 a delta) =
      Char2Degree21Frame.output a + C delta := by
  change m a + z a + r a + ell a + C (a 20 + delta) = _
  rw [map_add, ← add_assoc]
  rfl

theorem shift20_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree21Frame.output a)
      (Char2Degree21Frame.output (shift20 a delta)) 0 delta := by
  have hd : Char2Degree21Frame.output (shift20 a delta) +
      Char2Degree21Frame.output a = C delta := by rw [output_shift20, cancel_tail]
  refine ⟨?_, ?_⟩
  · rw [hd, natDegree_C]
  · rw [hd, coeff_C_zero]

end FastPoly.Char2Degree21Pivots
