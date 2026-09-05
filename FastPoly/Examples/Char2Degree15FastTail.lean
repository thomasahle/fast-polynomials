import FastPoly.Examples.Char2Degree15FastCore
import FastPoly.Examples.Char2Degree19InnerChanges

/-! Direct terminal pivots of the square-first degree-15 circuit.
Only the named cancelled branch is opened; no coefficient baseline is expanded. -/

namespace FastPoly.Char2Degree15Fast

set_option maxHeartbeats 20000

open Polynomial Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def increment (q : Keys R) (i : Fin 15) (delta : R) : Keys R :=
  Function.update q i (q i + delta)

private theorem assemble_r (a b c d e : R[X]) :
    a + b + (c + e) + d = (a + b + c + d) + e := by ac_rfl

private theorem assemble_head (a v b c r k d s : R[X]) :
    a * (v + d * s) + b + c + r + k =
      (a * v + b + c + r + k) + d * (a * s) := by ring

noncomputable def rightU (q : Keys R) : R[X] := z q + t q + C (q 5)

theorem u_increment4 (q : Keys R) (delta : R) :
    u (increment q 4 delta) = u q + C delta * rightU q := by
  change (y + t q + C ((q 4 + delta) + q 5 + q 7)) * rightU q = _
  have hk : (q 4 + delta) + q 5 + q 7 = (q 4 + q 5 + q 7) + delta := by ac_rfl
  rw [hk, map_add, ← add_assoc, add_mul]
  rfl

theorem output_increment4 (q : Keys R) (delta : R) :
    output (increment q 4 delta) =
      output q + C delta * ((t q + C (q 7)) * rightU q) := by
  have hr : r (increment q 4 delta) =
      r q + C delta * ((t q + C (q 7)) * rightU q) := by
    change (t q + C (q 7)) * (u (increment q 4 delta) + C (q 9)) = _
    rw [u_increment4, add_right_comm (u q), mul_add, mul_left_comm _ (C delta)]
    rfl
  rw [output, hr]
  change w q + s q + (r q + C delta * ((t q + C (q 7)) * rightU q)) + C (q 14) = _
  rw [output]
  exact assemble_r ..

theorem u_increment5 (q : Keys R) (delta : R) :
    u (increment q 5 delta) =
      u q + C delta * (y + z q + C (q 4 + q 7 + delta)) := by
  change (y + t q + C (q 4 + (q 5 + delta) + q 7)) *
    (z q + t q + C (q 5 + delta)) = _
  have hl : y + t q + C (q 4 + (q 5 + delta) + q 7) =
      (y + t q + C (q 4 + q 5 + q 7)) + C delta := by
    have hk : q 4 + (q 5 + delta) + q 7 = (q 4 + q 5 + q 7) + delta := by ac_rfl
    rw [hk, map_add, ← add_assoc]
  have hr : z q + t q + C (q 5 + delta) = (z q + t q + C (q 5)) + C delta := by
    rw [map_add, ← add_assoc]
  have hs : (y + t q + C (q 4 + q 5 + q 7)) + (z q + t q + C (q 5)) =
      y + z q + C (q 4 + q 7) := by
    simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero]
  rw [hl, hr, both_factors, hs]
  change u q + C delta * (y + z q + C (q 4 + q 7)) + C delta ^ 2 = _
  simp only [map_add, mul_add, pow_two, add_assoc]

theorem output_increment5 (q : Keys R) (delta : R) :
    output (increment q 5 delta) = output q +
      C delta * ((t q + C (q 7)) * (y + z q + C (q 4 + q 7 + delta))) := by
  have hr : r (increment q 5 delta) = r q +
      C delta * ((t q + C (q 7)) * (y + z q + C (q 4 + q 7 + delta))) := by
    change (t q + C (q 7)) * (u (increment q 5 delta) + C (q 9)) = _
    rw [u_increment5, add_right_comm (u q), mul_add, mul_left_comm _ (C delta)]
    rfl
  rw [output, hr]
  change w q + s q + (r q + C delta * ((t q + C (q 7)) *
    (y + z q + C (q 4 + q 7 + delta)))) + C (q 14) = _
  rw [output]
  exact assemble_r ..

private theorem nested_product_change (a b z c d : R[X]) :
    (a + d) * ((b + d) * z + c) = a * (b * z + c) +
      d * ((a + b + d) * z + c) := by ring

theorem output_increment7 (q : Keys R) (delta : R) :
    output (increment q 7 delta) = output q + C delta *
      ((y + C (q 4 + q 5 + delta)) * rightU q + C (q 9)) := by
  have hr : r (increment q 7 delta) = r q + C delta *
      ((y + C (q 4 + q 5 + delta)) * rightU q + C (q 9)) := by
    change (t q + C (q 7 + delta)) *
      ((y + t q + C (q 4 + q 5 + (q 7 + delta))) * rightU q + C (q 9)) = _
    have ha : t q + C (q 7 + delta) = (t q + C (q 7)) + C delta := by
      rw [map_add, ← add_assoc]
    have hb : y + t q + C (q 4 + q 5 + (q 7 + delta)) =
        (y + t q + C (q 4 + q 5 + q 7)) + C delta := by
      rw [← add_assoc (q 4 + q 5), map_add, ← add_assoc]
    have hs : (t q + C (q 7)) + (y + t q + C (q 4 + q 5 + q 7)) + C delta =
        y + C (q 4 + q 5 + delta) := by
      simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
        CharTwo.add_self_eq_zero, add_zero, zero_add]
    rw [ha, hb, nested_product_change, hs]
    rfl
  rw [output, hr]
  change w q + s q + (r q + C delta *
    ((y + C (q 4 + q 5 + delta)) * rightU q + C (q 9))) + C (q 14) = _
  rw [output]
  exact assemble_r ..

theorem low_increment6 (q : Keys R) (delta : R) :
    low (increment q 6 delta) = low q + C delta * (y + C (q 13)) := by
  change X * y + y ^ 2 + C ((q 6 + delta) + q 12) * y + C (q 13) * X +
    C ((q 6 + delta) * q 13 + q 10 * q 12 + q 10 * q 13) = _
  unfold low
  simp only [map_add, map_mul, add_mul, mul_add]
  ac_rfl

theorem output_increment6 (q : Keys R) (delta : R) :
    output (increment q 6 delta) =
      output q + C delta * (v q + y + C (q 13)) := by
  rw [output_split, low_increment6]
  change (X + y + C (q 6 + delta)) * v q + (y + C (q 10)) * z q +
    (low q + C delta * (y + C (q 13))) + r q + C (q 14) = _
  rw [output_split]
  unfold head
  simp only [map_add, add_mul, mul_add]
  ac_rfl

theorem v_increment8 (q : Keys R) (delta : R) :
    v (increment q 8 delta) = v q + C delta * (z q + C (q 11)) := by
  change (X + z q + C ((q 8 + delta) + q 11)) * (z q + C (q 11)) = _
  rw [add_right_comm (q 8) delta, map_add, ← add_assoc, add_mul]
  rfl

theorem output_increment8 (q : Keys R) (delta : R) :
    output (increment q 8 delta) =
      output q + C delta * (head q * (z q + C (q 11))) := by
  rw [output_split, v_increment8]
  change head q * (v q + C delta * (z q + C (q 11))) +
    (y + C (q 10)) * z q + low q + r q + C (q 14) = _
  rw [output_split]
  exact assemble_head (head q) (v q) ((y + C (q 10)) * z q)
    (low q) (r q) (C (q 14)) (C delta) (z q + C (q 11))

theorem r_increment9 (q : Keys R) (delta : R) :
    r (increment q 9 delta) = r q + C delta * (t q + C (q 7)) := by
  change (t q + C (q 7)) * (u q + C (q 9 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]
  rfl

theorem output_increment9 (q : Keys R) (delta : R) :
    output (increment q 9 delta) = output q + C delta * (t q + C (q 7)) := by
  rw [output, r_increment9]
  change w q + s q + (r q + C delta * (t q + C (q 7))) + C (q 14) = _
  rw [output]
  exact assemble_r ..

theorem low_increment10 (q : Keys R) (delta : R) :
    low (increment q 10 delta) = low q + C delta * C (q 12 + q 13) := by
  change X * y + y ^ 2 + C (q 6 + q 12) * y + C (q 13) * X +
    C (q 6 * q 13 + (q 10 + delta) * q 12 + (q 10 + delta) * q 13) = _
  unfold low
  simp only [map_add, map_mul, add_mul, mul_add]
  ac_rfl

theorem output_increment10 (q : Keys R) (delta : R) :
    output (increment q 10 delta) =
      output q + C delta * (z q + C (q 12 + q 13)) := by
  rw [output_split, low_increment10]
  change head q * v q + (y + C (q 10 + delta)) * z q +
    (low q + C delta * C (q 12 + q 13)) + r q + C (q 14) = _
  rw [output_split, map_add, ← add_assoc y, add_mul, mul_add]
  ac_rfl

theorem v_increment11 (q : Keys R) (delta : R) :
    v (increment q 11 delta) = v q + C delta * (X + C (q 8 + delta)) := by
  change (X + z q + C (q 8 + (q 11 + delta))) * (z q + C (q 11 + delta)) = _
  have he : (X + z q + C (q 8 + q 11)) + (z q + C (q 11)) =
      X + C (q 8) := by
    simp only [map_add, add_assoc, add_comm, add_left_comm,
      CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]
  have hl : X + z q + C (q 8 + (q 11 + delta)) =
      (X + z q + C (q 8 + q 11)) + C delta := by
    rw [← add_assoc (q 8), map_add, ← add_assoc]
  have hr : z q + C (q 11 + delta) = (z q + C (q 11)) + C delta := by
    rw [map_add, ← add_assoc]
  rw [hl, hr, both_factors, he]
  change v q + C delta * (X + C (q 8)) + C delta ^ 2 = _
  simp only [map_add, mul_add, pow_two, add_assoc]

theorem output_increment11 (q : Keys R) (delta : R) :
    output (increment q 11 delta) =
      output q + C delta * (head q * (X + C (q 8 + delta))) := by
  rw [output_split, v_increment11]
  change head q * (v q + C delta * (X + C (q 8 + delta))) +
    (y + C (q 10)) * z q + low q + r q + C (q 14) = _
  rw [output_split]
  exact assemble_head (head q) (v q) ((y + C (q 10)) * z q)
    (low q) (r q) (C (q 14)) (C delta) (X + C (q 8 + delta))

theorem low_increment12 (q : Keys R) (delta : R) :
    low (increment q 12 delta) = low q + C delta * (y + C (q 10)) := by
  change X * y + y ^ 2 + C (q 6 + (q 12 + delta)) * y + C (q 13) * X +
    C (q 6 * q 13 + q 10 * (q 12 + delta) + q 10 * q 13) = _
  unfold low
  simp only [map_add, map_mul, add_mul, mul_add]
  ac_rfl

theorem low_increment13 (q : Keys R) (delta : R) :
    low (increment q 13 delta) = low q + C delta * (X + C (q 6 + q 10)) := by
  change X * y + y ^ 2 + C (q 6 + q 12) * y + C (q 13 + delta) * X +
    C (q 6 * (q 13 + delta) + q 10 * q 12 + q 10 * (q 13 + delta)) = _
  unfold low
  simp only [map_add, map_mul, add_mul, mul_add]
  ac_rfl

theorem output_increment12 (q : Keys R) (delta : R) :
    output (increment q 12 delta) = output q + C delta * (y + C (q 10)) := by
  rw [output_split, low_increment12]
  change head q * v q + (y + C (q 10)) * z q +
    (low q + C delta * (y + C (q 10))) + r q + C (q 14) = _
  rw [output_split]
  ac_rfl

theorem output_increment13 (q : Keys R) (delta : R) :
    output (increment q 13 delta) = output q + C delta * (X + C (q 6 + q 10)) := by
  rw [output_split, low_increment13]
  change head q * v q + (y + C (q 10)) * z q +
    (low q + C delta * (X + C (q 6 + q 10))) + r q + C (q 14) = _
  rw [output_split]
  ac_rfl

theorem output_increment14 (q : Keys R) (delta : R) :
    output (increment q 14 delta) = output q + C delta := by
  change w q + s q + r q + C (q 14 + delta) = _
  rw [map_add, ← add_assoc]
  rfl


theorem rightU_monic (q : Keys R) : IsMonicOfDegree (rightU q) 5 :=
  ((t_monic q).add_left ((z_monic q).natDegree_eq ▸ (by omega : 4 < 5))).add_right
    (const_lt _ 5 (by omega))

theorem increment4_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 4 delta)) 10 delta := by
  apply unit_difference_of_split (output q) (output (increment q 4 delta))
    ((t q + C (q 7)) * rightU q) 10 delta 0 (by omega)
    (((t_monic q).add_right (const_lt _ 5 (by omega))).mul (rightU_monic q))
  rw [map_zero, add_zero, output_increment4]

theorem increment5_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 5 delta)) 9 delta := by
  have hs : IsMonicOfDegree (y + z q + C (q 4 + q 7 + delta)) 4 :=
    ((z_monic q).add_left ((y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 4))).add_right
      (const_lt _ 4 (by omega))
  apply unit_difference_of_split (output q) (output (increment q 5 delta))
    ((t q + C (q 7)) * (y + z q + C (q 4 + q 7 + delta))) 9 delta 0 (by omega)
    (((t_monic q).add_right (const_lt _ 5 (by omega))).mul hs)
  rw [map_zero, add_zero, output_increment5]

theorem increment7_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 7 delta)) 7 delta := by
  have hs : IsMonicOfDegree
      ((y + C (q 4 + q 5 + delta)) * rightU q + C (q 9)) 7 :=
    (((y_monic.add_right (const_lt _ 2 (by omega))).mul (rightU_monic q))).add_right
      (const_lt _ 7 (by omega))
  apply unit_difference_of_split (output q) (output (increment q 7 delta))
    ((y + C (q 4 + q 5 + delta)) * rightU q + C (q 9)) 7 delta 0 (by omega) hs
  rw [map_zero, add_zero, output_increment7]

theorem increment6_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 6 delta)) 8 delta := by
  have hs : IsMonicOfDegree (v q + y + C (q 13)) 8 :=
    ((v_monic q).add_right ((y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 8))).add_right
      (const_lt _ 8 (by omega))
  apply unit_difference_of_split (output q) (output (increment q 6 delta))
    (v q + y + C (q 13)) 8 delta 0 (by omega) hs
  rw [map_zero, add_zero, output_increment6]

theorem increment8_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 8 delta)) 6 delta := by
  apply unit_difference_of_split (output q) (output (increment q 8 delta))
    (head q * (z q + C (q 11))) 6 delta 0 (by omega)
    ((head_monic q).mul ((z_monic q).add_right (const_lt _ 4 (by omega))))
  rw [map_zero, add_zero, output_increment8]

theorem increment9_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 9 delta)) 5 delta := by
  apply unit_difference_of_split (output q) (output (increment q 9 delta))
    (t q + C (q 7)) 5 delta 0 (by omega)
    ((t_monic q).add_right (const_lt _ 5 (by omega)))
  rw [map_zero, add_zero, output_increment9]

theorem increment10_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 10 delta)) 4 delta := by
  apply unit_difference_of_split (output q) (output (increment q 10 delta))
    (z q + C (q 12 + q 13)) 4 delta 0 (by omega)
    ((z_monic q).add_right (const_lt _ 4 (by omega)))
  rw [map_zero, add_zero, output_increment10]

theorem increment11_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 11 delta)) 3 delta := by
  apply unit_difference_of_split (output q) (output (increment q 11 delta))
    (head q * (X + C (q 8 + delta))) 3 delta 0 (by omega)
    ((head_monic q).mul (isMonicOfDegree_X_add_one (q 8 + delta)))
  rw [map_zero, add_zero, output_increment11]

theorem increment12_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 12 delta)) 2 delta := by
  apply unit_difference_of_split (output q) (output (increment q 12 delta))
    (y + C (q 10)) 2 delta 0 (by omega)
    (y_monic.add_right (const_lt _ 2 (by omega)))
  rw [map_zero, add_zero, output_increment12]

theorem increment13_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 13 delta)) 1 delta := by
  apply unit_difference_of_split (output q) (output (increment q 13 delta))
    (X + C (q 6 + q 10)) 1 delta 0 (by omega)
    (isMonicOfDegree_X_add_one (q 6 + q 10))
  rw [map_zero, add_zero, output_increment13]

theorem increment14_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 14 delta)) 0 delta := by
  have he : output (increment q 14 delta) + output q = C delta := by
    rw [output_increment14, Char2Decoder.cancel_tail]
  constructor
  · rw [he, natDegree_C]
  · rw [he, coeff_C_zero]

end FastPoly.Char2Degree15Fast
