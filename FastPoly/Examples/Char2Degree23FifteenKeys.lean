import FastPoly.Examples.Char2Degree23FifteenSlope

/-! The explicit normalized degree-seven pivot of the supplied degree-23 inverse. -/

namespace FastPoly.Char2Degree23FifteenKeys

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23HighKeys Char2Degree23LowKeys Char2Degree23MiddleKeys
  Char2Degree23MiddleFrame Char2Degree23FifteenSlope

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift15 (a : ℕ → R) (d : R) : ℕ → R
  | 8 => a 8 + d
  | 10 => a 10 + d
  | 12 => a 12 + d
  | i => a i

theorem r_change (a : ℕ → R) (d : R) :
    r (shift15 a d) = r a + C d * (u a + C (a 13)) := by
  change (X + t a + C (a 12 + d)) * (u a + C (a 13)) = _
  rw [add_constant, add_mul]
  rfl

private theorem shift_head (y r g f h j k s : R[X]) :
    ((y + (r + s) + g) + f + h + j) + k =
      ((y + r + g) + f + h + j) + k + s := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem constant_change (a : ℕ → R) (d : R) :
    middleConstant (shift15 a d) = middleConstant a + C d * (u a + C (a 13)) := by
  change ((y + r (shift15 a d) + g a) + lastFactor a * u a +
      lastFactor a * C (a 21) + C (a 22)) + D a * crownBase a = _
  rw [r_change]
  change ((y + (r a + C d * (u a + C (a 13))) + g a) + lastFactor a * u a +
      lastFactor a * C (a 21) + C (a 22)) + D a * crownBase a =
    ((y + r a + g a) + lastFactor a * u a + lastFactor a * C (a 21) + C (a 22)) +
      D a * crownBase a + C d * (u a + C (a 13))
  exact shift_head _ _ _ _ _ _ _ _

private theorem collect (f w v c k b u d : R[X]) :
    f * (w + d * b) + (v + (c + d * u) + k) =
      (f * w + (v + c + k)) + d * (u + f * b) := by ring

theorem output_change (a : ℕ → R) (d : R) :
    output (shift15 a d) = output a + C d * rawSlope a := by
  have hw : Char2Degree23Cancellations.W (shift15 a d) = Char2Degree23Cancellations.W a +
      C d * (y + C (a 9) + C (a 11)) :=
    Char2Degree23MiddlePivots.W_shift12 a d
  rw [Char2Degree23MiddleFrame.output_eq (shift15 a d),
    Char2Degree23MiddleFrame.output_eq a, constant_change, hw]
  change wFactor a * (Char2Degree23Cancellations.W a + C d * (y + C (a 9) + C (a 11))) +
    (vFactor a * v a + (middleConstant a + C d * (u a + C (a 13))) + D a * C (a 19)) = _
  exact collect _ _ _ _ _ _ _ _

private theorem restore (x y : R[X]) : x = y + (x + y) := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem raw_difference (a : ℕ → R) (d : R) :
    output (shift15 a d) + output a = D a * C (d * rowEight a) + C d * peeled a := by
  rw [output_change, cancel_tail]
  have hs : rawSlope a = D a * C (rowEight a) + peeled a := by
    rw [← rawSlope_eq]
    exact restore _ _
  rw [hs, mul_add, map_mul]
  rw [← mul_assoc (C d) (D a), mul_comm (C d) (D a), mul_assoc]

theorem a10_15 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a10 (increment q 15 d) = Char2Degree23Coordinates.a10 q + d := by
  change q 12 + (Char2Degree23Coordinates.rho q + q 16 +
    Char2Degree23Coordinates.a11 q + ((q 15 + d) + q 16)) = _
  unfold Char2Degree23Coordinates.a10 Char2Degree23Coordinates.a12
  simp only [add_assoc, add_comm, add_left_comm]

theorem a8_15 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a8 (increment q 15 d) = Char2Degree23Coordinates.a8 q + d := by
  unfold Char2Degree23Coordinates.a8
  rw [a10_15]
  change q 9 + (q 16 ^ 2 + q 7 * q 16 + (Char2Degree23Coordinates.a10 q + d) + q 20 + q 18) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem slots15 (q : Fin 23 → R) (d : R) :
    SameRaw (shift15 (rawKeys q) d) (rawKeys (increment q 15 d)) := by
  constructor <;> simp only [shift15] <;>
    rw [rawKeys_core _ _ (by omega) (by omega), rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_15 q d).symm | exact (a10_15 q d).symm |
    (change (q 15 + q 16) + d = (q 15 + d) + q 16;
      simp only [add_assoc, add_comm, add_left_comm])

theorem increment15_change (q : Fin 23 → R) (d : R) :
    output (rawKeys (increment q 15 d)) = output (rawKeys q) + C d * peeled (rawKeys q) := by
  have hl : (C d * peeled (rawKeys q)).natDegree < 8 := by
    apply natDegree_mul_le.trans_lt
    rw [natDegree_C, (peeled_monic (rawKeys q)).natDegree_eq]
    omega
  exact Char2Degree23NormalizedPeel.increment (by omega) (slots15 q d) rfl
    (raw_difference (rawKeys q) d) hl

theorem increment15_unit (q : Fin 23 → R) (d : R) :
    Char2Degree19InnerTail.UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 15 d))) 7 d := by
  rw [increment15_change]
  exact Char2Degree21Frame.difference_scaled d (peeled_monic (rawKeys q))

end FastPoly.Char2Degree23FifteenKeys
