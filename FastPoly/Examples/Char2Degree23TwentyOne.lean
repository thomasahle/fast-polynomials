import FastPoly.Examples.Char2Degree23NormalizedPeel

/-!
# The supplied terminal q21 update of the degree-23 decoder

All four offsets of w+s move together, and the second offset of ell
moves by the same value. Their high columns cancel to a scalar multiple
of D; reading the installed row eight removes it. The remaining column
is the named monic linear polynomial, giving the actual row-one pivot.
-/

namespace FastPoly.Char2Degree23TwentyOne

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23HighKeys Char2Degree23LowKeys Char2Degree23MiddleFrame
  Char2Degree23MiddleKeys Char2Degree23Cancellations

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift21 (a : ℕ → R) (d : R) : ℕ → R
  | 8 => a 8 + d
  | 9 => a 9 + d
  | 10 => a 10 + d
  | 11 => a 11 + d
  | 17 => a 17 + d
  | i => a i

def rowEight (a : ℕ → R) : R := a 8 + a 9 + a 10 + a 11 + a 16

theorem line_sum (a : ℕ → R) : lowLine a + ellLinear a = C (rowEight a) := by
  unfold lowLine ellLinear rowEight
  simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem constant_change (a : ℕ → R) (d : R) :
    middleConstant (shift21 a d) = middleConstant a + D a * (C d * ellLinear a) := by
  have hc : crownBase (shift21 a d) = crownBase a + C d * ellLinear a := by
    change X + y + z a + g a + ellLinear a * (z a + C (a 17 + d)) = _
    rw [add_constant, mul_add, mul_comm (ellLinear a) (C d), ← add_assoc]
    rfl
  change (headBase a + lastFactor a * u a + lastFactor a * C (a 21) + C (a 22)) +
    D a * crownBase (shift21 a d) = _
  rw [hc, mul_add, ← add_assoc]
  rfl

private theorem collect (f w v c k d l e : R[X]) :
    (f + 1) * (w + d * l) + (v + (c + f * (d * e)) + k) =
      ((f + 1) * w + (v + c + k)) + (f * (d * (l + e)) + d * l) := by ring

theorem output_change (a : ℕ → R) (d : R) :
    output (shift21 a d) = output a +
      (D a * C (d * rowEight a) + C d * lowLine a) := by
  have hw : W (shift21 a d) = W a + C d * lowLine a := W_commonOffsets a d
  rw [Char2Degree23MiddleFrame.output_eq (shift21 a d),
    Char2Degree23MiddleFrame.output_eq a, hw, constant_change]
  change (D a + 1) * (W a + C d * lowLine a) +
    (vFactor a * v a + (middleConstant a + D a * (C d * ellLinear a)) + D a * C (a 19)) = _
  rw [collect, line_sum, ← map_mul]
  rfl

theorem raw_difference (a : ℕ → R) (d : R) :
    output (shift21 a d) + output a =
      D a * C (d * rowEight a) + C d * lowLine a := by
  rw [output_change, cancel_tail]

theorem tau21 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.tau (increment q 21 d) = Char2Degree23Coordinates.tau q + d := by
  dsimp [Char2Degree23Coordinates.tau, Char2Degree23Coordinates.gamma, increment, Function.update]
  ac_rfl

theorem a11_21 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a11 (increment q 21 d) = Char2Degree23Coordinates.a11 q + d := by
  unfold Char2Degree23Coordinates.a11
  rw [tau21]
  change q 13 + (Char2Degree23Coordinates.tau q + d) = _
  rw [← add_assoc]

theorem a10_21 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a10 (increment q 21 d) = Char2Degree23Coordinates.a10 q + d := by
  unfold Char2Degree23Coordinates.a10
  rw [a11_21]
  change q 12 + (Char2Degree23Coordinates.rho q + q 16 +
    (Char2Degree23Coordinates.a11 q + d) + Char2Degree23Coordinates.a12 q) = _
  ac_rfl

theorem a9_21 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a9 (increment q 21 d) = Char2Degree23Coordinates.a9 q + d := by
  unfold Char2Degree23Coordinates.a9
  rw [a11_21]
  change q 10 + (Char2Degree23Coordinates.rho q + (Char2Degree23Coordinates.a11 q + d) +
    q 20 + q 18) = _
  ac_rfl

theorem a8_21 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a8 (increment q 21 d) = Char2Degree23Coordinates.a8 q + d := by
  unfold Char2Degree23Coordinates.a8
  rw [a10_21]
  change q 9 + (q 16 ^ 2 + q 7 * q 16 + (Char2Degree23Coordinates.a10 q + d) + q 20 + q 18) = _
  ac_rfl

theorem slots21 (q : Fin 23 → R) (d : R) :
    SameRaw (shift21 (rawKeys q) d) (rawKeys (increment q 21 d)) := by
  constructor <;> simp only [shift21] <;>
    rw [rawKeys_core _ _ (by omega) (by omega), rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_21 q d).symm | exact (a9_21 q d).symm |
    exact (a10_21 q d).symm | exact (a11_21 q d).symm

theorem increment21_change (q : Fin 23 → R) (d : R) :
    output (rawKeys (increment q 21 d)) = output (rawKeys q) + C d * lowLine (rawKeys q) := by
  have hl : (C d * lowLine (rawKeys q)).natDegree < 8 := by
    apply natDegree_mul_le.trans_lt
    rw [natDegree_C, (lowLine_monic (rawKeys q)).natDegree_eq]
    omega
  exact Char2Degree23NormalizedPeel.increment (by omega) (slots21 q d) rfl
    (raw_difference (rawKeys q) d) hl

theorem increment21_unit (q : Fin 23 → R) (d : R) :
    Char2Degree19InnerTail.UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 21 d))) 1 d := by
  rw [increment21_change]
  exact Char2Degree21Frame.difference_scaled d (lowLine_monic (rawKeys q))

end FastPoly.Char2Degree23TwentyOne

