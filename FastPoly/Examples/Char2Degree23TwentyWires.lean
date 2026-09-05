import FastPoly.Examples.Char2Degree23TwentyQuadratic
import FastPoly.Examples.Char2Degree23SixteenFrame

/-! The final shared-wire cancellation: q20 leaves a named monic quadratic. -/

namespace FastPoly.Char2Degree23TwentyWires

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23Cancellations Char2Degree23MiddleFrame
  Char2Degree23TwentyCoordinates Char2Degree23TwentyQuadratic

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def cross (a : ℕ → R) (d : R) : R := (B a + 1) ^ 2 * d ^ 2 + B a * d * sigma a d
noncomputable def firstSlope (a : ℕ → R) : R[X] :=
  L a * wSlope a + C (B a + 1) * wLeft a + C (B a + 1) * (y + v a + C (a 9)) +
    C (B a) * (v a + C (a 11))
noncomputable def K (a : ℕ → R) (d : R) : R[X] :=
  C d * M a + C d ^ 2 * L a + C (sigma a d) * lowLine a + C (cross a d)

theorem v_change (a : ℕ → R) (d : R) : v (shift20 a d) = v a + C d * L a :=
  v_offset7 a d

theorem g_change (a : ℕ → R) (d : R) : g (shift20 a d) = g a + C d * E a := by
  change E a * (X + u a + C (a 15 + d)) = _
  rw [add_constant, mul_add, mul_comm _ (C d)]
  rfl

private theorem three_eq_one : (3 : R[X]) = 1 := by
  calc
    (3 : R[X]) = 2 + 1 := by ring
    _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]

private theorem four_eq_zero : (4 : R[X]) = 0 := by
  calc
    (4 : R[X]) = 2 + 2 := by ring
    _ = 0 := by rw [CharTwo.two_eq_zero, zero_add]

private theorem common_shift (p q r s l b d t : R[X]) :
    (p + ((b + 1) * d + t)) * (q + d * l + ((b + 1) * d + t)) +
      (r + (b * d + t)) * (s + d * l + t) =
    (p * q + r * s) +
      (d * (l * (p + r) + (b + 1) * p + (b + 1) * q + b * s) +
        d ^ 2 * l + t * (p + q + r + s) + ((b + 1) ^ 2 * d ^ 2 + b * d * t)) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, three_eq_one, mul_one, mul_zero, zero_add, add_zero]

private theorem shift_right (y v c t s : R[X]) :
    y + (v + t) + (c + s) = (y + v + c) + t + s := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem W_change (a : ℕ → R) (d : R) :
    W (shift20 a d) = W a + (C d * firstSlope a + C d ^ 2 * L a +
      C (sigma a d) * lowLine a + C (cross a d)) := by
  change (X + y + z a + C (a 8 + ((B a + 1) * d + sigma a d))) *
      (y + v (shift20 a d) + C (a 9 + ((B a + 1) * d + sigma a d))) +
    (z a + C (a 10 + (B a * d + sigma a d))) *
      (v (shift20 a d) + C (a 11 + sigma a d)) = _
  rw [v_change]
  simp only [map_add, map_mul, map_one]
  rw [shift_right]
  have hr : (v a + C d * L a) + (C (a 11) + C (sigma a d)) =
      (v a + C (a 11)) + C d * L a + C (sigma a d) := by
    simpa only [zero_add] using shift_right 0 (v a) (C (a 11)) (C d * L a) (C (sigma a d))
  rw [hr, ← add_assoc (X + y + z a) (C (a 8)), ← add_assoc (z a) (C (a 10))]
  change (wLeft a + ((C (B a) + 1) * C d + C (sigma a d))) *
      ((y + v a + C (a 9)) + C d * L a + ((C (B a) + 1) * C d + C (sigma a d))) +
    ((z a + C (a 10)) + (C (B a) * C d + C (sigma a d))) *
      ((v a + C (a 11)) + C d * L a + C (sigma a d)) = _
  rw [common_shift, w_left_sum, all_factor_sum]
  simp only [firstSlope, cross, map_add, map_mul, map_pow, map_one]
  rfl

private theorem cancel_first (x Y Z b c d e f g h i j : R[X]) :
    ((x + c) * (x + Y + g + i) + (b + c + 1) * (x + Y + Z + g) +
      (b + c + 1) * (Y + (x + c) * (Y + Z + f) + h) +
      (b + c) * ((x + c) * (Y + Z + f) + j)) +
      ((x + b + 1) * Z + (x + b) * d + e) =
    (x + c) * (x + f + g + i) + (x + b) * d + e +
      (b + c + 1) * (x + g + h) + (b + c) * j := by
  ring_nf
  simp only [CharTwo.two_eq_zero, three_eq_one, four_eq_zero, mul_one, mul_zero, zero_add, add_zero]

theorem firstSlope_add_E (a : ℕ → R) : firstSlope a + E a = M a := by
  have he : E a = ((X + C (a 2) + 1) * z a + (X + C (a 2)) * C (a 3)) + C (a 14) := by
    change h a + C (a 14) = _
    rw [Char2Degree23HighPivots.h_eq]
  rw [he, M_expanded]
  unfold firstSlope L wSlope wLeft B
  simp only [map_add, map_one]
  exact cancel_first X y (z a) (C (a 2)) (C (a 6)) (C (a 3)) (C (a 14))
    (C (a 7)) (C (a 8)) (C (a 9)) (C (a 10)) (C (a 11))

private theorem join (w g s n d b c e : R[X]) (hs : s + g = n) :
    (w + (d * s + b + c + e)) + d * g = w + (d * n + b + c + e) := by
  rw [← hs, mul_add]
  simp only [add_assoc, add_comm, add_left_comm]

private theorem regroup (w g s t : R[X]) : (w + s) + (g + t) = ((w + g) + s) + t := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem Wg_change (a : ℕ → R) (d : R) :
    W (shift20 a d) + g (shift20 a d) = (W a + g a) + K a d := by
  rw [W_change, g_change, regroup]
  exact join (W a + g a) (E a) (firstSlope a) (M a) (C d)
    (C d ^ 2 * L a) (C (sigma a d) * lowLine a) (C (cross a d)) (firstSlope_add_E a)

end FastPoly.Char2Degree23TwentyWires
