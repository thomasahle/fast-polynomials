import FastPoly.Examples.Char2Degree23FifteenKeys

/-! Local shared-wire changes for the supplied sixteenth normalized pivot. -/

namespace FastPoly.Char2Degree23SixteenWires

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23Cancellations Char2Degree23MiddleFrame

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def B (a : ℕ → R) : R := a 2 + a 6
def A (a : ℕ → R) : R := B a + 1
def gamma (a : ℕ → R) : R := a 2 + a 3 + a 6 + a 7 + a 8 + a 10 + a 16 + 1
def kappa (a : ℕ → R) (d : R) : R := (a 14 + a 5) * d + d ^ 2
def sigma (a : ℕ → R) (d : R) : R := kappa a d ^ 2 + gamma a * kappa a d + d
def cross (a : ℕ → R) (k s : R) : R := A a * B a * k ^ 2 + B a * k * s

def shift16 (a : ℕ → R) (d : R) : ℕ → R
  | 5 => a 5 + d
  | 7 => a 7 + kappa a d
  | 8 => a 8 + (B a * kappa a d + sigma a d)
  | 9 => a 9 + (A a * kappa a d + sigma a d)
  | 10 => a 10 + (A a * kappa a d + sigma a d)
  | 11 => a 11 + sigma a d
  | 12 => a 12 + d
  | 14 => a 14 + d
  | i => a i

noncomputable def L (a : ℕ → R) : R[X] := X + C (a 6)
noncomputable def N (a : ℕ → R) : R[X] :=
  L a * (X + C (a 7) + C (a 8) + C (a 10)) + (X + C (a 2)) * C (a 3) +
    C (a 4) + C (A a) * (X + C (a 8) + C (a 11)) + C (B a) * C (a 9)
noncomputable def firstSlope (a : ℕ → R) : R[X] :=
  L a * wSlope a + C (A a) * wLeft a + C (B a) * (y + v a + C (a 9)) +
    C (A a) * (v a + C (a 11))
noncomputable def K (a : ℕ → R) (d : R) : R[X] :=
  C (kappa a d) * N a + C (kappa a d) ^ 2 * L a + C (sigma a d) * lowLine a +
    C (cross a (kappa a d) (sigma a d)) + C d * (X + C (a 15))

theorem u_change (a : ℕ → R) (d : R) :
    u (shift16 a d) = u a + C d * G a := by
  rw [Char2Degree23HighFrame.u_eq (shift16 a d), Char2Degree23HighFrame.u_eq a]
  change G a * (h a + C (a 5 + d)) = _
  rw [add_constant, mul_add, mul_comm _ (C d)]
  rfl

private theorem g_pair (e g h t d : R[X]) :
    (e + d) * (g * (h + d) + t) =
      e * (g * h + t) + (d * t + (d * (e + h) + d ^ 2) * g) := by ring

theorem g_change (a : ℕ → R) (d : R) :
    g (shift16 a d) = g a + (C d * (X + C (a 15)) + C (kappa a d) * G a) := by
  have he : E a + H a = C (a 14 + a 5) := by
    change (h a + C (a 14)) + (h a + C (a 5)) = _
    simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]
  have hg (c : ℕ → R) : g c = E c * (G c * H c + (X + C (c 15))) := by
    change E c * (X + u c + C (c 15)) = _
    rw [Char2Degree23HighFrame.u_eq]
    congr 1
    simp only [add_assoc, add_comm, add_left_comm]
  rw [hg (shift16 a d), hg a]
  change (h a + C (a 14 + d)) * (G a * (h a + C (a 5 + d)) + (X + C (a 15))) = _
  rw [add_constant, add_constant]
  change (E a + C d) * (G a * (H a + C d) + (X + C (a 15))) = _
  rw [g_pair, he]
  have hk : C d * C (a 14 + a 5) + C d ^ 2 = C (kappa a d) := by
    rw [← map_mul, ← map_pow, ← map_add]
    congr 1
    unfold kappa
    rw [mul_comm d]
  rw [hk]

theorem v_change (a : ℕ → R) (d : R) :
    v (shift16 a d) = v a + C (kappa a d) * L a :=
  v_offset7 a (kappa a d)

private theorem three_eq_one : (3 : R[X]) = 1 := by
  calc
    (3 : R[X]) = 2 + 1 := by ring
    _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]

private theorem four_eq_zero : (4 : R[X]) = 0 := by
  calc
    (4 : R[X]) = 2 + 2 := by ring
    _ = 0 := by rw [CharTwo.two_eq_zero, zero_add]

private theorem common_shift (p q r s l b k t : R[X]) :
    (p + (b * k + t)) * (q + k * l + ((b + 1) * k + t)) +
      (r + ((b + 1) * k + t)) * (s + k * l + t) =
    (p * q + r * s) +
      (k * (l * (p + r) + (b + 1) * p + b * q + (b + 1) * s) +
        k ^ 2 * l + t * (p + q + r + s) + ((b + 1) * b * k ^ 2 + b * k * t)) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, three_eq_one, mul_one, mul_zero, zero_add, add_zero]

private theorem shift_right (y v c t s : R[X]) :
    y + (v + t) + (c + s) = (y + v + c) + t + s := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem W_change (a : ℕ → R) (d : R) :
    W (shift16 a d) = W a +
      (C (kappa a d) * firstSlope a + C (kappa a d) ^ 2 * L a +
        C (sigma a d) * lowLine a + C (cross a (kappa a d) (sigma a d))) := by
  change (X + y + z a + C (a 8 + (B a * kappa a d + sigma a d))) *
      (y + v (shift16 a d) + C (a 9 + (A a * kappa a d + sigma a d))) +
    (z a + C (a 10 + (A a * kappa a d + sigma a d))) *
      (v (shift16 a d) + C (a 11 + sigma a d)) = _
  rw [v_change]
  simp only [map_add, map_mul, A, map_one]
  rw [shift_right]
  have hr : (v a + C (kappa a d) * L a) + (C (a 11) + C (sigma a d)) =
      (v a + C (a 11)) + C (kappa a d) * L a + C (sigma a d) := by
    simpa only [zero_add] using
      shift_right 0 (v a) (C (a 11)) (C (kappa a d) * L a) (C (sigma a d))
  rw [hr]
  rw [← add_assoc (X + y + z a) (C (a 8)), ← add_assoc (z a) (C (a 10))]
  change (wLeft a + (C (B a) * C (kappa a d) + C (sigma a d))) *
      ((y + v a + C (a 9)) + C (kappa a d) * L a +
        ((C (B a) + 1) * C (kappa a d) + C (sigma a d))) +
    ((z a + C (a 10)) + ((C (B a) + 1) * C (kappa a d) + C (sigma a d))) *
      ((v a + C (a 11)) + C (kappa a d) * L a + C (sigma a d)) = _
  rw [common_shift, w_left_sum, all_factor_sum]
  simp only [firstSlope, cross, A, map_add, map_mul, map_pow, map_one]
  rfl

private theorem cancel_first (x Y Z b c d e f g h i j : R[X]) :
    ((x + c) * (x + Y + g + i) + (b + c + 1) * (x + Y + Z + g) +
      (b + c) * (Y + (x + c) * (Y + Z + f) + h) +
      (b + c + 1) * ((x + c) * (Y + Z + f) + j)) +
      ((x + b + 1) * Z + (x + b) * d + Y + e) =
    (x + c) * (x + f + g + i) + (x + b) * d + e +
      (b + c + 1) * (x + g + j) + (b + c) * h := by
  ring_nf
  simp only [CharTwo.two_eq_zero, four_eq_zero, mul_zero, zero_add, add_zero]

theorem firstSlope_add_G (a : ℕ → R) : firstSlope a + G a = N a := by
  have hg : G a = ((X + C (a 2) + 1) * z a + (X + C (a 2)) * C (a 3)) + y + C (a 4) := by
    change h a + y + C (a 4) = _
    rw [Char2Degree23HighPivots.h_eq]
  rw [hg]
  unfold firstSlope N L wSlope wLeft A B
  simp only [map_add, map_one]
  change _ + _ = _
  exact cancel_first X y (z a) (C (a 2)) (C (a 6)) (C (a 3)) (C (a 4))
    (C (a 7)) (C (a 8)) (C (a 9)) (C (a 10)) (C (a 11))

private theorem join (w g s n k b c e t : R[X]) (hs : s + g = n) :
    (w + (k * s + b + c + e)) + (t + k * g) = w + (k * n + b + c + e + t) := by
  rw [← hs, mul_add]
  simp only [add_assoc, add_comm, add_left_comm]

theorem Wg_change (a : ℕ → R) (d : R) :
    W (shift16 a d) + g (shift16 a d) = (W a + g a) + K a d := by
  rw [W_change, g_change]
  have hjoin := join (W a + g a) (G a) (firstSlope a) (N a) (C (kappa a d))
    (C (kappa a d) ^ 2 * L a) (C (sigma a d) * lowLine a)
    (C (cross a (kappa a d) (sigma a d))) (C d * (X + C (a 15))) (firstSlope_add_G a)
  have he (w g s t : R[X]) : (w + s) + (g + t) = (w + g) + s + t := by
    simp only [add_assoc, add_comm, add_left_comm]
  rw [he]
  exact hjoin

end FastPoly.Char2Degree23SixteenWires
