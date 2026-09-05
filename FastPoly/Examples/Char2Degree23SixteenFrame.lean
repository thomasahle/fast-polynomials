import FastPoly.Examples.Char2Degree23SixteenWires

/-! The displayed scalar row-eight column and monic degree-six residual. -/

namespace FastPoly.Char2Degree23SixteenFrame

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23HighFrame Char2Degree23Cancellations Char2Degree23MiddleFrame
  Char2Degree23SixteenWires

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def xi (a : ℕ → R) : R := a 6 * (a 7 + a 8 + a 10) + a 2 * a 3 + a 4 +
  A a * (a 8 + a 11) + B a * a 9 + a 16 * a 6
def rowEight (a : ℕ → R) (d : R) : R :=
  kappa a d * xi a + kappa a d ^ 2 * a 6 +
    sigma a d * (a 8 + a 9 + a 10 + a 11) + cross a (kappa a d) (sigma a d) + d * a 15
noncomputable def rLeft (a : ℕ → R) : R[X] := X + t a + C (a 12)
noncomputable def rDelta (a : ℕ → R) (d : R) : R[X] :=
  C d * (u a + C (a 13) + rLeft a * G a) + C d ^ 2 * G a
noncomputable def sixSlope (a : ℕ → R) : R[X] := G a * (X + C (a 5) + C (a 12) + C (a 20))
noncomputable def residual (a : ℕ → R) (d : R) : R[X] :=
  C d ^ 2 * G a + C (kappa a d) * L a + K a d + C d * C (a 13)
noncomputable def low (a : ℕ → R) (d : R) : R[X] := C d * sixSlope a + residual a d

private theorem three_eq_one : (3 : R[X]) = 1 := by
  calc
    (3 : R[X]) = 2 + 1 := by ring
    _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]

private theorem n_cancel (x b c d e f g h i j t : R[X]) :
    ((x + c) * (x + f + g + h) + (x + b) * d + e +
      (b + c + 1) * (x + g + i) + (b + c) * j) + (x + t) * (x + c) =
    (b + d + c + f + g + h + t + 1) * x +
      (c * (f + g + h) + b * d + e + (b + c + 1) * (g + i) + (b + c) * j + t * c) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, three_eq_one, mul_one, mul_zero, zero_add, add_zero]

theorem N_linear (a : ℕ → R) : N a + ellLinear a * L a = C (gamma a) * X + C (xi a) := by
  unfold N ellLinear L gamma xi A B
  simp only [map_add, map_mul, map_one]
  exact n_cancel X (C (a 2)) (C (a 6)) (C (a 3)) (C (a 4)) (C (a 7))
    (C (a 8)) (C (a 10)) (C (a 11)) (C (a 9)) (C (a 16))

private theorem group_N (n t l z c x k s d : R[X]) :
    (k * n + k ^ 2 * l + s * z + c + d * x) + k * t =
      k * (n + t) + k ^ 2 * l + s * z + c + d * x := by ring

private theorem linear_cancel (x k g t c z e d f : R[X]) :
    k * (g * x + t) + k ^ 2 * (x + c) + (k ^ 2 + g * k + d) * (x + z) + e + d * (x + f) =
      k * t + k ^ 2 * c + (k ^ 2 + g * k + d) * z + e + d * f := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem scalar_column (a : ℕ → R) (d : R) :
    K a d + C (kappa a d) * (ellLinear a * L a) = C (rowEight a d) := by
  unfold K
  rw [group_N, N_linear]
  have hs : C (sigma a d) = C (kappa a d) ^ 2 + C (gamma a) * C (kappa a d) + C d := by
    simp only [sigma, map_add, map_mul, map_pow]
  have hl : lowLine a = X + C (a 8 + a 9 + a 10 + a 11) := by
    simp only [lowLine, map_add, add_assoc]
  rw [hs, hl]
  change C (kappa a d) * (C (gamma a) * X + C (xi a)) +
    C (kappa a d) ^ 2 * (X + C (a 6)) +
    (C (kappa a d) ^ 2 + C (gamma a) * C (kappa a d) + C d) *
      (X + C (a 8 + a 9 + a 10 + a 11)) + C (cross a (kappa a d) (sigma a d)) +
      C d * (X + C (a 15)) = _
  rw [linear_cancel, ← hs]
  simp only [rowEight, map_add, map_mul, map_pow]

private theorem product_change (p q g d : R[X]) :
    (p + d) * (q + d * g) = p * q + (d * (q + p * g) + d ^ 2 * g) := by ring

private theorem shift_sum (u c v : R[X]) : u + v + c = (u + c) + v := by
  simp only [add_assoc, add_comm, add_left_comm]

private theorem inner_shift (x v c d : R[X]) : x + (v + d) + c = (x + v + c) + d := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem r_change (a : ℕ → R) (d : R) : r (shift16 a d) = r a + rDelta a d := by
  change (X + t a + C (a 12 + d)) * (u (shift16 a d) + C (a 13)) = _
  rw [add_constant, u_change, shift_sum (u a) (C (a 13)) (C d * G a)]
  exact product_change (rLeft a) (u a + C (a 13)) (G a) (C d)

theorem ell_change (a : ℕ → R) (d : R) :
    ell (shift16 a d) = ell a + C (kappa a d) * (ellLinear a * L a) := by
  change ellLinear a * (z a + v (shift16 a d) + C (a 17)) = _
  rw [v_change]
  have hr : z a + (v a + C (kappa a d) * L a) + C (a 17) =
      (z a + v a + C (a 17)) + C (kappa a d) * L a := by
    exact inner_shift _ _ _ _
  rw [hr, mul_add, ← mul_assoc, mul_comm (ellLinear a) (C (kappa a d)), mul_assoc]
  rfl

private theorem head_regroup (y v w s r g : R[X]) :
    y + v + w + s + r + g = y + v + ((w + s) + g) + r := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem head_grouped (a : ℕ → R) : head a = y + v a + (W a + g a) + r a :=
  head_regroup y (v a) (w a) (s a) (r a) (g a)

theorem crown_grouped (a : ℕ → R) :
    crownRight a = (X + y + z a) + (W a + g a) + ell a := by
  change X + y + z a + w a + s a + g a + ell a = _
  simp only [W, add_assoc]

private theorem add_three (y v w r dv dw dr : R[X]) :
    y + (v + dv) + (w + dw) + (r + dr) = (y + v + w + r) + (dv + dw + dr) := by
  simp only [add_assoc, add_comm, add_left_comm]

private theorem add_two (x w l dw dl : R[X]) :
    x + (w + dw) + (l + dl) = (x + w + l) + (dw + dl) := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem head_change (a : ℕ → R) (d : R) : head (shift16 a d) = head a +
    (C (kappa a d) * L a + K a d + rDelta a d) := by
  rw [head_grouped, head_grouped, v_change, Wg_change, r_change]
  exact add_three _ _ _ _ _ _ _

theorem crown_change (a : ℕ → R) (d : R) : crownRight (shift16 a d) = crownRight a +
    (K a d + C (kappa a d) * (ellLinear a * L a)) := by
  rw [crown_grouped, crown_grouped, Wg_change, ell_change]
  exact add_two _ _ _ _ _

private theorem output_transport (h f u c r j t o dh du dr : R[X]) :
    (h + dh) + f * ((u + du) + c * ((r + dr) + j) + t) + o =
    (h + f * (u + c * (r + j) + t) + o) + (dh + f * du + (f * c) * dr) := by ring

theorem output_change (a : ℕ → R) (d : R) : output (shift16 a d) = output a +
    ((C (kappa a d) * L a + K a d + rDelta a d) + lastFactor a * (C d * G a) +
      D a * C (rowEight a d)) := by
  change head (shift16 a d) + lastFactor a *
    (u (shift16 a d) + crownLeft a * (crownRight (shift16 a d) + C (a 19)) + C (a 21)) + C (a 22) = _
  rw [head_change, u_change, crown_change, output_transport, scalar_column]
  rfl

theorem slope_sum (a : ℕ → R) : u a + rLeft a * G a + lastFactor a * G a = sixSlope a := by
  have hsum : H a + rLeft a + lastFactor a = X + C (a 5) + C (a 12) + C (a 20) := by
    change (z a + t a + C (a 5)) + (X + t a + C (a 12)) + (z a + C (a 20)) = _
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero, add_zero, zero_add]
  rw [Char2Degree23HighFrame.u_eq, mul_comm (rLeft a) (G a), mul_comm (lastFactor a) (G a),
    ← mul_add, ← mul_add, hsum]
  rfl

private theorem residual_collect (k L K d u c r g f D t : R[X]) :
    ((k * L + K + (d * (u + c + r * g) + d ^ 2 * g)) + f * (d * g) + D * t) =
      D * t + (d * (u + r * g + f * g) + (d ^ 2 * g + k * L + K + d * c)) := by ring

theorem raw_difference (a : ℕ → R) (d : R) :
    output (shift16 a d) + output a = D a * C (rowEight a d) + low a d := by
  rw [output_change, cancel_tail]
  unfold rDelta
  rw [residual_collect, slope_sum]
  rfl

private theorem C_le (c : R) (n : ℕ) : (C c).natDegree ≤ n := by rw [natDegree_C]; omega

theorem N_degree (a : ℕ → R) : (N a).natDegree ≤ 2 := by
  have hlin : (X + C (a 7) + C (a 8) + C (a 10)).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (isMonicOfDegree_X_add_one (a 7)).natDegree_eq.le (C_le _ _)) (C_le _ _)
  have h1 : (L a * (X + C (a 7) + C (a 8) + C (a 10))).natDegree ≤ 2 :=
    natDegree_mul_le.trans (Nat.add_le_add (isMonicOfDegree_X_add_one (a 6)).natDegree_eq.le hlin)
  have h2 : ((X + C (a 2)) * C (a 3)).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans; rw [(isMonicOfDegree_X_add_one (a 2)).natDegree_eq, natDegree_C]; omega
  have h3 : (C (A a) * (X + C (a 8) + C (a 11))).natDegree ≤ 2 := by
    have hp := natDegree_add_le_of_degree_le (isMonicOfDegree_X_add_one (a 8)).natDegree_eq.le (C_le (a 11) 1)
    exact (natDegree_mul_le.trans (Nat.add_le_add (C_le (A a) 0) hp)).trans (by omega)
  have h4 : (C (B a) * C (a 9)).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans; rw [natDegree_C, natDegree_C]; omega
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 h2) (C_le _ _)) h3) h4

theorem K_degree (a : ℕ → R) (d : R) : (K a d).natDegree ≤ 2 := by
  have h1 : (C (kappa a d) * N a).natDegree ≤ 2 :=
    natDegree_mul_le.trans (Nat.add_le_add (C_le _ 0) (N_degree a))
  have hk : (C (kappa a d) ^ 2).natDegree ≤ 0 := by rw [← map_pow, natDegree_C]
  have h2 : (C (kappa a d) ^ 2 * L a).natDegree ≤ 2 :=
    (natDegree_mul_le.trans (Nat.add_le_add hk (isMonicOfDegree_X_add_one (a 6)).natDegree_eq.le)).trans (by omega)
  have h3 : (C (sigma a d) * lowLine a).natDegree ≤ 2 :=
    (natDegree_mul_le.trans (Nat.add_le_add (C_le _ 0) (lowLine_monic a).natDegree_eq.le)).trans (by omega)
  have h4 : (C d * (X + C (a 15))).natDegree ≤ 2 :=
    (natDegree_mul_le.trans (Nat.add_le_add (C_le _ 0) (isMonicOfDegree_X_add_one (a 15)).natDegree_eq.le)).trans (by omega)
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 h2) h3) (C_le _ _)) h4

theorem sixSlope_monic (a : ℕ → R) : IsMonicOfDegree (sixSlope a) 6 := by
  have hc (c : R) : (C c).natDegree < 1 := by rw [natDegree_C]; omega
  exact (G_monic a).mul (((isMonicOfDegree_X_add_one (a 5)).add_right (hc _)).add_right (hc _))

theorem residual_degree (a : ℕ → R) (d : R) : (residual a d).natDegree < 6 := by
  have hd : (C d ^ 2).natDegree ≤ 0 := by rw [← map_pow, natDegree_C]
  have h1 : (C d ^ 2 * G a).natDegree ≤ 5 :=
    natDegree_mul_le.trans (Nat.add_le_add hd (G_monic a).natDegree_eq.le)
  have h2 : (C (kappa a d) * L a).natDegree ≤ 5 :=
    (natDegree_mul_le.trans (Nat.add_le_add (C_le _ 0) (isMonicOfDegree_X_add_one (a 6)).natDegree_eq.le)).trans (by omega)
  have h3 : (K a d).natDegree ≤ 5 := (K_degree a d).trans (by omega)
  have h4 : (C d * C (a 13)).natDegree ≤ 5 := by
    apply natDegree_mul_le.trans; rw [natDegree_C, natDegree_C]; omega
  exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le h1 h2) h3) h4).trans_lt (by omega)

theorem low_degree (a : ℕ → R) (d : R) : (low a d).natDegree < 8 := by
  have hm : (C d * sixSlope a).natDegree ≤ 6 :=
    natDegree_mul_le.trans (Nat.add_le_add (C_le _ 0) (sixSlope_monic a).natDegree_eq.le)
  exact (natDegree_add_le_of_degree_le hm (residual_degree a d).le).trans_lt (by omega)

end FastPoly.Char2Degree23SixteenFrame
