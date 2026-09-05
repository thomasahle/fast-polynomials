import FastPoly.Examples.Char2Degree23TerminalRows
import FastPoly.Examples.Char2Degree23NormalizedPeel

/-!
# The actual two-row terminal column for q18 in degree23

The raw update changes only s, r and ell. After the explicit row-eight
column is removed, its residual is delta times a named quartic plus
delta squared. The quartic's two top rows are B+1 and B, so their sum
is a unit pivot. No degree-23 polynomial is expanded.
-/

namespace FastPoly.Char2Degree23EighteenFrame

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23LowFrame Char2Degree23TerminalRows Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift18 (a : ℕ → R) (d : R) : ℕ → R
  | 10 => a 10 + d
  | 11 => a 11 + d
  | 13 => a 13 + d
  | 16 => a 16 + d
  | i => a i

noncomputable def sSlope (a : ℕ → R) : R[X] :=
  z a + v a + C (a 10) + C (a 11)
noncomputable def ellSlope (a : ℕ → R) : R[X] := z a + v a + C (a 17)
noncomputable def low (a : ℕ → R) : R[X] := linear a + sSlope a

def rowEight (a : ℕ → R) (d : R) : R :=
  d * (a 10 + a 11 + a 17) + d ^ 2
def B (a : ℕ → R) : R := a 2 + a 6

theorem s_change (a : ℕ → R) (d : R) :
    s (shift18 a d) = s a + (C d * sSlope a + C (d ^ 2)) := by
  change (z a + C (a 10 + d)) * (v a + C (a 11 + d)) = _
  rw [Char2Degree23MiddleFrame.add_constant, Char2Degree23MiddleFrame.add_constant,
    both_factors, ← map_pow, add_assoc]
  have hs : (z a + C (a 10)) + (v a + C (a 11)) = sSlope a := by
    unfold sSlope
    ac_rfl
  rw [hs]
  rfl

theorem r_change (a : ℕ → R) (d : R) :
    r (shift18 a d) = r a + C d * linear a := by
  change linear a * (u a + C (a 13 + d)) = _
  rw [Char2Degree23MiddleFrame.add_constant, mul_add, mul_comm (linear a) (C d)]
  rfl

theorem ell_change (a : ℕ → R) (d : R) :
    ell (shift18 a d) = ell a + C d * ellSlope a := by
  change (X + C (a 16 + d)) * ellSlope a = _
  rw [Char2Degree23MiddleFrame.add_constant, add_mul]
  rfl

private theorem head_shift (y v w s r g ds dr : R[X]) :
    y + v + w + (s + ds) + (r + dr) + g =
      (y + v + w + s + r + g) + (ds + dr) := by ring

theorem head_change (a : ℕ → R) (d : R) :
    head (shift18 a d) = head a +
      ((C d * sSlope a + C (d ^ 2)) + C d * linear a) := by
  change y + v a + w a + s (shift18 a d) + r (shift18 a d) + g a = _
  rw [s_change, r_change]
  exact head_shift _ _ _ _ _ _ _ _

private theorem crown_shift (x y z w s g l ds dl : R[X]) :
    x + y + z + w + (s + ds) + g + (l + dl) =
      (x + y + z + w + s + g + l) + (ds + dl) := by ring

theorem crown_change (a : ℕ → R) (d : R) :
    crownRight (shift18 a d) = crownRight a +
      ((C d * sSlope a + C (d ^ 2)) + C d * ellSlope a) := by
  change X + y + z a + w a + s (shift18 a d) + g a + ell (shift18 a d) = _
  rw [s_change, ell_change]
  exact crown_shift _ _ _ _ _ _ _ _ _

private theorem collect (h f u l c k t o d s r e d2 : R[X]) :
    (h + ((d * s + d2) + d * r)) +
      f * (u + l * ((c + ((d * s + d2) + d * e)) + k) + t) + o =
    (h + f * (u + l * (c + k) + t) + o) +
      ((f * l) * (d * (s + e) + d2) + (d * (r + s) + d2)) := by ring

theorem slope_sum (a : ℕ → R) :
    sSlope a + ellSlope a = C (a 10 + a 11 + a 17) := by
  unfold sSlope ellSlope
  simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem output_change (a : ℕ → R) (d : R) :
    output (shift18 a d) = output a +
      (D a * C (rowEight a d) + (C d * low a + C (d ^ 2))) := by
  change head (shift18 a d) + lastFactor a *
    (u a + crownLeft a * (crownRight (shift18 a d) + C (a 19)) + C (a 21)) + C (a 22) = _
  rw [head_change, crown_change, collect, slope_sum]
  simp only [rowEight, map_add, map_mul]
  rfl

theorem raw_difference (a : ℕ → R) (d : R) :
    output (shift18 a d) + output a =
      D a * C (rowEight a d) + (C d * low a + C (d ^ 2)) := by
  rw [output_change, cancel_tail]

noncomputable def small (a : ℕ → R) : R[X] :=
  (X + C (a 2)) * C (a 3) + (X + C (a 6)) * C (a 7) +
    X + C (a 12 + a 10 + a 11)

private theorem low_collect (x z y a b c e k j l : R[X]) :
    (x + (x + a) * (z + c) + k) +
      (z + (x + b) * (y + z + e) + j + l) =
    (a + b + 1) * z + (x + b) * y +
      ((x + a) * c + (x + b) * e + x + (k + j + l)) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem low_shape (a : ℕ → R) :
    low a = C (B a + 1) * z a + (X + C (a 6)) * y + small a := by
  change (X + (X + C (a 2)) * (z a + C (a 3)) + C (a 12)) +
    (z a + (X + C (a 6)) * (y + z a + C (a 7)) + C (a 10) + C (a 11)) = _
  rw [low_collect]
  simp only [B, small, map_add, map_one]

private theorem C_le (c : R) (n : ℕ) : (C c).natDegree ≤ n := by
  rw [natDegree_C]
  exact Nat.zero_le _

theorem small_degree (a : ℕ → R) : (small a).natDegree ≤ 1 := by
  have h (b c : R) : ((X + C b) * C c).natDegree ≤ 1 := by
    apply natDegree_mul_le.trans
    rw [(isMonicOfDegree_X_add_one b).natDegree_eq, natDegree_C]
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (h _ _) (h _ _)) natDegree_X_le) (C_le _ _)

theorem cubic_monic (a : ℕ → R) : IsMonicOfDegree ((X + C (a 6)) * y) 3 :=
  (isMonicOfDegree_X_add_one (a 6)).mul y_monic

theorem low_degree (a : ℕ → R) : (low a).natDegree ≤ 4 := by
  rw [low_shape]
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      ((natDegree_C_mul_le _ _).trans (z_monic a).natDegree_eq.le)
      ((cubic_monic a).natDegree_eq.le.trans (by omega)))
    ((small_degree a).trans (by omega))

theorem low_four (a : ℕ → R) : (low a).coeff 4 = B a + 1 := by
  have hz : (z a).coeff 4 = 1 := by
    rw [← (z_monic a).natDegree_eq]
    exact (z_monic a).monic.coeff_natDegree
  have hc : ((X + C (a 6)) * y).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((cubic_monic a).natDegree_eq.trans_lt (by omega))
  have hs : (small a).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((small_degree a).trans_lt (by omega))
  rw [low_shape, coeff_add, coeff_add, coeff_C_mul, hz, hc, hs, mul_one, add_zero, add_zero]

theorem low_three (a : ℕ → R) : (low a).coeff 3 = B a := by
  have hc : ((X + C (a 6)) * y).coeff 3 = 1 := by
    rw [← (cubic_monic a).natDegree_eq]
    exact (cubic_monic a).monic.coeff_natDegree
  have hs : (small a).coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((small_degree a).trans_lt (by omega))
  rw [low_shape, coeff_add, coeff_add, coeff_C_mul, z_three, hc, hs, mul_one,
    add_zero, CharTwo.add_cancel_right]

end FastPoly.Char2Degree23EighteenFrame

