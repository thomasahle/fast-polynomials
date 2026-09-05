import FastPoly.Examples.Char2Degree23HighDifference

/-!
# The first five supplied degree-23 high pivots

These simple raw shifts certify rows 22 through 18 of the high frame.
The normalized coordinate change also changes some low offsets; transporting
these certificates to that change only requires equality of the nine raw
slots read by the high frame. No coefficient baseline is expanded.
-/

namespace FastPoly.Char2Degree23HighPivots

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23HighFrame Char2Degree23HighDifference Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift0 (a : ℕ → R) (delta : R) : ℕ → R
  | 2 => a 2 + delta
  | j => a j
def shift1 (a : ℕ → R) (delta : R) : ℕ → R
  | 1 => a 1 + delta
  | j => a j
def shift2 (a : ℕ → R) (delta : R) : ℕ → R
  | 0 => a 0 + delta
  | 1 => a 1 + delta
  | j => a j
def shift3 (a : ℕ → R) (delta : R) : ℕ → R
  | 3 => a 3 + delta
  | j => a j
def shift4 (a : ℕ → R) (delta : R) : ℕ → R
  | 4 => a 4 + delta
  | j => a j

omit [CharP R 2] [Nontrivial R] in
private theorem add_offset (p d c : R[X]) : (p + d) + c = (p + c) + d := by
  simp only [add_assoc, add_comm, add_left_comm]

/-- Only three constant offsets besides `h` enter the quintic factors. -/
theorem from_h_change (a b : ℕ → R) (slope : R[X]) (k : ℕ) (delta : R)
    (hs : IsMonicOfDegree slope k) (hk : k < 5)
    (hh : h b = h a + C delta * slope)
    (h4 : b 4 = a 4) (h5 : b 5 = a 5) (h14 : b 14 = a 14)
    (hd : (D b + D a).natDegree ≤ k + 2) :
    UnitDifference (output a) (output b) (18 + k) delta := by
  have he : E b = E a + C delta * slope := by
    change h b + C (b 14) = _
    rw [h14, hh, add_offset]
    rfl
  have hg : G b = G a + C delta * slope := by
    change h b + y + C (b 4) = _
    rw [h4, hh, add_offset (h a) (C delta * slope) y,
      add_offset (h a + y) (C delta * slope) (C (a 4))]
    rfl
  have hh' : H b = H a + C delta * slope := by
    change h b + C (b 5) = _
    rw [h5, hh, add_offset]
    rfl
  exact common_output_unit a b slope k delta hs hk he hg hh' hd

omit [CharP R 2] [Nontrivial R] in
private theorem linear_form (z l c : R[X]) : z + l * (z + c) = (l + 1) * z + l * c := by
  ring

omit [CharP R 2] [Nontrivial R] in
theorem h_eq (a : ℕ → R) :
    h a = (X + C (a 2) + 1) * z a + (X + C (a 2)) * C (a 3) :=
  linear_form (z a) (X + C (a 2)) (C (a 3))

omit [CharP R 2] [Nontrivial R] in
theorem h_change_z (a b : ℕ → R) (slope : R[X]) (delta : R)
    (hz : z b = z a + C delta * slope) (h2 : b 2 = a 2) (h3 : b 3 = a 3) :
    h b = h a + C delta * ((X + C (a 2) + 1) * slope) := by
  rw [h_eq b, h_eq a, h2, h3, hz, mul_add, mul_left_comm _ (C delta), add_offset]

noncomputable def frameSum (a : ℕ → R) : R[X] := X + y + C (a 20) + C (a 18)

omit [Nontrivial R] in
theorem frame_sum (a : ℕ → R) : lastFactor a + crownLeft a = frameSum a := by
  change (z a + C (a 20)) + (X + y + z a + C (a 18)) = _
  unfold frameSum
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

omit [CharP R 2] in
theorem frameSum_monic (a : ℕ → R) : IsMonicOfDegree (frameSum a) 2 := by
  have hc (c : R) : (C c).natDegree < 2 := by rw [natDegree_C]; omega
  exact (x_add_y_monic.add_right (hc _)).add_right (hc _)

/-- The two quartic factors share `z`; their leading changes cancel. -/
theorem D_change_z_degree (a b : ℕ → R) (d : R[X]) (k : ℕ)
    (hz : z b = z a + d) (h18 : b 18 = a 18) (h20 : b 20 = a 20)
    (hd : d.natDegree ≤ k) :
    (D b + D a).natDegree ≤ max (k + 2) (2 * k) := by
  have hl : lastFactor b = lastFactor a + d := by
    change z b + C (b 20) = _
    rw [h20, hz, add_offset]
    rfl
  have hr : crownLeft b = crownLeft a + d := by
    change X + y + z b + C (b 18) = _
    rw [h18, hz]
    change X + y + (z a + d) + C (a 18) = (X + y + z a + C (a 18)) + d
    simp only [add_assoc, add_comm, add_left_comm]
  have he : D b + D a = d * frameSum a + d ^ 2 := by
    change lastFactor b * crownLeft b + lastFactor a * crownLeft a = _
    rw [hl, hr, both_factors,
      add_assoc (lastFactor a * crownLeft a) (d * (lastFactor a + crownLeft a)) (d ^ 2),
      cancel_tail, frame_sum]
  have hm : (d * frameSum a).natDegree ≤ k + 2 :=
    natDegree_mul_le.trans (Nat.add_le_add hd (frameSum_monic a).natDegree_eq.le)
  have hp : (d ^ 2).natDegree ≤ 2 * k :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hd)
  rw [he]
  exact (natDegree_add_le _ _).trans (max_le_max hm hp)

omit [CharP R 2] [Nontrivial R] in
private theorem scaled_degree (delta : R) {slope : R[X]} {k : ℕ}
    (hs : IsMonicOfDegree slope k) : (C delta * slope).natDegree ≤ k := by
  apply natDegree_mul_le.trans
  rw [natDegree_C, hs.natDegree_eq, Nat.zero_add]

theorem h_shift0 (a : ℕ → R) (delta : R) :
    h (shift0 a delta) = h a + C delta * (z a + C (a 3)) := by
  change z a + (X + C (a 2 + delta)) * (z a + C (a 3)) = _
  rw [map_add, ← add_assoc (X : R[X]), add_mul, ← add_assoc]
  rfl

theorem shift0_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift0 a delta)) 22 delta := by
  have hc : (C (a 3)).natDegree < 4 := by rw [natDegree_C]; omega
  have hs := (z_monic a).add_right hc
  have hd : (D (shift0 a delta) + D a).natDegree ≤ 6 := by
    change (D a + D a).natDegree ≤ 6
    rw [CharTwo.add_self_eq_zero, natDegree_zero]
    omega
  exact from_h_change a _ _ 4 delta hs (by omega) (h_shift0 a delta) rfl rfl rfl hd

theorem z_shift1 (a : ℕ → R) (delta : R) :
    z (shift1 a delta) = z a + C delta * (y + C (a 0)) := by
  change (y + C (a 0)) * (X + y + C (a 1 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]
  rfl

theorem shift1_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift1 a delta)) 21 delta := by
  have hc (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
    rw [natDegree_C]
    exact hn
  have hy : IsMonicOfDegree (y + C (a 0)) 2 := y_monic.add_right (hc _ 2 (by omega))
  have hl : IsMonicOfDegree ((X : R[X]) + C (a 2) + 1) 1 :=
    (isMonicOfDegree_X_add_one (a 2)).add_right (by rw [natDegree_one]; omega)
  have hd := D_change_z_degree a (shift1 a delta) _ 2 (z_shift1 a delta) rfl rfl
    (scaled_degree delta hy)
  exact from_h_change a _ _ 3 delta (hl.mul hy) (by omega)
    (h_change_z a _ _ delta (z_shift1 a delta) rfl rfl) rfl rfl rfl
    (hd.trans (by omega))

private theorem low_factor_sum (y x c d : R[X]) : (y + c) + (x + y + d) = x + c + d := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem z_shift2 (a : ℕ → R) (delta : R) :
    z (shift2 a delta) = z a + C delta * (X + C (a 0) + C (a 1) + C delta) := by
  change (y + C (a 0 + delta)) * (X + y + C (a 1 + delta)) = _
  rw [map_add, map_add, ← add_assoc, ← add_assoc, both_factors,
    low_factor_sum, pow_two, add_assoc, ← mul_add]
  rfl

theorem shift2_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift2 a delta)) 20 delta := by
  have hc (c : R) : (C c).natDegree < 1 := by rw [natDegree_C]; omega
  have hs : IsMonicOfDegree ((X : R[X]) + C (a 0) + C (a 1) + C delta) 1 :=
    ((isMonicOfDegree_X_add_one (a 0)).add_right (hc _)).add_right (hc _)
  have hl : IsMonicOfDegree ((X : R[X]) + C (a 2) + 1) 1 :=
    (isMonicOfDegree_X_add_one (a 2)).add_right (by rw [natDegree_one]; omega)
  have hd := D_change_z_degree a (shift2 a delta) _ 1 (z_shift2 a delta) rfl rfl
    (scaled_degree delta hs)
  exact from_h_change a _ _ 2 delta (hl.mul hs) (by omega)
    (h_change_z a _ _ delta (z_shift2 a delta) rfl rfl) rfl rfl rfl
    (hd.trans (by omega))

theorem h_shift3 (a : ℕ → R) (delta : R) :
    h (shift3 a delta) = h a + C delta * (X + C (a 2)) := by
  change z a + (X + C (a 2)) * (z a + C (a 3 + delta)) = _
  rw [map_add, ← add_assoc (z a), mul_add, mul_comm _ (C delta), ← add_assoc]
  rfl

theorem shift3_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift3 a delta)) 19 delta := by
  have hd : (D (shift3 a delta) + D a).natDegree ≤ 3 := by
    change (D a + D a).natDegree ≤ 3
    rw [CharTwo.add_self_eq_zero, natDegree_zero]
    omega
  exact from_h_change a _ _ 1 delta (isMonicOfDegree_X_add_one (a 2)) (by omega)
    (h_shift3 a delta) rfl rfl rfl hd

theorem G_shift4 (a : ℕ → R) (delta : R) : G (shift4 a delta) = G a + C delta := by
  change h a + y + C (a 4 + delta) = (h a + y + C (a 4)) + C delta
  rw [map_add, ← add_assoc]

theorem high_shift4 (a : ℕ → R) (delta : R) :
    high (shift4 a delta) = high a + C delta * (D a * (E a * H a)) := by
  change D a * (E a * (G (shift4 a delta) * H a)) = _
  rw [G_shift4, add_mul, mul_add, mul_add,
    mul_left_comm (E a) (C delta), mul_left_comm (D a) (C delta)]
  rfl

theorem shift4_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift4 a delta)) 18 delta := by
  apply output_unit _ (by omega)
  rw [high_shift4]
  exact Char2Degree21Frame.difference_scaled delta ((D_monic a).mul ((E_monic a).mul (H_monic a)))

end FastPoly.Char2Degree23HighPivots
