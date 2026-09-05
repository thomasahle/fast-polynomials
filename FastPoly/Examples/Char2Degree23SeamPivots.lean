import FastPoly.Examples.Char2Degree23SeamDifference

/-!
# The compensated degree-23 high pivots at rows seventeen, sixteen, and fifteen

The supplied raw shifts are checked through named factor cancellations.
No coefficient baseline or complete circuit is expanded.
-/

namespace FastPoly.Char2Degree23SeamPivots

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23HighFrame Char2Degree23HighDifference Char2Degree23SeamDifference
  Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift5 (a : ℕ → R) (delta : R) : ℕ → R
  | 3 => a 3 + delta
  | 4 => a 4 + delta
  | 18 => a 18 + delta
  | j => a j
def shift6 (a : ℕ → R) (delta : R) : ℕ → R
  | 3 => a 3 + delta
  | 4 => a 4 + delta
  | 20 => a 20 + delta
  | j => a j
def shift7 (a : ℕ → R) (delta : R) : ℕ → R
  | 4 => a 4 + delta
  | 14 => a 14 + delta
  | j => a j

noncomputable def J5 (a : ℕ → R) : R[X] :=
  (X + y + C (a 18)) * (linear a + 1) + y + C (a 4) + linear a * C (a 3)
noncomputable def J6 (a : ℕ → R) : R[X] :=
  C (a 20) * (linear a + 1) + y + C (a 4) + linear a * C (a 3)

omit [Nontrivial R] in
private theorem frame_cancel (b z l c y a : R[X]) :
    (b + z) * l + ((l * z + c) + y + a) = b * l + y + a + c := by
  rw [add_mul, mul_comm z l]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

omit [CharP R 2] [Nontrivial R] in
theorem G_linear (a : ℕ → R) :
    G a = (linear a + 1) * z a + linear a * C (a 3) + y + C (a 4) := by
  change h a + y + C (a 4) = _
  rw [Char2Degree23HighPivots.h_eq]
  rfl

theorem inner5 (a : ℕ → R) : crownLeft a * (linear a + 1) + G a = J5 a := by
  have hc : crownLeft a = (X + y + C (a 18)) + z a := by
    change X + y + z a + C (a 18) = _
    simp only [add_assoc, add_comm, add_left_comm]
  rw [hc, G_linear, frame_cancel]
  rfl

theorem inner6 (a : ℕ → R) : lastFactor a * (linear a + 1) + G a = J6 a := by
  have hf : lastFactor a = C (a 20) + z a := add_comm _ _
  rw [hf, G_linear, frame_cancel]
  rfl

theorem frame5 (a : ℕ → R) :
    D a * (linear a + 1) + lastFactor a * G a = lastFactor a * J5 a := by
  change (lastFactor a * crownLeft a) * (linear a + 1) + lastFactor a * G a = _
  rw [mul_assoc, ← mul_add, inner5]

theorem frame6 (a : ℕ → R) :
    D a * (linear a + 1) + crownLeft a * G a = crownLeft a * J6 a := by
  change (lastFactor a * crownLeft a) * (linear a + 1) + crownLeft a * G a = _
  rw [mul_comm (lastFactor a) (crownLeft a), mul_assoc, ← mul_add, inner6]

omit [CharP R 2] in
theorem J5_monic (a : ℕ → R) : IsMonicOfDegree (J5 a) 3 := by
  have hc (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
    rw [natDegree_C]
    exact hn
  have hb : IsMonicOfDegree ((X : R[X]) + y + C (a 18)) 2 :=
    x_add_y_monic.add_right (hc _ 2 (by omega))
  have hl : (linear a * C (a 3)).natDegree < 3 := by
    apply natDegree_mul_le.trans_lt
    rw [(linear_monic a).natDegree_eq, natDegree_C]
    omega
  exact (((hb.mul (linear_one_monic a)).add_right
    (y_monic.natDegree_eq.trans_lt (by omega))).add_right (hc _ 3 (by omega))).add_right hl

omit [CharP R 2] in
theorem J6_monic (a : ℕ → R) : IsMonicOfDegree (J6 a) 2 := by
  have hfirst : (C (a 20) * (linear a + 1)).natDegree < 2 := by
    apply natDegree_mul_le.trans_lt
    rw [natDegree_C, (linear_one_monic a).natDegree_eq]
    omega
  have hc : (C (a 4)).natDegree < 2 := by rw [natDegree_C]; omega
  have hl : (linear a * C (a 3)).natDegree < 2 := by
    apply natDegree_mul_le.trans_lt
    rw [(linear_monic a).natDegree_eq, natDegree_C]
    omega
  exact ((y_monic.add_left hfirst).add_right hc).add_right hl

theorem D_shift5 (a : ℕ → R) (delta : R) :
    D (shift5 a delta) = D a + C delta * lastFactor a := by
  have hc : crownLeft (shift5 a delta) = crownLeft a + C delta := by
    change X + y + z a + C (a 18 + delta) = (X + y + z a + C (a 18)) + C delta
    rw [map_add, ← add_assoc]
  change lastFactor a * crownLeft (shift5 a delta) = _
  rw [hc, mul_add, mul_comm _ (C delta)]
  rfl

theorem D_shift6 (a : ℕ → R) (delta : R) :
    D (shift6 a delta) = D a + C delta * crownLeft a := by
  have hf : lastFactor (shift6 a delta) = lastFactor a + C delta := by
    change z a + C (a 20 + delta) = (z a + C (a 20)) + C delta
    rw [map_add, ← add_assoc]
  change lastFactor (shift6 a delta) * crownLeft a = _
  rw [hf, add_mul]
  rfl

theorem shift5_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift5 a delta)) 17 delta :=
  seam_output_unit a _ _ _ 3 delta (lastFactor_monic a) (J5_monic a) (by omega)
    (D_shift5 a delta) (Char2Degree23HighPivots.h_shift3 a delta)
    rfl rfl rfl (frame5 a)

theorem shift6_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift6 a delta)) 16 delta :=
  seam_output_unit a _ _ _ 2 delta (crownLeft_monic a) (J6_monic a) (by omega)
    (D_shift6 a delta) (Char2Degree23HighPivots.h_shift3 a delta)
    rfl rfl rfl (frame6 a)

omit [CharP R 2] [Nontrivial R] in
private theorem double_high (d e g h c : R[X]) :
    d * ((e + c) * ((g + c) * h)) =
      d * (e * (g * h)) + c * (d * ((e + g) * h)) + c ^ 2 * (d * h) := by
  ring

theorem E_add_G (a : ℕ → R) : E a + G a = y + C (a 14) + C (a 4) := by
  change (h a + C (a 14)) + (h a + y + C (a 4)) = _
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem high_shift7 (a : ℕ → R) (delta : R) :
    high (shift7 a delta) = high a +
      (C delta * (D a * ((y + C (a 14) + C (a 4)) * H a)) +
        C (delta ^ 2) * (D a * H a)) := by
  have he : E (shift7 a delta) = E a + C delta := by
    change h a + C (a 14 + delta) = (h a + C (a 14)) + C delta
    rw [map_add, ← add_assoc]
  have hg : G (shift7 a delta) = G a + C delta := by
    change h a + y + C (a 4 + delta) = (h a + y + C (a 4)) + C delta
    rw [map_add, ← add_assoc]
  change D a * (E (shift7 a delta) * (G (shift7 a delta) * H a)) = _
  rw [he, hg, double_high, E_add_G]
  change high a + C delta * (D a * ((y + C (a 14) + C (a 4)) * H a)) +
    (C delta) ^ 2 * (D a * H a) = _
  simp only [map_pow, add_assoc]

theorem shift7_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift7 a delta)) 15 delta := by
  have hc (c : R) : (C c).natDegree < 2 := by rw [natDegree_C]; omega
  have hs : IsMonicOfDegree (D a * ((y + C (a 14) + C (a 4)) * H a)) 15 :=
    (D_monic a).mul (((y_monic.add_right (hc _)).add_right (hc _)).mul (H_monic a))
  have ht : (C (delta ^ 2) * (D a * H a)).natDegree < 15 := by
    apply natDegree_mul_le.trans_lt
    rw [natDegree_C, ((D_monic a).mul (H_monic a)).natDegree_eq]
    omega
  exact output_unit (Char2Degree19InnerChanges.unit_difference_of_lower
    _ _ _ _ 15 delta hs ht (high_shift7 a delta)) (by omega)

end FastPoly.Char2Degree23SeamPivots
