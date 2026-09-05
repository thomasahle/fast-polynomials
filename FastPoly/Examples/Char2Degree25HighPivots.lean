import FastPoly.Examples.Char2Degree25HighDifference

/-! The first five raw pivots of the existing degree-twenty-five verifier.
The shifts are a2; a0; (a0,a1); a3; a4, in rows 24 through 20.
All quintic factors remain named throughout the telescope. -/

namespace FastPoly.Char2Degree25HighPivots

open Polynomial Char2Degree23RowEight Char2Degree23Frame
  Char2Degree25Frame Char2Degree25HighFrame Char2Degree25HighDifference
  Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift0 (a : ℕ → R) (delta : R) : ℕ → R
  | 2 => a 2 + delta
  | j => a j
def shift1 (a : ℕ → R) (delta : R) : ℕ → R
  | 0 => a 0 + delta
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

private theorem moving_one (p t c d : R[X]) :
    p + (t + d) + c = (p + t + c) + d := by ac_rfl
private theorem moving_two (p z t c d e : R[X]) :
    p + (z + e) + (t + d) + c = (p + z + t + c) + (d + e) := by ac_rfl
private theorem moving_two_plain (z t c d e : R[X]) :
    (z + e) + (t + d) + c = (z + t + c) + (d + e) := by ac_rfl

/-- Only five scalar slots besides t and z enter the five high factors. -/
theorem from_t_z_change (a b : ℕ → R) (slope e : R[X]) (k : ℕ) (delta : R)
    (hs : IsMonicOfDegree slope k) (he : e.natDegree < k)
    (ht : t b = t a + C delta * slope) (hz : z b = z a + e)
    (h4 : b 4 = a 4) (h5 : b 5 = a 5) (h12 : b 12 = a 12)
    (h18 : b 18 = a 18) (h23 : b 23 = a 23) :
    UnitDifference (Char2Degree25Frame.output a) (Char2Degree25Frame.output b) (k + 20) delta := by
  have hn : nRight b = nRight a + C delta * slope := by
    change t b + C (b 23) = _
    rw [ht, h23, add_right_comm]
    rfl
  have hh : hLeft b = hLeft a + (C delta * slope + e) := by
    change y + z b + t b + C (b 18) = _
    rw [hz, ht, h18]
    exact moving_two y (z a) (t a) (C (a 18)) (C delta * slope) e
  have hr : rLeft b = rLeft a + C delta * slope := by
    change X + t b + C (b 12) = _
    rw [ht, h12]
    exact moving_one X (t a) (C (a 12)) (C delta * slope)
  have hl : uLeft b = uLeft a + (C delta * slope + e) := by
    change y + z b + t b + C (b 4) = _
    rw [hz, ht, h4]
    exact moving_two y (z a) (t a) (C (a 4)) (C delta * slope) e
  have hu : uRight b = uRight a + (C delta * slope + e) := by
    change z b + t b + C (b 5) = _
    rw [hz, ht, h5]
    exact moving_two_plain (z a) (t a) (C (a 5)) (C delta * slope) e
  exact unit_from_common_change a b slope e k delta hs he hn hh hr hl hu

private theorem translated_t (l z c d s : R[X]) :
    l * ((z + d * s) + c) = l * (z + c) + d * (l * s) := by ring

theorem t_change_z (a b : ℕ → R) (slope : R[X]) (delta : R)
    (hz : z b = z a + C delta * slope) (h2 : b 2 = a 2) (h3 : b 3 = a 3) :
    t b = t a + C delta * ((X + C (a 2)) * slope) := by
  change (X + C (b 2)) * (z b + C (b 3)) = _
  rw [h2, h3, hz]
  exact translated_t (X + C (a 2)) (z a) (C (a 3)) (C delta) slope

private theorem scaled_degree (delta : R) {slope : R[X]} {k : ℕ}
    (hs : IsMonicOfDegree slope k) : (C delta * slope).natDegree ≤ k := by
  apply natDegree_mul_le.trans
  rw [natDegree_C, hs.natDegree_eq, Nat.zero_add]

theorem t_shift0 (a : ℕ → R) (delta : R) :
    t (shift0 a delta) = t a + C delta * (z a + C (a 3)) := by
  change (X + C (a 2 + delta)) * (z a + C (a 3)) = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

theorem shift0_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift0 a delta)) 24 delta := by
  have hc : (C (a 3) : R[X]).natDegree < 4 := by rw [natDegree_C]; omega
  apply from_t_z_change a (shift0 a delta) (z a + C (a 3)) 0 4 delta
    ((z_monic a).add_right hc) (by rw [natDegree_zero]; omega) (t_shift0 a delta)
    ?_ rfl rfl rfl rfl rfl
  rw [add_zero]
  rfl

theorem z_shift1 (a : ℕ → R) (delta : R) :
    z (shift1 a delta) = z a + C delta * (X + y + C (a 1)) := by
  change (y + C (a 0 + delta)) * (X + y + C (a 1)) = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

theorem shift1_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift1 a delta)) 23 delta := by
  have hc : (C (a 1) : R[X]).natDegree < 2 := by rw [natDegree_C]; omega
  have hz : IsMonicOfDegree (X + y + C (a 1)) 2 := x_add_y_monic.add_right hc
  have hs : IsMonicOfDegree ((X + C (a 2)) * (X + y + C (a 1))) 3 :=
    (isMonicOfDegree_X_add_one (a 2)).mul hz
  exact from_t_z_change a (shift1 a delta)
    ((X + C (a 2)) * (X + y + C (a 1))) (C delta * (X + y + C (a 1))) 3 delta hs
    ((scaled_degree delta hz).trans_lt (by omega))
    (t_change_z a _ _ delta (z_shift1 a delta) rfl rfl) (z_shift1 a delta)
    rfl rfl rfl rfl rfl

private theorem square_head_change (x y a b d : R[X]) :
    (y + (a + d)) * (x + y + (b + d)) =
      (y + a) * (x + y + b) + d * (x + (a + b + d)) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem z_shift2 (a : ℕ → R) (delta : R) :
    z (shift2 a delta) = z a + C delta * (X + C (a 0 + a 1 + delta)) := by
  change (y + C (a 0 + delta)) * (X + y + C (a 1 + delta)) = _
  unfold z
  simp only [map_add]
  exact square_head_change X y (C (a 0)) (C (a 1)) (C delta)

theorem shift2_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift2 a delta)) 22 delta := by
  have hz := isMonicOfDegree_X_add_one (a 0 + a 1 + delta)
  have hs : IsMonicOfDegree ((X + C (a 2)) * (X + C (a 0 + a 1 + delta))) 2 :=
    (isMonicOfDegree_X_add_one (a 2)).mul hz
  exact from_t_z_change a (shift2 a delta)
    ((X + C (a 2)) * (X + C (a 0 + a 1 + delta))) (C delta * (X + C (a 0 + a 1 + delta)))
    2 delta hs ((scaled_degree delta hz).trans_lt (by omega))
    (t_change_z a _ _ delta (z_shift2 a delta) rfl rfl) (z_shift2 a delta)
    rfl rfl rfl rfl rfl

theorem t_shift3 (a : ℕ → R) (delta : R) :
    t (shift3 a delta) = t a + C delta * (X + C (a 2)) := by
  change (X + C (a 2)) * (z a + C (a 3 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]
  rfl

theorem shift3_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift3 a delta)) 21 delta := by
  apply from_t_z_change a (shift3 a delta) (X + C (a 2)) 0 1 delta
    (isMonicOfDegree_X_add_one (a 2)) (by rw [natDegree_zero]; omega) (t_shift3 a delta)
    ?_ rfl rfl rfl rfl rfl
  rw [add_zero]
  rfl

theorem uLeft_shift4 (a : ℕ → R) (delta : R) :
    uLeft (shift4 a delta) = uLeft a + C delta := by
  change y + z a + t a + C (a 4 + delta) = _
  rw [map_add, ← add_assoc]
  rfl

theorem shift4_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift4 a delta)) 20 delta :=
  unit_from_uLeft_change a (shift4 a delta) delta rfl rfl rfl (uLeft_shift4 a delta) rfl

end FastPoly.Char2Degree25HighPivots

