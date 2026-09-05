import FastPoly.Examples.Char2Degree23MiddleFrame

/-!
# Six explicit middle pivots of the supplied degree-23 circuit

The shared-wire slopes have degrees six through one. Multiplication by
`D+1` gives the output pivots fourteen through nine; all other changes
are bounded before coefficients are read. These are the raw updates,
with the named scalar correction supplied by the existing key map.
-/

namespace FastPoly.Char2Degree23MiddlePivots

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23Cancellations Char2Degree23HighFrame Char2Degree23MiddleFrame
  Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def eta (a : ℕ → R) : R := a 14 * a 5 + a 15
def correction (a : ℕ → R) (delta : R) : R := delta * eta a
def shift8 (a : ℕ → R) (delta : R) : ℕ → R :=
  offset11 (offset6 a delta) (correction a delta)
def shift9 (a : ℕ → R) (delta : R) : ℕ → R :=
  offset8 (commonOffsets a (correction a delta)) delta
def shift10 (a : ℕ → R) (delta : R) : ℕ → R := offset9 a delta
def shift11 (a : ℕ → R) (delta : R) : ℕ → R :=
  offset7 (commonOffsets a (correction a delta)) delta
def shift12 (a : ℕ → R) (delta : R) : ℕ → R := offset10 (offset8 a delta) delta
def shift13 (a : ℕ → R) (delta : R) : ℕ → R := commonOffsets a delta

private theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

private theorem scaled_degree (c : R) {p : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) : (C c * p).natDegree ≤ n := by
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add]
  exact hp

private theorem v_change_bound (a : ℕ → R) (p : R[X]) (n k : ℕ) (delta : R)
    (hp : p.natDegree ≤ n) (h : 9 + n < 8 + k) :
    (vFactor a * ((v a + C delta * p) + v a)).natDegree < 8 + k := by
  rw [cancel_tail]
  apply natDegree_mul_le.trans_lt
  have hs := scaled_degree delta hp
  rw [(vFactor_monic a).natDegree_eq]
  omega

theorem W_shift8 (a : ℕ → R) (delta : R) :
    W (shift8 a delta) = W a +
      (C delta * ((y + z a + C (a 7)) * wSlope a) +
        C (correction a delta) * (z a + C (a 10))) := by
  rw [shift8, W_offset11, W_offset6]
  change (W a + C delta * ((y + z a + C (a 7)) * wSlope a)) +
    C (correction a delta) * (z a + C (a 10)) = _
  rw [add_assoc]

theorem shift8_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift8 a delta)) 14 delta := by
  have hs : IsMonicOfDegree (y + z a + C (a 7)) 4 :=
    (y_add_z_monic a).add_right (C_lt _ _ (by omega))
  have ht : (C (correction a delta) * (z a + C (a 10))).natDegree < 6 :=
    (scaled_degree _ ((z_monic a).add_right (C_lt _ _ (by omega))).natDegree_eq.le).trans_lt
      (by omega)
  have hw := Char2Degree19InnerChanges.unit_difference_of_lower _ _ _ _ 6 delta
    (hs.mul (wSlope_monic a)) ht (W_shift8 a delta)
  apply middle_unit a (shift8 a delta) 6 delta (by omega) rfl rfl rfl hw
  have hv : v (shift8 a delta) = v a + C delta * (y + z a + C (a 7)) :=
    v_offset6 a delta
  rw [hv]
  exact v_change_bound a _ 4 6 delta hs.natDegree_eq.le (by omega)

theorem W_shift9 (a : ℕ → R) (delta : R) :
    W (shift9 a delta) = W a +
      (C delta * (y + v a + C (a 9 + correction a delta)) +
        C (correction a delta) * lowLine a) := by
  rw [shift9, W_offset8, W_commonOffsets]
  change (W a + C (correction a delta) * lowLine a) +
    C delta * (y + v a + C (a 9 + correction a delta)) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem shift9_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift9 a delta)) 13 delta := by
  have hs : IsMonicOfDegree (y + v a + C (a 9 + correction a delta)) 5 :=
    ((v_monic a).add_left (y_monic.natDegree_eq.trans_lt (by omega))).add_right
      (C_lt _ _ (by omega))
  have ht : (C (correction a delta) * lowLine a).natDegree < 5 :=
    (scaled_degree _ (lowLine_monic a).natDegree_eq.le).trans_lt (by omega)
  exact middle_unit_fixed_v a (shift9 a delta) 5 delta (by omega) rfl rfl rfl rfl
    (Char2Degree19InnerChanges.unit_difference_of_lower _ _ _ _ 5 delta hs ht (W_shift9 a delta))

theorem shift10_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift10 a delta)) 12 delta := by
  apply middle_unit_fixed_v a (shift10 a delta) 4 delta (by omega) rfl rfl rfl rfl
  rw [shift10, W_offset9]
  exact Char2Degree21Frame.difference_scaled delta (wLeft_monic a)

theorem W_shift11 (a : ℕ → R) (delta : R) :
    W (shift11 a delta) = W a +
      (C delta * ((X + C (a 6)) * wSlope a) +
        C (correction a delta) * lowLine a) := by
  rw [shift11, W_offset7, W_commonOffsets, wSlope_commonOffsets]
  change (W a + C (correction a delta) * lowLine a) +
    C delta * ((X + C (a 6)) * wSlope a) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem shift11_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift11 a delta)) 11 delta := by
  have hs : IsMonicOfDegree ((X + C (a 6)) * wSlope a) 3 :=
    (isMonicOfDegree_X_add_one (a 6)).mul (wSlope_monic a)
  have ht : (C (correction a delta) * lowLine a).natDegree < 3 :=
    (scaled_degree _ (lowLine_monic a).natDegree_eq.le).trans_lt (by omega)
  have hw := Char2Degree19InnerChanges.unit_difference_of_lower _ _ _ _ 3 delta hs ht
    (W_shift11 a delta)
  apply middle_unit a (shift11 a delta) 3 delta (by omega) rfl rfl rfl hw
  have hv : v (shift11 a delta) = v a + C delta * (X + C (a 6)) :=
    v_offset7 (commonOffsets a (correction a delta)) delta
  rw [hv]
  exact v_change_bound a _ 1 3 delta (isMonicOfDegree_X_add_one (a 6)).natDegree_eq.le
    (by omega)

theorem W_shift12 (a : ℕ → R) (delta : R) :
    W (shift12 a delta) = W a + C delta * (y + C (a 9) + C (a 11)) := by
  rw [shift12, W_offset10, W_offset8]
  change (W a + C delta * (y + v a + C (a 9))) + C delta * (v a + C (a 11)) = _
  rw [add_assoc, ← mul_add]
  have hc : (y + v a + C (a 9)) + (v a + C (a 11)) = y + C (a 9) + C (a 11) := by
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero, add_zero, zero_add]
  rw [hc]

theorem shift12_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift12 a delta)) 10 delta := by
  apply middle_unit_fixed_v a (shift12 a delta) 2 delta (by omega) rfl rfl rfl rfl
  rw [W_shift12]
  exact Char2Degree21Frame.difference_scaled delta
    ((y_monic.add_right (C_lt _ _ (by omega))).add_right (C_lt _ _ (by omega)))

theorem shift13_unit (a : ℕ → R) (delta : R) :
    UnitDifference (output a) (output (shift13 a delta)) 9 delta := by
  apply middle_unit_fixed_v a (shift13 a delta) 1 delta (by omega) rfl rfl rfl rfl
  rw [shift13, W_commonOffsets]
  exact Char2Degree21Frame.difference_scaled delta (lowLine_monic a)

end FastPoly.Char2Degree23MiddlePivots
