import FastPoly.Examples.Char2Degree19InnerTail

/-! The three direct single-product pivots `q7,q10,q11`. -/

namespace FastPoly.Char2Degree19InnerSimple

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Crown Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- `q7` changes only `a15`. -/
def shift7 (a : ℕ → R) (delta : R) : ℕ → R
  | 15 => a 15 + delta
  | j => a j

theorem crown_shift7 (a : ℕ → R) (delta : R) :
    crown (shift7 a delta) = crown a + C delta * (v a + C (a 14)) := by
  have hu : u (shift7 a delta) = u a := rfl
  have hw : w (shift7 a delta) = w a := rfl
  have ha : shift7 a delta 17 = a 17 := rfl
  have hq : q (shift7 a delta) = q a + C delta * (v a + C (a 14)) := by
    change (v a + C (a 14)) * (t a + v a + s a + C (a 15 + delta)) =
      (v a + C (a 14)) * (t a + v a + s a + C (a 15)) +
        C delta * (v a + C (a 14))
    rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]
  rw [crown, hu, hw, hq, ha]
  unfold crown
  simp only [add_assoc, add_comm, add_left_comm]

theorem shift7_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift7 a delta)) 8 delta := by
  have hs : IsMonicOfDegree (v a + C (a 14)) 8 :=
    (v_monic a).add_right (by rw [natDegree_C]; omega)
  apply unit_difference_of_split _ _ _ 8 delta 0 (by omega) hs
  rw [map_zero, add_zero, crown_shift7]

/-- `q10` changes both offsets of the final quadratic product. -/
def shift10 (a : ℕ → R) (delta : R) : ℕ → R
  | 14 => a 14 + delta
  | 15 => a 15 + delta
  | j => a j

theorem crown_shift10 (a : ℕ → R) (delta : R) :
    crown (shift10 a delta) = crown a + (C delta * middle a + C (delta ^ 2)) := by
  have hu : u (shift10 a delta) = u a := rfl
  have hw : w (shift10 a delta) = w a := rfl
  have ha : shift10 a delta 17 = a 17 := rfl
  have hq : q (shift10 a delta) = q a + C delta * middle a + C (delta ^ 2) := by
    change (v a + C (a 14 + delta)) * (t a + v a + s a + C (a 15 + delta)) = _
    rw [map_add, map_add, ← add_assoc, ← add_assoc, both_factors, ← map_pow]
    have hs : (v a + C (a 14)) + (t a + v a + s a + C (a 15)) = middle a := by
      unfold middle
      simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]
    rw [hs]
    rfl
  rw [crown, hu, hw, hq, ha]
  unfold crown
  simp only [add_assoc, add_comm, add_left_comm]

theorem shift10_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift10 a delta)) 5 delta :=
  unit_difference_of_split _ _ _ 5 delta (delta ^ 2) (by omega) (middle_monic a)
    (crown_shift10 a delta)

/-- `q11` changes only the second offset of `w`. -/
def shift11 (a : ℕ → R) (delta : R) : ℕ → R
  | 9 => a 9 + delta
  | j => a j

noncomputable def slope11 (a : ℕ → R) : R[X] := X + y + z a + C (a 8)

theorem slope11_monic (a : ℕ → R) : IsMonicOfDegree (slope11 a) 4 := by
  have hxy : IsMonicOfDegree ((X : R[X]) + y) 2 :=
    y_monic.add_left (natDegree_X_le.trans_lt (by omega))
  exact ((z_monic a).add_left (hxy.natDegree_eq ▸ (by omega : 2 < 4))).add_right
    (by rw [natDegree_C]; omega)

theorem crown_shift11 (a : ℕ → R) (delta : R) :
    crown (shift11 a delta) = crown a + C delta * slope11 a := by
  have hu : u (shift11 a delta) = u a := rfl
  have hq : q (shift11 a delta) = q a := rfl
  have ha : shift11 a delta 17 = a 17 := rfl
  have hw : w (shift11 a delta) = w a + C delta * slope11 a := by
    change slope11 a * (y + v a + C (a 9 + delta)) =
      slope11 a * (y + v a + C (a 9)) + C delta * slope11 a
    rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]
  rw [crown, hu, hw, hq, ha]
  unfold crown
  simp only [add_assoc, add_comm, add_left_comm]

theorem shift11_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift11 a delta)) 4 delta := by
  apply unit_difference_of_split _ _ _ 4 delta 0 (by omega) (slope11_monic a)
  rw [map_zero, add_zero, crown_shift11]

end FastPoly.Char2Degree19InnerSimple
