import FastPoly.Examples.Char2Degree19InnerChanges

/-! The direct `q3` pivot, changing the linear factor of `t`. -/

namespace FastPoly.Char2Degree19InnerDirect

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Crown Char2Degree19InnerTail Char2Degree19InnerChanges

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem move_increment (a b c d : R[X]) : a + (b + d) + c = (a + b + c) + d := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem cancel_middle (y t z a b : R[X]) :
    (y + t + a) + (z + t + b) = y + z + a + b := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem assemble_outer (u w q c du dq : R[X]) :
    (u + du) + w + (q + dq) + c = (u + w + q + c) + (dq + du) := by
  simp only [add_assoc, add_comm, add_left_comm]

/-- The correction to `u` when both occurrences of `t` increase by `d`. -/
noncomputable def uCorrection (a : ℕ → R) (d : R[X]) : R[X] :=
  d * (y + z a + C (a 4) + C (a 5)) + d ^ 2

theorem u_change_t (a b : ℕ → R) (d : R[X])
    (hz : z b = z a) (ht : t b = t a + d) (h4 : b 4 = a 4) (h5 : b 5 = a 5) :
    u b = u a + uCorrection a d := by
  rw [u, hz, ht, h4, h5, move_increment, move_increment, both_factors,
    cancel_middle]
  exact add_assoc _ _ _

theorem uCorrection_degree (a : ℕ → R) (d : R[X]) (k : ℕ)
    (hk : k ≤ 4) (hd : d.natDegree ≤ k) : (uCorrection a d).natDegree ≤ k + 4 := by
  have hc (b : R) : (C b).natDegree < 4 := by rw [natDegree_C]; omega
  have hu : IsMonicOfDegree (y + z a + C (a 4) + C (a 5)) 4 :=
    (((z_monic a).add_left ((y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 4))).add_right
      (hc _)).add_right (hc _)
  have hm : (d * (y + z a + C (a 4) + C (a 5))).natDegree ≤ k + 4 := by
    calc
      _ ≤ d.natDegree + (y + z a + C (a 4) + C (a 5)).natDegree := natDegree_mul_le
      _ ≤ k + 4 := by rw [hu.natDegree_eq]; omega
  have hp : (d ^ 2).natDegree ≤ k + 4 := by
    calc
      _ ≤ 2 * d.natDegree := natDegree_pow_le
      _ ≤ k + 4 := by omega
  exact natDegree_add_le_of_degree_le hm hp

def shift3 (a : ℕ → R) (delta : R) : ℕ → R
  | 2 => a 2 + delta
  | j => a j

noncomputable def tSlope3 (a : ℕ → R) : R[X] := z a + C (a 3)
noncomputable def slope3 (a : ℕ → R) : R[X] := (v a + C (a 14)) * tSlope3 a

theorem t_shift3 (a : ℕ → R) (delta : R) :
    t (shift3 a delta) = t a + C delta * tSlope3 a := by
  change (X + C (a 2 + delta)) * tSlope3 a =
    (X + C (a 2)) * tSlope3 a + C delta * tSlope3 a
  rw [map_add, ← add_assoc, add_mul]

theorem crown_shift3 (a : ℕ → R) (delta : R) :
    crown (shift3 a delta) = crown a +
      (C delta * slope3 a + uCorrection a (C delta * tSlope3 a)) := by
  have hu : u (shift3 a delta) = u a + uCorrection a (C delta * tSlope3 a) :=
    u_change_t a _ _ rfl (t_shift3 a delta) rfl rfl
  have hw : w (shift3 a delta) = w a := rfl
  have ha : shift3 a delta 17 = a 17 := rfl
  have hq : q (shift3 a delta) = q a + C delta * slope3 a := by
    change (v a + C (a 14)) * (t (shift3 a delta) + v a + s a + C (a 15)) =
      (v a + C (a 14)) * (t a + v a + s a + C (a 15)) + C delta * slope3 a
    rw [t_shift3, add_right_comm (t a), add_right_comm (t a + v a),
      add_right_comm (t a + v a + s a), mul_add, mul_left_comm _ (C delta)]
    rfl
  rw [crown, hu, hw, hq, ha, assemble_outer]
  rfl

theorem shift3_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift3 a delta)) 12 delta := by
  have hts : IsMonicOfDegree (tSlope3 a) 4 :=
    (z_monic a).add_right (by rw [natDegree_C]; omega)
  have hs : IsMonicOfDegree (slope3 a) 12 :=
    ((v_monic a).add_right (by rw [natDegree_C]; omega)).mul hts
  have hd : (C delta * tSlope3 a).natDegree ≤ 4 := by
    calc
      _ ≤ (C delta).natDegree + (tSlope3 a).natDegree := natDegree_mul_le
      _ = 4 := by rw [natDegree_C, hts.natDegree_eq]
  exact unit_difference_of_lower _ _ _ _ 12 delta hs
    ((uCorrection_degree a _ 4 (by omega) hd).trans_lt (by omega)) (crown_shift3 a delta)

end FastPoly.Char2Degree19InnerDirect
