import FastPoly.Examples.Char2Degree19Crown

/-!
# Four terminal unit differences of the degree-19 inner crown

These are the supplied coordinate changes for `q12,q13,q14,q15`. The
identities are proved by changing only the affected gate input(s), leaving
all earlier gates named. The correction has degree `15-i` and coefficient
`delta` there. This is the input needed for an explicit descending decoder;
no coefficient baseline is expanded into the original keys.
-/

namespace FastPoly.Char2Degree19InnerTail

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Crown

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- A certificate for one displayed unit pivot and all rows above it. -/
structure UnitDifference (p p' : R[X]) (n : ℕ) (delta : R) : Prop where
  difference_degree : (p' + p).natDegree ≤ n
  pivot : (p' + p).coeff n = delta

theorem UnitDifference.higher {p p' : R[X]} {n : ℕ} {delta : R}
    (h : UnitDifference p p' n delta) (j : ℕ) (hj : n < j) : p'.coeff j = p.coeff j := by
  have hz : (p' + p).coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt (h.difference_degree.trans_lt hj)
  rw [coeff_add] at hz
  exact CharTwo.add_eq_zero.mp hz

theorem UnitDifference.row {p p' : R[X]} {n : ℕ} {delta : R}
    (h : UnitDifference p p' n delta) : p'.coeff n = p.coeff n + delta := by
  have hp := h.pivot
  rw [coeff_add] at hp
  rw [← hp, ← add_assoc, cancel_tail]

/-- One product with both factors translated by the same displayed value. -/
theorem both_factors (a b d : R[X]) :
    (a + d) * (b + d) = a * b + d * (a + b) + d ^ 2 := by
  rw [add_mul, mul_add, mul_add, mul_add, pow_two, mul_comm a d]
  simp only [add_assoc, add_comm, add_left_comm]

/-- Reassemble named wire changes without normalizing the wires themselves. -/
theorem assemble_last_two (u w q c d a b : R[X]) :
    u + (w + d * a) + (q + d * b) + c = (u + w + q + c) + d * (a + b) := by
  rw [mul_add]
  simp only [add_assoc, add_comm, add_left_comm]

theorem assemble_first_two (u w q c d a b e : R[X]) :
    (u + d * a + e) + (w + d * b) + q + c =
      (u + w + q + c) + (d * (a + b) + e) := by
  rw [mul_add]
  simp only [add_assoc, add_comm, add_left_comm]

theorem assemble_three (u w q c d a b m e : R[X]) :
    (u + d * a) + (w + d * b) + (q + d * m + e) + c =
      (u + w + q + c) + (d * (a + b + m) + e) := by
  rw [mul_add, mul_add]
  simp only [add_assoc, add_comm, add_left_comm]

private theorem slope14_cancel (y z x a b c : R[X]) :
    (y + z + a + b) + (x + y + z + c) = x + a + b + c := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

private theorem slope12_cancel (z t x y s a b c d : R[X]) :
    (z + t + a) + (x + y + z + b) + (t + s + c + d) =
      s + x + y + a + b + c + d := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem unit_difference_of_split (p p' slope : R[X]) (n : ℕ)
    (delta epsilon : R) (hn : 0 < n) (hs : IsMonicOfDegree slope n)
    (heq : p' = p + (C delta * slope + C epsilon)) : UnitDifference p p' n delta := by
  have hd : p' + p = C delta * slope + C epsilon := by rw [heq, cancel_tail]
  have hm : (C delta * slope).natDegree ≤ n := by
    calc
      _ ≤ (C delta).natDegree + slope.natDegree := natDegree_mul_le
      _ = n := by rw [natDegree_C, hs.natDegree_eq, zero_add]
  have hsrow : slope.coeff n = 1 := by
    rw [← hs.natDegree_eq]
    exact hs.monic.coeff_natDegree
  refine ⟨?_, ?_⟩
  · rw [hd]
    exact natDegree_add_le_of_degree_le hm (by rw [natDegree_C]; omega)
  · rw [hd, coeff_add, coeff_C_mul, hsrow, mul_one]
    have hn0 : n ≠ 0 := by omega
    simp only [coeff_C, hn0, ite_false, add_zero]

/-- `q13` changes exactly `a8` and `a15`. -/
def shift13 (a : ℕ → R) (delta : R) : ℕ → R
  | 8 => a 8 + delta
  | 15 => a 15 + delta
  | j => a j

private theorem w_shift13 (a : ℕ → R) (delta : R) :
    w (shift13 a delta) = w a + C delta * (y + v a + C (a 9)) := by
  change (X + y + z a + C (a 8 + delta)) * (y + v a + C (a 9)) =
    (X + y + z a + C (a 8)) * (y + v a + C (a 9)) +
      C delta * (y + v a + C (a 9))
  rw [map_add, ← add_assoc, add_mul]

private theorem q_shift13 (a : ℕ → R) (delta : R) :
    q (shift13 a delta) = q a + C delta * (v a + C (a 14)) := by
  change (v a + C (a 14)) * (t a + v a + s a + C (a 15 + delta)) =
    (v a + C (a 14)) * (t a + v a + s a + C (a 15)) +
      C delta * (v a + C (a 14))
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]

noncomputable def slope13 (a : ℕ → R) : R[X] := y + C (a 9) + C (a 14)

theorem crown_shift13 (a : ℕ → R) (delta : R) :
    crown (shift13 a delta) = crown a + C delta * slope13 a := by
  have hu : u (shift13 a delta) = u a := rfl
  have ha : shift13 a delta 17 = a 17 := rfl
  rw [crown, hu, w_shift13, q_shift13, ha]
  have hs : (y + v a + C (a 9)) + (v a + C (a 14)) = slope13 a := by
    unfold slope13
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]
  rw [assemble_last_two, hs]
  rfl

theorem shift13_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift13 a delta)) 2 delta := by
  have hc (b : R) : (C b).natDegree < 2 := by rw [natDegree_C]; omega
  have hs : IsMonicOfDegree (slope13 a) 2 :=
    (y_monic.add_right (hc _)).add_right (hc _)
  apply unit_difference_of_split _ _ _ 2 delta 0 (by omega) hs
  rw [map_zero, add_zero, crown_shift13]

/-- `q14` changes exactly `a4`, `a5`, and `a9`. -/
def shift14 (a : ℕ → R) (delta : R) : ℕ → R
  | 4 => a 4 + delta
  | 5 => a 5 + delta
  | 9 => a 9 + delta
  | j => a j

private theorem u_shift14 (a : ℕ → R) (delta : R) :
    u (shift14 a delta) = u a + C delta * (y + z a + C (a 4) + C (a 5)) + C (delta ^ 2) := by
  change (y + t a + C (a 4 + delta)) * (z a + t a + C (a 5 + delta)) = _
  rw [map_add, map_add, ← add_assoc, ← add_assoc, both_factors, ← map_pow]
  have hs : (y + t a + C (a 4)) + (z a + t a + C (a 5)) =
      y + z a + C (a 4) + C (a 5) := by
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]
  rw [hs]
  rfl

private theorem w_shift14 (a : ℕ → R) (delta : R) :
    w (shift14 a delta) = w a + C delta * (X + y + z a + C (a 8)) := by
  change (X + y + z a + C (a 8)) * (y + v a + C (a 9 + delta)) =
    (X + y + z a + C (a 8)) * (y + v a + C (a 9)) +
      C delta * (X + y + z a + C (a 8))
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]

noncomputable def slope14 (a : ℕ → R) : R[X] := X + C (a 4) + C (a 5) + C (a 8)

theorem crown_shift14 (a : ℕ → R) (delta : R) :
    crown (shift14 a delta) = crown a + (C delta * slope14 a + C (delta ^ 2)) := by
  have hq : q (shift14 a delta) = q a := rfl
  have ha : shift14 a delta 17 = a 17 := rfl
  rw [crown, u_shift14, w_shift14, hq, ha]
  have hs : (y + z a + C (a 4) + C (a 5)) + (X + y + z a + C (a 8)) =
      slope14 a := slope14_cancel y (z a) X (C (a 4)) (C (a 5)) (C (a 8))
  rw [assemble_first_two, hs]
  rfl

theorem shift14_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift14 a delta)) 1 delta := by
  have hc (b : R) : (C b).natDegree < 1 := by rw [natDegree_C]; omega
  have hs : IsMonicOfDegree (slope14 a) 1 :=
    (((isMonicOfDegree_X R).add_right (hc _)).add_right (hc _)).add_right (hc _)
  exact unit_difference_of_split _ _ _ 1 delta (delta ^ 2) (by omega) hs (crown_shift14 a delta)

/-- `q12` changes exactly `a4`, `a9`, `a14`, and `a15`. -/
def shift12 (a : ℕ → R) (delta : R) : ℕ → R
  | 4 => a 4 + delta
  | 9 => a 9 + delta
  | 14 => a 14 + delta
  | 15 => a 15 + delta
  | j => a j

private theorem u_shift12 (a : ℕ → R) (delta : R) :
    u (shift12 a delta) = u a + C delta * (z a + t a + C (a 5)) := by
  change (y + t a + C (a 4 + delta)) * (z a + t a + C (a 5)) =
    (y + t a + C (a 4)) * (z a + t a + C (a 5)) + C delta * (z a + t a + C (a 5))
  rw [map_add, ← add_assoc, add_mul]

private theorem w_shift12 (a : ℕ → R) (delta : R) :
    w (shift12 a delta) = w a + C delta * (X + y + z a + C (a 8)) := by
  change (X + y + z a + C (a 8)) * (y + v a + C (a 9 + delta)) =
    (X + y + z a + C (a 8)) * (y + v a + C (a 9)) +
      C delta * (X + y + z a + C (a 8))
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]

private theorem q_shift12 (a : ℕ → R) (delta : R) :
    q (shift12 a delta) = q a + C delta * middle a + C (delta ^ 2) := by
  change (v a + C (a 14 + delta)) * (t a + v a + s a + C (a 15 + delta)) = _
  rw [map_add, map_add, ← add_assoc, ← add_assoc, both_factors, ← map_pow]
  have hs : (v a + C (a 14)) + (t a + v a + s a + C (a 15)) = middle a := by
    unfold middle
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]
  rw [hs]
  rfl

noncomputable def slope12 (a : ℕ → R) : R[X] :=
  s a + X + y + C (a 5) + C (a 8) + C (a 14) + C (a 15)

theorem crown_shift12 (a : ℕ → R) (delta : R) :
    crown (shift12 a delta) = crown a + (C delta * slope12 a + C (delta ^ 2)) := by
  have ha : shift12 a delta 17 = a 17 := rfl
  rw [crown, u_shift12, w_shift12, q_shift12, ha]
  have hs : (z a + t a + C (a 5)) + (X + y + z a + C (a 8)) + middle a =
      slope12 a := slope12_cancel (z a) (t a) X y (s a)
        (C (a 5)) (C (a 8)) (C (a 14)) (C (a 15))
  rw [assemble_three, hs]
  rfl

theorem shift12_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift12 a delta)) 3 delta := by
  have hc (b : R) : (C b).natDegree < 3 := by rw [natDegree_C]; omega
  have hy : (y : R[X]).natDegree < 3 := (y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 3)
  have hsxy : IsMonicOfDegree (s a + X + y) 3 :=
    ((s_monic a).add_right (natDegree_X_le.trans_lt (by omega))).add_right hy
  have hs : IsMonicOfDegree (slope12 a) 3 :=
    (((hsxy.add_right (hc _)).add_right (hc _)).add_right (hc _)).add_right (hc _)
  exact unit_difference_of_split _ _ _ 3 delta (delta ^ 2) (by omega) hs (crown_shift12 a delta)

/-- The last crown coordinate is its output constant. -/
def shift15 (a : ℕ → R) (delta : R) : ℕ → R
  | 17 => a 17 + delta
  | j => a j

theorem crown_shift15 (a : ℕ → R) (delta : R) :
    crown (shift15 a delta) = crown a + C delta := by
  change u a + w a + q a + C (a 17 + delta) = (u a + w a + q a + C (a 17)) + C delta
  rw [map_add, ← add_assoc]

theorem shift15_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift15 a delta)) 0 delta := by
  have hd : crown (shift15 a delta) + crown a = C delta := by rw [crown_shift15, cancel_tail]
  constructor
  · rw [hd, natDegree_C]
  · rw [hd, coeff_C_zero]

end FastPoly.Char2Degree19InnerTail
