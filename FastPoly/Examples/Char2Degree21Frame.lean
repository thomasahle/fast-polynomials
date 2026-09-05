import FastPoly.Examples.Char2Degree19InnerChanges

/-!
# The existing degree-21 circuit as a degree-19 crown with a quintic frame

The first nine multiplication gates are exactly the named degree-19 gates.
Writing their checked crown as `C*`, the two final products combine to
`A * C* + T * D + z + r + a20`. The other summand has degree at most nine.
This frame transports local unit differences without opening coefficient
baselines or multiplying out the shared circuit.
-/

namespace FastPoly.Char2Degree21Frame

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Crown Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def core (a : ℕ → R) : R[X] := u a + w a + q a
noncomputable def ell (a : ℕ → R) : R[X] :=
  (s a + C (a 16)) * (core a + C (a 17))
noncomputable def m (a : ℕ → R) : R[X] :=
  (t a + s a + C (a 18)) * (z a + core a + C (a 19))
noncomputable def output (a : ℕ → R) : R[X] :=
  m a + z a + r a + ell a + C (a 20)

noncomputable def A (a : ℕ → R) : R[X] := t a + C (a 16) + C (a 18)
noncomputable def T (a : ℕ → R) : R[X] := t a + s a + C (a 18)
noncomputable def D (a : ℕ → R) : R[X] := z a + C (a 19) + C (a 17)
noncomputable def tail (a : ℕ → R) : R[X] :=
  T a * D a + z a + r a + C (a 20)

omit [Nontrivial R] in
private theorem cross_cancel (z c e f : R[X]) :
    (z + f + e) + (c + e) = z + c + f := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

omit [Nontrivial R] in
theorem cross_split (a : ℕ → R) :
    z a + core a + C (a 19) = D a + crown a :=
  (cross_cancel (z a) (core a) (C (a 17)) (C (a 19))).symm

omit [Nontrivial R] in
private theorem frame_cancel (t s c d : R[X]) :
    (t + s + d) + (s + c) = t + c + d := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

omit [Nontrivial R] in
theorem A_eq (a : ℕ → R) : T a + (s a + C (a 16)) = A a :=
  frame_cancel ..

omit [CharP R 2] [Nontrivial R] in
private theorem two_products (h d c s z r e : R[X]) :
    h * (d + c) + z + r + s * c + e =
      (h + s) * c + (h * d + z + r + e) := by
  rw [mul_add, add_mul]
  ac_rfl

omit [Nontrivial R] in
theorem output_eq (a : ℕ → R) : output a = A a * crown a + tail a := by
  change T a * (z a + core a + C (a 19)) + z a + r a +
    (s a + C (a 16)) * crown a + C (a 20) = _
  rw [cross_split, two_products, A_eq]
  rfl

omit [CharP R 2] [Nontrivial R] in
theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

theorem A_monic (a : ℕ → R) : IsMonicOfDegree (A a) 5 :=
  ((t_monic a).add_right (C_lt _ 5 (by omega))).add_right (C_lt _ 5 (by omega))

theorem T_monic (a : ℕ → R) : IsMonicOfDegree (T a) 5 :=
  ((t_monic a).add_right ((s_monic a).natDegree_eq ▸ (by omega : 3 < 5))).add_right
    (C_lt _ 5 (by omega))

theorem D_monic (a : ℕ → R) : IsMonicOfDegree (D a) 4 :=
  ((z_monic a).add_right (C_lt _ 4 (by omega))).add_right (C_lt _ 4 (by omega))

omit [CharP R 2] in
theorem r_monic (a : ℕ → R) : IsMonicOfDegree (r a) 3 :=
  (isMonicOfDegree_X_add_one (a 12)).mul (y_monic.add_right (C_lt _ 2 (by omega)))

theorem tail_degree (a : ℕ → R) : (tail a).natDegree ≤ 9 := by
  have htd : (T a * D a).natDegree = 9 := ((T_monic a).mul (D_monic a)).natDegree_eq
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le htd.le
      ((z_monic a).natDegree_eq ▸ (by omega : 4 ≤ 9)))
    ((r_monic a).natDegree_eq ▸ (by omega : 3 ≤ 9))) (C_lt _ 9 (by omega)).le

theorem output_monic (a : ℕ → R) : IsMonicOfDegree (output a) 21 := by
  rw [output_eq]
  exact ((A_monic a).mul (crown_monic a)).add_right
    ((tail_degree a).trans_lt (by omega))

omit [Nontrivial R] in
/-- A unit difference multiplied by a named monic wire. -/
theorem difference_mul {p p' g : R[X]} {n k : ℕ} {delta : R}
    (h : UnitDifference p p' n delta) (hg : IsMonicOfDegree g k) :
    UnitDifference (g * p) (g * p') (k + n) delta := by
  have heq : g * p' + g * p = g * (p' + p) := (mul_add ..).symm
  have hc : g.coeff k = 1 := by
    rw [← hg.natDegree_eq]
    exact hg.monic.coeff_natDegree
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact natDegree_mul_le.trans (Nat.add_le_add hg.natDegree_eq.le h.difference_degree)
  · rw [heq, coeff_mul_add_eq_of_natDegree_le hg.natDegree_eq.le h.difference_degree,
      hc, h.pivot, one_mul]

omit [Nontrivial R] in
private theorem chain_changes (p p' p'' : R[X]) :
    p'' + p = (p'' + p') + (p' + p) := by
  rw [add_assoc, CharTwo.add_cancel_left]

omit [Nontrivial R] in
/-- Changing only lower rows preserves a previously certified pivot. -/
theorem difference_lower {p p' p'' : R[X]} {n : ℕ} {delta : R}
    (h : UnitDifference p p' n delta) (hl : (p'' + p').natDegree < n) :
    UnitDifference p p'' n delta := by
  have hz : (p'' + p').coeff n = 0 := coeff_eq_zero_of_natDegree_lt hl
  refine ⟨?_, ?_⟩
  · rw [chain_changes p p' p'']
    exact natDegree_add_le_of_degree_le hl.le h.difference_degree
  · rw [chain_changes p p' p'', coeff_add, hz, h.pivot, zero_add]

omit [Nontrivial R] in
private theorem add_changes (p p' b b' : R[X]) :
    (p' + b') + (p + b) = (p' + p) + (b' + b) := by ac_rfl

omit [Nontrivial R] in
/-- A common frame plus a lower-degree tail transports the same unit pivot. -/
theorem difference_add_lower {p p' b b' : R[X]} {n : ℕ} {delta : R}
    (h : UnitDifference p p' n delta) (hl : (b' + b).natDegree < n) :
    UnitDifference (p + b) (p' + b') n delta := by
  have hz : (b' + b).coeff n = 0 := coeff_eq_zero_of_natDegree_lt hl
  refine ⟨?_, ?_⟩
  · rw [add_changes]
    exact natDegree_add_le_of_degree_le h.difference_degree hl.le
  · rw [add_changes, coeff_add, h.pivot, hz, add_zero]

omit [Nontrivial R] in
private theorem common_tail (p p' b : R[X]) :
    (p' + b) + (p + b) = p' + p := by
  rw [add_changes, CharTwo.add_self_eq_zero, add_zero]

omit [Nontrivial R] in
/-- Unlike the strict-degree variant this also applies at degree zero. -/
theorem difference_add {p p' b : R[X]} {n : ℕ} {delta : R}
    (h : UnitDifference p p' n delta) : UnitDifference (p + b) (p' + b) n delta := by
  refine ⟨?_, ?_⟩
  · rw [common_tail]
    exact h.difference_degree
  · rw [common_tail]
    exact h.pivot

omit [Nontrivial R] in
theorem difference_scaled {p slope : R[X]} {n : ℕ} (delta : R)
    (hs : IsMonicOfDegree slope n) :
    UnitDifference p (p + C delta * slope) n delta := by
  have heq : (p + C delta * slope) + p = C delta * slope := cancel_tail ..
  have hc : slope.coeff n = 1 := by
    rw [← hs.natDegree_eq]
    exact hs.monic.coeff_natDegree
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact natDegree_mul_le.trans (by rw [natDegree_C, hs.natDegree_eq, zero_add])
  · rw [heq, coeff_C_mul, hc, mul_one]

/-- Lift an unchanged quintic frame; the lower term may still change. -/
theorem output_difference {a b : ℕ → R} {n : ℕ} {delta : R}
    (h : UnitDifference (crown a) (crown b) n delta)
    (ha : A b = A a) (ht : (tail b + tail a).natDegree < 5 + n) :
    UnitDifference (output a) (output b) (5 + n) delta := by
  rw [output_eq a, output_eq b, ha]
  exact difference_add_lower (difference_mul h (A_monic a)) ht

/-- The common-tail case avoids requiring a positive pivot degree. -/
theorem output_difference_fixed {a b : ℕ → R} {n : ℕ} {delta : R}
    (h : UnitDifference (crown a) (crown b) n delta)
    (ha : A b = A a) (ht : tail b = tail a) :
    UnitDifference (output a) (output b) (5 + n) delta := by
  rw [output_eq a, output_eq b, ha, ht]
  exact difference_add (difference_mul h (A_monic a))

omit [Nontrivial R] in
/-- A moving-frame identity with only six opaque polynomial inputs. -/
theorem moving_frame (a a' c c' b b' : R[X]) :
    (a' * c' + b') + (a * c + b) =
      (a' + a) * c + (a' * (c' + c) + (b' + b)) := by
  rw [add_mul, mul_add]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

end FastPoly.Char2Degree21Frame
