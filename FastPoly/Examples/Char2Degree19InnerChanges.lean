import FastPoly.Examples.Char2Degree19InnerTail

/-!
# Degree-19 inner pivots from changes to named gates

The supplied coordinates q6 and q9 change only the gate `v`. The crown's
leading change is `middle * delta_v`; every other change has smaller degree.
This certifies the actual unit pivots without expanding their baselines.
-/

namespace FastPoly.Char2Degree19InnerChanges

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Crown Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

omit [Nontrivial R] in
/-- A monic leading change and an arbitrary named lower-degree remainder. -/
theorem unit_difference_of_lower (p p' slope tail : R[X]) (n : ℕ)
    (delta : R) (hs : IsMonicOfDegree slope n) (ht : tail.natDegree < n)
    (heq : p' = p + (C delta * slope + tail)) : UnitDifference p p' n delta := by
  have hd : p' + p = C delta * slope + tail := by rw [heq, cancel_tail]
  have hm : (C delta * slope).natDegree ≤ n := by
    calc
      _ ≤ (C delta).natDegree + slope.natDegree := natDegree_mul_le
      _ = n := by rw [natDegree_C, hs.natDegree_eq, zero_add]
  have hr : slope.coeff n = 1 := by
    rw [← hs.natDegree_eq]
    exact hs.monic.coeff_natDegree
  have hz : tail.coeff n = 0 := coeff_eq_zero_of_natDegree_lt ht
  refine ⟨?_, ?_⟩
  · rw [hd]
    exact natDegree_add_le_of_degree_le hm ht.le
  · rw [hd, coeff_add, coeff_C_mul, hr, hz, mul_one, add_zero]

noncomputable def wLeft (a : ℕ → R) : R[X] := X + y + z a + C (a 8)

omit [CharP R 2] in
theorem wLeft_monic (a : ℕ → R) : IsMonicOfDegree (wLeft a) 4 := by
  have hxy : IsMonicOfDegree ((X : R[X]) + y) 2 :=
    y_monic.add_left (natDegree_X_le.trans_lt (by omega))
  have hc : (C (a 8)).natDegree < 4 := by rw [natDegree_C]; omega
  exact ((z_monic a).add_left (hxy.natDegree_eq ▸ (by omega : 2 < 4))).add_right hc

noncomputable def vRemainder (a : ℕ → R) (d : R[X]) : R[X] :=
  d ^ 2 + wLeft a * d

/-- Only the three crown operations are opened; all input wires are opaque. -/
theorem crown_change_v (a b : ℕ → R) (d : R[X])
    (hu : u b = u a) (hm : middle b = middle a) (hl : qLow b = qLow a)
    (hw : w b = w a + wLeft a * d) (hv : v b = v a + d) (hc : b 17 = a 17) :
    crown b = crown a + (middle a * d + vRemainder a d) := by
  have hlow : crownLow b = crownLow a + wLeft a * d := by
    rw [crownLow, hu, hw, hl, hc]
    unfold crownLow
    ac_rfl
  rw [crown_split b, hv, hm, hlow, CharTwo.add_sq, mul_add, crown_split a]
  unfold vRemainder
  ac_rfl

omit [CharP R 2] in
theorem vRemainder_degree (a : ℕ → R) (d : R[X]) (k : ℕ)
    (hk : k ≤ 4) (hd : d.natDegree ≤ k) : (vRemainder a d).natDegree < k + 5 := by
  have hs : (d ^ 2).natDegree ≤ 2 * k := by
    calc
      _ ≤ 2 * d.natDegree := natDegree_pow_le
      _ ≤ 2 * k := by omega
  have hm : (wLeft a * d).natDegree ≤ 4 + k := by
    calc
      _ ≤ (wLeft a).natDegree + d.natDegree := natDegree_mul_le
      _ ≤ 4 + k := by rw [(wLeft_monic a).natDegree_eq]; omega
  exact (natDegree_add_le_of_degree_le (hs.trans (by omega)) hm).trans_lt (by omega)

theorem unit_from_v_change (a b : ℕ → R) (slope : R[X]) (k : ℕ)
    (delta : R) (hk : k ≤ 4) (hs : IsMonicOfDegree slope k)
    (h : crown b = crown a +
      (middle a * (C delta * slope) + vRemainder a (C delta * slope))) :
    UnitDifference (crown a) (crown b) (k + 5) delta := by
  have hd : (C delta * slope).natDegree ≤ k := by
    calc
      _ ≤ (C delta).natDegree + slope.natDegree := natDegree_mul_le
      _ = k := by rw [natDegree_C, hs.natDegree_eq, zero_add]
  have hmonic : IsMonicOfDegree (middle a * slope) (k + 5) := by
    simpa only [Nat.add_comm] using (middle_monic a).mul hs
  apply unit_difference_of_lower _ _ _ _ _ delta hmonic
    (vRemainder_degree a _ k hk hd)
  rw [h, mul_left_comm (middle a) (C delta)]

/-- q6 changes a7 only. -/
def shift6 (a : ℕ → R) (delta : R) : ℕ → R
  | 7 => a 7 + delta
  | j => a j

noncomputable def slope6 (a : ℕ → R) : R[X] := X + z a + C (a 6)

omit [CharP R 2] [Nontrivial R] in
theorem v_shift6 (a : ℕ → R) (delta : R) :
    v (shift6 a delta) = v a + C delta * slope6 a := by
  change (X + z a + C (a 6)) * (z a + C (a 7 + delta)) =
    (X + z a + C (a 6)) * (z a + C (a 7)) + C delta * (X + z a + C (a 6))
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]

omit [CharP R 2] [Nontrivial R] in
private theorem left_factor_change (l y v c d : R[X]) :
    l * (y + (v + d) + c) = l * (y + v + c) + l * d := by
  rw [← add_assoc y v d, add_right_comm (y + v) d c, mul_add]

theorem shift6_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift6 a delta)) 9 delta := by
  have hs : IsMonicOfDegree (slope6 a) 4 := by
    have hc : (C (a 6)).natDegree < 4 := by rw [natDegree_C]; omega
    exact ((z_monic a).add_left (natDegree_X_le.trans_lt (by omega))).add_right hc
  apply unit_from_v_change a (shift6 a delta) (slope6 a) 4 delta (by omega) hs
  apply crown_change_v a (shift6 a delta) (C delta * slope6 a) rfl rfl rfl
    ?_ (v_shift6 a delta) rfl
  change wLeft a * (y + v (shift6 a delta) + C (a 9)) =
    wLeft a * (y + v a + C (a 9)) + wLeft a * (C delta * slope6 a)
  rw [v_shift6]
  exact left_factor_change ..

/-- q9 changes both offsets of v by the same value. -/
def shift9 (a : ℕ → R) (delta : R) : ℕ → R
  | 6 => a 6 + delta
  | 7 => a 7 + delta
  | j => a j

noncomputable def slope9 (a : ℕ → R) (delta : R) : R[X] :=
  X + C (a 6) + C (a 7) + C delta

theorem v_shift9 (a : ℕ → R) (delta : R) :
    v (shift9 a delta) = v a + C delta * slope9 a delta := by
  change (X + z a + C (a 6 + delta)) * (z a + C (a 7 + delta)) = _
  rw [map_add, map_add, ← add_assoc, ← add_assoc, both_factors]
  have hs : (X + z a + C (a 6)) + (z a + C (a 7)) = X + C (a 6) + C (a 7) := by
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]
  rw [hs, pow_two, add_assoc, ← mul_add]
  rfl

theorem shift9_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift9 a delta)) 6 delta := by
  have hc (b : R) : (C b).natDegree < 1 := by rw [natDegree_C]; omega
  have hs : IsMonicOfDegree (slope9 a delta) 1 :=
    ((isMonicOfDegree_X_add_one (a 6)).add_right (hc _)).add_right (hc _)
  apply unit_from_v_change a (shift9 a delta) (slope9 a delta) 1 delta (by omega) hs
  apply crown_change_v a (shift9 a delta) (C delta * slope9 a delta) rfl rfl rfl
    ?_ (v_shift9 a delta) rfl
  change wLeft a * (y + v (shift9 a delta) + C (a 9)) =
    wLeft a * (y + v a + C (a 9)) + wLeft a * (C delta * slope9 a delta)
  rw [v_shift9]
  exact left_factor_change ..

end FastPoly.Char2Degree19InnerChanges
