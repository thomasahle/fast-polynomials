import FastPoly.Examples.Char2Degree19InnerChanges

/-!
# The degree-19 inner pivots changing z

The q4/q5 updates change z by a scalar times a monic quadratic/linear
polynomial. Their leading crown change is `delta_t * v`; the other named
gate changes have lower degree. No coefficient baseline is expanded.
-/

namespace FastPoly.Char2Degree19InnerZChanges

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Crown Char2Degree19InnerTail
  Char2Degree19InnerChanges

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def tDelta (a : ℕ → R) (d : R[X]) : R[X] := (X + C (a 2)) * d
noncomputable def vLinear (a : ℕ → R) : R[X] := X + C (a 6) + C (a 7)
noncomputable def vDelta (a : ℕ → R) (d : R[X]) : R[X] := d ^ 2 + vLinear a * d
noncomputable def uDelta (a : ℕ → R) (d : R[X]) : R[X] :=
  (y + t a + C (a 4)) * (d + tDelta a d) +
    tDelta a d * (z a + t a + C (a 5)) + tDelta a d * (d + tDelta a d)
noncomputable def wDelta (a : ℕ → R) (d : R[X]) : R[X] :=
  wLeft a * vDelta a d + d * (y + v a + C (a 9)) + d * vDelta a d
noncomputable def zRemainder (a : ℕ → R) (d : R[X]) : R[X] :=
  vDelta a d ^ 2 + middle a * vDelta a d + tDelta a d * vDelta a d +
    uDelta a d + wDelta a d + C (a 14) * tDelta a d

/-- Two changed inputs, with the previous gate and changes kept as atoms. -/
private theorem product_changes (a b d e : R[X]) :
    (a + d) * (b + e) = a * b + (a * e + d * b + d * e) := by
  rw [add_mul, mul_add, mul_add]
  ac_rfl

/-- A local identity for the square-plus-linear crown expression. -/
private theorem crown_changes (v m l d e f : R[X]) :
    (v + d) ^ 2 + (m + e) * (v + d) + (l + f) =
      (v ^ 2 + m * v + l) + (e * v + (d ^ 2 + m * d + e * d + f)) := by
  rw [CharTwo.add_sq, add_mul, mul_add, mul_add]
  ac_rfl

theorem t_change_z (a b : ℕ → R) (d : R[X])
    (ha : ∀ i, 2 ≤ i → b i = a i) (hz : z b = z a + d) :
    t b = t a + tDelta a d := by
  rw [t, ha 2 (by omega), ha 3 (by omega), hz, add_right_comm, mul_add]
  rfl

theorem v_change_z (a b : ℕ → R) (d : R[X])
    (ha : ∀ i, 2 ≤ i → b i = a i) (hz : z b = z a + d) :
    v b = v a + vDelta a d := by
  have hvTail : vTail b = vTail a + vLinear a * d := by
    rw [vTail, ha 6 (by omega), ha 7 (by omega), hz, mul_add]
    unfold vTail vLinear
    ac_rfl
  rw [v_split b, hz, hvTail, CharTwo.add_sq, v_split a]
  unfold vDelta
  ac_rfl

theorem u_change_z (a b : ℕ → R) (d : R[X])
    (ha : ∀ i, 2 ≤ i → b i = a i) (hz : z b = z a + d) :
    u b = u a + uDelta a d := by
  rw [u, t_change_z a b d ha hz, hz, ha 4 (by omega), ha 5 (by omega)]
  have h1 : y + (t a + tDelta a d) + C (a 4) =
      (y + t a + C (a 4)) + tDelta a d := by ac_rfl
  have h2 : (z a + d) + (t a + tDelta a d) + C (a 5) =
      (z a + t a + C (a 5)) + (d + tDelta a d) := by ac_rfl
  rw [h1, h2, product_changes]
  rfl

theorem w_change_z (a b : ℕ → R) (d : R[X])
    (ha : ∀ i, 2 ≤ i → b i = a i) (hz : z b = z a + d) :
    w b = w a + wDelta a d := by
  rw [w, hz, v_change_z a b d ha hz, ha 8 (by omega), ha 9 (by omega)]
  have h1 : X + y + (z a + d) + C (a 8) = wLeft a + d := by
    unfold wLeft
    ac_rfl
  have h2 : y + (v a + vDelta a d) + C (a 9) =
      (y + v a + C (a 9)) + vDelta a d := by ac_rfl
  rw [h1, h2, product_changes]
  rfl

theorem middle_change_z (a b : ℕ → R) (d : R[X])
    (ha : ∀ i, 2 ≤ i → b i = a i) (hz : z b = z a + d) :
    middle b = middle a + tDelta a d := by
  have hs : s b = s a := by rw [s, ha 10 (by omega), ha 11 (by omega)]; rfl
  rw [middle, t_change_z a b d ha hz, hs, ha 14 (by omega), ha 15 (by omega)]
  unfold middle
  ac_rfl

theorem qLow_change_z (a b : ℕ → R) (d : R[X])
    (ha : ∀ i, 2 ≤ i → b i = a i) (hz : z b = z a + d) :
    qLow b = qLow a + C (a 14) * tDelta a d := by
  have hs : s b = s a := by rw [s, ha 10 (by omega), ha 11 (by omega)]; rfl
  rw [qLow, t_change_z a b d ha hz, hs, ha 14 (by omega), ha 15 (by omega)]
  have h : (t a + tDelta a d) + s a + C (a 15) =
      (t a + s a + C (a 15)) + tDelta a d := by ac_rfl
  rw [h, mul_add]
  rfl

theorem crownLow_change_z (a b : ℕ → R) (d : R[X])
    (ha : ∀ i, 2 ≤ i → b i = a i) (hz : z b = z a + d) :
    crownLow b = crownLow a +
      (uDelta a d + wDelta a d + C (a 14) * tDelta a d) := by
  rw [crownLow, u_change_z a b d ha hz, w_change_z a b d ha hz,
    qLow_change_z a b d ha hz, ha 17 (by omega)]
  unfold crownLow
  ac_rfl

/-- z is the only changed input to this named-gate calculation. -/
theorem crown_change_z (a b : ℕ → R) (d : R[X])
    (ha : ∀ i, 2 ≤ i → b i = a i) (hz : z b = z a + d) :
    crown b = crown a + (tDelta a d * v a + zRemainder a d) := by
  rw [crown_split b, v_change_z a b d ha hz, middle_change_z a b d ha hz,
    crownLow_change_z a b d ha hz, crown_changes, crown_split a]
  unfold zRemainder
  ac_rfl

private theorem C_degree (c : R) : (C c).natDegree ≤ 0 := (natDegree_C c).le

private theorem degree_mul_le {p q : R[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) : (p * q).natDegree ≤ m + n :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

/-- All lower corrections are bounded at the gate level. -/
theorem zRemainder_degree (a : ℕ → R) (d : R[X]) (k : ℕ)
    (hk0 : 1 ≤ k) (hk2 : k ≤ 2) (hd : d.natDegree ≤ k) :
    (zRemainder a d).natDegree < k + 9 := by
  have ht : (tDelta a d).natDegree ≤ k + 1 := by
    simpa only [Nat.add_comm] using
      degree_mul_le (isMonicOfDegree_X_add_one (a 2)).natDegree_eq.le hd
  have hlin : (vLinear a).natDegree ≤ 1 := by
    have hc : (C (a 7)).natDegree < 1 := by rw [natDegree_C]; omega
    exact ((isMonicOfDegree_X_add_one (a 6)).add_right hc).natDegree_eq.le
  have hv : (vDelta a d).natDegree ≤ 2 * k := by
    have hs : (d ^ 2).natDegree ≤ 2 * k := by
      have h := natDegree_pow_le (p := d) (n := 2)
      omega
    exact natDegree_add_le_of_degree_le hs ((degree_mul_le hlin hd).trans (by omega))
  have hadd : (d + tDelta a d).natDegree ≤ k + 1 :=
    natDegree_add_le_of_degree_le (hd.trans (by omega)) ht
  have hu1 : (y + t a + C (a 4)).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (y_monic.natDegree_eq.le.trans (by omega)) (t_monic a).natDegree_eq.le)
      ((C_degree _).trans (by omega))
  have hu2 : (z a + t a + C (a 5)).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      ((z_monic a).natDegree_eq.le.trans (by omega)) (t_monic a).natDegree_eq.le)
      ((C_degree _).trans (by omega))
  have hu : (uDelta a d).natDegree ≤ k + 6 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      ((degree_mul_le hu1 hadd).trans (by omega))
      ((degree_mul_le ht hu2).trans (by omega)))
      ((degree_mul_le ht hadd).trans (by omega))
  have hwr : (y + v a + C (a 9)).natDegree ≤ 8 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (y_monic.natDegree_eq.le.trans (by omega)) (v_monic a).natDegree_eq.le)
      ((C_degree _).trans (by omega))
  have hw : (wDelta a d).natDegree ≤ k + 8 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      ((degree_mul_le (wLeft_monic a).natDegree_eq.le hv).trans (by omega))
      (degree_mul_le hd hwr)) ((degree_mul_le hd hv).trans (by omega))
  have hv2 : (vDelta a d ^ 2).natDegree ≤ k + 8 := by
    have h := natDegree_pow_le (p := vDelta a d) (n := 2)
    omega
  have hm : (middle a * vDelta a d).natDegree ≤ k + 8 :=
    (degree_mul_le (middle_monic a).natDegree_eq.le hv).trans (by omega)
  have htv : (tDelta a d * vDelta a d).natDegree ≤ k + 8 :=
    (degree_mul_le ht hv).trans (by omega)
  have hc : (C (a 14) * tDelta a d).natDegree ≤ k + 8 :=
    (degree_mul_le (C_degree _) ht).trans (by omega)
  exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le hv2 hm) htv) (hu.trans (by omega))) hw) hc).trans_lt
      (by omega)

theorem unit_from_z_change (a b : ℕ → R) (slope : R[X]) (k : ℕ)
    (delta : R) (hk0 : 1 ≤ k) (hk2 : k ≤ 2) (hs : IsMonicOfDegree slope k)
    (ha : ∀ i, 2 ≤ i → b i = a i) (hz : z b = z a + C delta * slope) :
    UnitDifference (crown a) (crown b) (k + 9) delta := by
  have hd : (C delta * slope).natDegree ≤ k := by
    calc
      _ ≤ (C delta).natDegree + slope.natDegree := natDegree_mul_le
      _ = k := by rw [natDegree_C, hs.natDegree_eq, zero_add]
  have hm : IsMonicOfDegree (((X + C (a 2)) * slope) * v a) (k + 9) := by
    convert ((isMonicOfDegree_X_add_one (a 2)).mul hs).mul (v_monic a) using 1 <;> omega
  apply unit_difference_of_lower _ _ _ _ _ delta hm
    (zRemainder_degree a _ k hk0 hk2 hd)
  rw [crown_change_z a b _ ha hz, tDelta, mul_left_comm _ (C delta), mul_assoc]

def shift4 (a : ℕ → R) (delta : R) : ℕ → R
  | 1 => a 1 + delta
  | j => a j

theorem shift4_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift4 a delta)) 11 delta := by
  have hc : (C (a 0)).natDegree < 2 := by rw [natDegree_C]; omega
  apply unit_from_z_change a (shift4 a delta) (y + C (a 0)) 2 delta
    (by omega) (by omega) (y_monic.add_right hc)
  · intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    rfl
  · change (y + C (a 0)) * (X + y + C (a 1 + delta)) =
      (y + C (a 0)) * (X + y + C (a 1)) + C delta * (y + C (a 0))
    rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]

def shift5 (a : ℕ → R) (delta : R) : ℕ → R
  | 0 => a 0 + delta
  | 1 => a 1 + delta
  | j => a j

theorem shift5_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift5 a delta)) 10 delta := by
  have hc (b : R) : (C b).natDegree < 1 := by rw [natDegree_C]; omega
  have hs : IsMonicOfDegree ((X : R[X]) + C (a 0) + C (a 1) + C delta) 1 :=
    ((isMonicOfDegree_X_add_one (a 0)).add_right (hc _)).add_right (hc _)
  apply unit_from_z_change a (shift5 a delta)
    (X + C (a 0) + C (a 1) + C delta) 1 delta (by omega) (by omega) hs
  · intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    rfl
  · change (y + C (a 0 + delta)) * (X + y + C (a 1 + delta)) = _
    rw [map_add, map_add, ← add_assoc, ← add_assoc, both_factors]
    have hs : (y + C (a 0)) + (X + y + C (a 1)) = X + C (a 0) + C (a 1) := by
      simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]
    rw [hs, pow_two, add_assoc, ← mul_add]
    rfl

end FastPoly.Char2Degree19InnerZChanges
