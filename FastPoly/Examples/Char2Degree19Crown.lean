import FastPoly.Examples.Char2Degree19Shell
import Mathlib.Algebra.Polynomial.Expand

/-!
# The existing degree-19 circuit's cubic-shell signature

The only gate identities opened here are its two quadratic products in `z`
and `v`. Each is rewritten once as a square plus a lower-degree correction.
All earlier gates stay named. Frobenius gives the missing odd square rows;
degree bounds kill the low corrections. This bridges the actual circuit to
the explicit outer inverse in `Char2Degree19Shell`.

The inner crown's thirteen coordinate pivots remain separate obligations.
-/

namespace FastPoly.Char2Degree19Crown

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Shell

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def y : R[X] := X ^ 2
noncomputable def z (a : ℕ → R) : R[X] :=
  (y + C (a 0)) * (X + y + C (a 1))
noncomputable def t (a : ℕ → R) : R[X] := (X + C (a 2)) * (z a + C (a 3))
noncomputable def u (a : ℕ → R) : R[X] :=
  (y + t a + C (a 4)) * (z a + t a + C (a 5))
noncomputable def v (a : ℕ → R) : R[X] :=
  (X + z a + C (a 6)) * (z a + C (a 7))
noncomputable def w (a : ℕ → R) : R[X] :=
  (X + y + z a + C (a 8)) * (y + v a + C (a 9))
noncomputable def s (a : ℕ → R) : R[X] := (X + C (a 10)) * (y + C (a 11))
noncomputable def r (a : ℕ → R) : R[X] := (X + C (a 12)) * (y + C (a 13))
noncomputable def q (a : ℕ → R) : R[X] :=
  (v a + C (a 14)) * (t a + v a + s a + C (a 15))
noncomputable def crown (a : ℕ → R) : R[X] := u a + w a + q a + C (a 17)
noncomputable def output (a : ℕ → R) : R[X] :=
  r a + (s a + C (a 16)) * crown a + C (a 18)

omit [CharP R 2] [Nontrivial R] in
private theorem const_lt (a : R) (n : ℕ) (hn : 0 < n) : (C a).natDegree < n := by
  rw [natDegree_C]
  exact hn

omit [CharP R 2] in
theorem y_monic : IsMonicOfDegree (y : R[X]) 2 := isMonicOfDegree_X_pow R 2

omit [CharP R 2] in
theorem z_monic (a : ℕ → R) : IsMonicOfDegree (z a) 4 := by
  have hxy : IsMonicOfDegree ((X : R[X]) + y) 2 :=
    y_monic.add_left (natDegree_X_le.trans_lt (by omega))
  exact (y_monic.add_right (const_lt _ 2 (by omega))).mul
    (hxy.add_right (const_lt _ 2 (by omega)))

theorem t_monic (a : ℕ → R) : IsMonicOfDegree (t a) 5 :=
  (isMonicOfDegree_X_add_one (a 2)).mul ((z_monic a).add_right (const_lt _ 4 (by omega)))

theorem u_monic (a : ℕ → R) : IsMonicOfDegree (u a) 10 := by
  have hyt : IsMonicOfDegree (y + t a) 5 :=
    (t_monic a).add_left ((y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 5))
  have hzt : IsMonicOfDegree (z a + t a) 5 :=
    (t_monic a).add_left ((z_monic a).natDegree_eq ▸ (by omega : 4 < 5))
  exact (hyt.add_right (const_lt _ 5 (by omega))).mul (hzt.add_right (const_lt _ 5 (by omega)))

theorem v_monic (a : ℕ → R) : IsMonicOfDegree (v a) 8 := by
  have hxz : IsMonicOfDegree (X + z a) 4 :=
    (z_monic a).add_left (natDegree_X_le.trans_lt (by omega))
  exact (hxz.add_right (const_lt _ 4 (by omega))).mul
    ((z_monic a).add_right (const_lt _ 4 (by omega)))

theorem w_monic (a : ℕ → R) : IsMonicOfDegree (w a) 12 := by
  have hxy : IsMonicOfDegree ((X : R[X]) + y) 2 :=
    y_monic.add_left (natDegree_X_le.trans_lt (by omega))
  have hxyz : IsMonicOfDegree (X + y + z a) 4 :=
    (z_monic a).add_left (hxy.natDegree_eq ▸ (by omega : 2 < 4))
  have hyv : IsMonicOfDegree (y + v a) 8 :=
    (v_monic a).add_left ((y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 8))
  exact (hxyz.add_right (const_lt _ 4 (by omega))).mul (hyv.add_right (const_lt _ 8 (by omega)))

omit [CharP R 2] in
theorem s_monic (a : ℕ → R) : IsMonicOfDegree (s a) 3 :=
  (isMonicOfDegree_X_add_one (a 10)).mul (y_monic.add_right (const_lt _ 2 (by omega)))

omit [CharP R 2] [Nontrivial R] in
/-- A local, three-input product identity; no circuit is expanded. -/
private theorem product_square (v a b : R[X]) :
    (v + a) * (v + b) = v ^ 2 + (a + b) * v + a * b := by
  rw [pow_two, add_mul, mul_add, mul_add, add_mul, mul_comm v b]
  simp only [add_assoc, add_comm, add_left_comm]

noncomputable def vTail (a : ℕ → R) : R[X] :=
  (X + C (a 6) + C (a 7)) * z a + (X + C (a 6)) * C (a 7)

theorem v_split (a : ℕ → R) : v a = z a ^ 2 + vTail a := by
  change (X + z a + C (a 6)) * (z a + C (a 7)) = _
  rw [add_right_comm X (z a), add_comm (X + C (a 6)), product_square]
  exact add_assoc _ _ _

theorem vTail_degree (a : ℕ → R) : (vTail a).natDegree ≤ 5 := by
  have h1 : IsMonicOfDegree ((X : R[X]) + C (a 6) + C (a 7)) 1 :=
    (isMonicOfDegree_X_add_one (a 6)).add_right (const_lt _ 1 (by omega))
  have hleft : ((X + C (a 6) + C (a 7)) * z a).natDegree = 5 :=
    (h1.mul (z_monic a)).natDegree_eq
  have hright : (((X : R[X]) + C (a 6)) * C (a 7)).natDegree ≤ 1 := by
    calc
      _ ≤ ((X : R[X]) + C (a 6)).natDegree + (C (a 7)).natDegree := natDegree_mul_le
      _ = 1 := by rw [(isMonicOfDegree_X_add_one (a 6)).natDegree_eq, natDegree_C]
  exact natDegree_add_le_of_degree_le hleft.le (hright.trans (by omega))

omit [Nontrivial R] in
/-- Frobenius reads a square row without opening any coefficients of `p`. -/
theorem square_coeff_odd (p : R[X]) (j : ℕ) : (p ^ 2).coeff (2 * j + 1) = 0 := by
  have hn : ¬ 2 ∣ 2 * j + 1 := by omega
  rw [← map_frobenius_expand 2 p, coeff_map, coeff_expand (by omega), if_neg hn, map_zero]

omit [Nontrivial R] in
theorem square_coeff_even (p : R[X]) (j : ℕ) : (p ^ 2).coeff (2 * j) = p.coeff j ^ 2 := by
  rw [← map_frobenius_expand 2 p, coeff_map, coeff_expand_mul' (by omega), frobenius_def]

theorem v_row7 (a : ℕ → R) : (v a).coeff 7 = 0 := by
  have hz : (vTail a).coeff 7 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((vTail_degree a).trans_lt (by omega))
  rw [v_split, coeff_add, square_coeff_odd (z a) 3, hz, add_zero]

noncomputable def middle (a : ℕ → R) : R[X] := t a + s a + C (a 14) + C (a 15)
noncomputable def qLow (a : ℕ → R) : R[X] := C (a 14) * (t a + s a + C (a 15))
noncomputable def crownLow (a : ℕ → R) : R[X] := u a + w a + qLow a + C (a 17)

theorem q_split (a : ℕ → R) : q a = v a ^ 2 + middle a * v a + qLow a := by
  change (v a + C (a 14)) * (t a + v a + s a + C (a 15)) = _
  have h : t a + v a + s a + C (a 15) = v a + (t a + s a + C (a 15)) := by ac_rfl
  rw [h, product_square]
  unfold middle qLow
  congr 2
  ac_rfl

theorem crown_split (a : ℕ → R) :
    crown a = v a ^ 2 + middle a * v a + crownLow a := by
  rw [crown, q_split]
  unfold crownLow
  ac_rfl

theorem middle_monic (a : ℕ → R) : IsMonicOfDegree (middle a) 5 := by
  have hts : IsMonicOfDegree (t a + s a) 5 :=
    (t_monic a).add_right ((s_monic a).natDegree_eq ▸ (by omega : 3 < 5))
  exact (hts.add_right (const_lt _ 5 (by omega))).add_right (const_lt _ 5 (by omega))

theorem crownLow_degree (a : ℕ → R) : (crownLow a).natDegree ≤ 12 := by
  have hts : IsMonicOfDegree (t a + s a + C (a 15)) 5 :=
    ((t_monic a).add_right ((s_monic a).natDegree_eq ▸ (by omega : 3 < 5))).add_right
      (const_lt _ 5 (by omega))
  have hq : (qLow a).natDegree ≤ 5 := by
    calc
      _ ≤ (C (a 14)).natDegree + (t a + s a + C (a 15)).natDegree := natDegree_mul_le
      _ = 5 := by rw [natDegree_C, hts.natDegree_eq]
  have huw : (u a + w a).natDegree ≤ 12 := natDegree_add_le_of_degree_le
    ((u_monic a).natDegree_eq ▸ (by omega : 10 ≤ 12)) (w_monic a).natDegree_eq.le
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le huw (hq.trans (by omega))) (by rw [natDegree_C]; omega)

theorem crown_monic (a : ℕ → R) : IsMonicOfDegree (crown a) 16 := by
  rw [crown_split]
  have hv : IsMonicOfDegree (v a ^ 2) 16 := (v_monic a).pow 2
  have hmv : IsMonicOfDegree (middle a * v a) 13 := (middle_monic a).mul (v_monic a)
  exact (hv.add_right (hmv.natDegree_eq ▸ (by omega : 13 < 16))).add_right
    ((crownLow_degree a).trans_lt (by omega))

theorem crown_row15 (a : ℕ → R) : (crown a).coeff 15 = 0 := by
  have hm : (middle a * v a).coeff 15 = 0 := coeff_eq_zero_of_natDegree_lt
    (((middle_monic a).mul (v_monic a)).natDegree_eq ▸ (by omega : 13 < 15))
  have hl : (crownLow a).coeff 15 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((crownLow_degree a).trans_lt (by omega))
  rw [crown_split, coeff_add, coeff_add, square_coeff_odd (v a) 7, hm, hl, add_zero, add_zero]

theorem crown_row14 (a : ℕ → R) : (crown a).coeff 14 = 0 := by
  have hm : (middle a * v a).coeff 14 = 0 := coeff_eq_zero_of_natDegree_lt
    (((middle_monic a).mul (v_monic a)).natDegree_eq ▸ (by omega : 13 < 14))
  have hl : (crownLow a).coeff 14 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((crownLow_degree a).trans_lt (by omega))
  rw [crown_split, coeff_add, coeff_add, square_coeff_even (v a) 7, v_row7,
    zero_pow (by omega), hm, hl, add_zero, add_zero]

theorem crown_row13 (a : ℕ → R) : (crown a).coeff 13 = 1 := by
  have hmv : IsMonicOfDegree (middle a * v a) 13 := (middle_monic a).mul (v_monic a)
  have hm : (middle a * v a).coeff 13 = 1 := by
    rw [← hmv.natDegree_eq]
    exact hmv.monic.coeff_natDegree
  have hl : (crownLow a).coeff 13 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((crownLow_degree a).trans_lt (by omega))
  rw [crown_split, coeff_add, coeff_add, square_coeff_odd (v a) 6, hm, hl, zero_add, add_zero]

theorem crown_signature (a : ℕ → R) : Signature (crown a) :=
  ⟨crown_monic a, crown_row15 a, crown_row14 a, crown_row13 a⟩

/-- The one cubic gate, with its output constant included. -/
theorem cubic_gate (a b d : R) :
    ((X : R[X]) + C a) * (X ^ 2 + C b) + C d = cubic (a, b, d) := by
  change ((X : R[X]) + C a) * (X ^ 2 + C b) + C d =
    X ^ 3 + (C a * X ^ 2 + C b * X + C (a * b + d))
  rw [map_add, map_mul, add_mul, mul_add, mul_add,
    ← pow_succ', mul_comm (X : R[X]) (C b)]
  simp only [add_assoc, add_comm, add_left_comm]

/-- The six outer offsets, with the still-undecoded crown kept as a wire. -/
noncomputable def outerData (a : ℕ → R) : Triple R × (R[X] × Triple R) :=
  ((a 10, a 11, a 16), crown a, a 12, a 13, a 18)

theorem output_eq_encode (a : ℕ → R) : output a = encode (outerData a) := by
  have hs : s a + C (a 16) = cubic (a 10, a 11, a 16) :=
    cubic_gate (a 10) (a 11) (a 16)
  have hr : r a + C (a 18) = cubic (a 12, a 13, a 18) :=
    cubic_gate (a 12) (a 13) (a 18)
  change r a + (s a + C (a 16)) * crown a + C (a 18) =
    cubic (a 10, a 11, a 16) * crown a + cubic (a 12, a 13, a 18)
  rw [hs, add_right_comm, hr, add_comm]

/-- The supplied explicit inverse recovers all six outer offsets and the
entire inner crown from the actual ten-product circuit output. -/
theorem decode_output (a : ℕ → R) : decode (output a) = outerData a := by
  rw [output_eq_encode]
  exact decode_encode (outerData a) (crown_signature a)

end FastPoly.Char2Degree19Crown
