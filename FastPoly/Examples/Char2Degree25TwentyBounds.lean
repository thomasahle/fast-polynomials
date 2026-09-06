import FastPoly.Examples.Char2Degree25TwentyWires
import FastPoly.Examples.Char2Degree25TopRows

/-! Degree-eleven bound for the supplied q20 raw direction.
The three named degree-eight brackets have only their top two rows read;
their explicit scalar columns cancel before multiplication by nRight. -/
namespace FastPoly.Char2Degree25TwentyBounds

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame Char2Degree25TwentyWires
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

private theorem Cle (c : R) (n : ℕ) : (C c).natDegree ≤ n := by rw [natDegree_C]; omega
private theorem scaled {p : R[X]} {n : ℕ} (a : R) (hp : p.natDegree ≤ n) :
    (C a * p).natDegree ≤ n := (natDegree_C_mul_le _ _).trans hp
private theorem Cscaled {p : R[X]} {n : ℕ} (a : R) (hp : p.natDegree ≤ n) :
    (p * C a).natDegree ≤ n := by rw [mul_comm]; exact scaled a hp
private theorem above {p : R[X]} {n j : ℕ} (hp : p.natDegree ≤ n) (hj : n < j) :
    p.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (hp.trans_lt hj)

theorem A_monic (a : ℕ → R) : IsMonicOfDegree (A a) 1 := isMonicOfDegree_X_add_one _
theorem L_monic (a : ℕ → R) : IsMonicOfDegree (L a) 1 := isMonicOfDegree_X_add_one _
theorem E_monic (a : ℕ → R) : IsMonicOfDegree (E a) 1 := isMonicOfDegree_X_add_one _
theorem U_monic (a : ℕ → R) : IsMonicOfDegree (U a) 5 :=
  (z_add_t_monic a).add_right (by rw [natDegree_C]; omega)
theorem P_monic (a : ℕ → R) : IsMonicOfDegree (P a) 4 :=
  ((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt (by omega))).add_right
    (by rw [natDegree_C]; omega)
theorem S_monic (a : ℕ → R) : IsMonicOfDegree (S a) 4 :=
  (z_monic a).add_right (by rw [natDegree_C]; omega)
theorem Q_monic (a : ℕ → R) : IsMonicOfDegree (Q a) 3 := by
  rw [Q_eq_inner]
  exact Char2Degree25RowThirteen.inner_monic a

theorem U_four (a : ℕ → R) : (U a).coeff 4 = a 2 := Char2Degree25TopRows.U_four a
theorem P_three (a : ℕ → R) : (P a).coeff 3 = 1 := Char2Degree25TopRows.P_three a
theorem Q_two (a : ℕ → R) : (Q a).coeff 2 = a 2 + 1 := by
  rw [Q_eq_inner]
  exact Char2Degree25TopRows.Q_two a

noncomputable def D2 (a : ℕ → R) : R[X] := rLeft a + G a + 1 + P a
noncomputable def V4 (a : ℕ → R) : R[X] := U a + y + v a + C (a 9)
noncomputable def V4low (a : ℕ → R) : R[X] :=
  C (a 7) * L a + C (a 3) * A a + (C (a 5) + C (a 9))
noncomputable def D3 (a : ℕ → R) (d : R) : R[X] := rLeft a + 1 + W a d
noncomputable def V2 (a : ℕ → R) (d : R) : R[X] := hLeft a + C d + U a
noncomputable def cubicLow (a : ℕ → R) : R[X] :=
  C (B a) * X + C (a 7) * L a + C (B a) * C (a 8) + C (a 3) * A a
noncomputable def D3low (a : ℕ → R) (d : R) : R[X] :=
  X + 1 + C (a 12) + cubicLow a + C (a 9) + C (k a d) * L a + C (c a d)

theorem D2_eq (a : ℕ → R) : D2 a = y + C (a 12 + a 14 + a 8 + 1) := by
  simp only [D2, rLeft, G, P, map_add, map_one, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem D2_monic (a : ℕ → R) : IsMonicOfDegree (D2 a) 2 := by
  rw [D2_eq]
  exact y_monic.add_right (by rw [natDegree_C]; omega)

private theorem vt_collect (ll aa yy zz c7 c3 : R[X]) :
    ll * (yy + zz + c7) + aa * (zz + c3) =
      (ll + aa) * zz + ll * yy + c7 * ll + c3 * aa := by ring

theorem L_add_A (a : ℕ → R) : L a + A a = C (B a) := by
  rw [L_eq, add_right_comm, CharTwo.add_self_eq_zero, zero_add]

theorem VT_eq (a : ℕ → R) : v a + t a =
    C (B a) * z a + L a * y + C (a 7) * L a + C (a 3) * A a := by
  change L a * (y + z a + C (a 7)) + A a * (z a + C (a 3)) = _
  rw [vt_collect, L_add_A]

private theorem v4_reorder (zz tt a5 yy vv a9 : R[X]) :
    (zz + tt + a5) + yy + vv + a9 = zz + yy + (vv + tt) + (a5 + a9) := by ring
private theorem v4_collect (zz yy bb ll c7 c3 cs : R[X]) :
    zz + yy + (bb * zz + ll * yy + c7 + c3) + cs =
      (bb + 1) * zz + (ll + 1) * yy + (c7 + c3 + cs) := by ring

theorem V4_eq (a : ℕ → R) : V4 a =
    C (B a + 1) * z a + (L a + 1) * y + V4low a := by
  have hb : (C (B a + 1) : R[X]) = C (B a) + 1 := by rw [map_add, map_one]
  rw [V4, U, v4_reorder, VT_eq, hb]
  exact v4_collect _ _ _ _ _ _ _

theorem V4low_degree (a : ℕ → R) : (V4low a).natDegree ≤ 1 :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (scaled _ (L_monic a).natDegree_eq.le) (scaled _ (A_monic a).natDegree_eq.le))
    (natDegree_add_le_of_degree_le (Cle _ _) (Cle _ _))

theorem Ly_monic (a : ℕ → R) : IsMonicOfDegree ((L a + 1) * y) 3 :=
  ((L_monic a).add_right (by rw [natDegree_one]; omega)).mul y_monic

theorem V4_degree (a : ℕ → R) : (V4 a).natDegree ≤ 4 := by
  rw [V4_eq]
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (scaled _ (z_monic a).natDegree_eq.le)
      ((Ly_monic a).natDegree_eq.le.trans (by omega)))
    ((V4low_degree a).trans (by omega))

theorem V4_four (a : ℕ → R) : (V4 a).coeff 4 = B a + 1 := by
  have hz := above (Ly_monic a).natDegree_eq.le (by omega : 3 < 4)
  have hl := above (V4low_degree a) (by omega : 1 < 4)
  rw [V4_eq, coeff_add, coeff_add, coeff_C_mul, Char2Degree25TopRows.z_four, mul_one, hz, hl, add_zero, add_zero]

theorem V4_three (a : ℕ → R) : (V4 a).coeff 3 = B a := by
  have hl := above (V4low_degree a) (by omega : 1 < 3)
  rw [V4_eq, coeff_add, coeff_add, coeff_C_mul, Char2Degree25TopRows.z_three,
    mul_one, Char2Degree25TopRows.monic_coeff (Ly_monic a), hl, add_zero, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

private theorem cubic_cancel (aa bb xx yy zz c7 c8 c3 : R[X]) :
    ((aa + bb) * (yy + zz + c7) + aa * (zz + c3)) + bb * (xx + yy + zz + c8) =
      aa * yy + (bb * xx + c7 * (aa + bb) + bb * c8 + c3 * aa) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem VT_P_eq (a : ℕ → R) : (v a + t a) + C (B a) * P a = A a * y + cubicLow a := by
  change (L a * (y + z a + C (a 7)) + A a * (z a + C (a 3))) +
    C (B a) * (X + y + z a + C (a 8)) = _
  rw [L_eq]
  change _ = A a * y +
    (C (B a) * X + C (a 7) * L a + C (B a) * C (a 8) + C (a 3) * A a)
  rw [L_eq]
  exact cubic_cancel _ _ _ _ _ _ _ _

theorem D3_eq (a : ℕ → R) (d : R) : D3 a d = A a * y + y + D3low a d := by
  have he : D3 a d = ((v a + t a) + C (B a) * P a) + y +
      (X + 1 + C (a 12) + C (a 9) + C (k a d) * L a + C (c a d)) := by
    unfold D3 rLeft W
    ac_rfl
  rw [he, VT_P_eq]
  unfold D3low
  ac_rfl

theorem cubicLow_degree (a : ℕ → R) : (cubicLow a).natDegree ≤ 1 :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (scaled _ natDegree_X_le)
        (scaled _ (L_monic a).natDegree_eq.le))
      (scaled _ (Cle _ _)))
    (scaled _ (A_monic a).natDegree_eq.le)

theorem D3low_degree (a : ℕ → R) (d : R) : (D3low a d).natDegree ≤ 1 :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          (natDegree_add_le_of_degree_le
            (natDegree_add_le_of_degree_le natDegree_X_le (by rw [natDegree_one]; omega))
            (Cle _ _)) (cubicLow_degree a)) (Cle _ _))
      (scaled _ (L_monic a).natDegree_eq.le)) (Cle _ _)

theorem D3_monic (a : ℕ → R) (d : R) : IsMonicOfDegree (D3 a d) 3 := by
  rw [D3_eq]
  exact (((A_monic a).mul y_monic).add_right
    (y_monic.natDegree_eq.trans_lt (by omega))).add_right ((D3low_degree a d).trans_lt (by omega))

theorem D3_two (a : ℕ → R) (d : R) : (D3 a d).coeff 2 = a 2 + 1 := by
  have hz := above (D3low_degree a d) (by omega : 1 < 2)
  have ha : (A a * y).coeff 2 = a 2 := by
    change ((X + C (a 2)) * y).coeff (1 + 1) = _
    rw [Char2Degree25TopRows.linear_mul_coeff, Char2Degree25TopRows.y_other 1 (by omega),
      Char2Degree25TopRows.y_two, zero_add, mul_one]
  rw [D3_eq, coeff_add, coeff_add, ha, Char2Degree25TopRows.y_two, hz, add_zero]

theorem V2_eq (a : ℕ → R) (d : R) : V2 a d = y + C (a 18 + d + a 5) := by
  simp only [V2, hLeft, U, map_add, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem V2_monic (a : ℕ → R) (d : R) : IsMonicOfDegree (V2 a d) 2 := by
  rw [V2_eq]
  exact y_monic.add_right (by rw [natDegree_C]; omega)

theorem W_monic (a : ℕ → R) (d : R) : IsMonicOfDegree (W a d) 5 := by
  have hp : (C (B a) * P a).natDegree < 5 :=
    (scaled _ (P_monic a).natDegree_eq.le).trans_lt (by omega)
  have hl : (C (k a d) * L a).natDegree < 5 :=
    (scaled _ (L_monic a).natDegree_eq.le).trans_lt (by omega)
  exact (((((v_monic a).add_left (y_monic.natDegree_eq.trans_lt (by omega))).add_right hp).add_right
    ((Cle (a 9) 0).trans_lt (by omega))).add_right hl).add_right
      ((Cle (c a d) 0).trans_lt (by omega))

private theorem paired_cancel (aa pp uu vv : R[X]) :
    aa * uu + pp * vv = (aa + pp) * uu + pp * (uu + vv) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem T1_eq (a : ℕ → R) : T1 a = D2 a * U a + P a * V4 a := by
  change (rLeft a + G a + 1) * U a + P a * (y + v a + C (a 9)) = _
  have hv : U a + (y + v a + C (a 9)) = V4 a := by simp only [V4, add_assoc]
  rw [paired_cancel]
  rw [hv]
  rfl

private theorem paired_second (aa hh uu ww : R[X]) :
    aa * uu + hh * ww = (aa + ww) * uu + (hh + uu) * ww := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem T2_eq (a : ℕ → R) (d : R) :
    T2 a d = D3 a d * U a + V2 a d * W a d := by
  change (rLeft a + 1) * U a + (hLeft a + C d) * W a d = _
  exact paired_second _ _ _ _

theorem T1_degree (a : ℕ → R) : (T1 a).natDegree ≤ 8 := by
  rw [T1_eq]
  exact natDegree_add_le_of_degree_le
    (((D2_monic a).mul (U_monic a)).natDegree_eq.le.trans (by omega))
    (natDegree_mul_le.trans (Nat.add_le_add (P_monic a).natDegree_eq.le (V4_degree a)))

theorem T2_monic (a : ℕ → R) (d : R) : IsMonicOfDegree (T2 a d) 8 := by
  rw [T2_eq]
  exact ((D3_monic a d).mul (U_monic a)).add_right
    (((V2_monic a d).mul (W_monic a d)).natDegree_eq.trans_lt (by omega))

theorem HQ_monic (a : ℕ → R) (d : R) : IsMonicOfDegree ((hLeft a + C d) * Q a) 8 :=
  ((hLeft_monic a).add_right ((Cle d 0).trans_lt (by omega))).mul (Q_monic a)
theorem JEL_monic (a : ℕ → R) : IsMonicOfDegree (jLeft a * E a * L a) 7 :=
  ((jLeft_monic a).mul (E_monic a)).mul (L_monic a)
theorem T3_monic (a : ℕ → R) (d : R) : IsMonicOfDegree (T3 a d) 8 :=
  (HQ_monic a d).add_right ((JEL_monic a).natDegree_eq.trans_lt (by omega))

theorem T1_eight (a : ℕ → R) : (T1 a).coeff 8 = B a + 1 := by
  have hz := above ((D2_monic a).mul (U_monic a)).natDegree_eq.le (by omega : 7 < 8)
  have hp : (P a * V4 a).coeff 8 = (P a).coeff 4 * (V4 a).coeff 4 :=
    coeff_mul_add_eq_of_natDegree_le (P_monic a).natDegree_eq.le (V4_degree a)
  rw [T1_eq, coeff_add, hz, zero_add, hp, Char2Degree25TopRows.monic_coeff (P_monic a), V4_four, one_mul]

theorem T1_seven (a : ℕ → R) : (T1 a).coeff 7 = 0 := by
  have hp : (P a * V4 a).coeff 7 =
      (P a).coeff 4 * (V4 a).coeff 3 + (P a).coeff 3 * (V4 a).coeff 4 :=
    Char2Degree25TopRows.two_top_product (dp := 3) (dq := 3) (P_monic a).natDegree_eq.le (V4_degree a)
  rw [T1_eq, coeff_add, Char2Degree25TopRows.monic_coeff ((D2_monic a).mul (U_monic a)),
    hp, Char2Degree25TopRows.monic_coeff (P_monic a), V4_three, P_three, V4_four, one_mul, one_mul]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem T2_eight (a : ℕ → R) (d : R) : (T2 a d).coeff 8 = 1 :=
  Char2Degree25TopRows.monic_coeff (T2_monic a d)

theorem T2_seven (a : ℕ → R) (d : R) : (T2 a d).coeff 7 = 0 := by
  have hp : (D3 a d * U a).coeff 7 =
      (D3 a d).coeff 3 * (U a).coeff 4 + (D3 a d).coeff 2 * (U a).coeff 5 :=
    Char2Degree25TopRows.two_top_product (dp := 2) (dq := 4)
      (D3_monic a d).natDegree_eq.le (U_monic a).natDegree_eq.le
  rw [T2_eq, coeff_add, hp, Char2Degree25TopRows.monic_coeff (D3_monic a d),
    U_four, D3_two, Char2Degree25TopRows.monic_coeff (U_monic a),
    Char2Degree25TopRows.monic_coeff ((V2_monic a d).mul (W_monic a d)), one_mul, mul_one]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem T3_eight (a : ℕ → R) (d : R) : (T3 a d).coeff 8 = 1 :=
  Char2Degree25TopRows.monic_coeff (T3_monic a d)

theorem T3_seven (a : ℕ → R) (d : R) : (T3 a d).coeff 7 = 0 := by
  have hh : IsMonicOfDegree (hLeft a + C d) 5 :=
    (hLeft_monic a).add_right ((Cle d 0).trans_lt (by omega))
  have hp : ((hLeft a + C d) * Q a).coeff 7 =
      (hLeft a + C d).coeff 5 * (Q a).coeff 2 + (hLeft a + C d).coeff 4 * (Q a).coeff 3 :=
    Char2Degree25TopRows.two_top_product (dp := 4) (dq := 2) hh.natDegree_eq.le (Q_monic a).natDegree_eq.le
  have h4 : (hLeft a + C d).coeff 4 = a 2 := by
    simp only [coeff_add, coeff_C_succ, add_zero, Char2Degree25TopRows.H_four]
  rw [T3, coeff_add, hp, Char2Degree25TopRows.monic_coeff hh, Q_two, h4,
    Char2Degree25TopRows.monic_coeff (Q_monic a), Char2Degree25TopRows.monic_coeff (JEL_monic a),
    one_mul, mul_one]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem low_degree (a : ℕ → R) (d : R) : (low a d).natDegree ≤ 5 := by
  have hsl : (S a * L a).natDegree ≤ 5 := ((S_monic a).mul (L_monic a)).natDegree_eq.le
  have hel : (E a * L a).natDegree ≤ 5 := ((E_monic a).mul (L_monic a)).natDegree_eq.le.trans (by omega)
  have hfirst : (S a * L a + rLeft a + E a * L a).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hsl (rLeft_monic a).natDegree_eq.le) hel
  have hx : (X + y + z a).natDegree ≤ 5 :=
    ((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt (by omega))).natDegree_eq.le.trans (by omega)
  have hsecond : (X + y + z a + v a + rLeft a * C (a 13) + C (a 19)).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hx (v_monic a).natDegree_eq.le)
        (Cscaled _ (rLeft_monic a).natDegree_eq.le)) (Cle _ _)
  exact natDegree_add_le_of_degree_le (scaled _ hfirst) (scaled _ hsecond)

theorem deltaN_degree8 (a : ℕ → R) (d : R) : (deltaN a d).natDegree ≤ 8 :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (scaled _ (T1_degree a)) (scaled _ (T2_monic a d).natDegree_eq.le))
      (scaled _ (T3_monic a d).natDegree_eq.le)) ((low_degree a d).trans (by omega))

private theorem column_cancel (d b l : R) : d * (b + 1) + l + (l + (b + 1) * d) = 0 := by
  rw [mul_comm d (b + 1)]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem deltaN_eight (a : ℕ → R) (d : R) : (deltaN a d).coeff 8 = 0 := by
  have hz := above (low_degree a d) (by omega : 5 < 8)
  rw [deltaN, coeff_add, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    T1_eight, T2_eight, T3_eight, hz, mul_one, mul_one, add_zero]
  exact column_cancel _ _ _

theorem deltaN_seven (a : ℕ → R) (d : R) : (deltaN a d).coeff 7 = 0 := by
  have hz := above (low_degree a d) (by omega : 5 < 7)
  simp only [deltaN, coeff_add, coeff_C_mul, T1_seven, T2_seven, T3_seven, hz, mul_zero, add_zero]

theorem deltaN_degree (a : ℕ → R) (d : R) : (deltaN a d).natDegree ≤ 6 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_cases h7 : j = 7
  · subst j; exact deltaN_seven a d
  by_cases h8 : j = 8
  · subst j; exact deltaN_eight a d
  exact above (deltaN_degree8 a d) (by omega)

theorem outputDelta_degree (a : ℕ → R) (d : R) : (outputDelta a d).natDegree ≤ 11 := by
  have hu : (C d * U a).natDegree ≤ 11 :=
    (scaled _ (U_monic a).natDegree_eq.le).trans (by omega)
  have he : (C (k a d) * (E a * L a)).natDegree ≤ 11 :=
    (scaled _ ((E_monic a).mul (L_monic a)).natDegree_eq.le).trans (by omega)
  have hn : (nRight a * deltaN a d).natDegree ≤ 11 :=
    natDegree_mul_le.trans (Nat.add_le_add (nRight_monic a).natDegree_eq.le (deltaN_degree a d))
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hu he) hn

theorem output_difference_degree (a : ℕ → R) (d : R) :
    (Char2Degree25Frame.output (shift a d) + Char2Degree25Frame.output a).natDegree ≤ 11 := by
  rw [output_shift, Char2Decoder.cancel_tail]
  exact outputDelta_degree a d

end FastPoly.Char2Degree25TwentyBounds
