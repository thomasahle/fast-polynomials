import FastPoly.Examples.Char2Degree25TwentyOneWires
import FastPoly.Examples.Char2Degree25TopRows

/-! Small cancellation frame for the q21 difference. The shared quintic
square is cancelled before any coefficient read. Only rows eight and seven
of the remaining degree-eight frame are read, leaving a degree-six slope
and a degree-eleven output difference. -/
namespace FastPoly.Char2Degree25TwentyOneBounds

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame Char2Degree25TwentyOneWires
open Char2Degree25RowThirteen (B L P)
open Char2Degree25TopRows
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def vt (a : ℕ → R) : R[X] :=
  C (B a) * z a + L a * y + L a * C (a 7) + A a * C (a 3)
noncomputable def H4 (a : ℕ → R) : R[X] := y + z a + C (a 18)
noncomputable def J2 (a : ℕ → R) : R[X] := X + y + C (a 20)
noncomputable def W4 (a : ℕ → R) (d : R) : R[X] := W a d + t a
noncomputable def V4 (a : ℕ → R) (d : R) : R[X] := V a d + t a
noncomputable def C3 (a : ℕ → R) (d : R) : R[X] :=
  H4 a + J2 a + W4 a d + V4 a d
noncomputable def cross (a : ℕ → R) (d : R) : R[X] :=
  t a * C3 a d + H4 a * W4 a d + J2 a * V4 a d

private theorem vt_identity (x y z a b c e : R[X]) :
    (x + b) * (y + z + c) + (x + a) * (z + e) =
      (a + b) * z + (x + b) * y + (x + b) * c + (x + a) * e := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem v_add_t (a : ℕ → R) : v a + t a = vt a := by
  change (X + C (a 6)) * (y + z a + C (a 7)) +
    (X + C (a 2)) * (z a + C (a 3)) = _
  rw [vt, show C (B a) = C (a 2) + C (a 6) by rw [B, map_add]]
  exact vt_identity _ _ _ _ _ _ _

private theorem collect_W4 (b q y v c k a t : R[X]) :
    (b * q + y + v + c + k * a) + t = b * q + y + (v + t) + c + k * a := by ring

theorem W4_shape (a : ℕ → R) (d : R) : W4 a d =
    C (B a) * Q a + y + vt a + C (a 9) + C (B a * d) * A a := by
  rw [W4, W, collect_W4, v_add_t]

private theorem collect_V4 (z v c b e d l t : R[X]) :
    (z + v + c + b * (e + d) * l) + t = z + (v + t) + c + b * (e + d) * l := by ring

theorem V4_shape (a : ℕ → R) (d : R) : V4 a d =
    z a + vt a + C (a 17) + C (B a) * (E a + C d) * L a := by
  rw [V4, V, collect_V4, v_add_t]

private theorem c3_collect (x y z h j b q vt c k a v e d l : R[X])
    (hk : k = b * d) (hab : a + l = b) :
    (y + z + h) + (x + y + j) +
      (b * q + y + vt + c + k * a) +
      (z + vt + v + b * (e + d) * l) =
    x + y + b * q + b * e * l + (h + j + c + v + b * b * d) := by
  have hthree : (3 : R[X]) = 1 := by
    calc
      (3 : R[X]) = 2 + 1 := by ring
      _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]
  rw [hk]
  have hcancel : b * d * a + b * d * l = b * b * d := by
    rw [← mul_add, hab]
    ring
  calc
    _ = x + y + b * q + b * e * l + (h + j + c + v) +
        (b * d * a + b * d * l) := by
      ring_nf
      simp only [CharTwo.two_eq_zero, hthree, mul_one, mul_zero, add_zero, zero_add]
    _ = _ := by rw [hcancel]; ring

theorem C3_shape (a : ℕ → R) (d : R) : C3 a d =
    X + y + C (B a) * Q a + C (B a) * E a * L a +
      C (a 18 + a 20 + a 9 + a 17 + B a * B a * d) := by
  rw [C3, W4_shape, V4_shape]
  have hab : A a + L a = C (B a) := by
    simp only [A, L, B, map_add, add_assoc, add_comm, add_left_comm,
      CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]
  have hc := c3_collect (X : R[X]) y (z a) (C (a 18)) (C (a 20)) (C (B a))
    (Q a) (vt a) (C (a 9)) (C (B a * d)) (A a) (C (a 17)) (E a) (C d) (L a)
    (map_mul C (B a) d) hab
  simp only [map_add, map_mul] at hc ⊢
  exact hc

private theorem shared_square (t h j w v : R[X]) :
    (t + h) * (t + w) + (t + j) * (t + v) =
      t * (h + j + w + v) + h * w + j * v := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem restore (p t : R[X]) : t + (p + t) = p := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem cross_eq (a : ℕ → R) (d : R) :
    hLeft a * W a d + jLeft a * V a d = cross a d := by
  have hh : hLeft a = t a + H4 a := by
    change y + z a + t a + C (a 18) = t a + (y + z a + C (a 18))
    ac_rfl
  have hj : jLeft a = t a + J2 a := by
    change X + y + t a + C (a 20) = t a + (X + y + C (a 20))
    ac_rfl
  have hw : W a d = t a + W4 a d := (restore (W a d) (t a)).symm
  have hv : V a d = t a + V4 a d := (restore (V a d) (t a)).symm
  rw [hh, hj, hw, hv]
  exact shared_square _ _ _ _ _

private theorem scaled_degree (c : R) {p : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) : (C c * p).natDegree ≤ n := by
  exact natDegree_mul_le.trans (by rw [natDegree_C]; omega)
private theorem right_constant_degree (c : R) {p : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) : (p * C c).natDegree ≤ n := by
  exact natDegree_mul_le.trans (by rw [natDegree_C]; omega)
private theorem mul_degree {p q : R[X]} {m n : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).natDegree ≤ m + n :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)
private theorem c_degree (c : R) (n : ℕ) : (C c : R[X]).natDegree ≤ n := by
  rw [natDegree_C]
  omega
private theorem A_monic (a : ℕ → R) : IsMonicOfDegree (A a) 1 :=
  isMonicOfDegree_X_add_one _
private theorem E_monic (a : ℕ → R) : IsMonicOfDegree (E a) 1 :=
  isMonicOfDegree_X_add_one _
private theorem Ly_monic (a : ℕ → R) : IsMonicOfDegree (L a * y) 3 :=
  (Char2Degree25RowThirteen.L_monic a).mul y_monic
private theorem EL_monic (a : ℕ → R) : IsMonicOfDegree (E a * L a) 2 :=
  (E_monic a).mul (Char2Degree25RowThirteen.L_monic a)

theorem vt_degree (a : ℕ → R) : (vt a).natDegree ≤ 4 :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (scaled_degree _ (z_monic a).natDegree_eq.le)
        ((Ly_monic a).natDegree_eq.le.trans (by omega)))
      ((right_constant_degree _ (Char2Degree25RowThirteen.L_monic a).natDegree_eq.le).trans (by omega)))
    ((right_constant_degree _ (A_monic a).natDegree_eq.le).trans (by omega))

theorem H4_monic (a : ℕ → R) : IsMonicOfDegree (H4 a) 4 :=
  ((z_monic a).add_left (y_monic.natDegree_eq.trans_lt (by omega))).add_right
    (by rw [natDegree_C]; omega)
theorem J2_monic (a : ℕ → R) : IsMonicOfDegree (J2 a) 2 :=
  x_add_y_monic.add_right (by rw [natDegree_C]; omega)

theorem W4_degree (a : ℕ → R) (d : R) : (W4 a d).natDegree ≤ 4 := by
  rw [W4_shape]
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          ((scaled_degree _ (Q_monic a).natDegree_eq.le).trans (by omega))
          (y_monic.natDegree_eq.le.trans (by omega))) (vt_degree a)) (c_degree _ _))
    ((scaled_degree _ (A_monic a).natDegree_eq.le).trans (by omega))

theorem V4_degree (a : ℕ → R) (d : R) : (V4 a d).natDegree ≤ 4 := by
  have he : (E a + C d).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (E_monic a).natDegree_eq.le (c_degree _ _)
  rw [V4_shape]
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (z_monic a).natDegree_eq.le (vt_degree a)) (c_degree _ _))
    ((mul_degree (scaled_degree _ he) (Char2Degree25RowThirteen.L_monic a).natDegree_eq.le).trans (by omega))

theorem C3_degree (a : ℕ → R) (d : R) : (C3 a d).natDegree ≤ 3 := by
  rw [C3_shape]
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (x_add_y_monic.natDegree_eq.le.trans (by omega))
        (scaled_degree _ (Q_monic a).natDegree_eq.le))
      ((mul_degree (scaled_degree _ (E_monic a).natDegree_eq.le)
        (Char2Degree25RowThirteen.L_monic a).natDegree_eq.le).trans (by omega))) (c_degree _ _)

private theorem vt_row (a : ℕ → R) (n : ℕ) (hn : 1 < n) :
    (vt a).coeff n = B a * (z a).coeff n + (L a * y).coeff n := by
  have hl : (L a * C (a 7)).coeff n = 0 := coeff_eq_zero_of_natDegree_lt
    ((right_constant_degree _ (Char2Degree25RowThirteen.L_monic a).natDegree_eq.le).trans_lt hn)
  have ha : (A a * C (a 3)).coeff n = 0 := coeff_eq_zero_of_natDegree_lt
    ((right_constant_degree _ (A_monic a).natDegree_eq.le).trans_lt hn)
  simp only [vt, coeff_add, coeff_C_mul, hl, ha, add_zero]

theorem vt_four (a : ℕ → R) : (vt a).coeff 4 = B a := by
  have hz : (L a * y).coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt
    ((Ly_monic a).natDegree_eq.trans_lt (by omega))
  rw [vt_row a 4 (by omega), z_four, hz, mul_one, add_zero]
theorem vt_three (a : ℕ → R) : (vt a).coeff 3 = B a + 1 := by
  rw [vt_row a 3 (by omega), z_three, monic_coeff (Ly_monic a), mul_one]

private theorem W4_row (a : ℕ → R) (d : R) (n : ℕ) (hn : 2 < n) :
    (W4 a d).coeff n = B a * (Q a).coeff n + (vt a).coeff n := by
  have hy : (y : R[X]).coeff n = 0 := coeff_eq_zero_of_natDegree_lt
    (y_monic.natDegree_eq.trans_lt hn)
  have hc : (C (a 9)).coeff n = 0 := coeff_eq_zero_of_natDegree_lt
    (by rw [natDegree_C]; omega)
  have ha : (C (B a * d) * A a).coeff n = 0 := coeff_eq_zero_of_natDegree_lt
    ((scaled_degree _ (A_monic a).natDegree_eq.le).trans_lt (by omega))
  rw [W4_shape]
  simp only [coeff_add, coeff_C_mul, hy, hc, ha, add_zero]

theorem W4_four (a : ℕ → R) (d : R) : (W4 a d).coeff 4 = B a := by
  have hq : (Q a).coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt
    ((Q_monic a).natDegree_eq.trans_lt (by omega))
  rw [W4_row a d 4 (by omega), hq, vt_four, mul_zero, zero_add]
theorem W4_three (a : ℕ → R) (d : R) : (W4 a d).coeff 3 = 1 := by
  rw [W4_row a d 3 (by omega), monic_coeff (Q_monic a), vt_three, mul_one,
    CharTwo.add_cancel_left]

theorem H4_four (a : ℕ → R) : (H4 a).coeff 4 = 1 := monic_coeff (H4_monic a)
theorem H4_three (a : ℕ → R) : (H4 a).coeff 3 = 1 := by
  simp only [H4, coeff_add, y_other 3 (by omega), z_three, coeff_C_succ,
    zero_add, add_zero]

private theorem C3_row (a : ℕ → R) (d : R) (n : ℕ) (hn : 0 < n) :
    (C3 a d).coeff n = ((X : R[X]) + y).coeff n +
      B a * (Q a).coeff n + B a * (E a * L a).coeff n := by
  have hc : (C (a 18 + a 20 + a 9 + a 17 + B a * B a * d)).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [natDegree_C]; exact hn)
  rw [C3_shape, mul_assoc (C (B a)) (E a) (L a)]
  simp only [coeff_add, coeff_C_mul, hc, add_zero]

theorem C3_three (a : ℕ → R) (d : R) : (C3 a d).coeff 3 = B a := by
  have hx : ((X : R[X]) + y).coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt
    (x_add_y_monic.natDegree_eq.trans_lt (by omega))
  have he : (E a * L a).coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt
    ((EL_monic a).natDegree_eq.trans_lt (by omega))
  rw [C3_row a d 3 (by omega), hx, he, monic_coeff (Q_monic a),
    mul_one, mul_zero, zero_add, add_zero]

theorem C3_two (a : ℕ → R) (d : R) : (C3 a d).coeff 2 = 1 + B a * a 2 := by
  rw [C3_row a d 2 (by omega), monic_coeff x_add_y_monic,
    Q_eq_inner, Q_two, monic_coeff (EL_monic a), mul_one, mul_add, mul_one]
  simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem cross_degree_eight (a : ℕ → R) (d : R) : (cross a d).natDegree ≤ 8 :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (mul_degree (t_monic a).natDegree_eq.le (C3_degree a d))
      (mul_degree (H4_monic a).natDegree_eq.le (W4_degree a d)))
    ((mul_degree (J2_monic a).natDegree_eq.le (V4_degree a d)).trans (by omega))

private theorem last_cross_zero (a : ℕ → R) (d : R) (n : ℕ) (hn : 6 < n) :
    (J2 a * V4 a d).coeff n = 0 := coeff_eq_zero_of_natDegree_lt
      ((mul_degree (J2_monic a).natDegree_eq.le (V4_degree a d)).trans_lt hn)

theorem cross_eight (a : ℕ → R) (d : R) : (cross a d).coeff 8 = 0 := by
  have htc := coeff_mul_add_eq_of_natDegree_le (t_monic a).natDegree_eq.le (C3_degree a d)
  have hhw := coeff_mul_add_eq_of_natDegree_le (H4_monic a).natDegree_eq.le (W4_degree a d)
  rw [cross, coeff_add, coeff_add, htc, hhw, last_cross_zero a d 8 (by omega),
    t_five, C3_three, H4_four, W4_four, one_mul, add_zero,
    CharTwo.add_self_eq_zero]

theorem cross_seven (a : ℕ → R) (d : R) : (cross a d).coeff 7 = 0 := by
  have htc := two_top_product (dp := 4) (dq := 2)
    (t_monic a).natDegree_eq.le (C3_degree a d)
  have hhw := two_top_product (dp := 3) (dq := 3)
    (H4_monic a).natDegree_eq.le (W4_degree a d)
  rw [cross, coeff_add, coeff_add, htc, hhw, last_cross_zero a d 7 (by omega),
    t_five, t_four, C3_two, C3_three, H4_four, H4_three, W4_four, W4_three]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem cross_degree (a : ℕ → R) (d : R) : (cross a d).natDegree ≤ 6 := by
  have h7 : (cross a d).natDegree ≤ 7 := natDegree_le_pred (cross_degree_eight a d) (cross_eight a d)
  exact natDegree_le_pred h7 (cross_seven a d)

theorem V_degree (a : ℕ → R) (d : R) : (V a d).natDegree ≤ 5 := by
  have hv : V a d = t a + V4 a d := (restore (V a d) (t a)).symm
  rw [hv]
  exact natDegree_add_le_of_degree_le (t_monic a).natDegree_eq.le
    ((V4_degree a d).trans (by omega))

theorem leftSlope_degree (a : ℕ → R) (d : R) : (leftSlope a d).natDegree ≤ 6 := by
  have hs : (Sleft a).natDegree ≤ 4 :=
    natDegree_add_le_of_degree_le (z_monic a).natDegree_eq.le (c_degree _ _)
  have hlow : (C (B a) * Sleft a * L a + C (B a) * rLeft a + V a d).natDegree ≤ 6 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        ((mul_degree (scaled_degree _ hs) (Char2Degree25RowThirteen.L_monic a).natDegree_eq.le).trans (by omega))
        ((scaled_degree _ (rLeft_monic a).natDegree_eq.le).trans (by omega)))
      ((V_degree a d).trans (by omega))
  change ((C (B a) * Sleft a * L a + C (B a) * rLeft a + V a d +
    hLeft a * W a d) + jLeft a * V a d).natDegree ≤ 6
  rw [add_assoc, cross_eq]
  exact natDegree_add_le_of_degree_le hlow (cross_degree a d)

theorem outputSlope_degree (a : ℕ → R) (d : R) : (outputSlope a d).natDegree ≤ 11 :=
  natDegree_add_le_of_degree_le ((V_degree a d).trans (by omega))
    (mul_degree (nRight_monic a).natDegree_eq.le (leftSlope_degree a d))

theorem output_difference_degree (a : ℕ → R) (d : R) :
    (Char2Degree25Frame.output (shift a d) + Char2Degree25Frame.output a).natDegree ≤ 11 := by
  rw [output_change]
  have hc : (Char2Degree25Frame.output a + C d * outputSlope a d) +
      Char2Degree25Frame.output a = C d * outputSlope a d := by
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero, add_zero, zero_add]
  rw [hc]
  exact scaled_degree _ (outputSlope_degree a d)

end FastPoly.Char2Degree25TwentyOneBounds
