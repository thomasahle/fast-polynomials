import FastPoly.Examples.Char2Degree25Frame

/-!
# The five-quintic high frame of the supplied degree-25 circuit

The final output's high part is the literal product
(t+a23)(y+z+t+a18)(X+t+a12)u, with u the two-quintic
product already present in the circuit. Its remaining part is monic of
degree twenty. No inverse claim is made by this structural lemma alone.
-/

namespace FastPoly.Char2Degree25HighFrame

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree23Cancellations
  Char2Degree25Frame

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def rLeft (a : ℕ → R) : R[X] := X + t a + C (a 12)
noncomputable def hTail (a : ℕ → R) : R[X] :=
  X + y + z a + u a + v a + w a + rLeft a * C (a 13) + C (a 19)
noncomputable def small (a : ℕ → R) : R[X] :=
  X + t a + u a + s a + RG a + ell a + j a + C (a 22)
noncomputable def high (a : ℕ → R) : R[X] :=
  nRight a * (hLeft a * (rLeft a * u a))
noncomputable def remainder (a : ℕ → R) : R[X] :=
  Char2Degree25Frame.head a + nRight a * (hLeft a * hTail a + small a) + C (a 24)

theorem hRight_split (a : ℕ → R) :
    hRight a = rLeft a * u a + hTail a := by
  change X + y + z a + u a + v a + w a + rLeft a * (u a + C (a 13)) + C (a 19) = _
  rw [mul_add]
  unfold hTail
  ac_rfl

theorem h_split (a : ℕ → R) :
    h a = hLeft a * (rLeft a * u a) + hLeft a * hTail a := by
  rw [h, hRight_split, mul_add]

theorem nLeft_split (a : ℕ → R) : nLeft a = h a + small a := by
  unfold nLeft small RG
  ac_rfl

private theorem collect (p f a b c o : R[X]) :
    p + (a + b + c) * f + o = f * a + (p + f * (b + c) + o) := by ring

theorem output_eq (a : ℕ → R) : Char2Degree25Frame.output a = high a + remainder a := by
  unfold Char2Degree25Frame.output n
  rw [nLeft_split, h_split]
  exact collect _ _ _ _ _ _

private theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

theorem rLeft_monic (a : ℕ → R) : IsMonicOfDegree (rLeft a) 5 :=
  ((t_monic a).add_left (natDegree_X_le.trans_lt (by omega))).add_right
    (C_lt _ _ (by omega))

theorem high_monic (a : ℕ → R) : IsMonicOfDegree (high a) 25 :=
  (nRight_monic a).mul ((hLeft_monic a).mul ((rLeft_monic a).mul (u_monic a)))

theorem hTail_monic (a : ℕ → R) : IsMonicOfDegree (hTail a) 10 := by
  have hx : ((X : R[X]) + y + z a).natDegree < 10 :=
    ((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt (by omega))).natDegree_eq.trans_lt (by omega)
  have hr : (rLeft a * C (a 13)).natDegree < 10 := by
    apply natDegree_mul_le.trans_lt
    rw [(rLeft_monic a).natDegree_eq, natDegree_C]
    omega
  exact (((((u_monic a).add_left hx).add_right
    ((v_monic a).natDegree_eq.trans_lt (by omega))).add_right
    ((w_monic a).natDegree_eq.trans_lt (by omega))).add_right hr).add_right
    (C_lt _ _ (by omega))

theorem small_degree (a : ℕ → R) : (small a).natDegree ≤ 14 :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          (natDegree_add_le_of_degree_le
            (natDegree_add_le_of_degree_le
              (natDegree_add_le_of_degree_le (natDegree_X_le.trans (by omega))
                ((t_monic a).natDegree_eq.le.trans (by omega)))
              ((u_monic a).natDegree_eq.le.trans (by omega)))
            ((s_monic a).natDegree_eq.le.trans (by omega)))
          (RG_monic a).natDegree_eq.le)
        ((ell_monic a).natDegree_eq.le.trans (by omega)))
      ((j_monic a).natDegree_eq.le.trans (by omega)))
    (by rw [natDegree_C]; omega)

theorem remainder_monic (a : ℕ → R) : IsMonicOfDegree (remainder a) 20 :=
  (((nRight_monic a).mul
    (((hLeft_monic a).mul (hTail_monic a)).add_right ((small_degree a).trans_lt (by omega)))).add_left
      ((Char2Degree25Frame.head_monic a).natDegree_eq.trans_lt (by omega))).add_right
    (C_lt _ _ (by omega))

/-- The fixed leading coefficient of the remainder cancels under any key update. -/
theorem remainder_difference_degree (a b : ℕ → R) :
    (remainder b + remainder a).natDegree ≤ 19 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_add]
  by_cases he : j = 20
  · subst j
    have hc (a : ℕ → R) : (remainder a).coeff 20 = 1 := by
      rw [← (remainder_monic a).natDegree_eq]
      exact (remainder_monic a).monic.coeff_natDegree
    rw [hc, hc, CharTwo.add_self_eq_zero]
  · have hz (a : ℕ → R) : (remainder a).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt ((remainder_monic a).natDegree_eq.trans_lt (by omega))
    rw [hz, hz, zero_add]

end FastPoly.Char2Degree25HighFrame

