import FastPoly.Examples.Char2Degree23RowEight

/-!
# Named degree bounds for the supplied degree-23 circuit

No gate is expanded into coefficients. The output's unique degree-23 term
is the product of its two quartic frame factors and its degree-15 `g` wire.
This supplies the frame for the verifier's remaining local pivot identities;
it is not, by itself, a coefficient inverse.
-/

namespace FastPoly.Char2Degree23Frame

open Polynomial Char2Degree23RowEight
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [Nontrivial R]

omit [Nontrivial R] in
private theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) :
    (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

theorem t_monic (a : ℕ → R) : IsMonicOfDegree (t a) 5 :=
  (isMonicOfDegree_X_add_one (a 2)).mul
    ((z_monic a).add_right (C_lt _ 4 (by omega)))

theorem z_add_t_monic (a : ℕ → R) : IsMonicOfDegree (z a + t a) 5 :=
  (t_monic a).add_left ((z_monic a).natDegree_eq.trans_lt (by omega))

theorem y_add_z_monic (a : ℕ → R) : IsMonicOfDegree (y + z a) 4 :=
  (z_monic a).add_left (y_monic.natDegree_eq.trans_lt (by omega))

theorem u_monic (a : ℕ → R) : IsMonicOfDegree (u a) 10 :=
  (((t_monic a).add_left ((y_add_z_monic a).natDegree_eq.trans_lt (by omega))).add_right
    (C_lt _ 5 (by omega))).mul
      ((z_add_t_monic a).add_right (C_lt _ 5 (by omega)))

theorem v_monic (a : ℕ → R) : IsMonicOfDegree (v a) 5 :=
  (isMonicOfDegree_X_add_one (a 6)).mul
    ((y_add_z_monic a).add_right (C_lt _ 4 (by omega)))

theorem w_monic (a : ℕ → R) : IsMonicOfDegree (w a) 9 :=
  (((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt (by omega))).add_right
    (C_lt _ 4 (by omega))).mul
    (((v_monic a).add_left (y_monic.natDegree_eq.trans_lt (by omega))).add_right
      (C_lt _ 5 (by omega)))

theorem s_monic (a : ℕ → R) : IsMonicOfDegree (s a) 9 :=
  ((z_monic a).add_right (C_lt _ 4 (by omega))).mul
    ((v_monic a).add_right (C_lt _ 5 (by omega)))

theorem r_monic (a : ℕ → R) : IsMonicOfDegree (r a) 15 :=
  (((t_monic a).add_left (natDegree_X_le.trans_lt (by omega))).add_right
    (C_lt _ 5 (by omega))).mul
      ((u_monic a).add_right (C_lt _ 10 (by omega)))

theorem g_monic (a : ℕ → R) : IsMonicOfDegree (g a) 15 :=
  ((z_add_t_monic a).add_right (C_lt _ 5 (by omega))).mul
    (((u_monic a).add_left (natDegree_X_le.trans_lt (by omega))).add_right
      (C_lt _ 10 (by omega)))

theorem ell_monic (a : ℕ → R) : IsMonicOfDegree (ell a) 6 :=
  (isMonicOfDegree_X_add_one (a 16)).mul
    (((v_monic a).add_left ((z_monic a).natDegree_eq.trans_lt (by omega))).add_right
      (C_lt _ 5 (by omega)))

/-- Keep the small terms as named wires while isolating the cubic branch. -/
noncomputable def crownTail (a : ℕ → R) : R[X] :=
  X + y + z a + w a + s a + ell a

omit [Nontrivial R] in
theorem crownRight_eq (a : ℕ → R) : crownRight a = g a + crownTail a := by
  change X + y + z a + w a + s a + g a + ell a = _
  unfold crownTail
  ac_rfl

theorem crownTail_degree (a : ℕ → R) : (crownTail a).natDegree ≤ 9 := by
  have hx : ((X : R[X]) + y + z a).natDegree ≤ 9 :=
    ((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt
      (by omega))).natDegree_eq.le.trans (by omega)
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le hx (w_monic a).natDegree_eq.le)
      (s_monic a).natDegree_eq.le)
    ((ell_monic a).natDegree_eq.le.trans (by omega))

theorem crownRight_monic (a : ℕ → R) : IsMonicOfDegree (crownRight a) 15 := by
  rw [crownRight_eq]
  exact (g_monic a).add_right ((crownTail_degree a).trans_lt (by omega))

theorem head_degree (a : ℕ → R) : (head a).natDegree ≤ 15 :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          (natDegree_add_le_of_degree_le
            (y_monic.natDegree_eq.le.trans (by omega))
            ((v_monic a).natDegree_eq.le.trans (by omega)))
          ((w_monic a).natDegree_eq.le.trans (by omega)))
        ((s_monic a).natDegree_eq.le.trans (by omega)))
      (r_monic a).natDegree_eq.le)
    (g_monic a).natDegree_eq.le

/-- The output is monic for every raw key vector, before any decoding. -/
theorem output_monic (a : ℕ → R) : IsMonicOfDegree (output a) 23 := by
  have hm : IsMonicOfDegree
      (crownLeft a * (crownRight a + C (a 19))) 19 :=
    (crownLeft_monic a).mul
      ((crownRight_monic a).add_right (C_lt _ 15 (by omega)))
  have hn : IsMonicOfDegree
      (lastFactor a * (u a + crownLeft a * (crownRight a + C (a 19)) + C (a 21))) 23 :=
    (lastFactor_monic a).mul
      ((hm.add_left ((u_monic a).natDegree_eq.trans_lt (by omega))).add_right
        (C_lt _ 19 (by omega)))
  exact (hn.add_left ((head_degree a).trans_lt (by omega))).add_right
    (C_lt _ 23 (by omega))

end FastPoly.Char2Degree23Frame
