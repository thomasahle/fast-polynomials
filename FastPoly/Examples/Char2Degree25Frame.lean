import FastPoly.Examples.Char2Degree23Cancellations

/-!
# The existing degree-25 circuit, with its shared first ten gates

These are the thirteen products in verify_n25_unitriangular_symbolic.py.
The first ten gates are literally the degree-23 wires already defined;
only the final three and their output differ. This file proves the
fixed gate degrees, not the still-pending 24-step coefficient inverse.
-/

namespace FastPoly.Char2Degree25Frame

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree23Cancellations
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [Nontrivial R]

noncomputable def hLeft (a : ℕ → R) : R[X] := y + z a + t a + C (a 18)
noncomputable def hRight (a : ℕ → R) : R[X] :=
  X + y + z a + u a + v a + w a + r a + C (a 19)
noncomputable def h (a : ℕ → R) : R[X] := hLeft a * hRight a
noncomputable def jLeft (a : ℕ → R) : R[X] := X + y + t a + C (a 20)
noncomputable def j (a : ℕ → R) : R[X] := jLeft a * (ell a + C (a 21))
noncomputable def nLeft (a : ℕ → R) : R[X] :=
  X + t a + u a + s a + r a + g a + ell a + h a + j a + C (a 22)
noncomputable def nRight (a : ℕ → R) : R[X] := t a + C (a 23)
noncomputable def n (a : ℕ → R) : R[X] := nLeft a * nRight a
noncomputable def head (a : ℕ → R) : R[X] := y + z a + u a + ell a
noncomputable def output (a : ℕ → R) : R[X] := head a + n a + C (a 24)

private theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

theorem hLeft_monic (a : ℕ → R) : IsMonicOfDegree (hLeft a) 5 :=
  ((t_monic a).add_left ((y_add_z_monic a).natDegree_eq.trans_lt (by omega))).add_right
    (C_lt _ _ (by omega))

theorem hRight_monic (a : ℕ → R) : IsMonicOfDegree (hRight a) 15 := by
  have hxy : ((X : R[X]) + y + z a).natDegree ≤ 10 :=
    ((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt (by omega))).natDegree_eq.le.trans (by omega)
  have hlow : ((X : R[X]) + y + z a + u a + v a + w a).natDegree ≤ 10 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le hxy (u_monic a).natDegree_eq.le)
        ((v_monic a).natDegree_eq.le.trans (by omega)))
      ((w_monic a).natDegree_eq.le.trans (by omega))
  exact ((r_monic a).add_left (hlow.trans_lt (by omega))).add_right (C_lt _ _ (by omega))

theorem h_monic (a : ℕ → R) : IsMonicOfDegree (h a) 20 :=
  (hLeft_monic a).mul (hRight_monic a)

theorem jLeft_monic (a : ℕ → R) : IsMonicOfDegree (jLeft a) 5 :=
  ((t_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt (by omega))).add_right
    (C_lt _ _ (by omega))

theorem j_monic (a : ℕ → R) : IsMonicOfDegree (j a) 11 :=
  (jLeft_monic a).mul ((ell_monic a).add_right (C_lt _ _ (by omega)))

theorem nLeft_monic (a : ℕ → R) : IsMonicOfDegree (nLeft a) 20 := by
  have hl : ((X : R[X]) + t a + u a + s a + r a + g a + ell a).natDegree ≤ 15 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          (natDegree_add_le_of_degree_le
            (natDegree_add_le_of_degree_le
              (natDegree_add_le_of_degree_le (natDegree_X_le.trans (by omega))
                ((t_monic a).natDegree_eq.le.trans (by omega)))
              ((u_monic a).natDegree_eq.le.trans (by omega)))
            ((s_monic a).natDegree_eq.le.trans (by omega)))
          (r_monic a).natDegree_eq.le)
        (g_monic a).natDegree_eq.le)
      ((ell_monic a).natDegree_eq.le.trans (by omega))
  exact (((h_monic a).add_left (hl.trans_lt (by omega))).add_right
    ((j_monic a).natDegree_eq.trans_lt (by omega))).add_right (C_lt _ _ (by omega))

theorem nRight_monic (a : ℕ → R) : IsMonicOfDegree (nRight a) 5 :=
  (t_monic a).add_right (C_lt _ _ (by omega))

theorem n_monic (a : ℕ → R) : IsMonicOfDegree (n a) 25 :=
  (nLeft_monic a).mul (nRight_monic a)

theorem head_monic (a : ℕ → R) : IsMonicOfDegree (head a) 10 :=
  ((u_monic a).add_left ((y_add_z_monic a).natDegree_eq.trans_lt (by omega))).add_right
    ((ell_monic a).natDegree_eq.trans_lt (by omega))

theorem output_monic (a : ℕ → R) : IsMonicOfDegree (output a) 25 :=
  ((n_monic a).add_left ((head_monic a).natDegree_eq.trans_lt (by omega))).add_right
    (C_lt _ _ (by omega))

end FastPoly.Char2Degree25Frame

