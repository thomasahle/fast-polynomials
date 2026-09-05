import FastPoly.Examples.Char2Degree17QuadraticOffsets

/-!
# Named wires of the supplied degree-17, nine-product circuit

All degree arguments follow the gate DAG. In `j` and `ell` the factors are
commuted to place the lower-degree factor first, as in the supplied inverse.
No coefficient polynomial is expanded through earlier gates.
-/

namespace FastPoly.Char2Degree17Wires

set_option maxHeartbeats 20000

open Polynomial

variable {R : Type*} [CommRing R]

abbrev Vector (R : Type*) := Fin 17 → R

noncomputable def y (a : Vector R) : R[X] := Char2Degree17QuadraticOffsets.y (a 0)
noncomputable def z (a : Vector R) : R[X] :=
  Char2UnequalOffsets.gate X (X + y a) (a 1, a 2)
noncomputable def t (a : Vector R) : R[X] :=
  Char2Degree17QuadraticOffsets.gate (a 0) (a 3, a 4)
noncomputable def u (a : Vector R) : R[X] :=
  Char2UnequalOffsets.gate (y a + z a) (z a + t a) (a 5, a 6)
noncomputable def v (a : Vector R) : R[X] :=
  Char2UnequalOffsets.gate (X + z a) (X + z a + t a + u a) (a 7, a 8)
noncomputable def h (a : Vector R) : R[X] := (y a + C (a 9)) * X
noncomputable def j (a : Vector R) : R[X] :=
  Char2UnequalOffsets.gate X (y a) (a 11, a 10)
noncomputable def ell (a : Vector R) : R[X] :=
  Char2UnequalOffsets.gate (h a) (t a) (a 13, a 12)
noncomputable def w (a : Vector R) : R[X] :=
  Char2UnequalOffsets.gate (X + u a) (u a + v a) (a 14, a 15)
noncomputable def output (a : Vector R) : R[X] := j a + ell a + w a + C (a 16)

section Degrees

variable [Nontrivial R]

theorem shifted_monic {p : R[X]} {d : ℕ} (hp : IsMonicOfDegree p d)
    (hd : 0 < d) (a : R) : IsMonicOfDegree (p + C a) d :=
  hp.add_right (by rw [natDegree_C]; exact hd)

theorem add_monic {p q : R[X]} {d e : ℕ}
    (hp : IsMonicOfDegree p d) (hq : IsMonicOfDegree q e) (hde : d < e) :
    IsMonicOfDegree (p + q) e :=
  IsMonicOfDegree.add_left (hp.natDegree_eq ▸ hde) hq

theorem gate_monic {p q : R[X]} {d e : ℕ}
    (hp : IsMonicOfDegree p d) (hq : IsMonicOfDegree q e)
    (hd : 0 < d) (he : 0 < e) (a : R × R) :
    IsMonicOfDegree (Char2UnequalOffsets.gate p q a) (d + e) :=
  (shifted_monic hp hd a.1).mul (shifted_monic hq he a.2)

theorem y_monic (a : Vector R) : IsMonicOfDegree (y a) 2 :=
  (isMonicOfDegree_X R).mul (isMonicOfDegree_X_add_one (a 0))

theorem higherZ_monic (a : Vector R) : IsMonicOfDegree (X + y a) 2 :=
  add_monic (isMonicOfDegree_X R) (y_monic a) (by omega)

theorem z_monic (a : Vector R) : IsMonicOfDegree (z a) 3 :=
  gate_monic (isMonicOfDegree_X R) (higherZ_monic a) (by omega) (by omega) _

theorem t_monic (a : Vector R) : IsMonicOfDegree (t a) 4 :=
  (shifted_monic (y_monic a) (by omega) (a 3)).mul
    (shifted_monic (higherZ_monic a) (by omega) (a 4))

theorem lowerU_monic (a : Vector R) : IsMonicOfDegree (y a + z a) 3 :=
  add_monic (y_monic a) (z_monic a) (by omega)

theorem higherU_monic (a : Vector R) : IsMonicOfDegree (z a + t a) 4 :=
  add_monic (z_monic a) (t_monic a) (by omega)

theorem u_monic (a : Vector R) : IsMonicOfDegree (u a) 7 :=
  gate_monic (lowerU_monic a) (higherU_monic a) (by omega) (by omega) _

theorem lowerV_monic (a : Vector R) : IsMonicOfDegree (X + z a) 3 :=
  add_monic (isMonicOfDegree_X R) (z_monic a) (by omega)

theorem higherV_monic (a : Vector R) : IsMonicOfDegree (X + z a + t a + u a) 7 :=
  add_monic (add_monic (lowerV_monic a) (t_monic a) (by omega))
    (u_monic a) (by omega)

theorem v_monic (a : Vector R) : IsMonicOfDegree (v a) 10 :=
  gate_monic (lowerV_monic a) (higherV_monic a) (by omega) (by omega) _

theorem h_monic (a : Vector R) : IsMonicOfDegree (h a) 3 :=
  (shifted_monic (y_monic a) (by omega) (a 9)).mul (isMonicOfDegree_X R)

theorem j_monic (a : Vector R) : IsMonicOfDegree (j a) 3 :=
  gate_monic (isMonicOfDegree_X R) (y_monic a) (by omega) (by omega) _

theorem ell_monic (a : Vector R) : IsMonicOfDegree (ell a) 7 :=
  gate_monic (h_monic a) (t_monic a) (by omega) (by omega) _

theorem lowerW_monic (a : Vector R) : IsMonicOfDegree (X + u a) 7 :=
  add_monic (isMonicOfDegree_X R) (u_monic a) (by omega)

theorem higherW_monic (a : Vector R) : IsMonicOfDegree (u a + v a) 10 :=
  add_monic (u_monic a) (v_monic a) (by omega)

theorem w_monic (a : Vector R) : IsMonicOfDegree (w a) 17 :=
  gate_monic (lowerW_monic a) (higherW_monic a) (by omega) (by omega) _

theorem output_monic (a : Vector R) : IsMonicOfDegree (output a) 17 :=
  shifted_monic (add_monic (add_monic (j_monic a) (ell_monic a) (by omega))
    (w_monic a) (by omega)) (by omega) (a 16)

end Degrees

theorem y_coeff_one (a : Vector R) : (y a).coeff 1 = a 0 := by
  simp only [y, Char2Degree17QuadraticOffsets.y, coeff_X_mul, coeff_add,
    coeff_X_zero, coeff_C_zero, zero_add]

theorem y_coeff_zero (a : Vector R) : (y a).coeff 0 = 0 :=
  coeff_X_mul_zero _

theorem h_coeff_one (a : Vector R) : (h a).coeff 1 = a 9 := by
  simp only [h, coeff_mul_X, coeff_add, y_coeff_zero, coeff_C_zero, zero_add]

end FastPoly.Char2Degree17Wires
