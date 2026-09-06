import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The retained paper's degree-eleven butterfly circuit, display (A.0).
This is not the square-first website circuit. All six products stay named. -/
namespace FastPoly.Char2PaperDegree11

open Polynomial
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def y (a : ℕ → R) : R[X] := X * (X + C (a 0))
noncomputable def z (a : ℕ → R) : R[X] :=
  (y a + C (a 1)) * (X + y a + C (a 2))
noncomputable def t (a : ℕ → R) : R[X] := X * (y a + C (a 3))
noncomputable def u (a : ℕ → R) : R[X] := (t a + C (a 4)) * (z a + C (a 5))
noncomputable def vLeft (a : ℕ → R) : R[X] := X + y a + t a + u a + C (a 6)
noncomputable def vRight (a : ℕ → R) : R[X] := z a + t a + C (a 7)
noncomputable def v (a : ℕ → R) : R[X] := vLeft a * vRight a
noncomputable def wLeft (a : ℕ → R) : R[X] := t a + C (a 8)
noncomputable def wRight (a : ℕ → R) : R[X] := y a + u a + C (a 9)
noncomputable def w (a : ℕ → R) : R[X] := wLeft a * wRight a
noncomputable def output (a : ℕ → R) : R[X] := v a + w a + C (a 10)

def sumKeys (a : ℕ → R) : R := a 1 + a 2
def h (a : ℕ → R) : R := a 5 + a 7 + a 8
def K7 (a : ℕ → R) : R := 1 + a 0 ^ 2 + a 0 ^ 4 + a 3
def K6 (a : ℕ → R) : R := 1 + a 0 + a 0 ^ 3 + a 0 ^ 5 + a 4
def K5 (a : ℕ → R) : R :=
  a 0 + a 0 ^ 2 + a 0 ^ 4 * a 3 + a 0 ^ 2 * a 3 + a 3

theorem const_lt (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

theorem y_monic (a : ℕ → R) : IsMonicOfDegree (y a) 2 :=
  (isMonicOfDegree_X R).mul (isMonicOfDegree_X_add_one (a 0))
theorem z_monic (a : ℕ → R) : IsMonicOfDegree (z a) 4 :=
  ((y_monic a).add_right (const_lt _ _ (by omega))).mul
    (((y_monic a).add_left (natDegree_X_le.trans_lt (by omega))).add_right
      (const_lt _ _ (by omega)))
theorem t_monic (a : ℕ → R) : IsMonicOfDegree (t a) 3 :=
  (isMonicOfDegree_X R).mul ((y_monic a).add_right (const_lt _ _ (by omega)))
theorem u_monic (a : ℕ → R) : IsMonicOfDegree (u a) 7 :=
  ((t_monic a).add_right (const_lt _ _ (by omega))).mul
    ((z_monic a).add_right (const_lt _ _ (by omega)))
theorem vLeft_monic (a : ℕ → R) : IsMonicOfDegree (vLeft a) 7 := by
  have hxy : ((X : R[X]) + y a).natDegree ≤ 2 :=
    natDegree_add_le_of_degree_le (natDegree_X_le.trans (by omega))
      (y_monic a).natDegree_eq.le
  have hlow : ((X : R[X]) + y a + t a).natDegree ≤ 3 :=
    natDegree_add_le_of_degree_le (hxy.trans (by omega)) (t_monic a).natDegree_eq.le
  exact ((u_monic a).add_left (hlow.trans_lt (by omega))).add_right
    (const_lt _ _ (by omega))
theorem vRight_monic (a : ℕ → R) : IsMonicOfDegree (vRight a) 4 :=
  ((z_monic a).add_right ((t_monic a).natDegree_eq.trans_lt (by omega))).add_right
    (const_lt _ _ (by omega))
theorem v_monic (a : ℕ → R) : IsMonicOfDegree (v a) 11 :=
  (vLeft_monic a).mul (vRight_monic a)
theorem wLeft_monic (a : ℕ → R) : IsMonicOfDegree (wLeft a) 3 :=
  (t_monic a).add_right (const_lt _ _ (by omega))
theorem wRight_monic (a : ℕ → R) : IsMonicOfDegree (wRight a) 7 :=
  ((u_monic a).add_left ((y_monic a).natDegree_eq.trans_lt (by omega))).add_right
    (const_lt _ _ (by omega))
theorem w_monic (a : ℕ → R) : IsMonicOfDegree (w a) 10 :=
  (wLeft_monic a).mul (wRight_monic a)
theorem output_monic (a : ℕ → R) : IsMonicOfDegree (output a) 11 :=
  ((v_monic a).add_right ((w_monic a).natDegree_eq.trans_lt (by omega))).add_right
    (const_lt _ _ (by omega))

theorem y_shape (a : ℕ → R) : y a = X ^ 2 + C (a 0) * X := by
  unfold y
  ring
theorem t_shape (a : ℕ → R) :
    t a = X ^ 3 + C (a 0) * X ^ 2 + C (a 3) * X := by
  rw [t, y_shape]
  ring

end FastPoly.Char2PaperDegree11
