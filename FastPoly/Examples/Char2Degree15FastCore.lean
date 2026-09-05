import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Named wires of the existing square-first degree-15 circuit

The eight gates and the linear key formulas are exactly those in
`char2/verify_n15_unitriangular_symbolic.py`, lines 105--154, and
`website/js/char2.js`'s degree-15 specification. This is not the older
`decode_n15_fastpoly.py` circuit.

The only polynomial identity here combines the two named output branches
`w + s`: their shared `z * v` cancels. No wire is expanded into coefficients
or a polynomial in the original keys.
-/

namespace FastPoly.Char2Degree15Fast

set_option maxHeartbeats 20000

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

abbrev Keys (R : Type*) := Fin 15 → R

/-- The supplied inverse linear coordinate change, in raw gate-offset order. -/
def keys (q : Keys R) : ℕ → R
  | 0 => q 2
  | 1 => q 1 + q 2
  | 2 => q 0
  | 3 => q 3
  | 4 => q 4 + q 5 + q 7
  | 5 => q 5
  | 6 => q 8 + q 11
  | 7 => q 11
  | 8 => q 6 + q 12 + q 13
  | 9 => q 13
  | 10 => q 12 + q 13
  | 11 => q 10 + q 13
  | 12 => q 7
  | 13 => q 9
  | 14 => q 14
  | _ => 0

noncomputable def y : R[X] := X ^ 2
noncomputable def z (q : Keys R) : R[X] :=
  (y + C (q 2)) * (X + y + C (q 1 + q 2))
noncomputable def t (q : Keys R) : R[X] :=
  (X + C (q 0)) * (z q + C (q 3))
noncomputable def u (q : Keys R) : R[X] :=
  (y + t q + C (q 4 + q 5 + q 7)) * (z q + t q + C (q 5))
noncomputable def v (q : Keys R) : R[X] :=
  (X + z q + C (q 8 + q 11)) * (z q + C (q 11))
noncomputable def w (q : Keys R) : R[X] :=
  (X + y + z q + C (q 6 + q 12 + q 13)) * (y + v q + C (q 13))
noncomputable def s (q : Keys R) : R[X] :=
  (z q + C (q 12 + q 13)) * (v q + C (q 10 + q 13))
noncomputable def r (q : Keys R) : R[X] :=
  (t q + C (q 7)) * (u q + C (q 9))
noncomputable def output (q : Keys R) : R[X] := w q + s q + r q + C (q 14)

/-- The degree-two coefficient of `v` after cancelling the shared `z * v`. -/
noncomputable def head (q : Keys R) : R[X] := X + y + C (q 6)

/-- The remaining low correction; all earlier wires remain named. -/
noncomputable def low (q : Keys R) : R[X] :=
  X * y + y ^ 2 + C (q 6 + q 12) * y + C (q 13) * X +
    C (q 6 * q 13 + q 10 * q 12 + q 10 * q 13)

/-- A local identity in independent ring elements, not in expanded wires. -/
private theorem branch_cancel (x y z v a b c d : R) :
    (x + y + z + (a + b + c)) * (y + v + c) +
      (z + (b + c)) * (v + (d + c)) =
    (x + y + a) * v + (y + d) * z +
      (x * y + y ^ 2 + (a + b) * y + c * x + (a * c + d * b + d * c)) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

/-- Cancel the large common branch once, before any coefficient is read. -/
theorem branches_split (q : Keys R) :
    w q + s q = head q * v q + (y + C (q 10)) * z q + low q := by
  unfold w s head low
  simp only [map_add, map_mul]
  exact branch_cancel X y (z q) (v q) (C (q 6)) (C (q 12)) (C (q 13)) (C (q 10))

theorem output_split (q : Keys R) :
    output q = head q * v q + (y + C (q 10)) * z q + low q + r q + C (q 14) := by
  rw [output, branches_split]

omit [CharP R 2] in
theorem const_lt (a : R) (n : ℕ) (hn : 0 < n) : (C a).natDegree < n := by
  rw [natDegree_C]
  exact hn

omit [CharP R 2] in
theorem mul_bound {p q : R[X]} {m n : ℕ} (hp : p.natDegree ≤ m)
    (hq : q.natDegree ≤ n) : (p * q).natDegree ≤ m + n :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

variable [Nontrivial R]

omit [CharP R 2] in
theorem y_monic : IsMonicOfDegree (y : R[X]) 2 := isMonicOfDegree_X_pow R 2

omit [CharP R 2] in
theorem z_monic (q : Keys R) : IsMonicOfDegree (z q) 4 := by
  have hxy : IsMonicOfDegree ((X : R[X]) + y) 2 :=
    y_monic.add_left (natDegree_X_le.trans_lt (by omega))
  exact (y_monic.add_right (const_lt _ 2 (by omega))).mul
    (hxy.add_right (const_lt _ 2 (by omega)))

omit [CharP R 2] in
theorem t_monic (q : Keys R) : IsMonicOfDegree (t q) 5 :=
  (isMonicOfDegree_X_add_one (q 0)).mul
    ((z_monic q).add_right (const_lt _ 4 (by omega)))

omit [CharP R 2] in
theorem u_monic (q : Keys R) : IsMonicOfDegree (u q) 10 := by
  have hyt : IsMonicOfDegree (y + t q) 5 :=
    (t_monic q).add_left ((y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 5))
  have hzt : IsMonicOfDegree (z q + t q) 5 :=
    (t_monic q).add_left ((z_monic q).natDegree_eq ▸ (by omega : 4 < 5))
  exact (hyt.add_right (const_lt _ 5 (by omega))).mul
    (hzt.add_right (const_lt _ 5 (by omega)))

omit [CharP R 2] in
theorem v_monic (q : Keys R) : IsMonicOfDegree (v q) 8 := by
  have hxz : IsMonicOfDegree (X + z q) 4 :=
    (z_monic q).add_left (natDegree_X_le.trans_lt (by omega))
  exact (hxz.add_right (const_lt _ 4 (by omega))).mul
    ((z_monic q).add_right (const_lt _ 4 (by omega)))

omit [CharP R 2] in
theorem r_monic (q : Keys R) : IsMonicOfDegree (r q) 15 :=
  ((t_monic q).add_right (const_lt _ 5 (by omega))).mul
    ((u_monic q).add_right (const_lt _ 10 (by omega)))

omit [CharP R 2] in
theorem head_monic (q : Keys R) : IsMonicOfDegree (head q) 2 :=
  (y_monic.add_left (natDegree_X_le.trans_lt (by omega))).add_right
    (const_lt _ 2 (by omega))

omit [CharP R 2] in
theorem low_degree (q : Keys R) : (low q).natDegree ≤ 4 := by
  have hy : (y : R[X]).natDegree ≤ 2 := y_monic.natDegree_eq.le
  have hxy : ((X : R[X]) * y).natDegree ≤ 4 :=
    (mul_bound natDegree_X_le hy).trans (by omega)
  have hyy : ((y : R[X]) ^ 2).natDegree ≤ 4 := (y_monic.pow 2).natDegree_eq.le
  have hcy : (C (q 6 + q 12) * y).natDegree ≤ 4 :=
    (mul_bound (natDegree_C _).le hy).trans (by omega)
  have hcx : (C (q 13) * X).natDegree ≤ 4 :=
    (mul_bound (natDegree_C _).le natDegree_X_le).trans (by omega)
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hxy hyy) hcy) hcx)
    ((natDegree_C _).le.trans (by omega))

theorem branches_monic (q : Keys R) : IsMonicOfDegree (w q + s q) 10 := by
  rw [branches_split]
  have hmain : IsMonicOfDegree (head q * v q) 10 := (head_monic q).mul (v_monic q)
  have hnext : IsMonicOfDegree ((y + C (q 10)) * z q) 6 :=
    (y_monic.add_right (const_lt _ 2 (by omega))).mul (z_monic q)
  exact (hmain.add_right (hnext.natDegree_eq ▸ (by omega : 6 < 10))).add_right
    ((low_degree q).trans_lt (by omega))

theorem output_monic (q : Keys R) : IsMonicOfDegree (output q) 15 :=
  ((r_monic q).add_left ((branches_monic q).natDegree_eq ▸ (by omega : 10 < 15))).add_right
    (const_lt _ 15 (by omega))

end FastPoly.Char2Degree15Fast
