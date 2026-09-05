import FastPoly.Examples.Char2Degree13FastCore
import Mathlib.Tactic.NormNum

/-! Small signatures used by the supplied nonmonotone degree-thirteen decoder.
Only z (degree four), w (degree eight), and cFactor (degree five) are opened.
The large output branches rFactor*v and sFactor*w stay opaque. -/

namespace FastPoly.Char2Degree13Fast

set_option maxHeartbeats 20000

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

def z1 (q : Keys R) : R := q 1 + q 2
def z0 (q : Keys R) : R := q 2 * (q 1 + q 2)

noncomputable def zShape (a b c : R) : R[X] :=
  X ^ 4 + X ^ 3 + C a * X ^ 2 + C b * X + C c

private theorem square_head (x a b : R) :
    (x + x ^ 2 + b) * (x ^ 2 + (a + b)) =
      x ^ 4 + x ^ 3 + a * x ^ 2 + (a + b) * x + b * (a + b) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem z_form (q : Keys R) : z q = zShape (q 1) (z1 q) (z0 q) := by
  unfold z y zShape z1 z0
  simp only [map_add, map_mul]
  exact square_head X (C (q 1)) (C (q 2))

theorem aFactor_form (q : Keys R) :
    aFactor q = zShape (q 1 + 1) (z1 q) (z0 q) := by
  rw [aFactor, z_form]
  unfold y zShape
  simp only [map_add, map_one]
  ring

theorem bFactor_form (q : Keys R) :
    bFactor q = zShape (q 1) (z1 q) (z0 q + q 3) := by
  rw [bFactor, z_form]
  unfold zShape
  rw [map_add]
  ac_rfl

def w4 (q : Keys R) : R := q 1 ^ 2 + q 1 + (q 3 + q 5)
def w3 (q : Keys R) : R := z1 q + (q 3 + q 5)
def w2 (q : Keys R) : R := z1 q ^ 2 + z0 q + (q 3 + q 5) * q 1 + q 3
def w1 (q : Keys R) : R := (q 3 + q 5) * z1 q
def w0 (q : Keys R) : R := z0 q ^ 2 + (q 3 + q 5) * z0 q + q 3 * q 5

noncomputable def wShape (c4 c3 c2 c1 c0 : R) : R[X] :=
  X ^ 8 + X ^ 5 + C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0

private theorem quartic_pair (x a b c d e : R) :
    (x ^ 2 + (x ^ 4 + x ^ 3 + a * x ^ 2 + b * x + c) + e) *
      ((x ^ 4 + x ^ 3 + a * x ^ 2 + b * x + c) + d) =
    x ^ 8 + x ^ 5 + (a ^ 2 + a + (d + e)) * x ^ 4 +
      (b + (d + e)) * x ^ 3 + (b ^ 2 + c + (d + e) * a + d) * x ^ 2 +
      (d + e) * b * x + (c ^ 2 + (d + e) * c + d * e) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem w_form (q : Keys R) : w q = wShape (w4 q) (w3 q) (w2 q) (w1 q) (w0 q) := by
  rw [w, aFactor, bFactor, z_form]
  unfold y zShape wShape w4 w3 w2 w1 w0
  simp only [map_add, map_mul, map_pow]
  exact quartic_pair X (C (q 1)) (C (z1 q)) (C (z0 q)) (C (q 3)) (C (q 5))

def c2 (q : Keys R) : R := z1 q + (q 0 + 1) * (q 1 + 1) + 1
def c1 (q : Keys R) : R := z0 q + q 4 + (q 0 + 1) * z1 q
def c0 (q : Keys R) : R := (q 0 + 1) * (z0 q + q 4) + q 6

noncomputable def cShape (c4 c3 c2 c1 c0 : R) : R[X] :=
  X ^ 5 + C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0

private theorem linear_quartic (x p a b c d e : R) :
    (x + (p + 1)) * (x ^ 2 + (x ^ 4 + x ^ 3 + a * x ^ 2 + b * x + c) + d) +
      (x ^ 2 + e) =
    x ^ 5 + p * x ^ 4 + (a + p) * x ^ 3 +
      (b + (p + 1) * (a + 1) + 1) * x ^ 2 +
      (c + d + (p + 1) * b) * x + ((p + 1) * (c + d) + e) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem cFactor_form (q : Keys R) :
    cFactor q = cShape (q 0) (q 1 + q 0) (c2 q) (c1 q) (c0 q) := by
  rw [cFactor, rFactor, aFactor, sFactor, z_form]
  unfold y zShape cShape c2 c1 c0
  simp only [map_add, map_mul, map_one]
  exact linear_quartic X (C (q 0)) (C (q 1)) (C (z1 q)) (C (z0 q))
    (C (q 4)) (C (q 6))

/- The following closed coefficient reads touch only the small displayed
signatures; no product antidiagonal or baseline circuit is expanded. -/

theorem w_coeff8 (q : Keys R) : (w q).coeff 8 = 1 := by
  rw [w_form]
  norm_num only [wShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem w_coeff7 (q : Keys R) : (w q).coeff 7 = 0 := by
  rw [w_form]
  norm_num only [wShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem w_coeff6 (q : Keys R) : (w q).coeff 6 = 0 := by
  rw [w_form]
  norm_num only [wShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem w_coeff5 (q : Keys R) : (w q).coeff 5 = 1 := by
  rw [w_form]
  norm_num only [wShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem cFactor_coeff5 (q : Keys R) : (cFactor q).coeff 5 = 1 := by
  rw [cFactor_form]
  norm_num only [cShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem cFactor_coeff4 (q : Keys R) : (cFactor q).coeff 4 = q 0 := by
  rw [cFactor_form]
  norm_num only [cShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem cFactor_coeff3 (q : Keys R) : (cFactor q).coeff 3 = q 1 + q 0 := by
  rw [cFactor_form]
  norm_num only [cShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem cFactor_coeff2 (q : Keys R) : (cFactor q).coeff 2 = c2 q := by
  rw [cFactor_form]
  norm_num only [cShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem aFactor_coeff4 (q : Keys R) : (aFactor q).coeff 4 = 1 := by
  rw [aFactor_form]
  norm_num only [zShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem aFactor_coeff3 (q : Keys R) : (aFactor q).coeff 3 = 1 := by
  rw [aFactor_form]
  norm_num only [zShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem aFactor_coeff2 (q : Keys R) : (aFactor q).coeff 2 = q 1 + 1 := by
  rw [aFactor_form]
  norm_num only [zShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem aFactor_coeff1 (q : Keys R) : (aFactor q).coeff 1 = z1 q := by
  rw [aFactor_form]
  norm_num only [zShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem bFactor_coeff4 (q : Keys R) : (bFactor q).coeff 4 = 1 := by
  rw [bFactor_form]
  norm_num only [zShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem bFactor_coeff3 (q : Keys R) : (bFactor q).coeff 3 = 1 := by
  rw [bFactor_form]
  norm_num only [zShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem bFactor_coeff2 (q : Keys R) : (bFactor q).coeff 2 = q 1 := by
  rw [bFactor_form]
  norm_num only [zShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

theorem bFactor_coeff1 (q : Keys R) : (bFactor q).coeff 1 = z1 q := by
  rw [bFactor_form]
  norm_num only [zShape, coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul,
    coeff_X, coeff_C, ite_true, ite_false, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add]

end FastPoly.Char2Degree13Fast
