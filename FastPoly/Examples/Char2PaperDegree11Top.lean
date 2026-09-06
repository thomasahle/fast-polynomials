import FastPoly.Examples.Char2PaperDegree11Core
import Mathlib.Tactic.NormNum

/-! The six high rows of the paper butterfly. Cancel its shared final
branches before inspecting the quartic z and its Frobenius square.
No coefficient list for the degree-eleven output is expanded. -/
namespace FastPoly.Char2PaperDegree11

open Polynomial
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def z2 (a : ℕ → R) : R := a 0 ^ 2 + a 0 + sumKeys a
def z1 (a : ℕ → R) : R := a 0 * sumKeys a + a 1
def z0 (a : ℕ → R) : R := a 1 * a 2

private theorem quartic_identity (x A b c : R[X]) :
    (x ^ 2 + A * x + b) * (x + (x ^ 2 + A * x) + c) =
      x ^ 4 + x ^ 3 + (A ^ 2 + A + (b + c)) * x ^ 2 +
        (A * (b + c) + b) * x + b * c := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add]

theorem z_shape (a : ℕ → R) : z a =
    X ^ 4 + X ^ 3 + C (z2 a) * X ^ 2 + C (z1 a) * X + C (z0 a) := by
  rw [z]
  simp only [y_shape, z2, z1, z0, sumKeys, map_add, map_pow, map_mul]
  exact quartic_identity X (C (a 0)) (C (a 1)) (C (a 2))

theorem z_square_shape (a : ℕ → R) : (z a) ^ 2 =
    X ^ 8 + X ^ 6 + C (z2 a ^ 2) * X ^ 4 +
      C (z1 a ^ 2) * X ^ 2 + C (z0 a ^ 2) := by
  rw [z_shape]
  simp only [CharTwo.add_sq, mul_pow, ← map_pow, ← pow_mul, Nat.reduceMul]

theorem t_square_shape (a : ℕ → R) : (t a) ^ 2 =
    X ^ 6 + C (a 0 ^ 2) * X ^ 4 + C (a 3 ^ 2) * X ^ 2 := by
  rw [t_shape]
  simp only [CharTwo.add_sq, mul_pow, ← map_pow, ← pow_mul, Nat.reduceMul]

/-- Coefficient reads keep z opaque inside its separately named square. -/
theorem z_coeff (a : ℕ → R) (j : ℕ) : (z a).coeff j =
    (if j = 4 then 1 else 0) + (if j = 3 then 1 else 0) +
      (if j = 2 then z2 a else 0) + (if j = 1 then z1 a else 0) +
      (if j = 0 then z0 a else 0) := by
  simp only [z_shape, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]

theorem z_square_coeff (a : ℕ → R) (j : ℕ) : (z a ^ 2).coeff j =
    (if j = 8 then 1 else 0) + (if j = 6 then 1 else 0) +
      (if j = 4 then z2 a ^ 2 else 0) + (if j = 2 then z1 a ^ 2 else 0) +
      (if j = 0 then z0 a ^ 2 else 0) := by
  simp only [z_square_shape, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C]

theorem t_square_coeff (a : ℕ → R) (j : ℕ) : (t a ^ 2).coeff j =
    (if j = 6 then 1 else 0) + (if j = 4 then a 0 ^ 2 else 0) +
      (if j = 2 then a 3 ^ 2 else 0) := by
  simp only [t_square_shape, coeff_add, coeff_X_pow, coeff_C_mul_X_pow]

/-- The cubic multiplier left after cancelling the two t*u columns. -/
noncomputable def highFactor (a : ℕ → R) : R[X] :=
  C (h a) * (t a + C (a 4)) + X + y a + t a
noncomputable def highLeft (a : ℕ → R) : R[X] := (t a + C (a 4)) * (z a) ^ 2
noncomputable def highRight (a : ℕ → R) : R[X] := highFactor a * z a
noncomputable def highPart (a : ℕ → R) : R[X] := highLeft a + highRight a + (t a) ^ 2

/-- All discarded summands have degree at most four, with each wire named. -/
noncomputable def lowPart (a : ℕ → R) : R[X] :=
  C (a 5 * (a 7 + a 8)) * (t a + C (a 4)) +
    C (a 6) * z a + X * t a + C (a 6 + a 9) * t a +
    C (a 7) * (X + y a + t a + C (a 6)) +
    C (a 8) * y a + C (a 8 * a 9) + C (a 10)

private theorem branch_collect (b U rr l c : R[X]) :
    (b + U) * rr + l * (c + U) = U * (rr + l) + b * rr + l * c := by ring

private theorem branch_right (zz tt c7 c8 : R[X]) :
    (zz + tt + c7) + (tt + c8) = zz + (c7 + c8) := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

private theorem equal_quartics (tt zz c4 c5 c7 c8 : R[X]) :
    ((tt + c4) * (zz + c5)) * (zz + (c7 + c8)) =
      (tt + c4) * zz ^ 2 + (c5 + c7 + c8) * (tt + c4) * zz +
        (c5 * (c7 + c8)) * (tt + c4) := by ring

private theorem small_branch (x yy zz tt c6 c7 c8 c9 : R[X]) :
    (x + yy + tt + c6) * (zz + tt + c7) + (tt + c8) * (yy + c9) =
      (x + yy + tt) * zz + tt ^ 2 +
        (c6 * zz + x * tt + (c6 + c9) * tt +
          c7 * (x + yy + tt + c6) + c8 * yy + c8 * c9) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add]

theorem output_high_split (a : ℕ → R) : output a = highPart a + lowPart a := by
  have hv : vLeft a = (X + y a + t a + C (a 6)) + u a := by
    simp only [vLeft, add_assoc, add_comm, add_left_comm]
  have hw : wRight a = (y a + C (a 9)) + u a := by
    simp only [wRight, add_assoc, add_comm, add_left_comm]
  have hr : vRight a + wLeft a = z a + C (a 7 + a 8) := by
    rw [vRight, wLeft, map_add]
    exact branch_right _ _ _ _
  have hu : u a * (z a + C (a 7 + a 8)) =
      highLeft a + C (h a) * (t a + C (a 4)) * z a +
        C (a 5 * (a 7 + a 8)) * (t a + C (a 4)) := by
    simp only [u, highLeft, h, map_add, map_mul]
    exact equal_quartics _ _ _ _ _ _
  have hs := small_branch X (y a) (z a) (t a)
    (C (a 6)) (C (a 7)) (C (a 8)) (C (a 9))
  rw [output, v, w, hv, hw, branch_collect, hr, hu]
  rw [vRight, wLeft, add_assoc
    (highLeft a + C (h a) * (t a + C (a 4)) * z a +
      C (a 5 * (a 7 + a 8)) * (t a + C (a 4))), hs]
  simp only [highPart, highRight, highFactor, lowPart, map_add, map_mul,
    add_mul]
  ring

private theorem scaled_degree (c : R) {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    (C c * p).natDegree ≤ n := by
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add]
  exact hp

theorem lowPart_degree (a : ℕ → R) : (lowPart a).natDegree ≤ 4 := by
  have ht4 : (t a + C (a 4)).natDegree ≤ 3 :=
    ((t_monic a).add_right (const_lt _ _ (by omega))).natDegree_eq.le
  have hxyt : ((X : R[X]) + y a + t a + C (a 6)).natDegree ≤ 3 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (natDegree_X_le.trans (by omega))
          ((y_monic a).natDegree_eq.le.trans (by omega))) (t_monic a).natDegree_eq.le)
      (by rw [natDegree_C]; omega)
  have hxt : ((X : R[X]) * t a).natDegree ≤ 4 :=
    natDegree_mul_le.trans (Nat.add_le_add natDegree_X_le (t_monic a).natDegree_eq.le)
  unfold lowPart
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          (natDegree_add_le_of_degree_le
            (natDegree_add_le_of_degree_le
              (natDegree_add_le_of_degree_le ((scaled_degree _ ht4).trans (by omega))
                (scaled_degree _ (z_monic a).natDegree_eq.le)) hxt)
            ((scaled_degree _ (t_monic a).natDegree_eq.le).trans (by omega)))
          ((scaled_degree _ hxyt).trans (by omega)))
        ((scaled_degree _ (y_monic a).natDegree_eq.le).trans (by omega)))
      (by rw [natDegree_C]; omega)) (by rw [natDegree_C]; omega)

theorem high_row (a : ℕ → R) (j : ℕ) (hj : 4 < j) :
    (output a).coeff j = (highPart a).coeff j := by
  have hz : (lowPart a).coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt ((lowPart_degree a).trans_lt hj)
  rw [output_high_split, coeff_add, hz, add_zero]

private theorem cubic_mul_row (p : R[X]) (b3 b2 b1 b0 : R) (j : ℕ) (hj : 3 ≤ j) :
    ((C b3 * X ^ 3 + C b2 * X ^ 2 + C b1 * X ^ 1 + C b0) * p).coeff j =
      b3 * p.coeff (j-3) + b2 * p.coeff (j-2) + b1 * p.coeff (j-1) + b0 * p.coeff j := by
  have hj2 : 2 ≤ j := by omega
  have hj1 : 1 ≤ j := by omega
  simp only [add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_pow_mul',
    hj, hj2, hj1, if_true]

theorem highLeft_row (a : ℕ → R) (j : ℕ) (hj : 3 ≤ j) :
    (highLeft a).coeff j = (z a ^ 2).coeff (j-3) + a 0 * (z a ^ 2).coeff (j-2) +
      a 3 * (z a ^ 2).coeff (j-1) + a 4 * (z a ^ 2).coeff j := by
  have ht : t a + C (a 4) =
      C (1 : R) * X ^ 3 + C (a 0) * X ^ 2 + C (a 3) * X ^ 1 + C (a 4) := by
    simp only [t_shape, map_one, one_mul, pow_one]
  rw [highLeft, ht, cubic_mul_row _ _ _ _ _ j hj, one_mul]

def factor3 (a : ℕ → R) : R := h a + 1
def factor2 (a : ℕ → R) : R := a 0 * (h a + 1) + 1
def factor1 (a : ℕ → R) : R := a 3 * (h a + 1) + a 0 + 1
def factor0 (a : ℕ → R) : R := h a * a 4

theorem highFactor_shape (a : ℕ → R) : highFactor a =
    C (factor3 a) * X ^ 3 + C (factor2 a) * X ^ 2 +
      C (factor1 a) * X ^ 1 + C (factor0 a) := by
  simp only [highFactor, t_shape, y_shape, factor3, factor2, factor1, factor0,
    map_add, map_mul, map_one, pow_one]
  ring

theorem highRight_row (a : ℕ → R) (j : ℕ) (hj : 3 ≤ j) :
    (highRight a).coeff j = factor3 a * (z a).coeff (j-3) +
      factor2 a * (z a).coeff (j-2) + factor1 a * (z a).coeff (j-1) +
      factor0 a * (z a).coeff j := by
  rw [highRight, highFactor_shape, cubic_mul_row _ _ _ _ _ j hj]

theorem output_row10 (a : ℕ → R) : (output a).coeff 10 = a 0 := by
  rw [high_row a 10 (by omega), highPart, coeff_add, coeff_add,
    highLeft_row a 10 (by omega), highRight_row a 10 (by omega)]
  simp only [z_square_coeff, z_coeff, t_square_coeff, Nat.reduceSub,
    Nat.reduceEqDiff, if_true, if_false,
    zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one]

theorem output_row9 (a : ℕ → R) : (output a).coeff 9 = a 3 + 1 := by
  rw [high_row a 9 (by omega), highPart, coeff_add, coeff_add,
    highLeft_row a 9 (by omega), highRight_row a 9 (by omega)]
  simp only [z_square_coeff, z_coeff, t_square_coeff, Nat.reduceSub,
    Nat.reduceEqDiff, if_true, if_false,
    zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;> ring

theorem output_row8 (a : ℕ → R) : (output a).coeff 8 = a 4 + a 0 := by
  rw [high_row a 8 (by omega), highPart, coeff_add, coeff_add,
    highLeft_row a 8 (by omega), highRight_row a 8 (by omega)]
  simp only [z_square_coeff, z_coeff, t_square_coeff, Nat.reduceSub,
    Nat.reduceEqDiff, if_true, if_false,
    zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;> ring

theorem output_row7_named (a : ℕ → R) :
    (output a).coeff 7 = z2 a ^ 2 + a 3 + factor3 a := by
  rw [high_row a 7 (by omega), highPart, coeff_add, coeff_add,
    highLeft_row a 7 (by omega), highRight_row a 7 (by omega)]
  simp only [z_square_coeff, z_coeff, t_square_coeff, Nat.reduceSub,
    Nat.reduceEqDiff, if_true, if_false,
    zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;> ring

theorem output_row6_named (a : ℕ → R) :
    (output a).coeff 6 = a 0 * z2 a ^ 2 + a 4 + factor3 a + factor2 a + 1 := by
  rw [high_row a 6 (by omega), highPart, coeff_add, coeff_add,
    highLeft_row a 6 (by omega), highRight_row a 6 (by omega)]
  simp only [z_square_coeff, z_coeff, t_square_coeff, Nat.reduceSub,
    Nat.reduceEqDiff, if_true, if_false,
    zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;> ring

theorem output_row5_named (a : ℕ → R) :
    (output a).coeff 5 = z1 a ^ 2 + a 3 * z2 a ^ 2 +
      factor3 a * z2 a + factor2 a + factor1 a := by
  rw [high_row a 5 (by omega), highPart, coeff_add, coeff_add,
    highLeft_row a 5 (by omega), highRight_row a 5 (by omega)]
  simp only [z_square_coeff, z_coeff, t_square_coeff, Nat.reduceSub,
    Nat.reduceEqDiff, if_true, if_false,
    zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] <;> ring

/-- First square row of (11.1), after the three leading unit reads. -/
theorem output_row7 (a : ℕ → R) :
    (output a).coeff 7 = K7 a + sumKeys a ^ 2 + h a := by
  rw [output_row7_named]
  simp only [z2, factor3, K7, CharTwo.add_sq, ← pow_mul, Nat.reduceMul]
  ring

/-- The companion row solves h with unit slope once row seven is read. -/
theorem output_row6 (a : ℕ → R) :
    (output a).coeff 6 = K6 a + a 0 * sumKeys a ^ 2 + (a 0 + 1) * h a := by
  rw [output_row6_named]
  simp only [z2, factor3, factor2, K6, CharTwo.add_sq, ← pow_mul, Nat.reduceMul]
  simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add]
  ring

/-- Second square row of (11.1), exposing a1 after s and h. -/
theorem output_row5 (a : ℕ → R) :
    (output a).coeff 5 = K5 a + a 0 ^ 2 * (sumKeys a ^ 2 + h a) +
      sumKeys a + a 1 ^ 2 + a 3 * sumKeys a ^ 2 + sumKeys a * h a + a 3 * h a := by
  have h3 : (3 : R) = 1 := by
    calc
      (3 : R) = (2 : R) + 1 := by norm_num only
      _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]
  rw [output_row5_named]
  simp only [z2, z1, factor3, factor2, factor1, K5,
    CharTwo.add_sq, mul_pow, ← pow_mul, Nat.reduceMul]
  simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add]
  ring_nf
  simp only [CharTwo.two_eq_zero, h3, mul_zero, zero_mul, mul_one, add_zero, zero_add]

end FastPoly.Char2PaperDegree11
