import FastPoly.Examples.Char2PaperDegree11Core

/-! The lower butterfly of the paper's actual (A.0) degree-eleven circuit,
equations (11.3)/(11.4). Baselines are evaluations of that same circuit,
with the displayed five or six offsets zeroed; no full output is expanded. -/
namespace FastPoly.Char2PaperDegree11

open Polynomial
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def baselineKeys (a : ℕ → R) : ℕ → R
  | 5 => 0
  | 7 => 0
  | 8 => h a
  | 9 => 0
  | 10 => 0
  | i => a i
def baseline0Keys (a : ℕ → R) : ℕ → R
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => h a
  | 9 => 0
  | 10 => 0
  | i => a i
noncomputable def B (a : ℕ → R) : R[X] := output (baselineKeys a)
noncomputable def B0 (a : ℕ → R) : R[X] := output (baseline0Keys a)
noncomputable def uBase (a : ℕ → R) : R[X] := (t a + C (a 4)) * z a
def kappa (a : ℕ → R) : R := a 5 * (h a + a 5)
noncomputable def residual (a : ℕ → R) : R[X] :=
  C (kappa a) * (t a + C (a 4)) + C (a 5) * y a +
    C (a 7) * (X + t a + C (a 6)) + C (a 9) * (t a + C (a 8)) + C (a 10)

theorem u_baseline (a : ℕ → R) : u (baselineKeys a) = uBase a := by
  change (t a + C (a 4)) * (z a + C 0) = _
  rw [map_zero, add_zero]
  rfl
theorem u_baseline0 (a : ℕ → R) : u (baseline0Keys a) = uBase a := by
  change (t a + C (a 4)) * (z a + C 0) = _
  rw [map_zero, add_zero]
  rfl

theorem B_form (a : ℕ → R) : B a =
    (X + y a + t a + uBase a + C (a 6)) * (z a + t a) +
      (t a + C (h a)) * (y a + uBase a) := by
  change (X + y a + t a + u (baselineKeys a) + C (a 6)) * (z a + t a + C 0) +
    (t a + C (h a)) * (y a + u (baselineKeys a) + C 0) + C 0 = _
  simp only [u_baseline, map_zero, add_zero]

theorem B0_form (a : ℕ → R) : B0 a =
    (X + y a + t a + uBase a) * (z a + t a) +
      (t a + C (h a)) * (y a + uBase a) := by
  change (X + y a + t a + u (baseline0Keys a) + C 0) * (z a + t a + C 0) +
    (t a + C (h a)) * (y a + u (baseline0Keys a) + C 0) + C 0 = _
  simp only [u_baseline0, map_zero, add_zero]

private theorem butterfly_identity (x y z t c4 c5 c6 c7 c8 c9 c10 : R[X]) :
    ((x + y + t + (t + c4) * (z + c5) + c6) * (z + t + c7) +
      (t + c8) * (y + (t + c4) * (z + c5) + c9) + c10) +
    ((x + y + t + (t + c4) * z + c6) * (z + t) +
      (t + (c5 + c7 + c8)) * (y + (t + c4) * z)) =
    (c5 * ((c5 + c7 + c8) + c5)) * (t + c4) + c5 * y +
      c7 * (x + t + c6) + c9 * (t + c8) + c10 := by
  have hfour : (4 : R[X]) = 0 := by
    calc
      (4 : R[X]) = 2 + 2 := by ring
      _ = 0 := by rw [CharTwo.two_eq_zero, zero_add]
  ring_nf
  simp only [CharTwo.two_eq_zero, hfour, mul_zero, add_zero, zero_add]

/-- Equation (11.3), proved only in the named final-gate frame. -/
theorem output_add_B (a : ℕ → R) : output a + B a = residual a := by
  rw [B_form]
  change ((X + y a + t a + (t a + C (a 4)) * (z a + C (a 5)) + C (a 6)) *
    (z a + t a + C (a 7)) + (t a + C (a 8)) *
      (y a + (t a + C (a 4)) * (z a + C (a 5)) + C (a 9)) + C (a 10)) +
    ((X + y a + t a + (t a + C (a 4)) * z a + C (a 6)) * (z a + t a) +
      (t a + C (h a)) * (y a + (t a + C (a 4)) * z a)) = _
  have hh : C (h a) = C (a 5) + C (a 7) + C (a 8) := by
    simp only [h, map_add]
  rw [residual, kappa, map_mul, map_add, hh]
  exact butterfly_identity X (y a) (z a) (t a) (C (a 4)) (C (a 5))
    (C (a 6)) (C (a 7)) (C (a 8)) (C (a 9)) (C (a 10))

private theorem baseline_constant (p q w c : R[X]) :
    ((p + c) * q + w) + (p * q + w) = c * q := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem B_add_B0 (a : ℕ → R) : B a + B0 a = C (a 6) * (z a + t a) := by
  rw [B_form, B0_form]
  exact baseline_constant _ _ _ _

private theorem telescope (p b c : R[X]) : p + c = (p + b) + (b + c) := by
  simp only [add_assoc, CharTwo.add_cancel_left]

theorem output_add_B0 (a : ℕ → R) :
    output a + B0 a = residual a + C (a 6) * (z a + t a) := by
  rw [telescope (output a) (B a) (B0 a), output_add_B, B_add_B0]

private theorem scaled_degree (c : R) {p : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) : (C c * p).natDegree ≤ n := by
  exact natDegree_mul_le.trans (by rw [natDegree_C]; omega)
private theorem C_degree (c : R) (n : ℕ) : (C c : R[X]).natDegree ≤ n := by
  rw [natDegree_C]
  omega

theorem residual_degree (a : ℕ → R) : (residual a).natDegree ≤ 3 := by
  have ht (c : R) : (t a + C c).natDegree ≤ 3 :=
    natDegree_add_le_of_degree_le (t_monic a).natDegree_eq.le (C_degree _ _)
  have hxt : ((X : R[X]) + t a + C (a 6)).natDegree ≤ 3 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (natDegree_X_le.trans (by omega))
        (t_monic a).natDegree_eq.le) (C_degree _ _)
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (scaled_degree _ (ht _))
          ((scaled_degree _ (y_monic a).natDegree_eq.le).trans (by omega)))
        (scaled_degree _ hxt)) (scaled_degree _ (ht _))) (C_degree _ _)

theorem baseline_pivot (a : ℕ → R) : (output a).coeff 4 + (B0 a).coeff 4 = a 6 := by
  have hres : (residual a).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((residual_degree a).trans_lt (by omega))
  have ht : (t a).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((t_monic a).natDegree_eq.trans_lt (by omega))
  have hz : (z a).coeff 4 = 1 := by
    rw [← (z_monic a).natDegree_eq]
    exact (z_monic a).monic.coeff_natDegree
  rw [← coeff_add, output_add_B0, coeff_add, hres, zero_add,
    coeff_C_mul, coeff_add, hz, ht, add_zero, mul_one]

private theorem y_row0 (a : ℕ → R) : (y a).coeff 0 = 0 := by
  simp only [y_shape, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
    Nat.reduceEqDiff, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero]
private theorem y_row1 (a : ℕ → R) : (y a).coeff 1 = a 0 := by
  simp only [y_shape, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
    Nat.reduceEqDiff, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero]
private theorem y_row2 (a : ℕ → R) : (y a).coeff 2 = 1 := by
  simp only [y_shape, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
    Nat.reduceEqDiff, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero]
private theorem y_row3 (a : ℕ → R) : (y a).coeff 3 = 0 := by
  simp only [y_shape, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
    Nat.reduceEqDiff, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero]
private theorem t_row0 (a : ℕ → R) : (t a).coeff 0 = 0 := by
  simp only [t_shape, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
    Nat.reduceEqDiff, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero]
private theorem t_row1 (a : ℕ → R) : (t a).coeff 1 = a 3 := by
  simp only [t_shape, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
    Nat.reduceEqDiff, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero]
private theorem t_row2 (a : ℕ → R) : (t a).coeff 2 = a 0 := by
  simp only [t_shape, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
    Nat.reduceEqDiff, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero]
private theorem t_row3 (a : ℕ → R) : (t a).coeff 3 = 1 := by
  simp only [t_shape, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
    Nat.reduceEqDiff, ite_true, ite_false, mul_zero, mul_one, zero_add, add_zero]

theorem residual_three (a : ℕ → R) : (residual a).coeff 3 = kappa a + a 7 + a 9 := by
  simp only [residual, coeff_add, coeff_C_mul, coeff_C_succ, coeff_X,
    t_row3, y_row3, Nat.reduceEqDiff, ite_false, mul_zero, mul_one, zero_add, add_zero]

theorem residual_two (a : ℕ → R) :
    (residual a).coeff 2 = a 0 * (kappa a + a 7 + a 9) + a 5 := by
  simp only [residual, coeff_add, coeff_C_mul, coeff_C_succ, coeff_X,
    t_row2, y_row2, Nat.reduceEqDiff, ite_false, mul_zero, mul_one, zero_add, add_zero]
  ring

theorem residual_one (a : ℕ → R) :
    (residual a).coeff 1 = a 3 * (kappa a + a 7 + a 9) + a 0 * a 5 + a 7 := by
  simp only [residual, coeff_add, coeff_C_mul, coeff_C_succ, coeff_X_one,
    t_row1, y_row1, mul_zero, mul_one, zero_add, add_zero]
  ring

theorem residual_zero (a : ℕ → R) : (residual a).coeff 0 =
    kappa a * a 4 + a 7 * a 6 + a 9 * a 8 + a 10 := by
  simp only [residual, coeff_add, coeff_C_mul, coeff_C_zero, coeff_X_zero,
    t_row0, y_row0, mul_zero, mul_one, zero_add, add_zero]

/-- The lower four expressions of (11.4), each with unit slope. -/
theorem recover_a5 (a : ℕ → R) : (residual a).coeff 2 + a 0 * (residual a).coeff 3 = a 5 := by
  simp only [residual_two, residual_three, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]
theorem recover_a7 (a : ℕ → R) :
    (residual a).coeff 1 + a 3 * (residual a).coeff 3 + a 0 * a 5 = a 7 := by
  simp only [residual_one, residual_three, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]
theorem recover_a9 (a : ℕ → R) : (residual a).coeff 3 + kappa a + a 7 = a 9 := by
  simp only [residual_three, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]
theorem recover_a8 (a : ℕ → R) : h a + a 5 + a 7 = a 8 := by
  simp only [h, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]
theorem recover_a10 (a : ℕ → R) :
    (residual a).coeff 0 + kappa a * a 4 + a 7 * a 6 + a 9 * a 8 = a 10 := by
  simp only [residual_zero, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]

end FastPoly.Char2PaperDegree11
