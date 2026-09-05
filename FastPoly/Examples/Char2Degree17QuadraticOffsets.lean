import FastPoly.Examples.Char2UnequalOffsets
import Mathlib.Tactic.Ring

/-!
# The equal-degree two-row solve in the existing degree-17 circuit

Write `y = X * (X + q0)`. In the gate `(y + a3) * (X + y + a4)`,
the rows two and one recover the two offsets by
`sigma = q3 + q0^2 + q0`, `a3 = q4 + q0*sigma`, `a4 = sigma + a3`.
This is the supplied verifier's exceptional gate; all unequal-degree gates
use `Char2UnequalOffsets.equiv`. No other degree-17 gate is expanded here.
-/

namespace FastPoly.Char2Degree17QuadraticOffsets

set_option maxHeartbeats 20000

open Polynomial Char2Decoder

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def y (q0 : R) : R[X] := X * (X + C q0)

noncomputable def gate (q0 : R) (a : R × R) : R[X] :=
  (y q0 + C a.1) * (X + y q0 + C a.2)

noncomputable def rows (q0 : R) (a : R × R) : R × R :=
  ((gate q0 a).coeff 2, (gate q0 a).coeff 1)

/-- The first pivot recovers the sum, not either offset in isolation. -/
def sigma (q0 : R) (q : R × R) : R := q.1 + (q0 * q0 + q0)

def recover (q0 : R) (q : R × R) : R × R :=
  let a3 := q.2 + q0 * sigma q0 q
  (a3, sigma q0 q + a3)

omit [CharP R 2] in
theorem y_eq (q0 : R) : y q0 = X ^ 2 + C q0 * X := by
  simp only [y, mul_add, pow_two, mul_comm X (C q0)]

omit [CharP R 2] in
theorem gate_form (q0 : R) (a : R × R) :
    gate q0 a = X ^ 4 + C (q0 + q0 + 1) * X ^ 3 +
      C ((q0 * q0 + q0) + (a.1 + a.2)) * X ^ 2 +
      C (q0 * (a.1 + a.2) + a.1) * X + C (a.1 * a.2) := by
  simp only [gate, y_eq, map_add, map_mul, map_one]
  ring

omit [CharP R 2] in
theorem gate_rows (q0 : R) (a : R × R) :
    rows q0 a = ((q0 * q0 + q0) + (a.1 + a.2), q0 * (a.1 + a.2) + a.1) := by
  have h13 : (1 : ℕ) ≠ 3 := by omega
  have h14 : (1 : ℕ) ≠ 4 := by omega
  have h12 : (1 : ℕ) ≠ 2 := by omega
  have h23 : (2 : ℕ) ≠ 3 := by omega
  have h24 : (2 : ℕ) ≠ 4 := by omega
  have h21 : (2 : ℕ) ≠ 1 := by omega
  have h20 : (2 : ℕ) ≠ 0 := by omega
  simp only [rows, gate_form, coeff_add, coeff_C_mul_X_pow,
    coeff_C_mul_X, coeff_X_pow, coeff_C,
    h12, h13, h14, h21, h20, h23, h24, one_ne_zero,
    ite_false, ite_true, zero_add, add_zero]

theorem sigma_rows (q0 : R) (a : R × R) : sigma q0 (rows q0 a) = a.1 + a.2 := by
  rw [gate_rows]
  exact cancel_tail _ _

theorem recover_rows (q0 : R) (a : R × R) : recover q0 (rows q0 a) = a := by
  have hs := sigma_rows q0 a
  simp only [recover, hs]
  rw [gate_rows]
  rw [cancel_tail]
  exact Prod.ext rfl (cancel_tail _ _)

theorem recovered_sum (q0 : R) (q : R × R) :
    (recover q0 q).1 + (recover q0 q).2 = sigma q0 q := by
  change (q.2 + q0 * sigma q0 q) +
    (sigma q0 q + (q.2 + q0 * sigma q0 q)) = _
  rw [← add_assoc, cancel_tail]

theorem rows_recover (q0 : R) (q : R × R) : rows q0 (recover q0 q) = q := by
  rw [gate_rows, recovered_sum]
  apply Prod.ext
  · change (q0 * q0 + q0) + (q.1 + (q0 * q0 + q0)) = q.1
    rw [← add_assoc, cancel_tail]
  · change q0 * sigma q0 q + (q.2 + q0 * sigma q0 q) = q.2
    rw [← add_assoc, cancel_tail]

noncomputable def equiv (q0 : R) : (R × R) ≃ (R × R) where
  toFun := rows q0
  invFun := recover q0
  left_inv := recover_rows q0
  right_inv := rows_recover q0

end FastPoly.Char2Degree17QuadraticOffsets
