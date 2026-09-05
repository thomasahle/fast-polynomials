import FastPoly.Examples.Char2Degree23LowKeys

/-!
# Two adjacent terminal rows, with the earlier wires kept named

The first quartic has coefficient one in both rows four and three.
Consequently the supplied q19 update changes both rows equally; the
decoder's row-four-plus-row-three shear is invariant. Only this quartic
is expanded, never the degree-23 circuit or the row-eight baseline.
-/

namespace FastPoly.Char2Degree23TerminalRows

open Polynomial Char2Degree23RowEight Char2Degree23HighKeys
  Char2Degree23LowKeys Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

private theorem quartic_shape (x a b : R) :
    (x * x + a) * (x + x * x + b) =
      x ^ 4 + x ^ 3 + (a + b) * x ^ 2 + a * x + a * b := by ring

theorem z_shape (a : ℕ → R) :
    z a = X ^ 4 + X ^ 3 + C (a 0 + a 1) * X ^ 2 +
      C (a 0) * X + C (a 0 * a 1) := by
  unfold z y
  simp only [map_add, map_mul]
  exact quartic_shape X (C (a 0)) (C (a 1))

theorem z_three (a : ℕ → R) : (z a).coeff 3 = 1 := by
  have h34 : (3 : ℕ) ≠ 4 := by omega
  have h32 : (3 : ℕ) ≠ 2 := by omega
  have h13 : (1 : ℕ) ≠ 3 := by omega
  have h30 : (3 : ℕ) ≠ 0 := by omega
  rw [z_shape]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_X_pow, coeff_C_mul, coeff_X,
    coeff_C, h34, h32, h13, h30, ite_true, ite_false, mul_zero, zero_add, add_zero]

theorem lastFactor_three (a : ℕ → R) : (lastFactor a).coeff 3 = 1 := by
  have h30 : (3 : ℕ) ≠ 0 := by omega
  rw [lastFactor, coeff_add, z_three]
  simp only [coeff_C, h30, ite_false, add_zero]

theorem lastFactor_four (a : ℕ → R) : (lastFactor a).coeff 4 = 1 := by
  rw [← (lastFactor_monic a).natDegree_eq]
  exact (lastFactor_monic a).monic.coeff_natDegree

theorem increment19_unit_four (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 19 delta))) 4 delta := by
  apply unit_difference_of_split _ _ (lastFactor (rawKeys q)) 4 delta 0 (by omega)
    (lastFactor_monic (rawKeys q))
  rw [map_zero, add_zero, mul_comm]
  exact increment19_change q delta

theorem increment19_three (q : Fin 23 → R) (delta : R) :
    (output (rawKeys (increment q 19 delta))).coeff 3 =
      (output (rawKeys q)).coeff 3 + delta := by
  rw [increment19_change, coeff_add, coeff_mul_C, lastFactor_three, one_mul]

/-- The earlier adapted row is unchanged, while row three has unit slope. -/
theorem increment19_adapted (q : Fin 23 → R) (delta : R) :
    (output (rawKeys (increment q 19 delta))).coeff 4 +
      (output (rawKeys (increment q 19 delta))).coeff 3 =
    (output (rawKeys q)).coeff 4 + (output (rawKeys q)).coeff 3 := by
  rw [(increment19_unit_four q delta).row, increment19_three,
    add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

end FastPoly.Char2Degree23TerminalRows
