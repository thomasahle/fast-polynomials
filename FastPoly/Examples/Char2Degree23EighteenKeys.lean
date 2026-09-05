import FastPoly.Examples.Char2Degree23EighteenFrame

/-!
# Normalized q18: the explicit unit row-four-plus-row-three pivot

The supplied key change is matched slot by slot to the checked raw update.
The previously read coefficient eight removes its high column. The two
remaining leading coefficients differ by one, giving the stated unit solve.
-/

namespace FastPoly.Char2Degree23EighteenKeys

open Polynomial Char2Degree23RowEight Char2Degree23HighKeys Char2Degree23LowKeys
  Char2Degree23MiddleKeys Char2Degree23EighteenFrame

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem tau18 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.tau (increment q 18 d) = Char2Degree23Coordinates.tau q + d := by
  dsimp [Char2Degree23Coordinates.tau, Char2Degree23Coordinates.gamma, increment, Function.update]
  ac_rfl

theorem a11_18 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a11 (increment q 18 d) = Char2Degree23Coordinates.a11 q + d := by
  unfold Char2Degree23Coordinates.a11
  rw [tau18]
  change q 13 + (Char2Degree23Coordinates.tau q + d) = _
  rw [← add_assoc]

theorem a10_18 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a10 (increment q 18 d) = Char2Degree23Coordinates.a10 q + d := by
  unfold Char2Degree23Coordinates.a10
  rw [a11_18]
  change q 12 + (Char2Degree23Coordinates.rho q + q 16 +
    (Char2Degree23Coordinates.a11 q + d) + Char2Degree23Coordinates.a12 q) = _
  ac_rfl

private theorem double_shift (a b c d e : R) :
    a + (b + (c + d) + e + d) = a + (b + c + e) := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem a9_18 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a9 (increment q 18 d) = Char2Degree23Coordinates.a9 q := by
  unfold Char2Degree23Coordinates.a9
  rw [a11_18]
  change q 10 + (Char2Degree23Coordinates.rho q + (Char2Degree23Coordinates.a11 q + d) +
    q 20 + (q 18 + d)) = _
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem a8_18 (q : Fin 23 → R) (d : R) :
    Char2Degree23Coordinates.a8 (increment q 18 d) = Char2Degree23Coordinates.a8 q := by
  unfold Char2Degree23Coordinates.a8
  rw [a10_18]
  change q 9 + (q 16 ^ 2 + q 7 * q 16 + (Char2Degree23Coordinates.a10 q + d) + q 20 + (q 18 + d)) = _
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem slots18 (q : Fin 23 → R) (d : R) :
    SameRaw (shift18 (rawKeys q) d) (rawKeys (increment q 18 d)) := by
  constructor <;> simp only [shift18] <;>
    rw [rawKeys_core _ _ (by omega) (by omega), rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_18 q d).symm | exact (a9_18 q d).symm |
    exact (a10_18 q d).symm | exact (a11_18 q d).symm |
    (change (q 17 + q 18) + d = q 17 + (q 18 + d); rw [add_assoc])

theorem residual_degree (a : ℕ → R) (d : R) :
    (C d * low a + C (d ^ 2)).natDegree ≤ 4 :=
  natDegree_add_le_of_degree_le
    ((natDegree_C_mul_le _ _).trans (low_degree a)) (by rw [natDegree_C]; omega)

theorem increment18_change (q : Fin 23 → R) (d : R) :
    output (rawKeys (increment q 18 d)) = output (rawKeys q) +
      (C d * low (rawKeys q) + C (d ^ 2)) :=
  Char2Degree23NormalizedPeel.increment (by omega) (slots18 q d) rfl
    (raw_difference (rawKeys q) d) ((residual_degree _ _).trans_lt (by omega))

theorem increment18_higher (q : Fin 23 → R) (d : R) (j : ℕ) (hj : 4 < j) :
    (output (rawKeys (increment q 18 d))).coeff j = (output (rawKeys q)).coeff j := by
  have hz : (C d * low (rawKeys q) + C (d ^ 2)).coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt ((residual_degree _ _).trans_lt hj)
  rw [increment18_change, coeff_add, hz, add_zero]

theorem increment18_four (q : Fin 23 → R) (d : R) :
    (output (rawKeys (increment q 18 d))).coeff 4 =
      (output (rawKeys q)).coeff 4 + d * (B (rawKeys q) + 1) := by
  have h40 : (4 : ℕ) ≠ 0 := by omega
  rw [increment18_change, coeff_add, coeff_add, coeff_C_mul, low_four]
  simp only [coeff_C, h40, ite_false, add_zero]

theorem increment18_three (q : Fin 23 → R) (d : R) :
    (output (rawKeys (increment q 18 d))).coeff 3 =
      (output (rawKeys q)).coeff 3 + d * B (rawKeys q) := by
  have h30 : (3 : ℕ) ≠ 0 := by omega
  rw [increment18_change, coeff_add, coeff_add, coeff_C_mul, low_three]
  simp only [coeff_C, h30, ite_false, add_zero]

private theorem unit_pair (a b d c : R) :
    (a + d * (c + 1)) + (b + d * c) = (a + b) + d := by
  rw [add_add_add_comm, mul_add, mul_one, Char2Decoder.cancel_tail]

/-- This is exactly the first row of the supplied terminal block inverse. -/
theorem increment18_adapted (q : Fin 23 → R) (d : R) :
    (output (rawKeys (increment q 18 d))).coeff 4 +
      (output (rawKeys (increment q 18 d))).coeff 3 =
    ((output (rawKeys q)).coeff 4 + (output (rawKeys q)).coeff 3) + d := by
  rw [increment18_four, increment18_three]
  exact unit_pair _ _ _ _

end FastPoly.Char2Degree23EighteenKeys

