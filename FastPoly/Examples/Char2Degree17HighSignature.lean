import FastPoly.Examples.Char2Degree17HighFrame
import FastPoly.Examples.Char2Degree19Crown

/-!
# Small leading signatures in the degree-17 high frame

The only convolution opened is one cubic times one quartic, at its top two
rows. A second four-term convolution reads the cubic factor of `A^2*B`.
Frobenius then gives output rows 16, 15, and 13 from named wire coefficients.
-/

namespace FastPoly.Char2Degree17HighSignature

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TerminalPivots Char2Degree17Q9Pivot Char2Degree17Q8Pivot
open Char2Degree17HighFrame Char2Degree17TerminalFrame

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem monic_row {p : R[X]} {d : ℕ} (hp : IsMonicOfDegree p d) : p.coeff d = 1 := by
  rw [← hp.natDegree_eq]
  exact hp.monic.coeff_natDegree

theorem mul34_coeff6 (p q : R[X]) (hp : IsMonicOfDegree p 3) (hq : IsMonicOfDegree q 4) :
    (p * q).coeff 6 = p.coeff 2 + q.coeff 3 := by
  have hp4 : p.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 3 < 4))
  have hp5 : p.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 3 < 5))
  have hp6 : p.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 3 < 6))
  have hq5 : q.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 4 < 5))
  have hq6 : q.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 4 < 6))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    hp4, hp5, hp6, hq5, hq6, monic_row hp, monic_row hq,
    mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]

theorem mul34_coeff5 (p q : R[X]) (hp : IsMonicOfDegree p 3) (hq : IsMonicOfDegree q 4) :
    (p * q).coeff 5 = p.coeff 1 + p.coeff 2 * q.coeff 3 + q.coeff 2 := by
  have hp4 : p.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 3 < 4))
  have hp5 : p.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 3 < 5))
  have hq5 : q.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 4 < 5))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    hp4, hp5, hq5, monic_row hp, monic_row hq,
    mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]

noncomputable def uLower (q : Vector R) : R[X] := dy q + dz q + C (au q).1
noncomputable def uHigher (q : Vector R) : R[X] := dz q + dt q + C (au q).2

theorem uLower_monic (q : Vector R) : IsMonicOfDegree (uLower q) 3 :=
  shifted_monic (add_monic (frame_y_monic q) (frame_z_monic q) (by omega))
    (by omega) (au q).1

theorem uHigher_monic (q : Vector R) : IsMonicOfDegree (uHigher q) 4 :=
  shifted_monic (add_monic (frame_z_monic q) (frame_t_monic q) (by omega))
    (by omega) (au q).2

theorem y_row1 (q : Vector R) : (dy q).coeff 1 = q 0 := by
  simp only [dy, Char2Degree17QuadraticOffsets.y, coeff_X_mul,
    coeff_add, coeff_X_zero, coeff_C_zero, zero_add]

theorem z_row2 (q : Vector R) : (dz q).coeff 2 = q 1 := congrArg Prod.fst (z_rows q)
theorem z_row1 (q : Vector R) : (dz q).coeff 1 = q 2 := congrArg Prod.snd (z_rows q)

theorem uLower_row2 (q : Vector R) : (uLower q).coeff 2 = 1 + q 1 := by
  have h20 : (2 : ℕ) ≠ 0 := by omega
  simp only [uLower, coeff_add, coeff_C, h20, ite_false,
    monic_row (frame_y_monic q), z_row2, add_zero]

theorem uLower_row1 (q : Vector R) : (uLower q).coeff 1 = q 0 + q 2 := by
  simp only [uLower, coeff_add, coeff_C, one_ne_zero, ite_false, y_row1, z_row1, add_zero]

theorem uHigher_row3 (q : Vector R) : (uHigher q).coeff 3 = 0 := by
  have h30 : (3 : ℕ) ≠ 0 := by omega
  simp only [uHigher, coeff_add, coeff_C, h30, ite_false,
    monic_row (frame_z_monic q), t_coeff_three, add_zero, CharTwo.add_self_eq_zero]

theorem uHigher_row2 (q : Vector R) : (uHigher q).coeff 2 = q 1 + q 3 := by
  have h20 : (2 : ℕ) ≠ 0 := by omega
  simp only [uHigher, coeff_add, coeff_C, h20, ite_false, z_row2, t_coeff_two, add_zero]

theorem u_row6 (q : Vector R) : (du q).coeff 6 = q 1 + 1 := by
  change (uLower q * uHigher q).coeff 6 = _
  rw [mul34_coeff6 _ _ (uLower_monic q) (uHigher_monic q), uLower_row2, uHigher_row3, add_zero, add_comm]

theorem u_row5 (q : Vector R) : (du q).coeff 5 = (q 0 + q 2) + (q 1 + q 3) := by
  change (uLower q * uHigher q).coeff 5 = _
  rw [mul34_coeff5 _ _ (uLower_monic q) (uHigher_monic q),
    uLower_row1, uHigher_row3, uHigher_row2, mul_zero, add_zero]

theorem A_row6 (q : Vector R) : (A q).coeff 6 = q 1 + 1 := by
  have h16 : (1 : ℕ) ≠ 6 := by omega
  simp only [A, coeff_add, coeff_X, h16, ite_false, zero_add, u_row6]

theorem A_row5 (q : Vector R) : (A q).coeff 5 = (q 0 + q 2) + (q 1 + q 3) := by
  have h15 : (1 : ℕ) ≠ 5 := by omega
  simp only [A, coeff_add, coeff_X, h15, ite_false, zero_add, u_row5]

theorem B_row2 (q : Vector R) : (B q).coeff 2 = q 1 := by
  have h12 : (1 : ℕ) ≠ 2 := by omega
  have h20 : (2 : ℕ) ≠ 0 := by omega
  simp only [B, coeff_add, coeff_X, coeff_C, h12, h20, ite_false, zero_add, add_zero, z_row2]

theorem B_row1 (q : Vector R) : (B q).coeff 1 = q 2 + 1 := by
  simp only [B, coeff_add, coeff_X, coeff_C, ite_true, one_ne_zero, ite_false,
    z_row1, add_zero]
  exact add_comm _ _

/-- Reconstruct only a cubic from its four named coefficients. -/
theorem cubic_form (p : R[X]) (hp : IsMonicOfDegree p 3) :
    p = X ^ 3 + C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, hp.natDegree_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
    pow_zero, pow_one, mul_one, zero_add, monic_row hp, map_one, one_mul]
  ac_rfl

theorem B_form (q : Vector R) :
    B q = X ^ 3 + C (q 1) * X ^ 2 + C (q 2 + 1) * X + C ((B q).coeff 0) := by
  have he := cubic_form (B q) (B_monic q)
  rw [B_row2, B_row1] at he
  exact he

theorem cubic_product_row (p : R[X]) (b0 b1 b2 : R) (j : ℕ) :
    (p * (X ^ 3 + C b2 * X ^ 2 + C b1 * X + C b0)).coeff (j + 3) =
      p.coeff j + p.coeff (j + 1) * b2 + p.coeff (j + 2) * b1 + p.coeff (j + 3) * b0 := by
  have h3 : 3 ≤ j + 3 := by omega
  have h2 : 2 ≤ j + 3 := by omega
  have e3 : j + 3 - 3 = j := by omega
  have e2 : j + 3 - 2 = j + 1 := by omega
  simp only [mul_add, ← mul_assoc, coeff_add, coeff_mul_X_pow', coeff_mul_X,
    coeff_mul_C, h3, h2, ite_true, e3, e2]

theorem squareB_row (q : Vector R) (j : ℕ) :
    (A q ^ 2 * B q).coeff (j + 3) =
      (A q ^ 2).coeff j + (A q ^ 2).coeff (j + 1) * q 1 +
        (A q ^ 2).coeff (j + 2) * (q 2 + 1) +
          (A q ^ 2).coeff (j + 3) * (B q).coeff 0 := by
  conv_lhs => rw [B_form]
  exact cubic_product_row _ _ _ _ j

theorem squareA_row10 (q : Vector R) :
    (A q ^ 2).coeff 10 = ((q 0 + q 2) + (q 1 + q 3)) ^ 2 := by
  have he : (A q ^ 2).coeff 10 = (A q).coeff 5 ^ 2 :=
    Char2Degree19Crown.square_coeff_even (A q) 5
  rw [A_row5] at he
  exact he

theorem squareA_row11 (q : Vector R) : (A q ^ 2).coeff 11 = 0 :=
  Char2Degree19Crown.square_coeff_odd (A q) 5

theorem squareA_row12 (q : Vector R) : (A q ^ 2).coeff 12 = (q 1 + 1) ^ 2 := by
  have he : (A q ^ 2).coeff 12 = (A q).coeff 6 ^ 2 :=
    Char2Degree19Crown.square_coeff_even (A q) 6
  rw [A_row6] at he
  exact he

theorem squareA_row13 (q : Vector R) : (A q ^ 2).coeff 13 = 0 :=
  Char2Degree19Crown.square_coeff_odd (A q) 6

theorem squareA_row14 (q : Vector R) : (A q ^ 2).coeff 14 = 1 := by
  have he : (A q ^ 2).coeff 14 = (A q).coeff 7 ^ 2 :=
    Char2Degree19Crown.square_coeff_even (A q) 7
  rw [monic_row (A_monic q), one_pow] at he
  exact he

theorem squareA_row15 (q : Vector R) : (A q ^ 2).coeff 15 = 0 :=
  Char2Degree19Crown.square_coeff_odd (A q) 7

theorem squareA_row16 (q : Vector R) : (A q ^ 2).coeff 16 = 0 := by
  have hA8 : (A q).coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt
    ((A_monic q).natDegree_eq ▸ (by omega : 7 < 8))
  have he : (A q ^ 2).coeff 16 = (A q).coeff 8 ^ 2 :=
    Char2Degree19Crown.square_coeff_even (A q) 8
  rw [hA8, zero_pow (by omega : 2 ≠ 0)] at he
  exact he

theorem outputQ_row16 (q : Vector R) : (outputQ q).coeff 16 = q 1 := by
  have hAS : (A q * S6 q).coeff 16 = 0 := coeff_eq_zero_of_natDegree_lt ((AS6_monic q).natDegree_eq ▸ (by omega : 13 < 16))
  have hb := squareB_row q 13
  simp only [Nat.reduceAdd] at hb
  rw [outputQ_coeff_high q 16 (by omega), high, coeff_add, hAS, add_zero,
    hb, squareA_row13, squareA_row14, squareA_row15, squareA_row16]
  simp only [zero_mul, one_mul, add_zero, zero_add]

theorem outputQ_row15 (q : Vector R) : (outputQ q).coeff 15 = (q 1 + 1) ^ 2 + (q 2 + 1) := by
  have hAS : (A q * S6 q).coeff 15 = 0 := coeff_eq_zero_of_natDegree_lt ((AS6_monic q).natDegree_eq ▸ (by omega : 13 < 15))
  have hb := squareB_row q 12
  simp only [Nat.reduceAdd] at hb
  rw [outputQ_coeff_high q 15 (by omega), high, coeff_add, hAS, add_zero,
    hb, squareA_row12, squareA_row13, squareA_row14, squareA_row15]
  simp only [zero_mul, one_mul, add_zero]

theorem outputQ_row13 (q : Vector R) :
    (outputQ q).coeff 13 = ((q 0 + q 2) + (q 1 + q 3)) ^ 2 +
      (q 1 + 1) ^ 2 * (q 2 + 1) + 1 := by
  have hb := squareB_row q 10
  simp only [Nat.reduceAdd] at hb
  rw [outputQ_coeff_high q 13 (by omega), high, coeff_add, monic_row (AS6_monic q),
    hb, squareA_row10, squareA_row11, squareA_row12, squareA_row13]
  simp only [zero_mul, add_zero]

end FastPoly.Char2Degree17HighSignature
