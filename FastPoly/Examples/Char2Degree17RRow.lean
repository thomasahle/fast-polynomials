import FastPoly.Examples.Char2Degree17HighSignature

/-!
# The explicit R pivot in degree seventeen's row fourteen

The constant term of B is recovered from row seven of the already checked
sextic identity. That row is zero, leaving one unit pivot for B's constant.
Only named coefficients of A, u, and v are used; v is not expanded.
-/

namespace FastPoly.Char2Degree17RRow

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TerminalFrame Char2Degree17TerminalPivots
open Char2Degree17Q8Pivot Char2Degree17HighFrame Char2Degree17HighSignature

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem u_row4 (q : Vector R) : (du q).coeff 4 = q 5 := congrArg Prod.fst (u_rows q)
theorem v_row7 (q : Vector R) : (dv q).coeff 7 = q 7 := congrArg Prod.fst (v_rows q)

theorem A_row4 (q : Vector R) : (A q).coeff 4 = q 5 := by
  have h14 : (1 : ℕ) ≠ 4 := by omega
  simp only [A, coeff_add, coeff_X, h14, ite_false, zero_add, u_row4]

theorem u_row7 (q : Vector R) : (du q).coeff 7 = 1 := by
  have hu : IsMonicOfDegree (du q) 7 := by simpa only [u_keys] using u_monic (keys q)
  exact monic_row hu

theorem AB_row7 (q : Vector R) : (A q * B q).coeff 7 = 1 + q 7 := by
  have hs : (S6 q).coeff 7 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((S6_monic q).natDegree_eq ▸ (by omega : 6 < 7))
  have he := congrArg (fun p : R[X] => p.coeff 7) (sextic_identity q)
  change (A q * B q + (du q + dv q)).coeff 7 = (S6 q).coeff 7 at he
  rw [coeff_add, coeff_add, u_row7, v_row7, hs] at he
  exact CharTwo.add_eq_zero.mp he

/-- The row-seven unit solve, with all other entries already known. -/
theorem B_row0 (q : Vector R) :
    (B q).coeff 0 = (1 + q 7) +
      (q 5 + ((q 0 + q 2) + (q 1 + q 3)) * q 1 + (q 1 + 1) * (q 2 + 1)) := by
  have he : (A q * B q).coeff 7 =
      (A q).coeff 4 + (A q).coeff 5 * q 1 +
        (A q).coeff 6 * (q 2 + 1) + (A q).coeff 7 * (B q).coeff 0 := by
    conv_lhs => rw [B_form]
    exact cubic_product_row (A q) _ _ _ 4
  rw [AB_row7, A_row4, A_row5, A_row6, monic_row (A_monic q), one_mul] at he
  rw [he, Char2Decoder.cancel_tail]

theorem outputQ_row14 (q : Vector R) :
    (outputQ q).coeff 14 = (1 + q 7) +
      (q 5 + ((q 0 + q 2) + (q 1 + q 3)) * q 1 + (q 1 + 1) * (q 2 + 1)) +
        (q 1 + 1) ^ 2 * q 1 := by
  have hAS : (A q * S6 q).coeff 14 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((AS6_monic q).natDegree_eq ▸ (by omega : 13 < 14))
  have he := squareB_row q 11
  simp only [Nat.reduceAdd] at he
  rw [outputQ_coeff_high q 14 (by omega), high, coeff_add, hAS, add_zero,
    he, squareA_row11, squareA_row12, squareA_row13, squareA_row14]
  simp only [zero_add, zero_mul, add_zero, one_mul]
  rw [B_row0, add_comm]

end FastPoly.Char2Degree17RRow
