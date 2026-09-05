import FastPoly.Examples.Char2Degree13FastLeading
import FastPoly.Examples.Char2Degree13FastTailPivots
import FastPoly.Examples.Char2UpdateTriangular
import Mathlib.Tactic.FinCases

/-! Explicit prefix inversion in the supplied nonmonotone coefficient order.
Finite cases below only select thirteen symbolic coordinate formulas or check
the fixed row permutation. There is no enumeration of field values or keys. -/

namespace FastPoly.Char2Degree13Fast

set_option maxHeartbeats 20000

open Polynomial Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- The active decoder reads these rows, in this exact order. -/
def row (i : Fin 13) : Fin 13 :=
  match i.val with
  | 0 => 12 | 1 => 11 | 2 => 10 | 3 => 7 | 4 => 6 | 5 => 9 | 6 => 8
  | 7 => 5 | 8 => 4 | 9 => 3 | 10 => 1 | 11 => 2 | _ => 0

/-- An explicitly supplied inverse for the fixed row permutation. -/
def inverseRow (i : Fin 13) : Fin 13 :=
  match i.val with
  | 0 => 12 | 1 => 10 | 2 => 11 | 3 => 9 | 4 => 8 | 5 => 7 | 6 => 4
  | 7 => 3 | 8 => 6 | 9 => 5 | 10 => 2 | 11 => 1 | _ => 0

theorem row_inverseRow (i : Fin 13) : row (inverseRow i) = i := by
  fin_cases i <;> rfl

theorem inverseRow_row (i : Fin 13) : inverseRow (row i) = i := by
  fin_cases i <;> rfl

noncomputable def coefficientRows (q : Keys R) (i : Fin 13) : R :=
  (output q).coeff (row i).val

theorem increment_pivot (q : Keys R) (i : Fin 13) (delta : R) :
    (output (increment q i delta)).coeff (row i).val =
      (output q).coeff (row i).val + delta := by
  fin_cases i
  · exact (increment0_unit q delta).row
  · exact (increment1_unit q delta).row
  · exact (increment2_unit q delta).row
  · exact increment3_pivot q delta
  · exact increment4_pivot q delta
  · exact increment5_pivot q delta
  · exact increment6_pivot q delta
  · exact increment7_pivot q delta
  · exact increment8_pivot q delta
  · exact increment9_pivot q delta
  · exact increment10_pivot q delta
  · exact increment11_pivot q delta
  · exact increment12_pivot q delta

private theorem rows_before1 (i : Fin 13) (hi : i.val < 1) :
    11 < (row i).val := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before2 (i : Fin 13) (hi : i.val < 2) :
    10 < (row i).val := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before3 (i : Fin 13) (hi : i.val < 3) :
    9 < (row i).val := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before4 (i : Fin 13) (hi : i.val < 4) :
    9 < (row i).val ∨ (row i).val = 7 := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before5 (i : Fin 13) (hi : i.val < 5) :
    9 < (row i).val ∨ (row i).val = 7 ∨ (row i).val = 6 := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before6 (i : Fin 13) (hi : i.val < 6) :
    8 < (row i).val ∨ (row i).val = 7 ∨ (row i).val = 6 := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before7 (i : Fin 13) (hi : i.val < 7) :
    5 < (row i).val := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before8 (i : Fin 13) (hi : i.val < 8) :
    4 < (row i).val := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before9 (i : Fin 13) (hi : i.val < 9) :
    3 < (row i).val := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before10 (i : Fin 13) (hi : i.val < 10) :
    1 < (row i).val := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before11 (i : Fin 13) (hi : i.val < 11) :
    2 < (row i).val ∨ (row i).val = 1 := by
  fin_cases i <;> norm_num only [row] at * <;> omega

private theorem rows_before12 (i : Fin 13) (hi : i.val < 12) :
    0 < (row i).val := by
  fin_cases i <;> norm_num only [row] at * <;> omega

/-- All earlier read rows are preserved by the displayed later-coordinate
change. Exceptional rows use their explicit zero-window certificates. -/
theorem increment_future (q : Keys R) (i j : Fin 13) (hij : i < j) (delta : R) :
    (output (increment q j delta)).coeff (row i).val = (output q).coeff (row i).val := by
  have hi : i.val < j.val := hij
  fin_cases j
  · change i.val < 0 at hi
    omega
  · exact (increment1_unit q delta).higher _ (rows_before1 i hi)
  · exact (increment2_unit q delta).higher _ (rows_before2 i hi)
  · exact increment3_above q delta _ (rows_before3 i hi)
  · rcases rows_before4 i hi with h | h
    · exact increment4_above q delta _ h
    · rw [h]
      exact increment4_preserves7 q delta
  · rcases rows_before5 i hi with h | h | h
    · exact increment5_above q delta _ h
    · rw [h]
      exact increment5_preserves7 q delta
    · rw [h]
      exact increment5_preserves6 q delta
  · rcases rows_before6 i hi with h | h | h
    · exact increment6_above q delta _ h
    · rw [h]
      exact increment6_preserves7 q delta
    · rw [h]
      exact increment6_preserves6 q delta
  · exact increment7_above q delta _ (rows_before7 i hi)
  · exact increment8_above q delta _ (rows_before8 i hi)
  · exact increment9_above q delta _ (rows_before9 i hi)
  · exact increment10_above q delta _ (rows_before10 i hi)
  · rcases rows_before11 i hi with h | h
    · exact increment11_above q delta _ h
    · rw [h]
      exact increment11_preserves1 q delta
  · exact increment12_above q delta _ (rows_before12 i hi)

theorem increment_eq_update (q : Keys R) (i : Fin 13) (value : R) :
    increment q i (q i + value) = Function.update q i value := by
  rw [increment, CharTwo.add_cancel_left]

theorem futureInvariant : Char2UpdateTriangular.FutureInvariant (coefficientRows (R := R)) := by
  intro q i j hij value
  change (output (Function.update q j value)).coeff (row i).val = (output q).coeff (row i).val
  rw [← increment_eq_update q j value]
  exact increment_future q i j hij (q j + value)

theorem unitPivot : Char2UpdateTriangular.UnitPivot (coefficientRows (R := R)) := by
  intro q i value
  change (output (Function.update q i value)).coeff (row i).val =
    (output q).coeff (row i).val + q i + value
  rw [← increment_eq_update q i value]
  exact (increment_pivot q i (q i + value)).trans (add_assoc _ _ _).symm

/-- Literal back-substitution, evaluating only the already recovered prefix. -/
noncomputable def decode (c : Keys R) : Keys R :=
  Char2UpdateTriangular.decode coefficientRows c

theorem decode_encode (q : Keys R) : decode (coefficientRows q) = q :=
  Char2UpdateTriangular.decode_encode _ futureInvariant unitPivot q

theorem encode_decode (c : Keys R) : coefficientRows (decode c) = c :=
  Char2UpdateTriangular.encode_decode _ futureInvariant unitPivot c

noncomputable def coefficientEquiv : Keys R ≃ Keys R :=
  Char2UpdateTriangular.equiv coefficientRows futureInvariant unitPivot

/-- Reorder the supplied rows into ordinary ascending coefficient order. -/
def reorderRows : Keys R ≃ Keys R where
  toFun c i := c (inverseRow i)
  invFun c i := c (row i)
  left_inv c := by
    funext i
    exact congrArg c (inverseRow_row i)
  right_inv c := by
    funext i
    exact congrArg c (row_inverseRow i)

noncomputable def ascendingEquiv : Keys R ≃ Keys R :=
  coefficientEquiv.trans reorderRows

theorem output_coefficient (q : Keys R) (i : Fin 13) :
    (output q).coeff i.val = ascendingEquiv q i := by
  change (output q).coeff i.val = (output q).coeff (row (inverseRow i)).val
  rw [row_inverseRow]

end FastPoly.Char2Degree13Fast
