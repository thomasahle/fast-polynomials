import FastPoly.Examples.Char2Degree17Q6Pivot

/-! The supplied degree17 row permutation, its inverse, and the exact row-ten
coordinate. The final polynomial remains a named gate expression. -/
namespace FastPoly.Char2Degree17Rows

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
  Char2Degree17TerminalFrame Char2Degree17TerminalPivots
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def row (i : Fin 17) : Fin 17 :=
  match i.val with
  | 0 => 16
  | 1 => 15
  | 2 => 13
  | 3 => 14
  | 4 => 12
  | 5 => 11
  | 6 => 10
  | 7 => 9
  | 8 => 8
  | 9 => 7
  | 10 => 6
  | 11 => 5
  | 12 => 4
  | 13 => 3
  | 14 => 2
  | 15 => 1
  | _ => 0

def inverseRow (i : Fin 17) : Fin 17 :=
  match i.val with
  | 0 => 16
  | 1 => 15
  | 2 => 14
  | 3 => 13
  | 4 => 12
  | 5 => 11
  | 6 => 10
  | 7 => 9
  | 8 => 8
  | 9 => 7
  | 10 => 6
  | 11 => 5
  | 12 => 4
  | 13 => 2
  | 14 => 3
  | 15 => 1
  | _ => 0

theorem row_inverseRow (i : Fin 17) : row (inverseRow i) = i := by
  fin_cases i <;> rfl

theorem inverseRow_row (i : Fin 17) : inverseRow (row i) = i := by
  fin_cases i <;> rfl

/-- An explicitly inverted permutation, not an inferred bijection. -/
def reorderRows : (Fin 17 → R) ≃ (Fin 17 → R) where
  toFun c i := c (inverseRow i)
  invFun c i := c (row i)
  left_inv c := by funext i; exact congrArg c (inverseRow_row i)
  right_inv c := by funext i; exact congrArg c (row_inverseRow i)

noncomputable def rows (z : Vector R) (i : Fin 17) : R :=
  (outputZ z).coeff (row i).val

theorem row_after_four (i : Fin 17) (hi : 4 ≤ i.val) :
    (row i).val = 16 - i.val := by
  fin_cases i <;> first | rfl | (change 4 ≤ (0 : ℕ) at hi; omega) |
    (change 4 ≤ (1 : ℕ) at hi; omega) |
    (change 4 ≤ (2 : ℕ) at hi; omega) |
    (change 4 ≤ (3 : ℕ) at hi; omega)

theorem row_decreasing_after_four (i j : Fin 17) (hi : 4 ≤ i.val) (hij : i < j) :
    (row j).val < (row i).val := by
  have hj : 4 ≤ j.val := le_trans hi (Nat.le_of_lt hij)
  rw [row_after_four i hi, row_after_four j hj]
  have hjlt := j.isLt
  change i.val < j.val at hij
  omega

/-- The normalized last gate reads row ten before either Frobenius low row. -/
theorem outputQ_row10 (q : Vector R) : (outputQ q).coeff 10 = q 14 := by
  have hj : IsMonicOfDegree (dj q) 3 := by
    simpa only [j_keys] using j_monic (keys q)
  have hl : IsMonicOfDegree (dell q) 7 := by
    simpa only [ell_keys] using ell_monic (keys q)
  have hzj : (dj q).coeff 10 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hj.natDegree_eq.trans_lt (by omega))
  have hzl : (dell q).coeff 10 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hl.natDegree_eq.trans_lt (by omega))
  have hw : (dw q).coeff 10 = q 14 := congrArg Prod.fst (w_rows q)
  rw [Char2Degree17Q9Pivot.outputQ_as_wires, coeff_add, coeff_add, coeff_add,
    hzj, hzl, hw]
  simp only [coeff_C, Nat.reduceEqDiff, ite_false, zero_add, add_zero]

theorem outputZ_row10 (z : Vector R) : (outputZ z).coeff 10 = z 6 :=
  outputQ_row10 (Char2Degree17TriangularCoordinates.qOfZ z)

theorem row10_future (z : Vector R) (j : Fin 17) (δ : R) (hj : 6 < j.val) :
    (outputZ (shift z j δ)).coeff 10 = (outputZ z).coeff 10 := by
  rw [outputZ_row10, outputZ_row10]
  exact shift_other z j 6 δ (by intro he; have hh := congrArg Fin.val he; omega)

theorem tail_unit (z : Vector R) (i : Fin 17) (δ : R)
    (hi : 6 ≤ i.val) (h7 : i ≠ 7) (h8 : i ≠ 8) :
    TopChange (outputZ z) (outputZ (shift z i δ)) (row i).val δ := by
  fin_cases i
  · change 6 ≤ (0 : ℕ) at hi
    omega
  · change 6 ≤ (1 : ℕ) at hi
    omega
  · change 6 ≤ (2 : ℕ) at hi
    omega
  · change 6 ≤ (3 : ℕ) at hi
    omega
  · change 6 ≤ (4 : ℕ) at hi
    omega
  · change 6 ≤ (5 : ℕ) at hi
    omega
  · exact outputZ_change z 4 δ
  · contradiction
  · contradiction
  · exact outputZ_change z 5 δ
  · exact Char2Degree17Q8Pivot.outputZ_change10 z δ
  · exact Char2Degree17Q9Pivot.outputZ_change11 z δ
  · exact outputZ_change z 2 δ
  · exact outputZ_change z 3 δ
  · exact outputZ_change z 0 δ
  · exact outputZ_change z 1 δ
  · exact outputZ_change z 6 δ

end FastPoly.Char2Degree17Rows

