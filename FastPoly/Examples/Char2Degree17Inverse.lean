import FastPoly.Examples.Char2Degree17Rows
import FastPoly.Examples.Char2Degree17Q5Pivot
import FastPoly.Examples.Char2PivotUpdates

/-! The existing degree17 decoder: explicit prefix back-substitution with
two square inverses, one fourth-power inverse, and unit pivots elsewhere.
Both compositions include the supplied original-key coordinate inverse. -/
namespace FastPoly.Char2Degree17Inverse

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
  Char2Degree17TriangularCoordinates Char2Degree17TerminalFrame
  Char2Degree17TerminalPivots Char2Degree17LeadingInverse
  Char2Degree17Q0Pivot Char2Degree17EPivot Char2Degree17Q6Pivot
  Char2Degree17Q5Pivot Char2Degree17Rows

set_option maxHeartbeats 20000
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

/-- The supplied two square pivots and single fourth-power pivot. -/
def depth (i : Fin 17) : ℕ :=
  match i.val with
  | 2 => 1
  | 7 => 1
  | 8 => 2
  | _ => 0

noncomputable def scalarPivot (i : Fin 17) : F ≃ F :=
  Char2Certificate.frobeniusPivot (depth i)

theorem scalarPivot_apply (i : Fin 17) (x : F) :
    scalarPivot i x = x ^ (2 ^ depth i) := rfl

theorem scalarPivot_zero (i : Fin 17) : scalarPivot (F := F) i 0 = 0 :=
  (iterateFrobeniusEquiv F 2 (depth i)).map_zero

theorem scalarPivot_add (i : Fin 17) (x y : F) :
    scalarPivot i (x + y) = scalarPivot i x + scalarPivot i y :=
  (iterateFrobeniusEquiv F 2 (depth i)).map_add x y

private theorem fourth_add (x y : F) : (x + y) ^ 4 = x ^ 4 + y ^ 4 :=
  (iterateFrobeniusEquiv F 2 2).map_add x y

theorem shift_eq_update (q : Vector F) (i : Fin 17) (value : F) :
    shift q i (q i + value) = Function.update q i value := by
  rw [shift, CharTwo.add_cancel_left]

theorem shift_pivot (z : Vector F) (i : Fin 17) (δ : F) :
    rows (shift z i δ) i = rows z i + scalarPivot i δ := by
  change (outputZ (shift z i δ)).coeff (row i).val =
    (outputZ z).coeff (row i).val + scalarPivot i δ
  rw [scalarPivot_apply]
  fin_cases i
  · change (outputZ (shift z 0 δ)).coeff 16 = (outputZ z).coeff 16 + δ ^ 1
    rw [pow_one, outputZ_row16, outputZ_row16, shift_self]
  · change (outputZ (shift z 1 δ)).coeff 15 = (outputZ z).coeff 15 + δ ^ 1
    rw [pow_one, outputZ_row15, outputZ_row15]
    simp only [shift, Function.update, Fin.reduceEq, dite_true, dite_false]
    exact add_right_comm _ _ _
  · change (outputZ (shift z 2 δ)).coeff 13 = (outputZ z).coeff 13 + δ ^ 2
    rw [outputZ_row13, outputZ_row13]
    simp only [shift, Function.update, Fin.reduceEq, dite_true, dite_false]
    rw [CharTwo.add_sq, add_right_comm]
  · change (outputZ (shift z 3 δ)).coeff 14 = (outputZ z).coeff 14 + δ ^ 1
    rw [pow_one, outputZ_row14, outputZ_row14]
    simp only [shift, Function.update, Fin.reduceEq, dite_true, dite_false]
    exact add_right_comm _ _ _
  · change (outputZ (shift z 4 δ)).coeff 12 = (outputZ z).coeff 12 + δ ^ 1
    rw [pow_one, outputZ_row12, outputZ_row12]
    simp only [shift, Function.update, Fin.reduceEq, dite_true, dite_false]
    exact add_right_comm _ _ _
  · change (outputZ (shift z 5 δ)).coeff 11 = (outputZ z).coeff 11 + δ ^ 1
    rw [pow_one, outputZ_row11, outputZ_row11]
    simp only [shift, Function.update, Fin.reduceEq, dite_true, dite_false]
    exact add_right_comm _ _ _
  · change (outputZ (shift z 6 δ)).coeff 10 = (outputZ z).coeff 10 + δ ^ 1
    rw [pow_one, outputZ_row10, outputZ_row10, shift_self]
  · change (outputZ (shift z 7 δ)).coeff 9 = (outputZ z).coeff 9 + δ ^ 2
    rw [outputZ_row9, outputZ_row9]
    simp only [shift, Function.update, Fin.reduceEq, dite_true, dite_false]
    rw [CharTwo.add_sq, add_right_comm]
  · change (outputZ (shift z 8 δ)).coeff 8 = (outputZ z).coeff 8 + δ ^ 4
    rw [outputZ_row8, outputZ_row8]
    simp only [shift, Function.update, Fin.reduceEq, dite_true, dite_false]
    rw [fourth_add, add_right_comm]
  · change (outputZ (shift z 9 δ)).coeff 7 = (outputZ z).coeff 7 + δ ^ 1
    rw [pow_one]
    exact (tail_unit z 9 δ (by omega) (by omega) (by omega)).row
  · change (outputZ (shift z 10 δ)).coeff 6 = (outputZ z).coeff 6 + δ ^ 1
    rw [pow_one]
    exact (tail_unit z 10 δ (by omega) (by omega) (by omega)).row
  · change (outputZ (shift z 11 δ)).coeff 5 = (outputZ z).coeff 5 + δ ^ 1
    rw [pow_one]
    exact (tail_unit z 11 δ (by omega) (by omega) (by omega)).row
  · change (outputZ (shift z 12 δ)).coeff 4 = (outputZ z).coeff 4 + δ ^ 1
    rw [pow_one]
    exact (tail_unit z 12 δ (by omega) (by omega) (by omega)).row
  · change (outputZ (shift z 13 δ)).coeff 3 = (outputZ z).coeff 3 + δ ^ 1
    rw [pow_one]
    exact (tail_unit z 13 δ (by omega) (by omega) (by omega)).row
  · change (outputZ (shift z 14 δ)).coeff 2 = (outputZ z).coeff 2 + δ ^ 1
    rw [pow_one]
    exact (tail_unit z 14 δ (by omega) (by omega) (by omega)).row
  · change (outputZ (shift z 15 δ)).coeff 1 = (outputZ z).coeff 1 + δ ^ 1
    rw [pow_one]
    exact (tail_unit z 15 δ (by omega) (by omega) (by omega)).row
  · change (outputZ (shift z 16 δ)).coeff 0 = (outputZ z).coeff 0 + δ ^ 1
    rw [pow_one]
    exact (tail_unit z 16 δ (by omega) (by omega) (by omega)).row

theorem shift_future (z : Vector F) (i j : Fin 17) (hij : i < j) (δ : F) :
    rows (shift z j δ) i = rows z i := by
  by_cases hi : 9 ≤ i.val
  · have hj : 6 ≤ j.val := by change i.val < j.val at hij; omega
    have h7 : j ≠ 7 := by intro he; subst j; change i.val < 7 at hij; omega
    have h8 : j ≠ 8 := by intro he; subst j; change i.val < 8 at hij; omega
    exact (tail_unit z j δ hj h7 h8).above _ (row_decreasing_after_four i j (by omega) hij)
  have hi9 : i.val < 9 := by omega
  change (outputZ (shift z j δ)).coeff (row i).val = (outputZ z).coeff (row i).val
  have hval : i.val < j.val := hij
  fin_cases i
  · exact headRows_shift_future z 0 j δ hval
  · exact headRows_shift_future z 1 j δ hval
  · exact headRows_shift_future z 2 j δ hval
  · exact headRows_shift_future z 3 j δ hval
  · exact row12_future z j δ hval
  · exact row11_future z j δ hval
  · exact row10_future z j δ hval
  · exact row9_future z j δ hval
  · exact row8_future z j δ hval
  · change (9 : ℕ) < 9 at hi9
    omega
  · change (10 : ℕ) < 9 at hi9
    omega
  · change (11 : ℕ) < 9 at hi9
    omega
  · change (12 : ℕ) < 9 at hi9
    omega
  · change (13 : ℕ) < 9 at hi9
    omega
  · change (14 : ℕ) < 9 at hi9
    omega
  · change (15 : ℕ) < 9 at hi9
    omega
  · change (16 : ℕ) < 9 at hi9
    omega

theorem futureInvariant : Char2UpdateTriangular.FutureInvariant (rows (R := F)) := by
  intro z i j hij value
  have h := shift_future z i j hij (z j + value)
  rw [shift_eq_update] at h
  exact h

theorem pivotUpdate : Char2PivotUpdates.PivotUpdate (rows (R := F)) scalarPivot := by
  intro z i value
  have h := shift_pivot z i (z i + value)
  rw [shift_eq_update, scalarPivot_add, ← add_assoc] at h
  exact h

/-- Recursive residual decoding using precisely the supplied scalar inverses. -/
noncomputable def decodeRows (c : Vector F) : Vector F :=
  Char2PivotUpdates.decode rows scalarPivot c

theorem decodeRows_eq (c : Vector F) (i : Fin 17) :
    decodeRows c i = (scalarPivot i).symm
      (c i + rows (Char2UpdateTriangular.knownPrefix i (decodeRows c)) i) :=
  Char2PivotUpdates.decode_eq _ _ c i

theorem decodeRows_encode (z : Vector F) : decodeRows (rows z) = z :=
  Char2PivotUpdates.decode_encode _ _ futureInvariant scalarPivot_zero pivotUpdate z

theorem encode_decodeRows (c : Vector F) : rows (decodeRows c) = c :=
  Char2PivotUpdates.encode_decode _ _ futureInvariant scalarPivot_zero pivotUpdate c

noncomputable def rowsEquiv : Vector F ≃ Vector F :=
  Char2PivotUpdates.equiv rows scalarPivot futureInvariant scalarPivot_zero pivotUpdate

noncomputable def normalizedCoefficientEquiv : Vector F ≃ Vector F :=
  rowsEquiv.trans reorderRows

theorem normalizedCoefficientEquiv_apply (z : Vector F) (i : Fin 17) :
    normalizedCoefficientEquiv z i = (outputZ z).coeff i.val := by
  change (outputZ z).coeff (row (inverseRow i)).val = _
  rw [row_inverseRow]

/-- The original raw-offset coefficient map, with an explicitly composed inverse. -/
noncomputable def coefficientEquiv : Vector F ≃ Vector F :=
  rawEquiv.trans normalizedCoefficientEquiv

theorem coefficientEquiv_symm_apply (c : Vector F) :
    coefficientEquiv.symm c = rawEquiv.symm (decodeRows (reorderRows.symm c)) := rfl

theorem decode_encode (a : Vector F) :
    rawEquiv.symm (decodeRows (reorderRows.symm (coefficientEquiv a))) = a := by
  rw [← coefficientEquiv_symm_apply, Equiv.symm_apply_apply]

theorem encode_decode (c : Vector F) :
    coefficientEquiv (rawEquiv.symm (decodeRows (reorderRows.symm c))) = c := by
  rw [← coefficientEquiv_symm_apply, Equiv.apply_symm_apply]

theorem outputZ_rawEquiv (a : Vector F) : outputZ (rawEquiv a) = output a := by
  change output (keys (qOfZ (zOfQ (coordinates a)))) = output a
  rw [qOfZ_zOfQ, keys_coordinates]

theorem coefficientEquiv_apply (a : Vector F) (i : Fin 17) :
    coefficientEquiv a i = (output a).coeff i.val := by
  change normalizedCoefficientEquiv (rawEquiv a) i = _
  rw [normalizedCoefficientEquiv_apply, outputZ_rawEquiv]

end FastPoly.Char2Degree17Inverse
