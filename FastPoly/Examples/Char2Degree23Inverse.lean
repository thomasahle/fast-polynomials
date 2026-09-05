import FastPoly.Examples.Char2Degree23FifteenKeys
import FastPoly.Examples.Char2Degree23SixteenKeys
import FastPoly.Examples.Char2Degree23EighteenKeys
import FastPoly.Examples.Char2Degree23TwentyKeys
import FastPoly.Examples.Char2Degree23TwentyOne
import FastPoly.Examples.Char2Degree23TerminalRows
import FastPoly.Examples.Char2Degree23RowUpdates
import FastPoly.Examples.Char2UpdateTriangular
import Mathlib.Tactic.FinCases

/-!
# Explicit two-sided inversion of the existing degree-23 circuit

Read descending coefficients, with row four replaced by row four plus row
three. Each step adds the target row to the named circuit at the recovered
prefix. The supplied unit columns prove both compositions. Undoing the
explicit key shear gives an inverse on the original raw offsets as well.
-/

namespace FastPoly.Char2Degree23Inverse

open Polynomial Char2Degree23HighKeys Char2Degree23Rows
  Char2Degree23RowUpdates Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- Dispatch the supplied ordinary unit-column certificates; no field values
are enumerated and no coefficient baseline is expanded. -/
theorem ordinary_unit (q : Fin 23 → R) (i : Fin 23) (d : R)
    (h18 : i ≠ 18) (h19 : i ≠ 19) :
    UnitDifference (Char2Degree23RowEight.output (rawKeys q))
      (Char2Degree23RowEight.output (rawKeys (increment q i d)))
      (22 - i.val) d := by
  fin_cases i
  · exact Char2Degree23HighKeys.increment0_unit q d
  · exact Char2Degree23HighKeys.increment1_unit q d
  · exact Char2Degree23HighKeys.increment2_unit q d
  · exact Char2Degree23HighKeys.increment3_unit q d
  · exact Char2Degree23HighKeys.increment4_unit q d
  · exact Char2Degree23HighKeys.increment5_unit q d
  · exact Char2Degree23HighKeys.increment6_unit q d
  · exact Char2Degree23HighKeys.increment7_unit q d
  · exact Char2Degree23MiddleKeys.increment8_unit q d
  · exact Char2Degree23MiddleKeys.increment9_unit q d
  · exact Char2Degree23MiddleKeys.increment10_unit q d
  · exact Char2Degree23MiddleKeys.increment11_unit q d
  · exact Char2Degree23MiddleKeys.increment12_unit q d
  · exact Char2Degree23MiddleKeys.increment13_unit q d
  · exact Char2Degree23LowKeys.increment14_unit q d
  · exact Char2Degree23FifteenKeys.increment15_unit q d
  · exact Char2Degree23SixteenKeys.increment16_unit q d
  · exact Char2Degree23LowKeys.increment17_unit q d
  · contradiction
  · contradiction
  · exact Char2Degree23TwentyKeys.increment20_unit q d
  · exact Char2Degree23TwentyOne.increment21_unit q d
  · exact Char2Degree23LowKeys.increment22_unit q d

/-- The actual output rows in the explicitly invertible sheared order. -/
noncomputable def rows (q : Fin 23 → R) : Fin 23 → R :=
  polynomialRows (Char2Degree23RowEight.output (rawKeys q))

theorem increment_pivot (q : Fin 23 → R) (i : Fin 23) (d : R) :
    rows (increment q i d) i = rows q i + d := by
  by_cases h18 : i = 18
  · subst i
    exact Char2Degree23EighteenKeys.increment18_adapted q d
  by_cases h19 : i = 19
  · subst i
    change polynomialRows _ 19 = polynomialRows _ 19 + d
    rw [polynomialRows_other _ 19 (by omega), polynomialRows_other _ 19 (by omega)]
    exact Char2Degree23TerminalRows.increment19_three q d
  exact regular_pivot h18 (ordinary_unit q i d h18 h19)

theorem increment_higher (q : Fin 23 → R) (i : Fin 23) (d : R)
    (j : Fin 23) (hj : j < i) : rows (increment q i d) j = rows q j := by
  by_cases h18 : i = 18
  · subst i
    have hne : j ≠ 18 := ne_of_lt hj
    change polynomialRows _ j = polynomialRows _ j
    rw [polynomialRows_other _ j hne, polynomialRows_other _ j hne]
    apply Char2Degree23EighteenKeys.increment18_higher
    change j.val < 18 at hj
    omega
  by_cases h19 : i = 19
  · subst i
    exact nineteen_higher (Char2Degree23TerminalRows.increment19_unit_four q d)
      (Char2Degree23TerminalRows.increment19_adapted q d) j hj
  exact regular_higher h19 (ordinary_unit q i d h18 h19) j hj

theorem increment_eq_update (q : Fin 23 → R) (i : Fin 23) (value : R) :
    increment q i (q i + value) = Function.update q i value := by
  rw [increment, CharTwo.add_cancel_left]

theorem futureInvariant : Char2UpdateTriangular.FutureInvariant (rows (R := R)) := by
  intro q i j hij value
  have h := increment_higher q j (q j + value) i hij
  rw [increment_eq_update] at h
  exact h

theorem unitPivot : Char2UpdateTriangular.UnitPivot (rows (R := R)) := by
  intro q i value
  have h := increment_pivot q i (q i + value)
  rw [increment_eq_update, ← add_assoc] at h
  exact h

/-- Literal recursive back-substitution at a named circuit prefix. -/
noncomputable def decodeRows (c : Fin 23 → R) : Fin 23 → R :=
  Char2UpdateTriangular.decode rows c

theorem decodeRows_eq (c : Fin 23 → R) (i : Fin 23) :
    decodeRows c i = c i +
      rows (Char2UpdateTriangular.knownPrefix i (decodeRows c)) i :=
  Char2UpdateTriangular.decode_eq _ c i

theorem decodeRows_encode (q : Fin 23 → R) : decodeRows (rows q) = q :=
  Char2UpdateTriangular.decode_encode _ futureInvariant unitPivot q

theorem encode_decodeRows (c : Fin 23 → R) : rows (decodeRows c) = c :=
  Char2UpdateTriangular.encode_decode _ futureInvariant unitPivot c

noncomputable def rowsEquiv : (Fin 23 → R) ≃ (Fin 23 → R) :=
  Char2UpdateTriangular.equiv rows futureInvariant unitPivot

/-- Undo the explicit coefficient-row shear after encoding. -/
noncomputable def normalizedCoefficientEquiv : (Fin 23 → R) ≃ (Fin 23 → R) :=
  rowsEquiv.trans rowEquiv.symm

theorem normalizedCoefficientEquiv_apply (q : Fin 23 → R) (i : Fin 23) :
    normalizedCoefficientEquiv q i =
      (Char2Degree23RowEight.output (rawKeys q)).coeff i.val :=
  congrFun (recover_coefficients _) i

/-- On raw keys, first invert the supplied key change, then read coefficients. -/
noncomputable def coefficientEquiv : (Fin 23 → R) ≃ (Fin 23 → R) :=
  Char2Degree23Keys.keyEquiv.symm.trans normalizedCoefficientEquiv

theorem coefficientEquiv_symm_apply (c : Fin 23 → R) :
    coefficientEquiv.symm c =
      Char2Degree23Keys.keyEquiv (decodeRows (rowEquiv c)) := rfl

theorem decode_encode (a : Fin 23 → R) :
    Char2Degree23Keys.keyEquiv (decodeRows (rowEquiv (coefficientEquiv a))) = a := by
  rw [← coefficientEquiv_symm_apply, Equiv.symm_apply_apply]

theorem encode_decode (c : Fin 23 → R) :
    coefficientEquiv (Char2Degree23Keys.keyEquiv (decodeRows (rowEquiv c))) = c := by
  rw [← coefficientEquiv_symm_apply, Equiv.apply_symm_apply]

theorem rawKeys_inverse (a : Fin 23 → R) :
    rawKeys (Char2Degree23Keys.keyEquiv.symm a) = Char2Degree23Keys.raw a := by
  unfold rawKeys
  rw [Equiv.apply_symm_apply]

/-- Public connection to the literal circuit on its original raw offsets. -/
theorem coefficientEquiv_apply (a : Fin 23 → R) (i : Fin 23) :
    coefficientEquiv a i =
      (Char2Degree23RowEight.output (Char2Degree23Keys.raw a)).coeff i.val := by
  change normalizedCoefficientEquiv (Char2Degree23Keys.keyEquiv.symm a) i = _
  rw [normalizedCoefficientEquiv_apply, rawKeys_inverse]

end FastPoly.Char2Degree23Inverse

