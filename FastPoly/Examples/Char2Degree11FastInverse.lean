import FastPoly.Examples.Char2Degree11FastUnits
import FastPoly.Examples.Char2UpdateTriangular
import Mathlib.Tactic.FinCases

/-! The explicit prefix-evaluation inverse for the eleven supplied coefficient
rows. Both compositions are checked; finite cases select the eleven symbolic
unit formulas, never field values or candidate keys. -/

namespace FastPoly.Char2Degree11Fast

set_option maxHeartbeats 20000

open Polynomial Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- A supplied unit slope for every normalized coordinate, with every later
coefficient preserved.  Case splitting here selects eleven symbolic formulas,
not field values or candidate inverse keys. -/
theorem increment_unit (q : Keys R) (i : Fin 11) (delta : R) :
    UnitDifference (output q) (output (increment q i delta)) (10 - i.val) delta := by
  fin_cases i
  · exact increment0_unit q delta
  · exact increment1_unit q delta
  · exact increment2_unit q delta
  · exact increment3_unit q delta
  · exact increment4_unit q delta
  · exact increment5_unit q delta
  · exact increment6_unit q delta
  · exact increment7_unit q delta
  · exact increment8_unit q delta
  · exact increment9_unit q delta
  · exact increment10_unit q delta

noncomputable def coefficientRows (q : Keys R) (i : Fin 11) : R :=
  (output q).coeff (10 - i.val)

theorem update_unit (q : Keys R) (i : Fin 11) (value : R) :
    UnitDifference (output q) (output (Function.update q i value)) (10 - i.val) (q i + value) := by
  have he : increment q i (q i + value) = Function.update q i value := by
    rw [increment, CharTwo.add_cancel_left]
  rw [← he]
  exact increment_unit q i (q i + value)

theorem futureInvariant : Char2UpdateTriangular.FutureInvariant (coefficientRows (R := R)) := by
  intro q i j hij value
  have hrow : 10 - j.val < 10 - i.val := by
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val at hij
    omega
  exact (update_unit q j value).higher _ hrow

theorem unitPivot : Char2UpdateTriangular.UnitPivot (coefficientRows (R := R)) := by
  intro q i value
  exact ((update_unit q i value).row).trans (add_assoc _ _ _).symm

/-- Actual descending back-substitution, evaluating the named circuit only at
the already recovered prefix. -/
noncomputable def decode (c : Keys R) : Keys R :=
  Char2UpdateTriangular.decode coefficientRows c

theorem decode_encode (q : Keys R) : decode (coefficientRows q) = q :=
  Char2UpdateTriangular.decode_encode _ futureInvariant unitPivot q

theorem encode_decode (c : Keys R) : coefficientRows (decode c) = c :=
  Char2UpdateTriangular.encode_decode _ futureInvariant unitPivot c

noncomputable def coefficientEquiv : Keys R ≃ Keys R :=
  Char2UpdateTriangular.equiv coefficientRows futureInvariant unitPivot

/-- Reverse the displayed descending rows into the standard coefficient order. -/
def reverseRows : Keys R ≃ Keys R where
  toFun c i := c i.rev
  invFun c i := c i.rev
  left_inv c := by
    funext i
    exact congrArg c (Fin.rev_rev i)
  right_inv c := by
    funext i
    exact congrArg c (Fin.rev_rev i)

noncomputable def ascendingEquiv : Keys R ≃ Keys R :=
  coefficientEquiv.trans reverseRows

theorem output_coefficient (q : Keys R) (i : Fin 11) :
    (output q).coeff i.val = ascendingEquiv q i := by
  change (output q).coeff i.val = (output q).coeff (10 - i.rev.val)
  congr 1
  have hi := i.isLt
  rw [Fin.val_rev]
  omega

end FastPoly.Char2Degree11Fast

