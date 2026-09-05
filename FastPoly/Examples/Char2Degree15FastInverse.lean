import FastPoly.Examples.Char2Degree15FastTail
import FastPoly.Examples.Char2Degree15FastLeading
import FastPoly.Examples.Char2UpdateTriangular
import Mathlib.Tactic.FinCases

/-! The literal prefix-evaluation inverse for all fifteen coefficient rows. -/

namespace FastPoly.Char2Degree15Fast

set_option maxHeartbeats 20000

open Polynomial Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem increment0_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 0 delta)) 14 delta := by
  have ht : t (increment q 0 delta) = t q + C delta * (z q + C (q 3)) := by
    change (X + C (q 0 + delta)) * (z q + C (q 3)) = _
    rw [map_add, ← add_assoc, add_mul]
    rfl
  apply unit_from_main_change q (increment q 0 delta) (z q + C (q 3)) 0 4 delta
    (by omega) (by omega) ((z_monic q).add_right (const_lt _ 4 (by omega)))
    (by rw [natDegree_zero]; omega) ?_ rfl ?_ rfl rfl
  · rw [mainWire, ht]
    change (t q + C delta * (z q + C (q 3))) + C (q 7) = _
    unfold mainWire
    ac_rfl
  · rw [add_zero]
    rfl

theorem z_increment1 (q : Keys R) (delta : R) :
    z (increment q 1 delta) = z q + C delta * (y + C (q 2)) := by
  change (y + C (q 2)) * (X + y + C ((q 1 + delta) + q 2)) = _
  rw [add_right_comm (q 1) delta, map_add, ← add_assoc, mul_add,
    mul_comm _ (C delta)]
  rfl

theorem increment1_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 1 delta)) 13 delta := by
  have hs2 : IsMonicOfDegree (y + C (q 2)) 2 :=
    y_monic.add_right (const_lt _ 2 (by omega))
  have ht : t (increment q 1 delta) =
      t q + C delta * ((X + C (q 0)) * (y + C (q 2))) := by
    change (X + C (q 0)) * (z (increment q 1 delta) + C (q 3)) = _
    rw [z_increment1, add_right_comm (z q), mul_add, mul_left_comm _ (C delta)]
    rfl
  have he : (C delta * (y + C (q 2))).natDegree < 3 :=
    (mul_bound (natDegree_C _).le hs2.natDegree_eq.le).trans_lt (by omega)
  apply unit_from_main_change q (increment q 1 delta)
    ((X + C (q 0)) * (y + C (q 2))) (C delta * (y + C (q 2))) 3 delta
    (by omega) (by omega) ((isMonicOfDegree_X_add_one (q 0)).mul hs2)
    he ?_ rfl ?_ rfl rfl
  · rw [mainWire, ht]
    change (t q + C delta * ((X + C (q 0)) * (y + C (q 2)))) + C (q 7) = _
    unfold mainWire
    ac_rfl
  · rw [gamma, z_increment1]
    change (z q + C delta * (y + C (q 2))) + C (q 5 + q 7) = _
    unfold gamma
    ac_rfl

theorem z_increment2 (q : Keys R) (delta : R) :
    z (increment q 2 delta) = z q + C delta * (X + C (q 1 + delta)) := by
  change (y + C (q 2 + delta)) * (X + y + C (q 1 + (q 2 + delta))) = _
  have hl : y + C (q 2 + delta) = (y + C (q 2)) + C delta := by
    rw [map_add, ← add_assoc]
  have hr : X + y + C (q 1 + (q 2 + delta)) =
      (X + y + C (q 1 + q 2)) + C delta := by
    rw [← add_assoc (q 1), map_add, ← add_assoc]
  have hs : (y + C (q 2)) + (X + y + C (q 1 + q 2)) = X + C (q 1) := by
    simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero, add_zero, zero_add]
  rw [hl, hr, both_factors, hs]
  change z q + C delta * (X + C (q 1)) + C delta ^ 2 = _
  simp only [map_add, mul_add, pow_two, add_assoc]

theorem increment2_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 2 delta)) 12 delta := by
  have hs1 := isMonicOfDegree_X_add_one (q 1 + delta)
  have ht : t (increment q 2 delta) =
      t q + C delta * ((X + C (q 0)) * (X + C (q 1 + delta))) := by
    change (X + C (q 0)) * (z (increment q 2 delta) + C (q 3)) = _
    rw [z_increment2, add_right_comm (z q), mul_add, mul_left_comm _ (C delta)]
    rfl
  have he : (C delta * (X + C (q 1 + delta))).natDegree < 2 :=
    (mul_bound (natDegree_C _).le hs1.natDegree_eq.le).trans_lt (by omega)
  apply unit_from_main_change q (increment q 2 delta)
    ((X + C (q 0)) * (X + C (q 1 + delta))) (C delta * (X + C (q 1 + delta))) 2 delta
    (by omega) (by omega) ((isMonicOfDegree_X_add_one (q 0)).mul hs1)
    he ?_ rfl ?_ rfl rfl
  · rw [mainWire, ht]
    change (t q + C delta * ((X + C (q 0)) * (X + C (q 1 + delta)))) + C (q 7) = _
    unfold mainWire
    ac_rfl
  · rw [gamma, z_increment2]
    change (z q + C delta * (X + C (q 1 + delta))) + C (q 5 + q 7) = _
    unfold gamma
    ac_rfl

theorem increment3_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 3 delta)) 11 delta := by
  have ht : t (increment q 3 delta) = t q + C delta * (X + C (q 0)) := by
    change (X + C (q 0)) * (z q + C (q 3 + delta)) = _
    rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]
    rfl
  apply unit_from_main_change q (increment q 3 delta) (X + C (q 0)) 0 1 delta
    (by omega) (by omega) (isMonicOfDegree_X_add_one (q 0))
    (by rw [natDegree_zero]; omega) ?_ rfl ?_ rfl rfl
  · rw [mainWire, ht]
    change (t q + C delta * (X + C (q 0))) + C (q 7) = _
    unfold mainWire
    ac_rfl
  · rw [add_zero]
    rfl

/-- A supplied unit slope for every normalized coordinate, with every later
coefficient preserved.  Case splitting here selects fifteen symbolic formulas,
not field values or candidate inverse keys. -/
theorem increment_unit (q : Keys R) (i : Fin 15) (delta : R) :
    UnitDifference (output q) (output (increment q i delta)) (14 - i.val) delta := by
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
  · exact increment11_unit q delta
  · exact increment12_unit q delta
  · exact increment13_unit q delta
  · exact increment14_unit q delta

noncomputable def coefficientRows (q : Keys R) (i : Fin 15) : R :=
  (output q).coeff (14 - i.val)

theorem update_unit (q : Keys R) (i : Fin 15) (value : R) :
    UnitDifference (output q) (output (Function.update q i value)) (14 - i.val) (q i + value) := by
  have he : increment q i (q i + value) = Function.update q i value := by
    rw [increment, CharTwo.add_cancel_left]
  rw [← he]
  exact increment_unit q i (q i + value)

theorem futureInvariant : Char2UpdateTriangular.FutureInvariant (coefficientRows (R := R)) := by
  intro q i j hij value
  have hrow : 14 - j.val < 14 - i.val := by
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

theorem output_coefficient (q : Keys R) (i : Fin 15) :
    (output q).coeff i.val = ascendingEquiv q i := by
  change (output q).coeff i.val = (output q).coeff (14 - i.rev.val)
  congr 1
  have hi := i.isLt
  rw [Fin.val_rev]
  omega

end FastPoly.Char2Degree15Fast
