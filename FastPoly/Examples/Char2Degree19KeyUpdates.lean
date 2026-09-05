import FastPoly.Examples.Char2Degree19Coordinates
import FastPoly.Examples.Char2Degree19InnerDirect
import FastPoly.Examples.Char2Degree19InnerZChanges
import FastPoly.Examples.Char2Degree19InnerChanges
import FastPoly.Examples.Char2Degree19InnerSimple
import FastPoly.Examples.Char2Degree19InnerSeam
import Mathlib.Tactic.IntervalCases

/-!
# The supplied degree-19 normalized-key updates

The coordinate inverse is kept separate from the circuit.  Each lemma below
checks just the small key formulas against one already certified circuit
shift.  In particular the eighth coordinate changes the last raw offset by
`delta ^ 2 + delta`; no coefficient baseline is expanded.
-/

namespace FastPoly.Char2Degree19KeyUpdates

set_option maxHeartbeats 20000

open Char2Degree19Coordinates Char2Degree19Crown Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Extend the actual nineteen-key inverse by zero, not by its last branch. -/
def rawKeys (q : Fin 19 → R) (i : ℕ) : R :=
  if h : i < 19 then keys q ⟨i, h⟩ else 0

omit [CharP R 2] in
theorem rawKeys_fin (q : Fin 19 → R) (i : Fin 19) :
    rawKeys q i.val = keys q i := by
  simp only [rawKeys, dif_pos i.isLt]

/-- Add a displayed correction to one normalized key. -/
def increment (q : Fin 19 → R) (i : Fin 19) (delta : R) : Fin 19 → R :=
  Function.update q i (q i + delta)

omit [CharP R 2] in
theorem rawKeys_shift3 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 3 delta) =
      Char2Degree19InnerDirect.shift3 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> rfl
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerDirect.shift3, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift4 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 4 delta) =
      Char2Degree19InnerZChanges.shift4 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 1.
      change ((q 4 + delta) + q 5) = ((q 4 + q 5) + delta)
      simp only [add_assoc, add_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerZChanges.shift4, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift5 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 5 delta) =
      Char2Degree19InnerZChanges.shift5 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 1.
      change (q 4 + (q 5 + delta)) = ((q 4 + q 5) + delta)
      simp only [add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerZChanges.shift5, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift6 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 6 delta) =
      Char2Degree19InnerChanges.shift6 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 7.
      change ((q 6 + delta) + (q 8 + q 9)) = ((q 6 + (q 8 + q 9)) + delta)
      simp only [add_assoc, add_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerChanges.shift6, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift7 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 7 delta) =
      Char2Degree19InnerSimple.shift7 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 15.
      change ((q 7 + delta) + ((((q 10 + q 12) + q 13) + (q 8) ^ 2) + q 8)) = ((q 7 + ((((q 10 + q 12) + q 13) + (q 8) ^ 2) + q 8)) + delta)
      simp only [add_assoc, add_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerSimple.shift7, rawKeys, dif_neg hk]

theorem rawKeys_shift8 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 8 delta) =
      Char2Degree19InnerSeam.shift8 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 7.
      change (q 6 + ((q 8 + delta) + q 9)) = ((q 6 + (q 8 + q 9)) + delta)
      simp only [add_assoc, add_comm, add_left_comm]
    · -- Raw offset 15.
      change (q 7 + ((((q 10 + q 12) + q 13) + ((q 8 + delta)) ^ 2) + (q 8 + delta))) = ((q 7 + ((((q 10 + q 12) + q 13) + (q 8) ^ 2) + q 8)) + ((delta) ^ 2 + delta))
      simp only [CharTwo.add_sq, add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerSeam.shift8, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift9 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 9 delta) =
      Char2Degree19InnerChanges.shift9 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 7.
      change (q 6 + (q 8 + (q 9 + delta))) = ((q 6 + (q 8 + q 9)) + delta)
      simp only [add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerChanges.shift9, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift10 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 10 delta) =
      Char2Degree19InnerSimple.shift10 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 14.
      change ((q 10 + delta) + q 12) = ((q 10 + q 12) + delta)
      simp only [add_assoc, add_comm]
    · -- Raw offset 15.
      change (q 7 + (((((q 10 + delta) + q 12) + q 13) + (q 8) ^ 2) + q 8)) = ((q 7 + ((((q 10 + q 12) + q 13) + (q 8) ^ 2) + q 8)) + delta)
      simp only [add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerSimple.shift10, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift11 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 11 delta) =
      Char2Degree19InnerSimple.shift11 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 9.
      change ((q 11 + delta) + (q 12 + q 14)) = ((q 11 + (q 12 + q 14)) + delta)
      simp only [add_assoc, add_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerSimple.shift11, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift12 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 12 delta) =
      Char2Degree19InnerTail.shift12 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 4.
      change ((q 12 + delta) + q 14) = ((q 12 + q 14) + delta)
      simp only [add_assoc, add_comm]
    · -- Raw offset 9.
      change (q 11 + ((q 12 + delta) + q 14)) = ((q 11 + (q 12 + q 14)) + delta)
      simp only [add_assoc, add_comm, add_left_comm]
    · -- Raw offset 14.
      change (q 10 + (q 12 + delta)) = ((q 10 + q 12) + delta)
      simp only [add_comm, add_left_comm]
    · -- Raw offset 15.
      change (q 7 + ((((q 10 + (q 12 + delta)) + q 13) + (q 8) ^ 2) + q 8)) = ((q 7 + ((((q 10 + q 12) + q 13) + (q 8) ^ 2) + q 8)) + delta)
      simp only [add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerTail.shift12, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift13 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 13 delta) =
      Char2Degree19InnerTail.shift13 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 15.
      change (q 7 + ((((q 10 + q 12) + (q 13 + delta)) + (q 8) ^ 2) + q 8)) = ((q 7 + ((((q 10 + q 12) + q 13) + (q 8) ^ 2) + q 8)) + delta)
      simp only [add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerTail.shift13, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift14 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 14 delta) =
      Char2Degree19InnerTail.shift14 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> try rfl
    · -- Raw offset 4.
      change (q 12 + (q 14 + delta)) = ((q 12 + q 14) + delta)
      simp only [add_comm, add_left_comm]
    · -- Raw offset 9.
      change (q 11 + (q 12 + (q 14 + delta))) = ((q 11 + (q 12 + q 14)) + delta)
      simp only [add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerTail.shift14, rawKeys, dif_neg hk]

omit [CharP R 2] in
theorem rawKeys_shift15 (q : Fin 19 → R) (delta : R) :
    rawKeys (increment q 15 delta) =
      Char2Degree19InnerTail.shift15 (rawKeys q) delta := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> rfl
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [Char2Degree19InnerTail.shift15, rawKeys, dif_neg hk]

/-- The inner coordinate at index `j` is normalized key `j+3`. -/
def innerIndex (j : Fin 13) : Fin 19 := ⟨j.val + 3, by omega⟩

/-- Dispatch only among the thirteen supplied changes, never among field values. -/
def rawShift (j : Fin 13) (a : ℕ → R) (delta : R) : ℕ → R :=
  match j.val with
  | 0 => Char2Degree19InnerDirect.shift3 a delta
  | 1 => Char2Degree19InnerZChanges.shift4 a delta
  | 2 => Char2Degree19InnerZChanges.shift5 a delta
  | 3 => Char2Degree19InnerChanges.shift6 a delta
  | 4 => Char2Degree19InnerSimple.shift7 a delta
  | 5 => Char2Degree19InnerSeam.shift8 a delta
  | 6 => Char2Degree19InnerChanges.shift9 a delta
  | 7 => Char2Degree19InnerSimple.shift10 a delta
  | 8 => Char2Degree19InnerSimple.shift11 a delta
  | 9 => Char2Degree19InnerTail.shift12 a delta
  | 10 => Char2Degree19InnerTail.shift13 a delta
  | 11 => Char2Degree19InnerTail.shift14 a delta
  | _ => Char2Degree19InnerTail.shift15 a delta

theorem rawKeys_increment (q : Fin 19 → R) (j : Fin 13) (delta : R) :
    rawKeys (increment q (innerIndex j) delta) = rawShift j (rawKeys q) delta := by
  fin_cases j
  · exact rawKeys_shift3 q delta
  · exact rawKeys_shift4 q delta
  · exact rawKeys_shift5 q delta
  · exact rawKeys_shift6 q delta
  · exact rawKeys_shift7 q delta
  · exact rawKeys_shift8 q delta
  · exact rawKeys_shift9 q delta
  · exact rawKeys_shift10 q delta
  · exact rawKeys_shift11 q delta
  · exact rawKeys_shift12 q delta
  · exact rawKeys_shift13 q delta
  · exact rawKeys_shift14 q delta
  · exact rawKeys_shift15 q delta

variable [Nontrivial R]

theorem rawShift_unit (a : ℕ → R) (j : Fin 13) (delta : R) :
    UnitDifference (crown a) (crown (rawShift j a delta)) (12 - j.val) delta := by
  fin_cases j
  · exact Char2Degree19InnerDirect.shift3_unit a delta
  · exact Char2Degree19InnerZChanges.shift4_unit a delta
  · exact Char2Degree19InnerZChanges.shift5_unit a delta
  · exact Char2Degree19InnerChanges.shift6_unit a delta
  · exact Char2Degree19InnerSimple.shift7_unit a delta
  · exact Char2Degree19InnerSeam.shift8_unit a delta
  · exact Char2Degree19InnerChanges.shift9_unit a delta
  · exact Char2Degree19InnerSimple.shift10_unit a delta
  · exact Char2Degree19InnerSimple.shift11_unit a delta
  · exact Char2Degree19InnerTail.shift12_unit a delta
  · exact Char2Degree19InnerTail.shift13_unit a delta
  · exact Char2Degree19InnerTail.shift14_unit a delta
  · exact Char2Degree19InnerTail.shift15_unit a delta

/-- The normalized-coordinate change inherits the supplied unit difference. -/
theorem increment_unit (q : Fin 19 → R) (j : Fin 13) (delta : R) :
    UnitDifference (crown (rawKeys q))
      (crown (rawKeys (increment q (innerIndex j) delta))) (12 - j.val) delta := by
  rw [rawKeys_increment]
  exact rawShift_unit _ j delta

end FastPoly.Char2Degree19KeyUpdates
