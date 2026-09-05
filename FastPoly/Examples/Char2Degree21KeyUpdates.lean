import FastPoly.Examples.Char2Degree21Coordinates
import FastPoly.Examples.Char2Degree21Leading
import Mathlib.Tactic.IntervalCases

/-!
# Exact normalized-key changes for the degree-21 circuit

Each supplied inverse-key formula is checked against its named raw-key
shift. Only these small coordinate formulas are opened; the circuit and
all coefficient baselines remain opaque.
-/

namespace FastPoly.Char2Degree21KeyUpdates

set_option maxHeartbeats 20000

open Char2Degree21Coordinates Char2Degree21Pivots

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The original 21 raw keys, zero outside their actual range. -/
def rawKeys (q : Fin 21 → R) (i : ℕ) : R :=
  if h : i < 21 then keys q ⟨i, h⟩ else 0

def increment (q : Fin 21 → R) (i : Fin 21) (delta : R) : Fin 21 → R :=
  Function.update q i (q i + delta)

theorem rawKeys_shift0 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 0 delta) = shift0 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift0, Char2Degree19InnerSimple.shift7, Char2Degree19InnerDirect.shift3]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift0, Char2Degree19InnerSimple.shift7, Char2Degree19InnerDirect.shift3, rawKeys, dif_neg hk]

theorem rawKeys_shift1 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 1 delta) = shift1 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift1, Char2Degree19InnerZChanges.shift4]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift1, Char2Degree19InnerZChanges.shift4, rawKeys, dif_neg hk]

theorem rawKeys_shift2 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 2 delta) = shift2 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift2, Char2Degree19InnerZChanges.shift5]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift2, Char2Degree19InnerZChanges.shift5, rawKeys, dif_neg hk]

theorem rawKeys_shift3 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 3 delta) = shift3 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift3, Char2Degree19InnerSeam.shift8]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift3, Char2Degree19InnerSeam.shift8, rawKeys, dif_neg hk]

theorem rawKeys_shift4 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 4 delta) = shift4 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift4]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift4, rawKeys, dif_neg hk]

theorem rawKeys_shift5 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 5 delta) = shift5 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift5]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift5, rawKeys, dif_neg hk]

theorem rawKeys_shift6 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 6 delta) = shift6 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift6, Char2Degree19InnerChanges.shift6]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift6, Char2Degree19InnerChanges.shift6, rawKeys, dif_neg hk]

theorem rawKeys_shift7 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 7 delta) = shift7 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift7, Char2Degree19InnerSimple.shift7]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift7, Char2Degree19InnerSimple.shift7, rawKeys, dif_neg hk]

private theorem q8_offset (k b u v e f g h d : R) :
    k + ((b + d) + (b + d) ^ 2 + u * (b + d) + v * (b + d) + e + f + g + h) =
      (k + (b + b ^ 2 + u * b + v * b + e + f + g + h)) +
        (d ^ 2 + d * (1 + u + v)) := by
  rw [CharTwo.add_sq]
  simp only [mul_add, mul_one]
  rw [mul_comm u d, mul_comm v d]
  simp only [add_assoc, add_comm, add_left_comm]

theorem rawKeys_shift8 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 8 delta) = shift8 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    · change q 6 + ((q 8 + delta) + q 3 + q 9) =
        (q 6 + (q 8 + q 3 + q 9)) + delta
      ac_rfl
    · exact q8_offset (q 7) (q 8) (q 0) (q 5) (a14 q) (q 13)
        (q 3 ^ 2) (q 3) delta
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift8, rawKeys, dif_neg hk]

theorem rawKeys_shift9 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 9 delta) = shift9 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift9, Char2Degree19InnerChanges.shift9]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift9, Char2Degree19InnerChanges.shift9, rawKeys, dif_neg hk]

theorem rawKeys_shift10 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 10 delta) = shift10 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift10, Char2Degree19InnerSimple.shift10]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift10, Char2Degree19InnerSimple.shift10, rawKeys, dif_neg hk]

theorem rawKeys_shift11 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 11 delta) = shift11 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift11, Char2Degree19InnerSimple.shift11]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift11, Char2Degree19InnerSimple.shift11, rawKeys, dif_neg hk]

theorem rawKeys_shift12 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 12 delta) = shift12 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift12, Char2Degree19InnerTail.shift12]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift12, Char2Degree19InnerTail.shift12, rawKeys, dif_neg hk]

theorem rawKeys_shift13 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 13 delta) = shift13 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift13, Char2Degree19InnerTail.shift13]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift13, Char2Degree19InnerTail.shift13, rawKeys, dif_neg hk]

theorem rawKeys_shift14 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 14 delta) = shift14 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift14, Char2Degree19InnerTail.shift14]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift14, Char2Degree19InnerTail.shift14, rawKeys, dif_neg hk]

theorem rawKeys_shift15 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 15 delta) = shift15 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift15]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift15, rawKeys, dif_neg hk]

theorem rawKeys_shift16 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 16 delta) = shift16 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift16]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift16, rawKeys, dif_neg hk]

theorem rawKeys_shift17 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 17 delta) = shift17 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift17]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift17, rawKeys, dif_neg hk]

theorem rawKeys_shift18 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 18 delta) = shift18 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift18]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift18, rawKeys, dif_neg hk]

theorem rawKeys_shift19 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 19 delta) = shift19 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift19]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift19, rawKeys, dif_neg hk]

theorem rawKeys_shift20 (q : Fin 21 → R) (delta : R) :
    rawKeys (increment q 20 delta) = shift20 (rawKeys q) delta := by
  funext j
  by_cases hj : j < 21
  · interval_cases j <;> try rfl
    all_goals
      dsimp [rawKeys, keys, a4, a9, a14, a15, a15Correction,
        increment, Function.update, Char2Degree21Pivots.shift20]
      simp only [CharTwo.add_sq, mul_add, add_mul, mul_one,
        add_assoc, add_comm, add_left_comm]
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 21 := ⟨j - 21, by omega⟩
    have hk : ¬ k + 21 < 21 := by omega
    simp only [Char2Degree21Pivots.shift20, rawKeys, dif_neg hk]

/-- The 21 certified raw-key changes, indexed in descending coefficient order. -/
def rawShift (j : Fin 21) (a : ℕ → R) (delta : R) : ℕ → R :=
  match j.val with
  | 0 => shift0 a delta
  | 1 => shift1 a delta
  | 2 => shift2 a delta
  | 3 => shift3 a delta
  | 4 => shift4 a delta
  | 5 => shift5 a delta
  | 6 => shift6 a delta
  | 7 => shift7 a delta
  | 8 => shift8 a delta
  | 9 => shift9 a delta
  | 10 => shift10 a delta
  | 11 => shift11 a delta
  | 12 => shift12 a delta
  | 13 => shift13 a delta
  | 14 => shift14 a delta
  | 15 => shift15 a delta
  | 16 => shift16 a delta
  | 17 => shift17 a delta
  | 18 => shift18 a delta
  | 19 => shift19 a delta
  | _ => shift20 a delta

theorem rawKeys_increment (q : Fin 21 → R) (j : Fin 21) (delta : R) :
    rawKeys (increment q j delta) = rawShift j (rawKeys q) delta := by
  fin_cases j
  · exact rawKeys_shift0 q delta
  · exact rawKeys_shift1 q delta
  · exact rawKeys_shift2 q delta
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
  · exact rawKeys_shift16 q delta
  · exact rawKeys_shift17 q delta
  · exact rawKeys_shift18 q delta
  · exact rawKeys_shift19 q delta
  · exact rawKeys_shift20 q delta

variable [Nontrivial R]

theorem rawShift_unit (a : ℕ → R) (j : Fin 21) (delta : R) :
    Char2Degree19InnerTail.UnitDifference
      (Char2Degree21Frame.output a) (Char2Degree21Frame.output (rawShift j a delta))
      (20 - j.val) delta := by
  fin_cases j
  · exact shift0_unit a delta
  · exact shift1_unit a delta
  · exact shift2_unit a delta
  · exact shift3_unit a delta
  · exact shift4_unit a delta
  · exact shift5_unit a delta
  · exact shift6_unit a delta
  · exact shift7_unit a delta
  · exact shift8_unit a delta
  · exact shift9_unit a delta
  · exact shift10_unit a delta
  · exact shift11_unit a delta
  · exact shift12_unit a delta
  · exact shift13_unit a delta
  · exact shift14_unit a delta
  · exact shift15_unit a delta
  · exact shift16_unit a delta
  · exact shift17_unit a delta
  · exact shift18_unit a delta
  · exact shift19_unit a delta
  · exact shift20_unit a delta

theorem increment_unit (q : Fin 21 → R) (j : Fin 21) (delta : R) :
    Char2Degree19InnerTail.UnitDifference
      (Char2Degree21Frame.output (rawKeys q))
      (Char2Degree21Frame.output (rawKeys (increment q j delta)))
      (20 - j.val) delta := by
  rw [rawKeys_increment]
  exact rawShift_unit (rawKeys q) j delta

end FastPoly.Char2Degree21KeyUpdates
