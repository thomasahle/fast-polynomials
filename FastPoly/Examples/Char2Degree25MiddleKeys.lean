import FastPoly.Examples.Char2Degree25MiddleCoordinates
import FastPoly.Examples.Char2Degree25RowFourteen
import FastPoly.Examples.Char2Degree25RowTwelve
import Mathlib.Tactic.IntervalCases

/-! The four supplied normalized middle pivots, using the factored key formulas. -/

namespace FastPoly.Char2Degree25MiddleKeys

open Char2Degree25MiddleCoordinates Char2Degree25PrefixCoordinates
  Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def factoredKeys (q : Fin 25 → R) : ℕ → R
  | 0 => q 1 + q 2
  | 1 => q 2
  | 2 => q 0
  | 3 => q 3
  | 4 => q 4 + q 5 + q 7 + q 20
  | 5 => q 7
  | 6 => q 6
  | 7 => a7 q
  | 8 => a8 q
  | 9 => a9 q
  | 10 => q 14
  | 11 => q 15
  | 12 => q 5 + q 8
  | 13 => a13 q
  | 14 => q 22
  | 15 => q 16
  | 16 => q 21
  | 17 => q 13
  | 18 => q 20
  | 19 => q 17
  | 20 => q 23
  | 21 => q 18
  | 22 => q 19
  | 23 => q 8
  | 24 => q 24
  | _ => 0

theorem keys_formula (q : Fin 25 → R) : Char2Degree25MiddleCoordinates.keys q = factoredKeys q := by
  funext i
  have h0 := middle_other q 0 (by omega) (by omega) (by omega) (by omega)
  have h1 := middle_other q 1 (by omega) (by omega) (by omega) (by omega)
  have h2 := middle_other q 2 (by omega) (by omega) (by omega) (by omega)
  have h3 := middle_other q 3 (by omega) (by omega) (by omega) (by omega)
  have h4 := middle_other q 4 (by omega) (by omega) (by omega) (by omega)
  have h5 := middle_other q 5 (by omega) (by omega) (by omega) (by omega)
  have h6 := middle_other q 6 (by omega) (by omega) (by omega) (by omega)
  have h7 := middle_other q 7 (by omega) (by omega) (by omega) (by omega)
  have h8 := middle_other q 8 (by omega) (by omega) (by omega) (by omega)
  have h13 := middle_other q 13 (by omega) (by omega) (by omega) (by omega)
  have h14 := middle_other q 14 (by omega) (by omega) (by omega) (by omega)
  have h15 := middle_other q 15 (by omega) (by omega) (by omega) (by omega)
  have h16 := middle_other q 16 (by omega) (by omega) (by omega) (by omega)
  have h17 := middle_other q 17 (by omega) (by omega) (by omega) (by omega)
  have h18 := middle_other q 18 (by omega) (by omega) (by omega) (by omega)
  have h19 := middle_other q 19 (by omega) (by omega) (by omega) (by omega)
  have h20 := middle_other q 20 (by omega) (by omega) (by omega) (by omega)
  have h21 := middle_other q 21 (by omega) (by omega) (by omega) (by omega)
  have h22 := middle_other q 22 (by omega) (by omega) (by omega) (by omega)
  have h23 := middle_other q 23 (by omega) (by omega) (by omega) (by omega)
  have h24 := middle_other q 24 (by omega) (by omega) (by omega) (by omega)
  unfold Char2Degree25MiddleCoordinates.keys Char2Degree25PrefixCoordinates.keys factoredKeys
  split <;> simp only [middle_nine, middle_ten, middle_eleven, middle_twelve,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]

theorem B_keys (q : Fin 25 → R) :
    Char2Degree25RowThirteen.B (Char2Degree25MiddleCoordinates.keys q) = B q := by
  rw [keys_formula]
  rfl

theorem a7_increment9 (q : Fin 25 → R) (d : R) : a7 (increment q 9 d) = a7 q + d := by
  change (q 9 + d) + a13 q + q 12 = _
  unfold a7
  simp only [add_assoc, add_comm, add_left_comm]

theorem a9_increment10 (q : Fin 25 → R) (d : R) : a9 (increment q 10 d) = a9 q + d := by
  change (q 10 + d) + tail10 q + B q * tail11 q = _
  unfold a9
  simp only [add_assoc, add_comm, add_left_comm]

theorem a13_increment11 (q : Fin 25 → R) (d : R) : a13 (increment q 11 d) = a13 q + d := by
  change (q 11 + d) + tail11 q = _
  unfold a13
  simp only [add_assoc, add_comm, add_left_comm]

theorem a7_increment11 (q : Fin 25 → R) (d : R) : a7 (increment q 11 d) = a7 q + d := by
  unfold a7
  rw [a13_increment11]
  change q 9 + (a13 q + d) + q 12 = _
  simp only [add_assoc, add_comm, add_left_comm]

private theorem linear_tail (b s x c e d : R) :
    b * (s + (x + d) + c) + e = (b * (s + x + c) + e) + b * d := by ring

theorem tail10_increment11 (q : Fin 25 → R) (d : R) :
    tail10 (increment q 11 d) = tail10 q + B q * d := by
  change B q * (shared q + (q 11 + d) + q 22) + q 22 = _
  exact linear_tail _ _ _ _ _ _

theorem a9_increment11 (q : Fin 25 → R) (d : R) : a9 (increment q 11 d) = a9 q + B q * d := by
  unfold a9
  rw [tail10_increment11]
  change q 10 + (tail10 q + B q * d) + B q * tail11 q = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a8_increment12 (q : Fin 25 → R) (d : R) : a8 (increment q 12 d) = a8 q + d := by
  change (q 12 + d) + tail12 q = _
  unfold a8
  simp only [add_assoc, add_comm, add_left_comm]

theorem a7_increment12 (q : Fin 25 → R) (d : R) : a7 (increment q 12 d) = a7 q + d := by
  change q 9 + a13 q + (q 12 + d) = _
  unfold a7
  simp only [add_assoc]

theorem keys_increment9 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 9 d) =
      Char2Degree25RowFifteen.shift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> first | rfl | exact a7_increment9 q d
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_increment10 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 10 d) =
      Char2Degree25RowFourteen.shift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> first | rfl | exact a9_increment10 q d
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_increment11 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 11 d) =
      Char2Degree25RowThirteen.shift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> first | rfl | exact a7_increment11 q d | exact a9_increment11 q d | exact a13_increment11 q d
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_increment12 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 12 d) =
      Char2Degree25RowTwelve.shift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> first | rfl | exact a7_increment12 q d | exact a8_increment12 q d
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem increment9_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (increment q 9 d))) 15 d := by
  rw [keys_increment9]
  exact Char2Degree25RowFifteen.unit _ d

theorem increment10_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (increment q 10 d))) 14 d := by
  rw [keys_increment10]
  exact Char2Degree25RowFourteen.unit _ d

theorem increment11_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (increment q 11 d))) 13 d := by
  rw [keys_increment11]
  exact Char2Degree25RowThirteen.shift_unit _ d

theorem increment12_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (increment q 12 d))) 12 d := by
  rw [keys_increment12]
  exact Char2Degree25RowTwelve.shift_unit _ d

end FastPoly.Char2Degree25MiddleKeys
