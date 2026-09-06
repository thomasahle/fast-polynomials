import FastPoly.Examples.Char2Degree25TerminalSlots
import FastPoly.Examples.Char2Degree25RemainderUnit
import FastPoly.Examples.Char2Degree25LatePeel

/-! Actual terminal unit steps from explicit small head remainders.
The earlier corrections are represented by their actual raw a7/a17
differences, never by expanded coefficient expressions. The combined
row-three direction is the supplied q21/q20 action. -/
namespace FastPoly.Char2Degree25TerminalUnits

open Polynomial Char2Degree19InnerTail Char2Degree25TerminalSlots
open Char2Degree25TailCoordinates (keys output)
open Char2Degree25TerminalHead
open Char2Degree25TwentyTwoWires (E U)
open Char2Degree25RowThirteen (L ellSlope)
open Char2CoefficientShearTransport (increment)
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]
attribute [local irreducible] keys output

noncomputable def delta7 (q r : Fin 25 → R) : R := keys r 7 + keys q 7
noncomputable def delta17 (q r : Fin 25 → R) : R := keys r 17 + keys q 17

private theorem recover_delta (a b : R) : b = a + (b + a) := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem raw7_delta (q r : Fin 25 → R) : keys r 7 = keys q 7 + delta7 q r :=
  recover_delta _ _
theorem raw17_delta (q r : Fin 25 → R) : keys r 17 = keys q 17 + delta17 q r :=
  recover_delta _ _

theorem theta_keys (q : Fin 25 → R) (d : R) :
    Char2Degree25TerminalHead.theta (keys q) d = Char2Degree25TerminalSlots.theta q d := by
  change (Char2Degree25RowThirteen.B (keys q) + 1) * d = _
  rw [Char2Degree25TerminalSlots.B_keys]
  rfl

private theorem collect_row4 (u e k l c : R[X]) :
    u + e * (k * l + c) = u + k * (e * l) + c * e := by ring
private theorem collect_row2 (e k l c : R[X]) :
    e * (k * l + c) = k * (e * l) + c * e := by ring

theorem head20 (q : Fin 25 → R) (d : R) :
    Char2Degree25Frame.head (keys (increment q 20 d)) + Char2Degree25Frame.head (keys q) =
      row4Head (keys q) d (delta7 q (increment q 20 d)) (delta17 q (increment q 20 d)) := by
  have hb := sameBase_of_prefix q (increment q 20 d) (increment_prefix q 20 d (by omega))
  have h16 : keys (increment q 20 d) 16 = keys q 16 + 0 := by
    rw [add_zero]
    exact raw16_increment20 q d
  have hh := hb.head_change d (delta7 q (increment q 20 d)) 0
    (delta17 q (increment q 20 d)) (raw4_increment20 q d) (raw7_delta q _)
    h16 (raw17_delta q _)
  rw [hh]
  simp only [map_zero, zero_mul, add_zero]
  exact collect_row4 (C d * U (keys q)) (E (keys q))
    (C (delta7 q (increment q 20 d))) (L (keys q)) (C (delta17 q (increment q 20 d)))

theorem head21 (q : Fin 25 → R) (d : R) :
    Char2Degree25Frame.head (keys (step21 q d)) + Char2Degree25Frame.head (keys q) =
      row3Head (keys q) d (delta7 q (step21 q d)) (delta17 q (step21 q d)) := by
  have hb := sameBase_of_prefix q (step21 q d) (step21_prefix q d)
  have hh := hb.head_change (Char2Degree25TerminalSlots.theta q d) (delta7 q (step21 q d)) d
    (delta17 q (step21 q d)) (raw4_step21 q d) (raw7_delta q _)
    (raw16_step21 q d) (raw17_delta q _)
  simpa only [row3Head, theta_keys] using hh

theorem head22 (q : Fin 25 → R) (d : R) :
    Char2Degree25Frame.head (keys (increment q 22 d)) + Char2Degree25Frame.head (keys q) =
      row2Remainder (keys q) d (delta17 q (increment q 22 d)) := by
  have hb := sameBase_of_prefix q (increment q 22 d) (increment_prefix q 22 d (by omega))
  have h4 : keys (increment q 22 d) 4 = keys q 4 + 0 := by
    rw [add_zero]
    exact raw4_increment22 q d
  have h16 : keys (increment q 22 d) 16 = keys q 16 + 0 := by
    rw [add_zero]
    exact raw16_increment22 q d
  have hh := hb.head_change 0 d 0 (delta17 q (increment q 22 d))
    h4 (raw7_increment22 q d) h16 (raw17_delta q _)
  rw [hh]
  simp only [map_zero, zero_mul, zero_add, add_zero]
  exact collect_row2 (E (keys q)) (C d) (L (keys q)) (C (delta17 q (increment q 22 d)))

private theorem telescope (a b c : R[X]) : (c + b) + (b + a) = c + a := by
  simp only [add_assoc, CharTwo.add_cancel_left]

theorem degree_step21 (q : Fin 25 → R) (d : R) :
    (output (step21 q d) + output q).natDegree ≤ 4 := by
  have ht := telescope (output q) (output (increment q 21 d)) (output (step21 q d))
  rw [← ht]
  exact natDegree_add_le_of_degree_le
    (Char2Degree25LatePeel.degree20 (increment q 21 d) (Char2Degree25TerminalSlots.theta q d))
    (Char2Degree25LatePeel.degree21 q d)

private theorem actual_unit (q r : Fin 25 → R)
    (hp : ∀ i : Fin 25, i.val < 9 → r i = q i) (hc : r 24 = q 24)
    (hd : (output r + output q).natDegree ≤ 4)
    (rem quotient : R[X]) (row : ℕ) (d : R)
    (hh : Char2Degree25Frame.head (keys r) + Char2Degree25Frame.head (keys q) =
      rem + Char2Degree25Frame.nRight (keys q) * quotient)
    (hu : UnitDifference 0 rem row d) (hr : row < 5) :
    UnitDifference (output q) (output r) row d := by
  rw [Char2Degree25TailCoordinates.output_eq q, Char2Degree25TailCoordinates.output_eq r]
  have hd' : (Char2Degree25Frame.output (keys r) + Char2Degree25Frame.output (keys q)).natDegree ≤ 4 := by
    simpa only [Char2Degree25TailCoordinates.output_eq] using hd
  exact Char2Degree25RemainderUnit.unit_from_head
    (nRight_of_prefix q r hp) (constant_of_value q r hc) hd' hh hu hr

theorem unit20 (q : Fin 25 → R) (d : R) :
    UnitDifference (output q) (output (increment q 20 d)) 4 d := by
  apply actual_unit q (increment q 20 d) (increment_prefix q 20 d (by omega))
    (increment_constant q 20 d (by omega)) (Char2Degree25LatePeel.degree20 q d)
    (row4Remainder (keys q) d (delta7 q (increment q 20 d)) (delta17 q (increment q 20 d)))
    (C d) 4 d
  · rw [head20]
    exact row4_split _ _ _ _
  · exact row4_unit _ _ _ _
  · omega

theorem unit_step21 (q : Fin 25 → R) (d : R) :
    UnitDifference (output q) (output (step21 q d)) 3 d := by
  apply actual_unit q (step21 q d) (step21_prefix q d) (step21_constant q d) (degree_step21 q d)
    (row3Remainder (keys q) d (delta7 q (step21 q d)) (delta17 q (step21 q d)))
    (C (Char2Degree25TerminalHead.theta (keys q) d + d)) 3 d
  · rw [head21]
    exact row3_split _ _ _ _
  · exact row3_unit _ _ _ _
  · omega

theorem unit22 (q : Fin 25 → R) (d : R) :
    UnitDifference (output q) (output (increment q 22 d)) 2 d := by
  apply actual_unit q (increment q 22 d) (increment_prefix q 22 d (by omega))
    (increment_constant q 22 d (by omega)) (Char2Degree25LatePeel.degree22 q d)
    (row2Remainder (keys q) d (delta17 q (increment q 22 d))) 0 2 d
  · rw [mul_zero, add_zero]
    exact head22 q d
  · exact row2_unit _ _ _
  · omega

end FastPoly.Char2Degree25TerminalUnits
