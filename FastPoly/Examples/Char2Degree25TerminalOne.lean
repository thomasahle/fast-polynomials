import FastPoly.Examples.Char2Degree25TerminalUnits
import FastPoly.Examples.Char2Degree25TailRowEleven
import FastPoly.Examples.Char2Degree25RowElevenRead

/-! The actual last nonconstant decoder step. Its preserved normalized
row eleven forces the raw a17 correction to equal the supplied a20
increment. The head remainder is then the explicit linear polynomial
d*(X+C a16); no earlier correction is expanded. -/
namespace FastPoly.Char2Degree25TerminalOne

open Polynomial Char2Degree19InnerTail Char2Degree25TerminalSlots
open Char2Degree25TailCoordinates (keys output)
open Char2Degree25RowElevenRead
open Char2CoefficientShearTransport (increment)
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]
attribute [local irreducible] keys output

/-- All potentially changed raw slots are explicitly excluded. -/
theorem fixed_slot23 (q : Fin 25 → R) (d : R) (i : ℕ)
    (h10 : i ≠ 10) (h11 : i ≠ 11) (h15 : i ≠ 15) (h17 : i ≠ 17)
    (h19 : i ≠ 19) (h20 : i ≠ 20) (h21 : i ≠ 21) (h22 : i ≠ 22) :
    keys (increment q 23 d) i = keys q i := by
  rw [Char2Degree25TailSlots.keys_other _ i h10 h11 h15 h17 h19 h21 h22,
    Char2Degree25TailSlots.keys_other _ i h10 h11 h15 h17 h19 h21 h22,
    Char2Degree25MiddleKeys.keys_formula, Char2Degree25MiddleKeys.keys_formula]
  by_cases hi : i < 25
  · interval_cases i <;> first | omega | rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem sameFixed23 (q : Fin 25 → R) (d : R) :
    SameFixed (keys q) (keys (increment q 23 d)) := by
  constructor <;> apply fixed_slot23 <;> omega

/-- The already normalized row eleven uniquely supplies this actual raw offset. -/
theorem raw17_increment23 (q : Fin 25 → R) (d : R) :
    keys (increment q 23 d) 17 = keys q 17 + d := by
  have hrow := Char2Degree25TailRowEleven.late_difference_row11 q 23 (by omega) d
  have hrow' : (Char2Degree25Frame.output (keys (increment q 23 d)) +
      Char2Degree25Frame.output (keys q)).coeff 11 = 0 := by
    simpa only [Char2Degree25TailCoordinates.output_eq] using hrow
  exact (sameFixed23 q d).offset17_eq d (raw20_increment23 q d) hrow'

private theorem increment_delta (a d : R) : (a + d) + a = d := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem head23 (q : Fin 25 → R) (d : R) :
    Char2Degree25Frame.head (keys (increment q 23 d)) + Char2Degree25Frame.head (keys q) =
      Char2Degree25TerminalHead.row1Remainder (keys q) d := by
  have hh := (sameFixed23 q d).head_change
  rw [raw17_increment23, increment_delta] at hh
  exact hh

theorem unit23 (q : Fin 25 → R) (d : R) :
    UnitDifference (output q) (output (increment q 23 d)) 1 d := by
  have hd := Char2Degree25LatePeel.degree23 q d
  have hd' : (Char2Degree25Frame.output (keys (increment q 23 d)) +
      Char2Degree25Frame.output (keys q)).natDegree ≤ 4 := by
    simpa only [Char2Degree25TailCoordinates.output_eq] using hd
  have hh : Char2Degree25Frame.head (keys (increment q 23 d)) + Char2Degree25Frame.head (keys q) =
      Char2Degree25TerminalHead.row1Remainder (keys q) d + Char2Degree25Frame.nRight (keys q) * 0 := by
    rw [mul_zero, add_zero]
    exact head23 q d
  rw [Char2Degree25TailCoordinates.output_eq q,
    Char2Degree25TailCoordinates.output_eq (increment q 23 d)]
  exact Char2Degree25RemainderUnit.unit_from_head
    (nRight_of_prefix q (increment q 23 d) (increment_prefix q 23 d (by omega)))
    (constant_of_value q (increment q 23 d) (increment_constant q 23 d (by omega)))
    hd' hh (Char2Degree25TerminalHead.row1_unit (keys q) d) (by omega)

end FastPoly.Char2Degree25TerminalOne
