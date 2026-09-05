import FastPoly.Examples.Char2Degree25PrefixCoordinates
import FastPoly.Examples.Char2Degree25RowSeventeen
import FastPoly.Examples.Char2Degree25RowEighteen
import FastPoly.Examples.Char2Degree25RowSixteen

/-! Transport of the first nine actual raw unit differences through the exact
partial key equivalence. Coordinates q9 through q24 remain raw placeholders.
This file does not claim a complete output inverse or final normalization.
The finite raw-slot cases only check the explicitly supplied linear map. -/

namespace FastPoly.Char2Degree25PrefixPivots

open Polynomial Char2Degree19InnerTail Char2Degree25PrefixCoordinates

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem keys_increment0 (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    keys (increment q 0 delta) = Char2Degree25HighPivots.shift0 (keys q) delta := by
  funext j
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    dsimp only [keys, increment, Char2Degree25HighPivots.shift0, Function.update] <;> ac_rfl

theorem increment0_unit (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q 0 delta))) 24 delta := by
  rw [keys_increment0]
  exact Char2Degree25HighPivots.shift0_unit (keys q) delta

theorem keys_increment1 (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    keys (increment q 1 delta) = Char2Degree25HighPivots.shift1 (keys q) delta := by
  funext j
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    dsimp only [keys, increment, Char2Degree25HighPivots.shift1, Function.update] <;> ac_rfl

theorem increment1_unit (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q 1 delta))) 23 delta := by
  rw [keys_increment1]
  exact Char2Degree25HighPivots.shift1_unit (keys q) delta

theorem keys_increment2 (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    keys (increment q 2 delta) = Char2Degree25HighPivots.shift2 (keys q) delta := by
  funext j
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    dsimp only [keys, increment, Char2Degree25HighPivots.shift2, Function.update] <;> ac_rfl

theorem increment2_unit (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q 2 delta))) 22 delta := by
  rw [keys_increment2]
  exact Char2Degree25HighPivots.shift2_unit (keys q) delta

theorem keys_increment3 (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    keys (increment q 3 delta) = Char2Degree25HighPivots.shift3 (keys q) delta := by
  funext j
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    dsimp only [keys, increment, Char2Degree25HighPivots.shift3, Function.update] <;> ac_rfl

theorem increment3_unit (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q 3 delta))) 21 delta := by
  rw [keys_increment3]
  exact Char2Degree25HighPivots.shift3_unit (keys q) delta

theorem keys_increment4 (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    keys (increment q 4 delta) = Char2Degree25HighPivots.shift4 (keys q) delta := by
  funext j
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    dsimp only [keys, increment, Char2Degree25HighPivots.shift4, Function.update] <;> ac_rfl

theorem increment4_unit (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q 4 delta))) 20 delta := by
  rw [keys_increment4]
  exact Char2Degree25HighPivots.shift4_unit (keys q) delta

theorem keys_increment5 (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    keys (increment q 5 delta) = Char2Degree25SeamFrame.shift5 (keys q) delta := by
  funext j
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    dsimp only [keys, increment, Char2Degree25SeamFrame.shift5, Function.update] <;> ac_rfl

theorem increment5_unit (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q 5 delta))) 19 delta := by
  rw [keys_increment5]
  exact Char2Degree25SeamFrame.shift5_unit (keys q) delta

theorem keys_increment6 (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    keys (increment q 6 delta) = Char2Degree25RowEighteen.shift6 (keys q) delta := by
  funext j
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    dsimp only [keys, increment, Char2Degree25RowEighteen.shift6, Function.update] <;> ac_rfl

theorem increment6_unit (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q 6 delta))) 18 delta := by
  rw [keys_increment6]
  exact Char2Degree25RowEighteen.shift6_unit (keys q) delta

theorem keys_increment7 (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    keys (increment q 7 delta) = Char2Degree25RowSeventeen.shift7 (keys q) delta := by
  funext j
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    dsimp only [keys, increment, Char2Degree25RowSeventeen.shift7, Function.update] <;> ac_rfl

theorem increment7_unit (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q 7 delta))) 17 delta := by
  rw [keys_increment7]
  exact Char2Degree25RowSeventeen.shift7_unit (keys q) delta

theorem keys_increment8 (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    keys (increment q 8 delta) = Char2Degree25RowSixteen.shift (keys q) delta := by
  funext j
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    dsimp only [keys, increment, Char2Degree25RowSixteen.shift, Function.update] <;> ac_rfl

theorem increment8_unit (q : Char2Degree25PrefixCoordinates.Vector R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q 8 delta))) 16 delta := by
  rw [keys_increment8]
  exact Char2Degree25RowSixteen.shift_unit (keys q) delta

end FastPoly.Char2Degree25PrefixPivots

