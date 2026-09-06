import FastPoly.Examples.Char2Degree25MiddleKeys
import FastPoly.Examples.Char2Degree25RowEleven
import FastPoly.Examples.Char2Degree25RowsTenNine

/-! Four remaining raw-coordinate unit steps transported through the checked
first thirteen coordinate shears. The factored middle offsets are unchanged
by q13/q14/q15/q24, so these key identities are literal slot equalities.
No middle tail or output coefficient is expanded. This does not normalize
the remaining decoder coordinates. -/

namespace FastPoly.Char2Degree25LowerRawKeys

open Char2Degree25MiddleCoordinates Char2Degree25MiddleKeys
  Char2Degree25PrefixCoordinates Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem keys_increment13 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 13 d) =
      Char2Degree25RowEleven.shift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_increment14 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 14 d) =
      Char2Degree25RowsTenNine.shift10 (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_increment15 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 15 d) =
      Char2Degree25RowsTenNine.shift11 (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_increment24 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 24 d) =
      Char2Degree25RowEleven.constantShift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem increment13_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (increment q 13 d))) 11 d := by
  rw [keys_increment13]
  exact Char2Degree25RowEleven.unit _ d

theorem increment14_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (increment q 14 d))) 10 d := by
  rw [keys_increment14]
  exact Char2Degree25RowsTenNine.shift10_unit _ d

theorem increment15_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (increment q 15 d))) 9 d := by
  rw [keys_increment15]
  exact Char2Degree25RowsTenNine.shift11_unit _ d

theorem increment24_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (increment q 24 d))) 0 d := by
  rw [keys_increment24]
  exact Char2Degree25RowEleven.constant_unit _ d

end FastPoly.Char2Degree25LowerRawKeys
