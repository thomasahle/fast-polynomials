import FastPoly.Examples.Char2Degree25MiddleKeys
import FastPoly.Examples.Char2Degree25RowEight
import FastPoly.Examples.Char2Degree25RowsSevenSixFive

/-! The supplied coupled lower directions through the checked first thirteen
coordinate shears. Each action displays its complete vector update, changes
only coordinates up to its pivot, and has the checked raw output unit slope.
No coefficient normalization or complete decoder is asserted here. -/

namespace FastPoly.Char2Degree25CoupledLowerKeys

open Char2Degree25MiddleKeys Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def step16 (q : Fin 25 → R) (d : R) : Fin 25 → R :=
  Function.update
    (Function.update (Function.update q 14 (q 14 + d))
      15 (q 15 + (q 0 + q 6 + 1) * d)) 16 (q 16 + d)

def step17 (q : Fin 25 → R) (d : R) : Fin 25 → R :=
  Function.update (Function.update q 16 (q 16 + d)) 17 (q 17 + d)

def step18 (q : Fin 25 → R) (d : R) : Fin 25 → R :=
  Function.update (Function.update (Function.update q 15 (q 15 + d))
    17 (q 17 + d)) 18 (q 18 + d)

def step19 (q : Fin 25 → R) (d : R) : Fin 25 → R :=
  Function.update q 19 (q 19 + d)

theorem step16_pivot (q : Fin 25 → R) (d : R) : step16 q d 16 = q 16 + d := rfl
theorem step17_pivot (q : Fin 25 → R) (d : R) : step17 q d 17 = q 17 + d := rfl
theorem step18_pivot (q : Fin 25 → R) (d : R) : step18 q d 18 = q 18 + d := rfl
theorem step19_pivot (q : Fin 25 → R) (d : R) : step19 q d 19 = q 19 + d := rfl

theorem step16_other (q : Fin 25 → R) (d : R) (k : Fin 25)
    (h14 : k ≠ 14) (h15 : k ≠ 15) (h16 : k ≠ 16) : step16 q d k = q k := by
  simp only [step16, Function.update_of_ne h16,
    Function.update_of_ne h15, Function.update_of_ne h14]

theorem step17_other (q : Fin 25 → R) (d : R) (k : Fin 25)
    (h16 : k ≠ 16) (h17 : k ≠ 17) : step17 q d k = q k := by
  simp only [step17, Function.update_of_ne h17, Function.update_of_ne h16]

theorem step18_other (q : Fin 25 → R) (d : R) (k : Fin 25)
    (h15 : k ≠ 15) (h17 : k ≠ 17) (h18 : k ≠ 18) : step18 q d k = q k := by
  simp only [step18, Function.update_of_ne h18,
    Function.update_of_ne h17, Function.update_of_ne h15]

theorem step19_other (q : Fin 25 → R) (d : R) (k : Fin 25)
    (h19 : k ≠ 19) : step19 q d k = q k :=
  Function.update_of_ne h19 ..

theorem step16_later (q : Fin 25 → R) (d : R) (k : Fin 25)
    (hk : (16 : Fin 25) < k) : step16 q d k = q k := by
  apply step16_other <;> omega

theorem step17_later (q : Fin 25 → R) (d : R) (k : Fin 25)
    (hk : (17 : Fin 25) < k) : step17 q d k = q k := by
  apply step17_other <;> omega

theorem step18_later (q : Fin 25 → R) (d : R) (k : Fin 25)
    (hk : (18 : Fin 25) < k) : step18 q d k = q k := by
  apply step18_other <;> omega

theorem step19_later (q : Fin 25 → R) (d : R) (k : Fin 25)
    (hk : (19 : Fin 25) < k) : step19 q d k = q k := by
  apply step19_other
  omega

theorem keys_step16 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (step16 q d) =
      Char2Degree25RowEight.shift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_step17 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (step17 q d) =
      Char2Degree25RowsSevenSixFive.shift7 (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_step18 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (step18 q d) =
      Char2Degree25RowsSevenSixFive.shift6 (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_step19 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (step19 q d) =
      Char2Degree25RowsSevenSixFive.shift5 (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem step16_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (step16 q d))) 8 d := by
  rw [keys_step16]
  exact Char2Degree25RowEight.shift_unit _ d

theorem step17_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (step17 q d))) 7 d := by
  rw [keys_step17]
  exact Char2Degree25RowsSevenSixFive.shift7_unit _ d

theorem step18_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (step18 q d))) 6 d := by
  rw [keys_step18]
  exact Char2Degree25RowsSevenSixFive.shift6_unit _ d

theorem step19_unit (q : Fin 25 → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys (step19 q d))) 5 d := by
  rw [keys_step19]
  exact Char2Degree25RowsSevenSixFive.shift5_unit _ d

end FastPoly.Char2Degree25CoupledLowerKeys
