import FastPoly.Examples.Char2Degree25TailSlots
import FastPoly.Examples.Char2Degree25HeadChange
import FastPoly.Examples.Char2Degree25LateScalars

/-! Slot facts for the actual partially normalized terminal directions.
The seven earlier coefficient corrections are kept opaque through TailSlots;
only the displayed small middle-coordinate inputs are inspected. -/
namespace FastPoly.Char2Degree25TerminalSlots

open Char2Degree25TailSlots Char2Degree25MiddleKeys Char2Degree25HeadChange
open Char2Degree25MiddleCoordinates (B)
open Char2CoefficientShearTransport (increment)
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def theta (q : Fin 25 → R) (d : R) : R := (B q + 1) * d
def step21 (q : Fin 25 → R) (d : R) : Fin 25 → R :=
  increment (increment q 21 d) 20 (theta q d)

theorem sameBase_of_prefix (q r : Fin 25 → R)
    (h : ∀ i : Fin 25, i.val < 9 → r i = q i) :
    SameBase (Char2Degree25TailCoordinates.keys q) (Char2Degree25TailCoordinates.keys r) := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h6 := h 6 (by omega)
  have h7 := h 7 (by omega)
  constructor
  · rw [raw0, raw0, keys_formula, keys_formula]
    change r 1 + r 2 = q 1 + q 2
    rw [h1, h2]
  · rw [raw1, raw1, keys_formula, keys_formula]
    exact h2
  · rw [raw2, raw2, keys_formula, keys_formula]
    exact h0
  · rw [raw3, raw3, keys_formula, keys_formula]
    exact h3
  · rw [raw5, raw5, keys_formula, keys_formula]
    exact h7
  · rw [raw6, raw6, keys_formula, keys_formula]
    exact h6

theorem nRight_of_prefix (q r : Fin 25 → R)
    (h : ∀ i : Fin 25, i.val < 9 → r i = q i) :
    Char2Degree25Frame.nRight (Char2Degree25TailCoordinates.keys r) =
      Char2Degree25Frame.nRight (Char2Degree25TailCoordinates.keys q) := by
  have ht := (sameBase_of_prefix q r h).t_eq
  have h23 : Char2Degree25TailCoordinates.keys r 23 = Char2Degree25TailCoordinates.keys q 23 := by
    rw [raw23, raw23, keys_formula, keys_formula]
    exact h 8 (by omega)
  rw [Char2Degree25Frame.nRight, Char2Degree25Frame.nRight, ht, h23]

theorem constant_of_value (q r : Fin 25 → R) (h : r 24 = q 24) :
    Char2Degree25TailCoordinates.keys r 24 = Char2Degree25TailCoordinates.keys q 24 := by
  rw [raw24, raw24, keys_formula, keys_formula]
  exact h

theorem B_keys (q : Fin 25 → R) :
    Char2Degree25RowThirteen.B (Char2Degree25TailCoordinates.keys q) = B q := by
  rw [Char2Degree25RowThirteen.B, raw2, raw6, keys_formula]
  rfl

theorem increment_prefix (q : Fin 25 → R) (j : Fin 25) (d : R)
    (hj : 20 ≤ j.val) (i : Fin 25) (hi : i.val < 9) :
    increment q j d i = q i := by
  exact Function.update_of_ne (show i ≠ j by omega) ..

theorem increment_constant (q : Fin 25 → R) (j : Fin 25) (d : R)
    (hj : j ≠ 24) : increment q j d 24 = q 24 :=
  Function.update_of_ne hj.symm ..

theorem step21_prefix (q : Fin 25 → R) (d : R) (i : Fin 25) (hi : i.val < 9) :
    step21 q d i = q i := by
  rw [step21, increment_prefix (increment q 21 d) 20 (theta q d) (by omega) i hi]
  exact increment_prefix q 21 d (by omega) i hi

theorem step21_constant (q : Fin 25 → R) (d : R) : step21 q d 24 = q 24 := rfl

theorem raw4_increment20 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (increment q 20 d) 4 =
      Char2Degree25TailCoordinates.keys q 4 + d := by
  rw [raw4, raw4, keys_formula, keys_formula]
  exact (add_assoc (q 4 + q 5 + q 7) (q 20) d).symm

theorem raw16_increment20 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (increment q 20 d) 16 =
      Char2Degree25TailCoordinates.keys q 16 := by
  rw [raw16, raw16, keys_formula, keys_formula]
  rfl

theorem raw4_step21 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (step21 q d) 4 =
      Char2Degree25TailCoordinates.keys q 4 + theta q d := by
  rw [raw4, raw4, keys_formula, keys_formula]
  exact (add_assoc (q 4 + q 5 + q 7) (q 20) (theta q d)).symm

theorem raw16_step21 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (step21 q d) 16 =
      Char2Degree25TailCoordinates.keys q 16 + d := by
  rw [raw16, raw16, keys_formula, keys_formula]
  rfl

theorem raw4_increment22 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (increment q 22 d) 4 =
      Char2Degree25TailCoordinates.keys q 4 := by
  rw [raw4, raw4, keys_formula, keys_formula]
  rfl

theorem raw16_increment22 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (increment q 22 d) 16 =
      Char2Degree25TailCoordinates.keys q 16 := by
  rw [raw16, raw16, keys_formula, keys_formula]
  rfl

theorem raw7_increment22 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (increment q 22 d) 7 =
      Char2Degree25TailCoordinates.keys q 7 + d := by
  rw [raw7, raw7, keys_formula, keys_formula]
  exact Char2Degree25LateScalars.a7_increment22 q d

theorem raw4_increment23 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (increment q 23 d) 4 =
      Char2Degree25TailCoordinates.keys q 4 := by
  rw [raw4, raw4, keys_formula, keys_formula]
  rfl

theorem raw16_increment23 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (increment q 23 d) 16 =
      Char2Degree25TailCoordinates.keys q 16 := by
  rw [raw16, raw16, keys_formula, keys_formula]
  rfl

theorem raw7_increment23 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (increment q 23 d) 7 =
      Char2Degree25TailCoordinates.keys q 7 := by
  rw [raw7, raw7, keys_formula, keys_formula]
  rfl

theorem raw20_increment23 (q : Fin 25 → R) (d : R) :
    Char2Degree25TailCoordinates.keys (increment q 23 d) 20 =
      Char2Degree25TailCoordinates.keys q 20 + d := by
  rw [raw20, raw20, keys_formula, keys_formula]
  rfl

end FastPoly.Char2Degree25TerminalSlots
