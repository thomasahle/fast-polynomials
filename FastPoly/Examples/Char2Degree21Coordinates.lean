import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Tactic.FinCases

/-!
# The supplied two-sided degree-21 key-coordinate inverse

These are (A.26)--(A.29), as recorded in
`char2/verify_n21_unitriangular_symbolic.py`.  The nonlinear correction to
raw offset fifteen remains named, and each composition cancels that same
displayed correction.  No coefficient baseline or circuit is expanded.
-/

namespace FastPoly.Char2Degree21Coordinates

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2]

abbrev Vector (R : Type*) := Fin 21 → R

def a4 (q : Vector R) : R := q 12 + q 14
def a9 (q : Vector R) : R := q 11 + a4 q
def a14 (q : Vector R) : R := q 10 + q 12

/-- The displayed correction in (A.29), without expanding known offsets. -/
def a15Correction (q : Vector R) : R :=
  q 8 + q 8 ^ 2 + q 0 * q 8 + q 5 * q 8 + a14 q + q 13 + q 3 ^ 2 + q 3

def a15 (q : Vector R) : R := q 7 + a15Correction q

/-- The exact supplied polynomial inverse from normalized to original raw keys. -/
def keys (q : Vector R) (i : Fin 21) : R :=
  match i.val with
  | 0 => q 2
  | 1 => q 1 + q 2
  | 2 => q 0
  | 3 => q 3
  | 4 => a4 q
  | 5 => q 14
  | 6 => q 9
  | 7 => q 6 + (q 8 + q 3 + q 9)
  | 8 => q 13
  | 9 => a9 q
  | 10 => q 5
  | 11 => q 8
  | 12 => q 18
  | 13 => q 19
  | 14 => a14 q
  | 15 => a15 q
  | 16 => q 4 + q 16
  | 17 => q 17
  | 18 => q 16
  | 19 => q 15
  | _ => q 20

def q12 (a : Vector R) : R := a 4 + a 5

/-- The forward seventh-coordinate correction, in the same grouping. -/
def q7Correction (a : Vector R) : R :=
  a 11 + a 11 ^ 2 + a 2 * a 11 + a 10 * a 11 + a 14 + a 8 + a 3 ^ 2 + a 3

/-- The supplied forward change, regrouped only to expose its cancellations. -/
def coordinates (a : Vector R) (i : Fin 21) : R :=
  match i.val with
  | 0 => a 2
  | 1 => a 1 + a 0
  | 2 => a 0
  | 3 => a 3
  | 4 => a 16 + a 18
  | 5 => a 10
  | 6 => a 7 + (a 11 + a 3 + a 6)
  | 7 => a 15 + q7Correction a
  | 8 => a 11
  | 9 => a 6
  | 10 => a 14 + q12 a
  | 11 => a 9 + a 4
  | 12 => q12 a
  | 13 => a 8
  | 14 => a 5
  | 15 => a 19
  | 16 => a 18
  | 17 => a 17
  | 18 => a 12
  | 19 => a 13
  | _ => a 20

theorem q12_keys (q : Vector R) : q12 (keys q) = q 12 :=
  CharTwo.add_cancel_right _ _

omit [CharP R 2] in
theorem q7Correction_keys (q : Vector R) : q7Correction (keys q) = a15Correction q := rfl

theorem coordinates_keys (q : Vector R) : coordinates (keys q) = q := by
  funext i
  fin_cases i
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · rfl
  · change a14 q + q12 (keys q) = q 10
    rw [q12_keys]
    exact CharTwo.add_cancel_right _ _
  · exact CharTwo.add_cancel_right _ _
  · exact q12_keys q
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem a4_coordinates (a : Vector R) : a4 (coordinates a) = a 4 :=
  CharTwo.add_cancel_right _ _

theorem a14_coordinates (a : Vector R) : a14 (coordinates a) = a 14 :=
  CharTwo.add_cancel_right _ _

theorem a9_coordinates (a : Vector R) : a9 (coordinates a) = a 9 := by
  change (a 9 + a 4) + a4 (coordinates a) = a 9
  rw [a4_coordinates, CharTwo.add_cancel_right]

/-- The nonlinear correction is preserved literally after its named affine read. -/
theorem a15Correction_coordinates (a : Vector R) :
    a15Correction (coordinates a) = q7Correction a := by
  change a 11 + a 11 ^ 2 + a 2 * a 11 + a 10 * a 11 +
    a14 (coordinates a) + a 8 + a 3 ^ 2 + a 3 = q7Correction a
  rw [a14_coordinates]
  rfl

theorem a15_coordinates (a : Vector R) : a15 (coordinates a) = a 15 := by
  change (a 15 + q7Correction a) + a15Correction (coordinates a) = a 15
  rw [a15Correction_coordinates, CharTwo.add_cancel_right]

theorem keys_coordinates (a : Vector R) : keys (coordinates a) = a := by
  funext i
  fin_cases i
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · rfl
  · exact a4_coordinates a
  · rfl
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · exact a9_coordinates a
  · rfl
  · rfl
  · rfl
  · rfl
  · exact a14_coordinates a
  · exact a15_coordinates a
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · rfl
  · rfl
  · rfl

/-- Both compositions of the verifier's explicit polynomial key change. -/
def coordinateEquiv : Vector R ≃ Vector R where
  toFun := coordinates
  invFun := keys
  left_inv := keys_coordinates
  right_inv := coordinates_keys

end FastPoly.Char2Degree21Coordinates
