import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Tactic.FinCases

/-!
# Explicit degree-19 key-coordinate inverse

These are the existing formulas (A.15)--(A.16) in
`char2/verify_n19_unitriangular_symbolic.py`. Sums are grouped so that each
proof cancels exactly the displayed known correction. No expression in the
original nineteen keys is expanded or normalized.

This equivalence is the key-coordinate change, not the thirteen remaining
coefficient pivots of the inner crown.
-/

namespace FastPoly.Char2Degree19Coordinates

set_option maxHeartbeats 20000
open Char2Decoder

variable {R : Type*} [CommRing R] [CharP R 2]

abbrev Vector (R : Type*) := Fin 19 → R

def a4 (q : Vector R) : R := q 12 + q 14
def a9 (q : Vector R) : R := q 11 + a4 q
def a14 (q : Vector R) : R := q 10 + q 12
def a15 (q : Vector R) : R := q 7 + (a14 q + q 13 + q 8 ^ 2 + q 8)

/-- The supplied inverse formulas, with already recovered offsets kept named. -/
def keys (q : Vector R) (i : Fin 19) : R :=
  match i.val with
  | 0 => q 5
  | 1 => q 4 + q 5
  | 2 => q 3
  | 3 => q 8
  | 4 => a4 q
  | 5 => q 14
  | 6 => q 9
  | 7 => q 6 + (q 8 + q 9)
  | 8 => q 13
  | 9 => a9 q
  | 10 => q 0
  | 11 => q 1
  | 12 => q 16
  | 13 => q 17
  | 14 => a14 q
  | 15 => a15 q
  | 16 => q 2
  | 17 => q 15
  | _ => q 18

def q12 (a : Vector R) : R := a 4 + a 5

/-- The forward formulas, regrouped around the same named corrections. -/
def coordinates (a : Vector R) (i : Fin 19) : R :=
  match i.val with
  | 0 => a 10
  | 1 => a 11
  | 2 => a 16
  | 3 => a 2
  | 4 => a 1 + a 0
  | 5 => a 0
  | 6 => a 7 + (a 3 + a 6)
  | 7 => a 15 + (a 14 + a 8 + a 3 ^ 2 + a 3)
  | 8 => a 3
  | 9 => a 6
  | 10 => a 14 + q12 a
  | 11 => a 9 + a 4
  | 12 => q12 a
  | 13 => a 8
  | 14 => a 5
  | 15 => a 17
  | 16 => a 12
  | 17 => a 13
  | _ => a 18

theorem q12_keys (q : Vector R) : q12 (keys q) = q 12 :=
  CharTwo.add_cancel_right _ _

theorem coordinates_keys (q : Vector R) : coordinates (keys q) = q := by
  funext i
  fin_cases i
  · rfl
  · rfl
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

theorem a4_coordinates (a : Vector R) : a4 (coordinates a) = a 4 :=
  CharTwo.add_cancel_right _ _

theorem a14_coordinates (a : Vector R) : a14 (coordinates a) = a 14 :=
  CharTwo.add_cancel_right _ _

theorem a9_coordinates (a : Vector R) : a9 (coordinates a) = a 9 := by
  change (a 9 + a 4) + a4 (coordinates a) = a 9
  rw [a4_coordinates, CharTwo.add_cancel_right]

theorem a15_coordinates (a : Vector R) : a15 (coordinates a) = a 15 := by
  change (a 15 + (a 14 + a 8 + a 3 ^ 2 + a 3)) +
    (a14 (coordinates a) + a 8 + a 3 ^ 2 + a 3) = a 15
  rw [a14_coordinates, CharTwo.add_cancel_right]

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
  · rfl
  · rfl
  · rfl

/-- The actual two-sided polynomial coordinate inverse used by the verifier. -/
def coordinateEquiv : Vector R ≃ Vector R where
  toFun := coordinates
  invFun := keys
  left_inv := keys_coordinates
  right_inv := coordinates_keys

end FastPoly.Char2Degree19Coordinates
