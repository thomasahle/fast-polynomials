import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Tactic.FinCases

/-! The exact first-nine-step partial coordinate map from the existing degree-25
certificate. Coordinates q9 through q24 are still raw placeholders in decoder
pivot order, not the final fully normalized coordinates. The linear map below
has a supplied inverse checked in both directions; no circuit is expanded. -/

namespace FastPoly.Char2Degree25PrefixCoordinates

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2]

abbrev Vector (R : Type*) := Fin 25 → R

/-- Raw gate offsets after the first nine existing elementary coordinate steps. -/
def keys (q : Vector R) : ℕ → R
  | 0 => q 1 + q 2
  | 1 => q 2
  | 2 => q 0
  | 3 => q 3
  | 4 => q 4 + q 5 + q 7 + q 20
  | 5 => q 7
  | 6 => q 6
  | 7 => q 9
  | 8 => q 12
  | 9 => q 10
  | 10 => q 14
  | 11 => q 15
  | 12 => q 5 + q 8
  | 13 => q 11
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

/-- The same supplied map, restricted to the twenty-five actual raw slots. -/
def rawKeys (q : Vector R) (i : Fin 25) : R := keys q i.val

/-- Explicit inverse: the final sixteen coordinates remain raw placeholders. -/
def coordinates (a : Vector R) (i : Fin 25) : R :=
  match i.val with
  | 0 => a 2
  | 1 => a 0 + a 1
  | 2 => a 1
  | 3 => a 3
  | 4 => a 4 + a 5 + a 12 + a 18 + a 23
  | 5 => a 12 + a 23
  | 6 => a 6
  | 7 => a 5
  | 8 => a 23
  | 9 => a 7
  | 10 => a 9
  | 11 => a 13
  | 12 => a 8
  | 13 => a 17
  | 14 => a 10
  | 15 => a 11
  | 16 => a 15
  | 17 => a 19
  | 18 => a 21
  | 19 => a 22
  | 20 => a 18
  | 21 => a 16
  | 22 => a 14
  | 23 => a 20
  | 24 => a 24
  | _ => 0

theorem coordinates_rawKeys (q : Vector R) : coordinates (rawKeys q) = q := by
  funext i
  fin_cases i <;> first
    | rfl
    | simp only [coordinates, rawKeys, keys, add_assoc, add_comm, add_left_comm,
        CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add] <;> rfl

theorem rawKeys_coordinates (a : Vector R) : rawKeys (coordinates a) = a := by
  funext i
  fin_cases i <;> first
    | rfl
    | simp only [coordinates, rawKeys, keys, add_assoc, add_comm, add_left_comm,
        CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add] <;> rfl

/-- This is a raw-key equivalence, not a coefficient/output inverse claim. -/
def keyEquiv : Vector R ≃ Vector R where
  toFun := rawKeys
  invFun := coordinates
  left_inv := coordinates_rawKeys
  right_inv := rawKeys_coordinates

def increment (q : Vector R) (i : Fin 25) (delta : R) : Vector R :=
  Function.update q i (q i + delta)

end FastPoly.Char2Degree25PrefixCoordinates
