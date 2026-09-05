import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Tactic.FinCases

/-!
# The explicit degree-23 polynomial key-coordinate change

This is (A.37)--(A.38) of `char2/verify_n23.py`, before the row-eight
correction to `a19`. Each auxiliary quantity is named. The two compositions
are checked by cancelling the displayed corrections, never by expanding the
resulting polynomials in the original keys.

`coreEquiv` leaves coordinate 14 in slot 19. The separate circuit-specific
row-eight shear is still required to turn that slot into the output coefficient.
This module alone is not the complete coefficient decoder.
-/

namespace FastPoly.Char2Degree23Coordinates

open Char2Decoder
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2]

abbrev Vector (R : Type*) := Fin 23 → R

def eta (q : Vector R) : R := q 7 * q 16 + q 16 ^ 2 + q 20
def rho (q : Vector R) : R := (q 0 + q 8) * eta q + q 7 * q 16 + q 16 ^ 2
def gamma (q : Vector R) : R := q 0 + q 3 + q 5 + q 6 + q 8 + q 9 + q 11 + 1
def tau (q : Vector R) : R :=
  q 16 ^ 4 + (gamma q + q 7 ^ 2) * q 16 ^ 2 + (q 7 * gamma q + 1) * q 16 +
    q 20 ^ 2 + gamma q * q 20 + q 18 + q 21

def a12 (q : Vector R) : R := q 15 + q 16
def a11 (q : Vector R) : R := q 13 + tau q
def a10 (q : Vector R) : R := q 12 + (rho q + q 16 + a11 q + a12 q)
def a9 (q : Vector R) : R := q 10 + (rho q + a11 q + q 20 + q 18)
def a8 (q : Vector R) : R := q 9 + (q 16 ^ 2 + q 7 * q 16 + a10 q + q 20 + q 18)

/-- The supplied inverse key formulas, with the row-eight shear not yet applied. -/
def keysCore (q : Vector R) (i : Fin 23) : R :=
  match i.val with
  | 0 => q 2
  | 1 => q 1 + q 2
  | 2 => q 0
  | 3 => q 3 + (q 5 + q 6)
  | 4 => q 4 + (q 7 + q 5 + q 6)
  | 5 => q 16
  | 6 => q 8
  | 7 => q 11 + eta q
  | 8 => a8 q
  | 9 => a9 q
  | 10 => a10 q
  | 11 => a11 q
  | 12 => a12 q
  | 13 => q 17 + q 18
  | 14 => q 7 + q 16
  | 15 => q 20
  | 16 => q 18
  | 17 => q 21
  | 18 => q 5
  | 19 => q 14
  | 20 => q 6
  | 21 => q 19
  | _ => q 22

def q3 (a : Vector R) : R := a 3 + (a 18 + a 20)
def q7 (a : Vector R) : R := a 5 + a 14
def q9 (a : Vector R) : R := a 8 + (a 5 ^ 2 + q7 a * a 5 + a 10 + a 15 + a 16)
def q11 (a : Vector R) : R := a 7 + (q7 a * a 5 + a 5 ^ 2 + a 15)
def rhoKeys (a : Vector R) : R :=
  (a 2 + a 6) * (q7 a * a 5 + a 5 ^ 2 + a 15) + q7 a * a 5 + a 5 ^ 2
def gammaKeys (a : Vector R) : R :=
  a 2 + q3 a + a 18 + a 20 + a 6 + q9 a + q11 a + 1
def tauKeys (a : Vector R) : R :=
  a 5 ^ 4 + (gammaKeys a + q7 a ^ 2) * a 5 ^ 2 + (q7 a * gammaKeys a + 1) * a 5 +
    a 15 ^ 2 + gammaKeys a * a 15 + a 16 + a 17

/-- The forward coordinate map, grouped to expose exactly the inverse pivots. -/
def coordinates (a : Vector R) (i : Fin 23) : R :=
  match i.val with
  | 0 => a 2
  | 1 => a 0 + a 1
  | 2 => a 0
  | 3 => q3 a
  | 4 => a 4 + (q7 a + a 18 + a 20)
  | 5 => a 18
  | 6 => a 20
  | 7 => q7 a
  | 8 => a 6
  | 9 => q9 a
  | 10 => a 9 + (rhoKeys a + a 11 + a 15 + a 16)
  | 11 => q11 a
  | 12 => a 10 + (rhoKeys a + a 5 + a 11 + a 12)
  | 13 => a 11 + tauKeys a
  | 14 => a 19
  | 15 => a 5 + a 12
  | 16 => a 5
  | 17 => a 13 + a 16
  | 18 => a 16
  | 19 => a 21
  | 20 => a 15
  | 21 => a 17
  | _ => a 22

theorem q3_keysCore (q : Vector R) : q3 (keysCore q) = q 3 :=
  CharTwo.add_cancel_right _ _

theorem q7_keysCore (q : Vector R) : q7 (keysCore q) = q 7 := by
  change q 16 + (q 7 + q 16) = q 7
  rw [add_comm (q 7), CharTwo.add_cancel_left]

theorem q9_keysCore (q : Vector R) : q9 (keysCore q) = q 9 := by
  change a8 q + (q 16 ^ 2 + q7 (keysCore q) * q 16 + a10 q + q 20 + q 18) = q 9
  rw [q7_keysCore]
  exact CharTwo.add_cancel_right _ _

theorem q11_keysCore (q : Vector R) : q11 (keysCore q) = q 11 := by
  change (q 11 + eta q) + (q7 (keysCore q) * q 16 + q 16 ^ 2 + q 20) = q 11
  rw [q7_keysCore]
  exact CharTwo.add_cancel_right _ _

theorem rhoKeys_keysCore (q : Vector R) : rhoKeys (keysCore q) = rho q := by
  change (q 0 + q 8) * (q7 (keysCore q) * q 16 + q 16 ^ 2 + q 20) +
    q7 (keysCore q) * q 16 + q 16 ^ 2 = rho q
  rw [q7_keysCore]
  rfl

theorem gammaKeys_keysCore (q : Vector R) : gammaKeys (keysCore q) = gamma q := by
  change q 0 + q3 (keysCore q) + q 5 + q 6 + q 8 + q9 (keysCore q) +
    q11 (keysCore q) + 1 = gamma q
  rw [q3_keysCore, q9_keysCore, q11_keysCore]
  rfl

theorem tauKeys_keysCore (q : Vector R) : tauKeys (keysCore q) = tau q := by
  change q 16 ^ 4 + (gammaKeys (keysCore q) + q7 (keysCore q) ^ 2) * q 16 ^ 2 +
    (q7 (keysCore q) * gammaKeys (keysCore q) + 1) * q 16 + q 20 ^ 2 +
    gammaKeys (keysCore q) * q 20 + q 18 + q 21 = tau q
  rw [gammaKeys_keysCore, q7_keysCore]
  rfl

theorem coordinates_keysCore (q : Vector R) : coordinates (keysCore q) = q := by
  funext i
  fin_cases i
  · rfl
  · change q 2 + (q 1 + q 2) = q 1
    rw [add_comm (q 1), CharTwo.add_cancel_left]
  · rfl
  · exact q3_keysCore q
  · change (q 4 + (q 7 + q 5 + q 6)) + (q7 (keysCore q) + q 5 + q 6) = q 4
    rw [q7_keysCore, CharTwo.add_cancel_right]
  · rfl
  · rfl
  · exact q7_keysCore q
  · rfl
  · exact q9_keysCore q
  · change a9 q + (rhoKeys (keysCore q) + a11 q + q 20 + q 18) = q 10
    rw [rhoKeys_keysCore]
    exact CharTwo.add_cancel_right _ _
  · exact q11_keysCore q
  · change a10 q + (rhoKeys (keysCore q) + q 16 + a11 q + a12 q) = q 12
    rw [rhoKeys_keysCore]
    exact CharTwo.add_cancel_right _ _
  · change a11 q + tauKeys (keysCore q) = q 13
    rw [tauKeys_keysCore]
    exact CharTwo.add_cancel_right _ _
  · rfl
  · change q 16 + (q 15 + q 16) = q 15
    rw [add_comm (q 15), CharTwo.add_cancel_left]
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

omit [CharP R 2] in
theorem rho_coordinates (a : Vector R) : rho (coordinates a) = rhoKeys a := rfl

omit [CharP R 2] in
theorem gamma_coordinates (a : Vector R) : gamma (coordinates a) = gammaKeys a := rfl

omit [CharP R 2] in
theorem tau_coordinates (a : Vector R) : tau (coordinates a) = tauKeys a := rfl

theorem a12_coordinates (a : Vector R) : a12 (coordinates a) = a 12 :=
  cancel_tail _ _

theorem a11_coordinates (a : Vector R) : a11 (coordinates a) = a 11 := by
  change (a 11 + tauKeys a) + tau (coordinates a) = a 11
  rw [tau_coordinates, CharTwo.add_cancel_right]

theorem a10_coordinates (a : Vector R) : a10 (coordinates a) = a 10 := by
  change (a 10 + (rhoKeys a + a 5 + a 11 + a 12)) +
    (rho (coordinates a) + a 5 + a11 (coordinates a) + a12 (coordinates a)) = a 10
  rw [rho_coordinates, a11_coordinates, a12_coordinates, CharTwo.add_cancel_right]

theorem a9_coordinates (a : Vector R) : a9 (coordinates a) = a 9 := by
  change (a 9 + (rhoKeys a + a 11 + a 15 + a 16)) +
    (rho (coordinates a) + a11 (coordinates a) + a 15 + a 16) = a 9
  rw [rho_coordinates, a11_coordinates, CharTwo.add_cancel_right]

theorem a8_coordinates (a : Vector R) : a8 (coordinates a) = a 8 := by
  change (a 8 + (a 5 ^ 2 + q7 a * a 5 + a 10 + a 15 + a 16)) +
    (a 5 ^ 2 + q7 a * a 5 + a10 (coordinates a) + a 15 + a 16) = a 8
  rw [a10_coordinates, CharTwo.add_cancel_right]

theorem keysCore_coordinates (a : Vector R) : keysCore (coordinates a) = a := by
  funext i
  fin_cases i
  · rfl
  · exact cancel_tail _ _
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · exact a8_coordinates a
  · exact a9_coordinates a
  · exact a10_coordinates a
  · exact a11_coordinates a
  · exact a12_coordinates a
  · exact CharTwo.add_cancel_right _ _
  · exact cancel_tail _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The supplied polynomial key change with its explicit two-sided inverse.
The subsequent row-eight shear must be composed separately. -/
def coreEquiv : Vector R ≃ Vector R where
  toFun := keysCore
  invFun := coordinates
  left_inv := coordinates_keysCore
  right_inv := keysCore_coordinates

end FastPoly.Char2Degree23Coordinates
