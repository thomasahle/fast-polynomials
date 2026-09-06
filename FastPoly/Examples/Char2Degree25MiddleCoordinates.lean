import FastPoly.Examples.Char2Degree25PrefixCoordinates

/-!
# The next four supplied degree25 coordinate shears

These are exactly tails9 through12 from the existing symbolic certificate,
written with a shared quadratic tail. Their inverses are explicit coordinate
shears, composed in reverse order. Coordinates13 through24 remain raw
placeholders: this is not yet the complete output coefficient inverse.
-/
namespace FastPoly.Char2Degree25MiddleCoordinates

open Char2Decoder
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2]
abbrev Vector (R : Type*) := Fin 25 → R

def B (q : Vector R) : R := q 0 + q 6
def shared (q : Vector R) : R := q 20 * (q 4 + q 5 + q 7 + q 20)
def tail9 (q : Vector R) : R := shared q + q 11 + q 22 + q 21 + q 12
def tail10 (q : Vector R) : R := B q * (shared q + q 11 + q 22) + q 22
def tail11 (q : Vector R) : R :=
  B q * q 21 + q 20 * (q 0 + q 4 + q 5 + q 6 + q 7 + q 20 + 1) + q 22
def tail12 (q : Vector R) : R := shared q + q 22 + q 21

theorem tail9_independent : Independent (9 : Fin 25) (tail9 (R := R)) := by
  intro q value
  simp only [tail9, shared, Function.update, Fin.reduceEq, dite_false]

theorem tail10_independent : Independent (10 : Fin 25) (tail10 (R := R)) := by
  intro q value
  simp only [tail10, B, shared, Function.update, Fin.reduceEq, dite_false]

theorem tail11_independent : Independent (11 : Fin 25) (tail11 (R := R)) := by
  intro q value
  simp only [tail11, B, Function.update, Fin.reduceEq, dite_false]

theorem tail12_independent : Independent (12 : Fin 25) (tail12 (R := R)) := by
  intro q value
  simp only [tail12, shared, Function.update, Fin.reduceEq, dite_false]

def shear9 : Vector R ≃ Vector R := coordinateShear 9 tail9 tail9_independent
def shear10 : Vector R ≃ Vector R := coordinateShear 10 tail10 tail10_independent
def shear11 : Vector R ≃ Vector R := coordinateShear 11 tail11 tail11_independent
def shear12 : Vector R ≃ Vector R := coordinateShear 12 tail12 tail12_independent

/-- Install the supplied elementary substitutions in reverse composition order. -/
def middleEquiv : Vector R ≃ Vector R :=
  ((shear12.trans shear11).trans shear10).trans shear9

theorem middleEquiv_apply (q : Vector R) :
    middleEquiv q = shear9 (shear10 (shear11 (shear12 q))) := rfl

theorem middleEquiv_symm_apply (q : Vector R) :
    middleEquiv.symm q = shear12 (shear11 (shear10 (shear9 q))) := rfl

theorem decode_encode (q : Vector R) : middleEquiv.symm (middleEquiv q) = q :=
  middleEquiv.symm_apply_apply q

theorem encode_decode (q : Vector R) : middleEquiv (middleEquiv.symm q) = q :=
  middleEquiv.apply_symm_apply q

/-- Complete raw-key equivalence for the first thirteen elementary substitutions. -/
def keyEquiv : Vector R ≃ Vector R :=
  middleEquiv.trans Char2Degree25PrefixCoordinates.keyEquiv

def keys (q : Vector R) : ℕ → R :=
  Char2Degree25PrefixCoordinates.keys (middleEquiv q)

theorem raw_decode_encode (q : Vector R) : keyEquiv.symm (keyEquiv q) = q :=
  keyEquiv.symm_apply_apply q

theorem raw_encode_decode (a : Vector R) : keyEquiv (keyEquiv.symm a) = a :=
  keyEquiv.apply_symm_apply a

/-- Named factored offset expressions; these keep subsequent pivot changes small. -/
def a13 (q : Vector R) : R := q 11 + tail11 q
def a8 (q : Vector R) : R := q 12 + tail12 q
def a7 (q : Vector R) : R := q 9 + a13 q + q 12
def a9 (q : Vector R) : R := q 10 + tail10 q + B q * tail11 q

theorem middle_other (q : Vector R) (i : Fin 25)
    (h9 : i ≠ 9) (h10 : i ≠ 10) (h11 : i ≠ 11) (h12 : i ≠ 12) :
    middleEquiv q i = q i := by
  change Function.update _ 9 _ i = _
  rw [Function.update_of_ne h9]
  change Function.update _ 10 _ i = _
  rw [Function.update_of_ne h10]
  change Function.update _ 11 _ i = _
  rw [Function.update_of_ne h11]
  change Function.update _ 12 _ i = _
  exact Function.update_of_ne h12 ..

theorem middle_eleven (q : Vector R) : middleEquiv q 11 = a13 q := by
  simp only [middleEquiv, shear9, shear10, shear11, shear12, Equiv.trans_apply,
    coordinateShear, Equiv.coe_fn_mk, shear, a13, tail11, B, Function.update, Fin.reduceEq,
    dite_true, dite_false]

theorem middle_twelve (q : Vector R) : middleEquiv q 12 = a8 q := by
  simp only [middleEquiv, shear9, shear10, shear11, shear12, Equiv.trans_apply,
    coordinateShear, Equiv.coe_fn_mk, shear, a8, tail12, shared, Function.update, Fin.reduceEq,
    dite_true, dite_false]

theorem middle_ten (q : Vector R) : middleEquiv q 10 = a9 q := by
  simp only [middleEquiv, shear9, shear10, shear11, shear12, Equiv.trans_apply,
    coordinateShear, Equiv.coe_fn_mk, shear, a9, tail10, tail11, B, shared, Function.update,
    Fin.reduceEq, dite_true, dite_false]
  ring

private theorem nine_collect (a s b t c d e : R) :
    a + (s + (b + t) + c + d + (e + (s + c + d))) = a + (b + t) + e := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem middle_nine (q : Vector R) : middleEquiv q 9 = a7 q := by
  have h : middleEquiv q 9 = q 9 +
      (shared q + (q 11 + tail11 q) + q 22 + q 21 + (q 12 + tail12 q)) := rfl
  rw [h, a7, a13, tail12]
  exact nine_collect _ _ _ _ _ _ _

theorem keys_seven (q : Vector R) : keys q 7 = a7 q := middle_nine q
theorem keys_eight (q : Vector R) : keys q 8 = a8 q := middle_twelve q
theorem keys_nine (q : Vector R) : keys q 9 = a9 q := middle_ten q
theorem keys_thirteen (q : Vector R) : keys q 13 = a13 q := middle_eleven q

end FastPoly.Char2Degree25MiddleCoordinates
