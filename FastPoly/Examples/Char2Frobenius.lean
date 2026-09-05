import FastPoly.Examples.Char2Triangular
import Mathlib.FieldTheory.Perfect

namespace FastPoly.Char2Certificate

variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

/-- The named Frobenius pivot and its explicit inverse in a perfect field.
This assumption holds for every finite field of characteristic two. -/
noncomputable def frobeniusPivot (depth : ℕ) : F ≃ F :=
  (iterateFrobeniusEquiv F 2 depth).toEquiv

theorem frobeniusPivot_apply (depth : ℕ) (x : F) :
    frobeniusPivot depth x = x ^ (2 ^ depth) := rfl

end FastPoly.Char2Certificate
