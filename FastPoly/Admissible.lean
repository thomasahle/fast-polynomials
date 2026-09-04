import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# `d`-admissibility

The paper's global characteristic hypothesis (`appendix:constructions`, final form:
characteristic `0` or characteristic `p > n`), packaged as the form the decoders actually
consume: every integer `1 ≤ n ≤ d` is a unit of the coefficient ring.  Composite pivot
slopes (`k(k-1)`, `k²`, `2m`, …) are obtained by multiplying unit factors that are each
at most `d` — never by requiring the composite value itself to be at most `d`.
-/

namespace FastPoly

/-- `d`-admissibility: every integer `1 ≤ n ≤ d` is a unit of `R`.  For a field this is
implied by characteristic `0`, and by characteristic `p > d`. -/
def Admissible (R : Type*) [CommRing R] (d : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ d → IsUnit (n : R)

namespace Admissible

variable {R : Type*} [CommRing R] {d e : ℕ}

theorem mono (h : Admissible R d) (he : e ≤ d) : Admissible R e :=
  fun n h1 h2 => h n h1 (le_trans h2 he)

theorem isUnit_cast (h : Admissible R d) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ d) :
    IsUnit (n : R) :=
  h n h1 h2

/-- Composite slopes: a product of two admissible integers is a unit (each factor at most
`d`; the product may exceed `d`). -/
theorem isUnit_mul_cast (h : Admissible R d) {m n : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ d)
    (hn1 : 1 ≤ n) (hn : n ≤ d) : IsUnit ((m * n : ℕ) : R) := by
  rw [Nat.cast_mul]
  exact (h m hm1 hm).mul (h n hn1 hn)

theorem isUnit_two (h : Admissible R d) (h2 : 2 ≤ d) : IsUnit (2 : R) := by
  have h' := h 2 (by omega) h2
  rwa [Nat.cast_ofNat] at h'

end Admissible

/-- Characteristic zero fields are `d`-admissible for every `d`. -/
theorem admissible_of_charZero (F : Type*) [Field F] [CharZero F] (d : ℕ) :
    Admissible F d :=
  fun n h1 _ => isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by omega))

/-- A field of characteristic `p > d` is `d`-admissible. -/
theorem admissible_of_charP (F : Type*) [Field F] (p : ℕ) [CharP F p] {d : ℕ}
    (hd : d < p) : Admissible F d := by
  intro n h1 h2
  refine isUnit_iff_ne_zero.2 (fun h0 => ?_)
  have hdvd : p ∣ n := (CharP.cast_eq_zero_iff F p n).1 h0
  have hle : p ≤ n := Nat.le_of_dvd (by omega) hdvd
  omega

end FastPoly
