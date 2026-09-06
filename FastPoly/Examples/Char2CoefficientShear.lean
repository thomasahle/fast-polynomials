import FastPoly.Examples.Char2UpdateTriangular
import Mathlib.Algebra.Polynomial.Basic

/-!
# Explicit normalization of a supplied unit coefficient pivot

The correction is two evaluations of the existing circuit: zero the pivot,
then zero all coordinates not preceding it. No correction polynomial is
expanded. The resulting coordinate shear is its own explicit inverse.
-/

namespace FastPoly.Char2CoefficientShear

open Polynomial

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] {n : ℕ}

def zeroAt (j : Fin n) (q : Fin n → R) : Fin n → R :=
  Function.update q j 0

def prefixAt (j : Fin n) (q : Fin n → R) : Fin n → R :=
  Char2UpdateTriangular.knownPrefix j q

def baseline (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
    (q : Fin n → R) : R := (f (prefixAt j q)).coeff m

def tail (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
    (q : Fin n → R) : R :=
  (f (zeroAt j q)).coeff m + baseline f j m q

theorem zeroAt_update (j : Fin n) (q : Fin n → R) (value : R) :
    zeroAt j (Function.update q j value) = zeroAt j q := by
  unfold zeroAt
  exact Function.update_idem (a := j) value 0 q

theorem prefix_congr (j : Fin n) (q r : Fin n → R)
    (h : ∀ k, k < j → q k = r k) : prefixAt j q = prefixAt j r := by
  funext k
  by_cases hk : k < j
  · simp only [prefixAt, Char2UpdateTriangular.knownPrefix, hk, if_true]
    exact h k hk
  · simp only [prefixAt, Char2UpdateTriangular.knownPrefix, hk, if_false]

theorem prefix_update (j k : Fin n) (hjk : j ≤ k) (q : Fin n → R)
    (value : R) : prefixAt j (Function.update q k value) = prefixAt j q := by
  apply prefix_congr
  intro i hi
  exact Function.update_of_ne (ne_of_lt (lt_of_lt_of_le hi hjk)) ..

theorem baseline_congr (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
    (q r : Fin n → R) (h : ∀ k, k < j → q k = r k) :
    baseline f j m q = baseline f j m r := by
  unfold baseline
  rw [prefix_congr j q r h]

theorem baseline_update (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
    (k : Fin n) (hjk : j ≤ k) (q : Fin n → R) (value : R) :
    baseline f j m (Function.update q k value) = baseline f j m q := by
  unfold baseline
  rw [prefix_update j k hjk]

theorem tail_independent (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ) :
    Char2Decoder.Independent j (tail f j m) := by
  intro q value
  unfold tail
  rw [zeroAt_update, baseline_update f j m j (le_refl j)]

/-- The inverse uses exactly the same displayed coefficient correction. -/
def coordinateShear (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ) :
    (Fin n → R) ≃ (Fin n → R) :=
  Char2Decoder.coordinateShear j (tail f j m) (tail_independent f j m)

theorem coordinateShear_apply (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
    (q : Fin n → R) :
    coordinateShear f j m q = Function.update q j (q j + tail f j m q) := rfl

theorem coordinateShear_symm_apply (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
    (q : Fin n → R) :
    (coordinateShear f j m).symm q =
      Function.update q j (q j + tail f j m q) := rfl

theorem decode_encode (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
    (q : Fin n → R) :
    (coordinateShear f j m).symm (coordinateShear f j m q) = q :=
  (coordinateShear f j m).symm_apply_apply q

theorem encode_decode (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
    (q : Fin n → R) :
    coordinateShear f j m ((coordinateShear f j m).symm q) = q :=
  (coordinateShear f j m).apply_symm_apply q

variable (f : (Fin n → R) → R[X]) (j : Fin n) (m : ℕ)
  (hu : ∀ (q : Fin n → R) (δ : R),
    (f (Function.update q j (q j + δ))).coeff m = (f q).coeff m + δ)

include hu

/-- The supplied unit update recovers the exact affine dependence on the pivot. -/
theorem coeff_zeroAt (q : Fin n → R) :
    (f q).coeff m = q j + (f (zeroAt j q)).coeff m := by
  have he : Function.update (zeroAt j q) j ((zeroAt j q) j + q j) = q := by
    simp only [zeroAt, Function.update_self, zero_add,
      Function.update_idem, Function.update_eq_self]
  have h := hu (zeroAt j q) (q j)
  rw [he] at h
  exact h.trans (add_comm _ _)

theorem coefficient_normalized (q : Fin n → R) :
    (f (coordinateShear f j m q)).coeff m = q j + baseline f j m q := by
  rw [coordinateShear_apply, hu, coeff_zeroAt f j m hu q]
  unfold tail
  rw [add_assoc, ← add_assoc ((f (zeroAt j q)).coeff m),
    CharTwo.add_self_eq_zero, zero_add]

/-- Agreement outside the pivot makes its unit coefficient an injective readout. -/
theorem coefficient_ext (q r : Fin n → R)
    (hout : ∀ k, k ≠ j → q k = r k)
    (hrow : (f q).coeff m = (f r).coeff m) : q = r := by
  have hz : zeroAt j q = zeroAt j r := by
    funext k
    by_cases hk : k = j
    · subst k
      simp only [zeroAt, Function.update_self]
    · simp only [zeroAt, Function.update_of_ne hk]
      exact hout k hk
  rw [coeff_zeroAt f j m hu q, coeff_zeroAt f j m hu r, hz] at hrow
  have hj : q j = r j := add_right_cancel hrow
  funext k
  by_cases hk : k = j
  · subst k
    exact hj
  · exact hout k hk

/-- A coupled change is the displayed shear once its other slots and normalized
coefficient are checked. This identifies it without expanding the correction. -/
theorem coordinateShear_unique (q b : Fin n → R)
    (hout : ∀ k, k ≠ j → b k = q k)
    (hrow : (f b).coeff m = q j + baseline f j m q) :
    b = coordinateShear f j m q := by
  apply coefficient_ext f j m hu
  · intro k hk
    rw [coordinateShear_apply, Function.update_of_ne hk]
    exact hout k hk
  · exact hrow.trans (coefficient_normalized f j m hu q).symm

end FastPoly.Char2CoefficientShear
