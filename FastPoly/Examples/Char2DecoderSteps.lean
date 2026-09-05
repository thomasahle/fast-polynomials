import Mathlib.Algebra.CharP.Two
import Mathlib.Logic.Equiv.Basic

/-!
# Small, compositional steps for the supplied characteristic-two decoders

The inverse is part of each construction. A tail is treated as an opaque
function, not expanded into a polynomial in the original keys. In particular,
`coordinateShear` is the elementary substitution used by the 24-step certificate
in `char2/verify_n25_unitriangular_symbolic.py`.

These lemmas certify inverse steps, not the circuit-specific coefficient
identities or the independence of the supplied tails. Those remain separate
obligations when instantiating a decoder.
-/

namespace FastPoly.Char2Decoder

-- Deliberately below Lean's default: every proof is a small decoder step.
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Cancel a known tail without looking inside it. -/
theorem cancel_tail (tail value : R) : (tail + value) + tail = value := by
  rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]

/-- The scalar unit pivot and its displayed inverse are the same translation. -/
def unitPivot (tail : R) : R ≃ R where
  toFun value := value + tail
  invFun value := value + tail
  left_inv value := CharTwo.add_cancel_right value tail
  right_inv value := CharTwo.add_cancel_right value tail

/-- A block may depend on earlier recovered quantities; those stay unchanged. -/
def dependentBlock {P A B : Type*} (block : P → A ≃ B) : (P × A) ≃ (P × B) where
  toFun q := (q.1, block q.1 q.2)
  invFun c := (c.1, (block c.1).symm c.2)
  left_inv q := Prod.ext rfl ((block q.1).symm_apply_apply q.2)
  right_inv c := Prod.ext rfl ((block c.1).apply_symm_apply c.2)

section CoordinateShear

variable {ι : Type*} [DecidableEq ι]

/-- The chosen offset must not occur in its own correction. -/
def Independent (pivot : ι) (tail : (ι → R) → R) : Prop :=
  ∀ q value, tail (Function.update q pivot value) = tail q

/-- One of the explicitly supplied elementary changes `b_p = q_i + tail`.
Other keys are preserved; only the named pivot is updated. -/
def shear (pivot : ι) (tail : (ι → R) → R) (q : ι → R) : ι → R :=
  Function.update q pivot (q pivot + tail q)

omit [CharP R 2] in
theorem shear_pivot (pivot : ι) (tail : (ι → R) → R) (q : ι → R) :
    shear pivot tail q pivot = q pivot + tail q := Function.update_self ..

omit [CharP R 2] in
theorem shear_other (pivot : ι) (tail : (ι → R) → R) (q : ι → R)
    (j : ι) (h : j ≠ pivot) : shear pivot tail q j = q j :=
  Function.update_of_ne h ..

omit [CharP R 2] in
theorem tail_shear (pivot : ι) (tail : (ι → R) → R)
    (ht : Independent pivot tail) (q : ι → R) :
    tail (shear pivot tail q) = tail q := ht q _

theorem shear_involutive (pivot : ι) (tail : (ι → R) → R)
    (ht : Independent pivot tail) : Function.Involutive (shear pivot tail) := by
  intro q
  funext j
  by_cases h : j = pivot
  · subst j
    rw [shear_pivot, shear_pivot, tail_shear pivot tail ht,
      CharTwo.add_cancel_right]
  · rw [shear_other pivot tail _ j h, shear_other pivot tail _ j h]

/-- Compose these equivalences in the supplied order. `Equiv.trans` reverses
the order of the explicit inverse steps; no combined key expression is needed. -/
def coordinateShear (pivot : ι) (tail : (ι → R) → R)
    (ht : Independent pivot tail) : (ι → R) ≃ (ι → R) where
  toFun := shear pivot tail
  invFun := shear pivot tail
  left_inv := shear_involutive pivot tail ht
  right_inv := shear_involutive pivot tail ht

omit [CommRing R] [CharP R 2] in
/-- An independence certificate can be built by structural recursion on a
small expression, preserving already-certified subexpressions. -/
theorem independent_const (pivot : ι) (c : R) : Independent pivot (fun _ => c) :=
  fun _ _ => rfl

omit [CommRing R] [CharP R 2] in
theorem independent_read (pivot j : ι) (h : j ≠ pivot) :
    Independent (R := R) pivot (fun q => q j) :=
  fun _ _ => Function.update_of_ne h ..

omit [CharP R 2] in
theorem independent_add (pivot : ι) (f g : (ι → R) → R)
    (hf : Independent pivot f) (hg : Independent pivot g) :
    Independent pivot (fun q => f q + g q) := by
  intro q value
  exact congrArg₂ (· + ·) (hf q value) (hg q value)

omit [CharP R 2] in
theorem independent_mul (pivot : ι) (f g : (ι → R) → R)
    (hf : Independent pivot f) (hg : Independent pivot g) :
    Independent pivot (fun q => f q * g q) := by
  intro q value
  exact congrArg₂ (· * ·) (hf q value) (hg q value)

omit [CharP R 2] in
theorem independent_pow (pivot : ι) (f : (ι → R) → R)
    (hf : Independent pivot f) (n : ℕ) :
    Independent pivot (fun q => f q ^ n) := by
  intro q value
  exact congrArg (· ^ n) (hf q value)

end CoordinateShear

end FastPoly.Char2Decoder
