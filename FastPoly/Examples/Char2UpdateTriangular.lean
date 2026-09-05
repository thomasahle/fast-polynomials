import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega

/-!
# Explicit triangular inversion from single-coordinate identities

A circuit certificate only needs to show that changing a later coordinate
preserves an earlier row, and that changing the current coordinate has unit
slope. Finite coordinate resets then justify the named baseline. The inverse
is the actual recursive back-substitution, with both compositions checked.
No baseline polynomial is expanded and no finite-field enumeration is used.
-/

namespace FastPoly.Char2UpdateTriangular

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] {n : ℕ}

abbrev Vector (n : ℕ) (R : Type*) := Fin n → R

def FutureInvariant (f : Vector n R → Vector n R) : Prop :=
  ∀ q i j, i < j → ∀ value, f (Function.update q j value) i = f q i

def UnitPivot (f : Vector n R → Vector n R) : Prop :=
  ∀ q i value, f (Function.update q i value) i = f q i + q i + value

/-- Keep only the coordinates already read by the inverse. -/
def knownPrefix (i : Fin n) (q : Vector n R) : Vector n R :=
  fun j => if j < i then q j else 0

omit [CommRing R] [CharP R 2] in
/-- Telescope a supplied single-coordinate invariance identity. This is an
induction on the set of coordinates, not on possible field values. -/
theorem invariant_resets (f : Vector n R → Vector n R) (hf : FutureInvariant f)
    (i : Fin n) (q r : Vector n R) (s : Finset (Fin n))
    (hs : ∀ j ∈ s, i < j) : f (s.piecewise r q) i = f q i := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.piecewise_empty]
  | @insert j s hj ih =>
    rw [Finset.piecewise_insert,
      hf _ i j (hs j (Finset.mem_insert_self j s)) (r j)]
    exact ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))

omit [CommRing R] [CharP R 2] in
theorem row_congr (f : Vector n R → Vector n R) (hf : FutureInvariant f)
    (i : Fin n) (q r : Vector n R) (h : ∀ j, j ≤ i → q j = r j) : f q i = f r i := by
  let s : Finset (Fin n) := Finset.univ.filter (fun j => i < j)
  have hs : ∀ j ∈ s, i < j := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have he : s.piecewise r q = r := by
    funext j
    by_cases hij : i < j
    · simp only [s, Finset.piecewise, Finset.mem_filter, Finset.mem_univ,
        true_and, hij, if_true]
    · simp only [s, Finset.piecewise, Finset.mem_filter, Finset.mem_univ,
        true_and, hij, if_false]
      exact h j (le_of_not_gt hij)
  rw [← invariant_resets f hf i q r s hs, he]

omit [CharP R 2] in
/-- The baseline is an evaluation of the named circuit at its prefix, not
a flattened expression in the original parameters. -/
theorem row_eq (f : Vector n R → Vector n R) (hf : FutureInvariant f)
    (hu : UnitPivot f) (q : Vector n R) (i : Fin n) :
    f q i = q i + f (knownPrefix i q) i := by
  have he : f (Function.update (knownPrefix i q) i (q i)) i = f q i := by
    apply row_congr f hf i
    intro j hj
    by_cases hji : j = i
    · subst j
      exact Function.update_self ..
    · rw [Function.update_of_ne hji]
      exact if_pos (lt_of_le_of_ne hj hji)
  have h0 : knownPrefix i q i = 0 := if_neg (lt_irrefl i)
  have hrow := hu (knownPrefix i q) i (q i)
  rw [he, h0, add_zero] at hrow
  exact hrow.trans (add_comm _ _)

/-- The supplied unit-pivot inverse, evaluated in increasing coordinate order. -/
noncomputable def decode (f : Vector n R → Vector n R) (c : Vector n R) (i : Fin n) : R :=
  c i + f (fun j => if _h : j < i then decode f c j else 0) i
termination_by i.val

omit [CharP R 2] in
theorem decode_eq (f : Vector n R → Vector n R) (c : Vector n R) (i : Fin n) :
    decode f c i = c i + f (knownPrefix i (decode f c)) i := by
  rw [decode]
  rfl

theorem decode_encode (f : Vector n R → Vector n R) (hf : FutureInvariant f)
    (hu : UnitPivot f) (q : Vector n R) : decode f (f q) = q := by
  have h : ∀ k, ∀ hk : k < n, decode f (f q) ⟨k, hk⟩ = q ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have he : knownPrefix ⟨k, hk⟩ (decode f (f q)) = knownPrefix ⟨k, hk⟩ q := by
        funext j
        by_cases hj : j.val < k
        · simp only [knownPrefix, show j < (⟨k, hk⟩ : Fin n) from hj, if_true]
          exact ih j.val hj j.isLt
        · simp only [knownPrefix, show ¬ j < (⟨k, hk⟩ : Fin n) from hj, if_false]
      rw [decode_eq, he, row_eq f hf hu q, CharTwo.add_cancel_right]
  funext i
  exact h i.val i.isLt

theorem encode_decode (f : Vector n R → Vector n R) (hf : FutureInvariant f)
    (hu : UnitPivot f) (c : Vector n R) : f (decode f c) = c := by
  funext i
  rw [row_eq f hf hu, decode_eq, CharTwo.add_cancel_right]

/-- A two-sided inverse assembled entirely from the explicit update identities. -/
noncomputable def equiv (f : Vector n R → Vector n R) (hf : FutureInvariant f)
    (hu : UnitPivot f) : Vector n R ≃ Vector n R where
  toFun := f
  invFun := decode f
  left_inv := decode_encode f hf hu
  right_inv := encode_decode f hf hu

end FastPoly.Char2UpdateTriangular
