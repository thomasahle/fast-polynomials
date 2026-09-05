import FastPoly.Examples.Char2UpdateTriangular

/-!
# Explicit back-substitution with supplied, possibly Frobenius, pivots

The scalar inverse at each row is supplied as an equivalence fixing zero.
Single-coordinate identities justify the named prefix baseline, and the
decoder applies that scalar inverse to the residual. Both compositions are
proved without expanding the circuit or solving an existential goal.
-/

namespace FastPoly.Char2PivotUpdates

open Char2UpdateTriangular
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] {n : ℕ}

/-- The certificate states how changing the current input changes its row. -/
def PivotUpdate (f : Vector n R → Vector n R) (p : Fin n → R ≃ R) : Prop :=
  ∀ q i value, f (Function.update q i value) i = f q i + p i (q i) + p i value

omit [CharP R 2] in
theorem row_eq (f : Vector n R → Vector n R) (p : Fin n → R ≃ R)
    (hf : FutureInvariant f) (hp : ∀ i, p i 0 = 0) (hu : PivotUpdate f p)
    (q : Vector n R) (i : Fin n) :
    f q i = p i (q i) + f (knownPrefix i q) i := by
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
  rw [he, h0, hp, add_zero] at hrow
  exact hrow.trans (add_comm _ _)

/-- At each row, apply the supplied scalar inverse to the residual. -/
noncomputable def decode (f : Vector n R → Vector n R) (p : Fin n → R ≃ R)
    (c : Vector n R) (i : Fin n) : R :=
  (p i).symm (c i + f (fun j => if _h : j < i then decode f p c j else 0) i)
termination_by i.val

omit [CharP R 2] in
theorem decode_eq (f : Vector n R → Vector n R) (p : Fin n → R ≃ R)
    (c : Vector n R) (i : Fin n) :
    decode f p c i = (p i).symm (c i + f (knownPrefix i (decode f p c)) i) := by
  rw [decode]
  rfl

theorem decode_encode (f : Vector n R → Vector n R) (p : Fin n → R ≃ R)
    (hf : FutureInvariant f) (hp : ∀ i, p i 0 = 0) (hu : PivotUpdate f p)
    (q : Vector n R) : decode f p (f q) = q := by
  have h : ∀ k, ∀ hk : k < n, decode f p (f q) ⟨k, hk⟩ = q ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have he : knownPrefix ⟨k, hk⟩ (decode f p (f q)) = knownPrefix ⟨k, hk⟩ q := by
        funext j
        by_cases hj : j.val < k
        · simp only [knownPrefix, show j < (⟨k, hk⟩ : Fin n) from hj, if_true]
          exact ih j.val hj j.isLt
        · simp only [knownPrefix, show ¬ j < (⟨k, hk⟩ : Fin n) from hj, if_false]
      rw [decode_eq, he, row_eq f p hf hp hu q, CharTwo.add_cancel_right,
        Equiv.symm_apply_apply]
  funext i
  exact h i.val i.isLt

theorem encode_decode (f : Vector n R → Vector n R) (p : Fin n → R ≃ R)
    (hf : FutureInvariant f) (hp : ∀ i, p i 0 = 0) (hu : PivotUpdate f p)
    (c : Vector n R) : f (decode f p c) = c := by
  funext i
  rw [row_eq f p hf hp hu, decode_eq, Equiv.apply_symm_apply,
    CharTwo.add_cancel_right]

noncomputable def equiv (f : Vector n R → Vector n R) (p : Fin n → R ≃ R)
    (hf : FutureInvariant f) (hp : ∀ i, p i 0 = 0) (hu : PivotUpdate f p) :
    Vector n R ≃ Vector n R where
  toFun := f
  invFun := decode f p
  left_inv := decode_encode f p hf hp hu
  right_inv := encode_decode f p hf hp hu

end FastPoly.Char2PivotUpdates
