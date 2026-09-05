import FastPoly.Polynomial.MonicEvaluation
import Mathlib.Algebra.CharP.Lemmas

/-!
# Explicit triangular decoding for the finite characteristic-two circuits

The decoder is descending back-substitution in the chosen coefficient order.
Each pivot is an explicitly supplied equivalence (identity, or a Frobenius
power over a perfect field); the row tail depends only on earlier coordinates.
No search, Jacobian criterion, or finite-field enumeration is used.
-/

namespace FastPoly.Char2Certificate

open Polynomial

universe u
variable {F : Type u} [Field F]

/-- Earlier coordinates, with the as-yet undecoded suffix set to zero. -/
def prefixVector (i : ℕ) (q : ℕ → F) : ℕ → F := fun j => if j < i then q j else 0

/-- The actual recursive decoder, not merely an existence argument. -/
noncomputable def decode (pivot : ℕ → F ≃ F) (tail : ℕ → (ℕ → F) → F)
    (c : ℕ → F) (i : ℕ) : F :=
  (pivot i).symm (c i - tail i (fun j => if h : j < i then decode pivot tail c j else 0))
termination_by i

theorem decode_eq (pivot : ℕ → F ≃ F) (tail : ℕ → (ℕ → F) → F)
    (c : ℕ → F) (i : ℕ) :
    decode pivot tail c i =
      (pivot i).symm (c i - tail i (prefixVector i (decode pivot tail c))) := by
  rw [decode]
  rfl

/-- An explicit triangular coordinate map, in decoder order. -/
def encode (pivot : ℕ → F ≃ F) (tail : ℕ → (ℕ → F) → F) (q : ℕ → F) : ℕ → F :=
  fun i => pivot i (q i) + tail i q

/-- The sole structural hypothesis checked by each finite coefficient certificate. -/
def Causal (n : ℕ) (tail : ℕ → (ℕ → F) → F) : Prop :=
  ∀ i, i < n → ∀ q r, (∀ j, j < i → q j = r j) → tail i q = tail i r

theorem decode_encode (n : ℕ) (pivot : ℕ → F ≃ F)
    (tail : ℕ → (ℕ → F) → F) (ht : Causal n tail) (q : ℕ → F) :
    ∀ i, i < n → decode pivot tail (encode pivot tail q) i = q i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have he : tail i (prefixVector i (decode pivot tail (encode pivot tail q))) = tail i q := by
      apply ht i hi
      intro j hj
      simp only [prefixVector, if_pos hj]
      exact ih j hj (Nat.lt_trans hj hi)
    rw [decode_eq, he, encode, add_sub_cancel_right, Equiv.symm_apply_apply]

theorem encode_decode (n : ℕ) (pivot : ℕ → F ≃ F)
    (tail : ℕ → (ℕ → F) → F) (ht : Causal n tail) (c : ℕ → F) :
    ∀ i, i < n → encode pivot tail (decode pivot tail c) i = c i := by
  intro i hi
  have he : tail i (prefixVector i (decode pivot tail c)) = tail i (decode pivot tail c) := by
    apply ht i hi
    intro j hj
    exact if_pos hj
  simp only [encode]
  rw [decode_eq, he, Equiv.apply_symm_apply, sub_add_cancel]

/-- The finite coordinate map, with no unspecified suffix parameters. -/
def encodeFin {n : ℕ} (pivot : ℕ → F ≃ F) (tail : ℕ → (ℕ → F) → F)
    (q : Fin n → F) : Fin n → F := fun i => encode pivot tail (extendFin q) i

noncomputable def decodeFin {n : ℕ} (pivot : ℕ → F ≃ F)
    (tail : ℕ → (ℕ → F) → F) (c : Fin n → F) : Fin n → F :=
  fun i => decode pivot tail (extendFin c) i

theorem decodeFin_encodeFin {n : ℕ} (pivot : ℕ → F ≃ F)
    (tail : ℕ → (ℕ → F) → F) (ht : Causal n tail) (q : Fin n → F) :
    decodeFin pivot tail (encodeFin pivot tail q) = q := by
  have h : ∀ i, ∀ hi : i < n,
      decode pivot tail (extendFin (encodeFin pivot tail q)) i = q ⟨i, hi⟩ := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      have he : tail i (prefixVector i
          (decode pivot tail (extendFin (encodeFin pivot tail q)))) =
          tail i (extendFin q) := by
        apply ht i hi
        intro j hj
        simp only [prefixVector, if_pos hj, extendFin, dif_pos (Nat.lt_trans hj hi)]
        exact ih j hj (Nat.lt_trans hj hi)
      rw [decode_eq, he]
      simp only [extendFin, dif_pos hi, encodeFin, encode]
      rw [add_sub_cancel_right, Equiv.symm_apply_apply]
  funext i
  exact h i i.isLt

theorem encodeFin_decodeFin {n : ℕ} (pivot : ℕ → F ≃ F)
    (tail : ℕ → (ℕ → F) → F) (ht : Causal n tail) (c : Fin n → F) :
    encodeFin pivot tail (decodeFin pivot tail c) = c := by
  funext i
  have he : tail i (extendFin (decodeFin pivot tail c)) =
      tail i (decode pivot tail (extendFin c)) := by
    apply ht i i.isLt
    intro j hj
    simp only [extendFin, dif_pos (Nat.lt_trans hj i.isLt), decodeFin]
  simp only [encodeFin, encode, he, extendFin, dif_pos i.isLt, decodeFin]
  have h := encode_decode n pivot tail ht (extendFin c) i i.isLt
  simpa only [encode, extendFin, dif_pos i.isLt] using h

/-- Both directions of the explicit finite triangular decoder. -/
noncomputable def triangularEquiv {n : ℕ} (pivot : ℕ → F ≃ F)
    (tail : ℕ → (ℕ → F) → F) (ht : Causal n tail) :
    (Fin n → F) ≃ (Fin n → F) where
  toFun := encodeFin pivot tail
  invFun := decodeFin pivot tail
  left_inv := decodeFin_encodeFin pivot tail ht
  right_inv := encodeFin_decodeFin pivot tail ht

/-- Reorder the decoded coefficient rows into ascending polynomial degree. -/
def rowEquiv {n : ℕ} (rows : Fin n ≃ Fin n) : (Fin n → F) ≃ (Fin n → F) where
  toFun c := fun j => c (rows.symm j)
  invFun c := fun i => c (rows i)
  left_inv c := by funext i; simp only [Equiv.symm_apply_apply]
  right_inv c := by funext i; simp only [Equiv.apply_symm_apply]

noncomputable def coefficientEquiv {n : ℕ} (pivot : ℕ → F ≃ F)
    (tail : ℕ → (ℕ → F) → F) (ht : Causal n tail) (rows : Fin n ≃ Fin n) :
    (Fin n → F) ≃ (Fin n → F) :=
  (triangularEquiv pivot tail ht).trans (rowEquiv rows)

/-- The public evaluation theorem uses the same polynomial as the certificate. -/
theorem evaluation_bijective {n : ℕ} (hn : 1 ≤ n)
    (pivot : ℕ → F ≃ F) (tail : ℕ → (ℕ → F) → F)
    (ht : Causal n tail) (rows : Fin n ≃ Fin n) (P : (Fin n → F) → F[X])
    (hP : ∀ q, P q = monicOfCoefficients (coefficientEquiv pivot tail ht rows q))
    (x : Fin n → F) (hx : Function.Injective x) :
    Function.Bijective (fun q => fun i => (P q).eval (x i)) := by
  have he := (monicOfCoefficients_eval_bijective hn x hx).comp
    (coefficientEquiv pivot tail ht rows).bijective
  simpa only [Function.comp_def, ← hP] using he

end FastPoly.Char2Certificate
