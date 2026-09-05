import FastPoly.Examples.Char2Degree19KeyUpdates
import FastPoly.Examples.Char2UpdateTriangular

/-!
# Explicit inverse of the thirteen inner degree-19 coefficient rows

Fix the three shell keys, put the supplied inner coordinates in positions
3 through 15, and keep the unused outer keys zero.  The inverse is literal
back-substitution: at each step evaluate the named crown at the already
decoded prefix and add the requested coefficient.  Its two compositions
follow from the thirteen certified unit differences, without expanding a
baseline polynomial or searching for any key.
-/

namespace FastPoly.Char2Degree19InnerInverse

set_option maxHeartbeats 20000

open Char2Degree19KeyUpdates Char2Degree19Crown Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2]

/-- Fixed shell, thirteen inner keys, and three harmless zero outer keys. -/
def embed (shell : Fin 3 → R) (inner : Fin 13 → R) (i : Fin 19) : R :=
  if h : i.val < 3 then shell ⟨i.val, h⟩
  else if h' : i.val < 16 then inner ⟨i.val - 3, by omega⟩ else 0

omit [CharP R 2] in
theorem embed_shell (shell : Fin 3 → R) (inner : Fin 13 → R) (i : Fin 3) :
    embed shell inner ⟨i.val, by omega⟩ = shell i := by
  simp only [embed, dif_pos i.isLt]

omit [CharP R 2] in
theorem embed_inner (shell : Fin 3 → R) (inner : Fin 13 → R) (j : Fin 13) :
    embed shell inner (innerIndex j) = inner j := by
  have h3 : ¬ j.val + 3 < 3 := by omega
  have h16 : j.val + 3 < 16 := by omega
  simp only [embed, innerIndex, dif_neg h3, dif_pos h16, Nat.add_sub_cancel]

omit [CharP R 2] in
/-- Embedding commutes with replacement of one inner coordinate. -/
theorem embed_update (shell : Fin 3 → R) (inner : Fin 13 → R)
    (j : Fin 13) (value : R) :
    embed shell (Function.update inner j value) =
      Function.update (embed shell inner) (innerIndex j) value := by
  funext i
  by_cases hij : i = innerIndex j
  · subst i
    rw [embed_inner, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hij]
    by_cases h3 : i.val < 3
    · simp only [embed, dif_pos h3]
    · by_cases h16 : i.val < 16
      · have hne : (⟨i.val - 3, by omega⟩ : Fin 13) ≠ j := by
          intro he
          have hv := congrArg Fin.val he
          apply hij
          apply Fin.ext
          change i.val = j.val + 3
          change i.val - 3 = j.val at hv
          omega
        simp only [embed, dif_neg h3, dif_pos h16, Function.update_of_ne hne]
      · simp only [embed, dif_neg h3, dif_neg h16]

variable [Nontrivial R]

/-- Convert a replacement into the characteristic-two increment it requires. -/
theorem update_unit (shell : Fin 3 → R) (inner : Fin 13 → R)
    (j : Fin 13) (value : R) :
    UnitDifference (crown (rawKeys (embed shell inner)))
      (crown (rawKeys (embed shell (Function.update inner j value))))
      (12 - j.val) (inner j + value) := by
  have he : increment (embed shell inner) (innerIndex j) (inner j + value) =
      embed shell (Function.update inner j value) := by
    rw [increment, embed_inner, CharTwo.add_cancel_left, embed_update]
  have hu := increment_unit (embed shell inner) j (inner j + value)
  rw [he] at hu
  exact hu

/-- Read the crown in descending order, from coefficient twelve to zero. -/
noncomputable def innerRows (shell : Fin 3 → R) (inner : Fin 13 → R)
    (i : Fin 13) : R :=
  (crown (rawKeys (embed shell inner))).coeff (12 - i.val)

theorem futureInvariant (shell : Fin 3 → R) :
    Char2UpdateTriangular.FutureInvariant (innerRows shell) := by
  intro inner i j hij value
  have hrow : 12 - j.val < 12 - i.val := by
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val at hij
    omega
  exact (update_unit shell inner j value).higher (12 - i.val) hrow

theorem unitPivot (shell : Fin 3 → R) :
    Char2UpdateTriangular.UnitPivot (innerRows shell) := by
  intro inner i value
  change (crown (rawKeys (embed shell (Function.update inner i value)))).coeff
      (12 - i.val) =
    (crown (rawKeys (embed shell inner))).coeff (12 - i.val) + inner i + value
  rw [(update_unit shell inner i value).row, add_assoc]

/-- The actual inverse, retaining the crown as a named prefix baseline. -/
noncomputable def decode (shell : Fin 3 → R) (rows : Fin 13 → R) : Fin 13 → R :=
  Char2UpdateTriangular.decode (innerRows shell) rows

omit [CharP R 2] [Nontrivial R] in
/-- One literal back-substitution step, with only earlier keys in the baseline. -/
theorem decode_eq (shell : Fin 3 → R) (rows : Fin 13 → R) (i : Fin 13) :
    decode shell rows i = rows i +
      innerRows shell (Char2UpdateTriangular.knownPrefix i (decode shell rows)) i :=
  Char2UpdateTriangular.decode_eq _ rows i

theorem decode_encode (shell : Fin 3 → R) (inner : Fin 13 → R) :
    decode shell (innerRows shell inner) = inner :=
  Char2UpdateTriangular.decode_encode _ (futureInvariant shell) (unitPivot shell) inner

theorem encode_decode (shell : Fin 3 → R) (rows : Fin 13 → R) :
    innerRows shell (decode shell rows) = rows :=
  Char2UpdateTriangular.encode_decode _ (futureInvariant shell) (unitPivot shell) rows

/-- The two-sided inner coefficient equivalence; its inverse is explicit. -/
noncomputable def innerEquiv (shell : Fin 3 → R) : (Fin 13 → R) ≃ (Fin 13 → R) :=
  Char2UpdateTriangular.equiv (innerRows shell) (futureInvariant shell) (unitPivot shell)

theorem innerEquiv_apply (shell : Fin 3 → R) (inner : Fin 13 → R) :
    innerEquiv shell inner = innerRows shell inner := rfl

theorem innerEquiv_symm_apply (shell : Fin 3 → R) (rows : Fin 13 → R) :
    (innerEquiv shell).symm rows = decode shell rows := rfl

end FastPoly.Char2Degree19InnerInverse
