import FastPoly.Examples.Char2Degree21KeyUpdates
import FastPoly.Examples.Char2UpdateTriangular
import FastPoly.Polynomial.MonicEvaluation

/-!
# The explicit two-sided degree-21 coefficient decoder

The inverse reads coefficients from degree twenty down to zero. At each
row it adds the requested coefficient to the named circuit evaluated at
the already decoded prefix. The 21 supplied unit differences prove both
compositions; no baseline coefficients are expanded. Composing with the
displayed key-coordinate inverse recovers the original raw offsets too.
-/

namespace FastPoly.Char2Degree21Inverse

set_option maxHeartbeats 20000

open Char2Degree21KeyUpdates Char2Degree21Coordinates Char2Degree19InnerTail

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem update_unit (q : Fin 21 → R) (j : Fin 21) (value : R) :
    UnitDifference (Char2Degree21Frame.output (rawKeys q))
      (Char2Degree21Frame.output (rawKeys (Function.update q j value)))
      (20 - j.val) (q j + value) := by
  have he : increment q j (q j + value) = Function.update q j value := by
    rw [increment, CharTwo.add_cancel_left]
  have hu := increment_unit q j (q j + value)
  rw [he] at hu
  exact hu

/-- The circuit's coefficient rows, ordered in the direction of decoding. -/
noncomputable def descendingRows (q : Fin 21 → R) (i : Fin 21) : R :=
  (Char2Degree21Frame.output (rawKeys q)).coeff (20 - i.val)

theorem futureInvariant : Char2UpdateTriangular.FutureInvariant
    (descendingRows (R := R)) := by
  intro q i j hij value
  have hrow : 20 - j.val < 20 - i.val := by
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val at hij
    omega
  exact (update_unit q j value).higher _ hrow

theorem unitPivot : Char2UpdateTriangular.UnitPivot
    (descendingRows (R := R)) := by
  intro q i value
  change (Char2Degree21Frame.output (rawKeys (Function.update q i value))).coeff
      (20 - i.val) =
    (Char2Degree21Frame.output (rawKeys q)).coeff (20 - i.val) + q i + value
  rw [(update_unit q i value).row, add_assoc]

/-- Literal recursive back-substitution; circuit evaluation remains named. -/
noncomputable def decodeRows (c : Fin 21 → R) : Fin 21 → R :=
  Char2UpdateTriangular.decode descendingRows c

theorem decodeRows_eq (c : Fin 21 → R) (i : Fin 21) :
    decodeRows c i = c i +
      descendingRows (Char2UpdateTriangular.knownPrefix i (decodeRows c)) i :=
  Char2UpdateTriangular.decode_eq _ c i

theorem decodeRows_encode (q : Fin 21 → R) :
    decodeRows (descendingRows q) = q :=
  Char2UpdateTriangular.decode_encode _ futureInvariant unitPivot q

theorem encode_decodeRows (c : Fin 21 → R) :
    descendingRows (decodeRows c) = c :=
  Char2UpdateTriangular.encode_decode _ futureInvariant unitPivot c

noncomputable def descendingEquiv : (Fin 21 → R) ≃ (Fin 21 → R) :=
  Char2UpdateTriangular.equiv descendingRows futureInvariant unitPivot

omit [CommRing R] [CharP R 2] [Nontrivial R] in
/-- The same row reversal is used for encoding and decoding. -/
def reverseRows (c : Fin 21 → R) (i : Fin 21) : R := c ⟨20 - i.val, by omega⟩

omit [CommRing R] [CharP R 2] [Nontrivial R] in
theorem reverseRows_reverseRows (c : Fin 21 → R) :
    reverseRows (reverseRows c) = c := by
  funext i
  change c ⟨20 - (20 - i.val), _⟩ = c i
  congr 1
  apply Fin.ext
  have hi := i.isLt
  change 20 - (20 - i.val) = i.val
  omega

omit [CommRing R] [CharP R 2] [Nontrivial R] in
def reverseEquiv : (Fin 21 → R) ≃ (Fin 21 → R) where
  toFun := reverseRows
  invFun := reverseRows
  left_inv := reverseRows_reverseRows
  right_inv := reverseRows_reverseRows

/-- The normalized keys are equivalent to all 21 low coefficients. -/
noncomputable def normalizedCoefficientEquiv : (Fin 21 → R) ≃ (Fin 21 → R) :=
  descendingEquiv.trans reverseEquiv

theorem normalizedCoefficientEquiv_apply (q : Fin 21 → R) (i : Fin 21) :
    normalizedCoefficientEquiv q i =
      (Char2Degree21Frame.output (rawKeys q)).coeff i := by
  change (Char2Degree21Frame.output (rawKeys q)).coeff (20 - (20 - i.val)) = _
  have hi := i.isLt
  have he : 20 - (20 - i.val) = i.val := by omega
  rw [he]

/-- First reverse the rows, then decode the normalized keys, then apply the
supplied polynomial key inverse. This is an explicit original-key inverse. -/
noncomputable def coefficientEquiv : (Fin 21 → R) ≃ (Fin 21 → R) :=
  coordinateEquiv.trans normalizedCoefficientEquiv

theorem coefficientEquiv_symm_apply (c : Fin 21 → R) :
    (coefficientEquiv (R := R)).symm c = keys (decodeRows (reverseRows c)) := rfl

theorem decode_encode (a : Fin 21 → R) :
    keys (decodeRows (reverseRows (coefficientEquiv a))) = a := by
  rw [← coefficientEquiv_symm_apply, Equiv.symm_apply_apply]

theorem encode_decode (c : Fin 21 → R) :
    coefficientEquiv (keys (decodeRows (reverseRows c))) = c := by
  rw [← coefficientEquiv_symm_apply, Equiv.apply_symm_apply]

section Field

variable {F : Type*} [Field F] [CharP F 2]

theorem rawKeys_coordinates (a : Fin 21 → F) : rawKeys (coordinates a) = extendFin a := by
  funext i
  simp only [rawKeys, keys_coordinates, extendFin]

/-- Public bridge to the literal original-key circuit, in ordinary coefficient order. -/
theorem coefficientEquiv_apply (a : Fin 21 → F) (i : Fin 21) :
    coefficientEquiv a i = (Char2Degree21Frame.output (extendFin a)).coeff i := by
  change normalizedCoefficientEquiv (coordinates a) i = _
  rw [normalizedCoefficientEquiv_apply, rawKeys_coordinates]

end Field

end FastPoly.Char2Degree21Inverse
