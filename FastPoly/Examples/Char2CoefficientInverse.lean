import FastPoly.Examples.Char2UpdateTriangular
import FastPoly.Examples.Char2Degree19InnerTail

/-! Explicit coefficient inversion from supplied descending unit columns.
The inverse reads a named circuit at each recovered prefix. Coefficient
reversal is a displayed involution, so both compositions are checked without
expanding any circuit, searching parameters, or asserting invertibility. -/
namespace FastPoly.Char2CoefficientInverse

open Polynomial Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] {n : ℕ}

def increment (q : Fin n → R) (i : Fin n) (d : R) : Fin n → R :=
  Function.update q i (q i + d)
noncomputable def rows (f : (Fin n → R) → R[X]) (q : Fin n → R) (i : Fin n) : R :=
  (f q).coeff (n - 1 - i.val)

variable (f : (Fin n → R) → R[X])
  (hu : ∀ (q : Fin n → R) (i : Fin n) (d : R),
    UnitDifference (f q) (f (increment q i d)) (n - 1 - i.val) d)

theorem increment_eq_update (q : Fin n → R) (i : Fin n) (value : R) :
    increment q i (q i + value) = Function.update q i value := by
  rw [increment, CharTwo.add_cancel_left]

include hu in
theorem futureInvariant : Char2UpdateTriangular.FutureInvariant (rows f) := by
  intro q i j hij value
  have hi := i.isLt
  have hj := j.isLt
  have h := (hu q j (q j + value)).higher (n - 1 - i.val) (by omega)
  rw [increment_eq_update] at h
  exact h

include hu in
theorem unitPivot : Char2UpdateTriangular.UnitPivot (rows f) := by
  intro q i value
  have h := (hu q i (q i + value)).row
  rw [increment_eq_update, ← add_assoc] at h
  exact h

noncomputable def decodeRows (c : Fin n → R) : Fin n → R :=
  Char2UpdateTriangular.decode (rows f) c

theorem decodeRows_eq (c : Fin n → R) (i : Fin n) :
    decodeRows f c i = c i +
      rows f (Char2UpdateTriangular.knownPrefix i (decodeRows f c)) i :=
  Char2UpdateTriangular.decode_eq _ c i

include hu in
theorem decodeRows_encode (q : Fin n → R) : decodeRows f (rows f q) = q :=
  Char2UpdateTriangular.decode_encode _ (futureInvariant f hu) (unitPivot f hu) q
include hu in
theorem encode_decodeRows (c : Fin n → R) : rows f (decodeRows f c) = c :=
  Char2UpdateTriangular.encode_decode _ (futureInvariant f hu) (unitPivot f hu) c

omit [CommRing R] [CharP R 2] [Nontrivial R] in
def reverseRows : (Fin n → R) ≃ (Fin n → R) where
  toFun c i := c i.rev
  invFun c i := c i.rev
  left_inv c := by funext i; exact congrArg c (Fin.rev_rev i)
  right_inv c := by funext i; exact congrArg c (Fin.rev_rev i)

noncomputable def coefficientEquiv : (Fin n → R) ≃ (Fin n → R) :=
  (Char2UpdateTriangular.equiv (rows f) (futureInvariant f hu) (unitPivot f hu)).trans reverseRows

theorem coefficientEquiv_apply (q : Fin n → R) (i : Fin n) :
    coefficientEquiv f hu q i = (f q).coeff i.val := by
  change (f q).coeff (n - 1 - i.rev.val) = _
  have hi := i.isLt
  have he : n - 1 - i.rev.val = i.val := by
    change n - 1 - (n - (i.val + 1)) = i.val
    omega
  rw [he]

theorem coefficientEquiv_symm_apply (c : Fin n → R) :
    (coefficientEquiv f hu).symm c = decodeRows f (reverseRows c) := rfl

theorem decode_encode (q : Fin n → R) :
    decodeRows f (reverseRows (coefficientEquiv f hu q)) = q := by
  rw [← coefficientEquiv_symm_apply f hu, Equiv.symm_apply_apply]
theorem encode_decode (c : Fin n → R) :
    coefficientEquiv f hu (decodeRows f (reverseRows c)) = c := by
  rw [← coefficientEquiv_symm_apply f hu, Equiv.apply_symm_apply]

end FastPoly.Char2CoefficientInverse
