import FastPoly.Examples.Char2Degree23Keys

/-!
# The explicit coefficient-row change used by the degree-23 decoder

Reverse the coefficient order, then replace row four by row four plus
row three. Both operations have displayed inverses; the second is a
self-inverse shear. This is the terminal block's unit-pivot row order,
not a claim that the full circuit inverse is already assembled.
-/

namespace FastPoly.Char2Degree23Rows

open Polynomial Char2Decoder
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2]
abbrev Vector (R : Type*) := Fin 23 → R

def reverseRows : Vector R ≃ Vector R where
  toFun c i := c i.rev
  invFun c i := c i.rev
  left_inv c := by funext i; exact congrArg c (Fin.rev_rev i)
  right_inv c := by funext i; exact congrArg c (Fin.rev_rev i)

/-- The terminal inverse first reads [x^4]P+[x^3]P. -/
def adjacentShear : Vector R ≃ Vector R :=
  coordinateShear (18 : Fin 23) (fun c => c 19)
    (independent_read 18 19 (by omega))

/-- The full row transformation and its supplied inverse. -/
def rowEquiv : Vector R ≃ Vector R := reverseRows.trans adjacentShear

theorem rowEquiv_apply (c : Vector R) :
    rowEquiv c = Function.update (fun i => c i.rev) 18 (c 4 + c 3) := rfl

theorem rowEquiv_symm_apply (c : Vector R) :
    rowEquiv.symm c = fun i => (Function.update c 18 (c 18 + c 19)) i.rev := rfl

theorem decode_encode (c : Vector R) : rowEquiv.symm (rowEquiv c) = c :=
  rowEquiv.symm_apply_apply c

theorem encode_decode (c : Vector R) : rowEquiv (rowEquiv.symm c) = c :=
  rowEquiv.apply_symm_apply c

noncomputable def polynomialRows (p : R[X]) : Vector R :=
  rowEquiv (fun i => p.coeff i.val)

theorem polynomialRows_eighteen (p : R[X]) :
    polynomialRows p 18 = p.coeff 4 + p.coeff 3 := by
  unfold polynomialRows
  rw [rowEquiv_apply, Function.update_self]
  rfl

theorem polynomialRows_other (p : R[X]) (i : Fin 23) (hi : i ≠ 18) :
    polynomialRows p i = p.coeff (22 - i.val) := by
  unfold polynomialRows
  rw [rowEquiv_apply, Function.update_of_ne hi]
  congr 1
  rw [Fin.val_rev]
  omega

/-- Undoing the supplied row shear recovers the actual ascending coefficients. -/
theorem recover_coefficients (p : R[X]) :
    rowEquiv.symm (polynomialRows p) = fun i => p.coeff i.val :=
  decode_encode _

end FastPoly.Char2Degree23Rows
