import FastPoly.Examples.Char2Degree13FastRealization

/-!
# Explicit inverse on the paper's original thirteen raw offsets

The degree-thirteen circuit of appendix display (A.0) is the existing Fast13
circuit. Its active normalized coordinate q9 is a3+a4, whereas (13.1) uses
a4; these conventions differ by the earlier-coordinate shear q9 += q8.
Here both linear raw-coordinate maps are supplied literally. Composing their
inverse with the checked Fast13 decoder proves the raw coefficient and
evaluation bijections, without changing the seven circuit products.
-/

namespace FastPoly.Char2PaperDegree13Inverse

open Polynomial
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2]
abbrev Keys (R : Type*) := Fin 13 → R

/-- Raw offsets to the normalized coordinates actually used by Fast13. -/
def toFast (a : Keys R) (i : Fin 13) : R :=
  match i.val with
  | 0 => a 5 | 1 => a 11 + a 12 | 2 => a 12 | 3 => a 9
  | 4 => a 8 | 5 => a 10 | 6 => a 1 | 7 => a 7
  | 8 => a 3 | 9 => a 3 + a 4 | 10 => a 6 | 11 => a 2 | _ => a 0

/-- The displayed inverse linear map, in the original raw-offset order. -/
def fromFast (q : Keys R) (i : Fin 13) : R := Char2Degree13Fast.keys q i.val

theorem fromFast_toFast (a : Keys R) : fromFast (toFast a) = a := by
  funext i
  fin_cases i <;>
    simp only [fromFast, toFast, Char2Degree13Fast.keys, CharTwo.add_cancel_left,
      CharTwo.add_cancel_right] <;> rfl

theorem toFast_fromFast (q : Keys R) : toFast (fromFast q) = q := by
  funext i
  fin_cases i <;>
    simp only [fromFast, toFast, Char2Degree13Fast.keys, CharTwo.add_cancel_left,
      CharTwo.add_cancel_right] <;> rfl

def rawCoordinateEquiv : Keys R ≃ Keys R where
  toFun := toFast
  invFun := fromFast
  left_inv := fromFast_toFast
  right_inv := toFast_fromFast

/-- Exactly the coordinates printed in appendix equation (13.1). -/
def paperCoordinates (a : Keys R) : Keys R :=
  Function.update (toFast a) 9 (a 4)

theorem paper_to_fast (a : Keys R) :
    Function.update (paperCoordinates a) 9 (paperCoordinates a 8 + paperCoordinates a 9) =
      toFast a := by
  unfold paperCoordinates
  simp only [Function.update_of_ne (by omega : (8 : Fin 13) ≠ 9), Function.update_self,
    Function.update_idem]
  change Function.update (toFast a) 9 (toFast a 9) = toFast a
  exact Function.update_eq_self _ _

/-- Literal named wires of the degree-thirteen row of display (A.0). -/
noncomputable def y : R[X] := X ^ 2
noncomputable def z (a : Keys R) : R[X] := (X + y + C (a 12)) * (y + C (a 11))
noncomputable def w (a : Keys R) : R[X] := (y + z a + C (a 10)) * (z a + C (a 9))
noncomputable def v (a : Keys R) : R[X] := (y + z a + C (a 8)) * (w a + C (a 7))
noncomputable def u (a : Keys R) : R[X] := (z a + v a + C (a 6)) * (X + C (a 5))
noncomputable def t (a : Keys R) : R[X] := (X + y + C (a 4)) * (X + C (a 3))
noncomputable def s (a : Keys R) : R[X] := (w a + t a + C (a 2)) * (y + C (a 1))
noncomputable def output (a : Keys R) : R[X] := u a + v a + s a + C (a 0)

theorem z_fromFast (q : Keys R) : z (fromFast q) = Char2Degree13Fast.z q := rfl
theorem w_fromFast (q : Keys R) : w (fromFast q) = Char2Degree13Fast.w q := by
  unfold w
  rw [z_fromFast]
  rfl
theorem v_fromFast (q : Keys R) : v (fromFast q) = Char2Degree13Fast.v q := by
  unfold v
  rw [z_fromFast, w_fromFast]
  rfl
theorem u_fromFast (q : Keys R) : u (fromFast q) = Char2Degree13Fast.u q := by
  unfold u
  rw [z_fromFast, v_fromFast]
  rfl
theorem t_fromFast (q : Keys R) : t (fromFast q) = Char2Degree13Fast.t q := rfl
theorem s_fromFast (q : Keys R) : s (fromFast q) = Char2Degree13Fast.s q := by
  unfold s
  rw [w_fromFast, t_fromFast]
  rfl
theorem output_fromFast (q : Keys R) : output (fromFast q) = Char2Degree13Fast.output q := by
  unfold output
  rw [u_fromFast, v_fromFast, s_fromFast]
  rfl

theorem output_toFast (a : Keys R) : output a = Char2Degree13Fast.output (toFast a) := by
  have h := output_fromFast (toFast a)
  rw [fromFast_toFast] at h
  exact h

variable [Nontrivial R]

/-- The coefficient inverse is the checked prefix solve followed by the
explicit inverse raw-key map. Coefficients are in ordinary ascending order. -/
noncomputable def coefficientEquiv : Keys R ≃ Keys R :=
  rawCoordinateEquiv.trans Char2Degree13Fast.ascendingEquiv

theorem coefficientEquiv_apply (a : Keys R) (i : Fin 13) :
    coefficientEquiv a i = (output a).coeff i.val := by
  change Char2Degree13Fast.ascendingEquiv (toFast a) i = _
  rw [output_toFast, Char2Degree13Fast.output_coefficient]

theorem coefficientEquiv_symm_apply (c : Keys R) :
    coefficientEquiv.symm c = fromFast (Char2Degree13Fast.ascendingEquiv.symm c) := rfl

noncomputable def encode (a : Keys R) : Keys R := fun i => (output a).coeff i.val
noncomputable def decode (c : Keys R) : Keys R :=
  fromFast (Char2Degree13Fast.ascendingEquiv.symm c)

theorem encode_eq (a : Keys R) : encode a = coefficientEquiv a :=
  funext fun i => (coefficientEquiv_apply a i).symm

theorem decode_encode (a : Keys R) : decode (encode a) = a := by
  rw [encode_eq]
  change coefficientEquiv.symm (coefficientEquiv a) = a
  exact coefficientEquiv.symm_apply_apply a

theorem encode_decode (c : Keys R) : encode (decode c) = c := by
  rw [encode_eq]
  change coefficientEquiv (coefficientEquiv.symm c) = c
  exact coefficientEquiv.apply_symm_apply c

theorem coefficient_bijective : Function.Bijective (encode (R := R)) := by
  have he : encode (R := R) = coefficientEquiv := funext encode_eq
  rw [he]
  exact coefficientEquiv.bijective

section Evaluation

variable {F : Type*} [Field F] [CharP F 2]

theorem decoder_polynomial (c : Keys F) : output (decode c) = monicOfCoefficients c := by
  rw [decode, output_fromFast]
  exact Char2Degree13Fast.decoder_polynomial c

/-- Lagrange interpolation, the supplied prefix solve, and the literal
inverse linear raw-coordinate map, in that order. -/
noncomputable def evaluationEquiv (x : Fin 13 → F) (hx : Function.Injective x) :
    Keys F ≃ (Fin 13 → F) :=
  rawCoordinateEquiv.trans (Char2Degree13Fast.evaluationEquiv x hx)

theorem evaluationEquiv_apply (x : Fin 13 → F) (hx : Function.Injective x) (a : Keys F) :
    evaluationEquiv x hx a = fun i => (output a).eval (x i) := by
  change Char2Degree13Fast.evaluationEquiv x hx (toFast a) = _
  rw [Char2Degree13Fast.evaluationEquiv_apply, output_toFast]

theorem evaluationEquiv_symm_apply (x : Fin 13 → F) (hx : Function.Injective x)
    (values : Fin 13 → F) :
    (evaluationEquiv x hx).symm values =
      decode (ExplicitEvaluationInverse.decode x values) := by
  change fromFast ((Char2Degree13Fast.evaluationEquiv x hx).symm values) = _
  rw [Char2Degree13Fast.evaluationEquiv_symm_apply]
  rfl

theorem evaluation_decode_encode (x : Fin 13 → F) (hx : Function.Injective x) (a : Keys F) :
    decode (ExplicitEvaluationInverse.decode x (fun i => (output a).eval (x i))) = a := by
  rw [← evaluationEquiv_apply x hx a, ← evaluationEquiv_symm_apply x hx]
  exact (evaluationEquiv x hx).symm_apply_apply a

theorem evaluation_encode_decode (x : Fin 13 → F) (hx : Function.Injective x)
    (values : Fin 13 → F) :
    (fun i => (output (decode (ExplicitEvaluationInverse.decode x values))).eval (x i)) = values := by
  rw [← evaluationEquiv_apply x hx, ← evaluationEquiv_symm_apply x hx]
  exact (evaluationEquiv x hx).apply_symm_apply values

end Evaluation
end FastPoly.Char2PaperDegree13Inverse
