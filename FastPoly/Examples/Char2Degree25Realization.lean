import FastPoly.Examples.Char2Degree25Program
import FastPoly.Examples.Char2Degree25Inverse
import FastPoly.Examples.ExplicitCircuitConstruction
import FastPoly.Examples.ExplicitEvaluationInverse

/-!
# The supplied thirteen-product degree-25 construction and its explicit inverse

The two-sided raw-key inverse is prefix coefficient back-substitution followed
by the supplied invertible coordinate changes. This file connects it to the
literal program and arbitrary monic targets. Evaluation inversion is explicit
Lagrange interpolation followed by that same decoder.
-/
namespace FastPoly.Char2Degree25Realization

set_option maxHeartbeats 20000
open Polynomial Char2Certificate Char2Degree25Inverse
variable {F : Type*} [Field F] [CharP F 2]

noncomputable def polynomial (a : Fin 25 → F) : F[X] :=
  Char2Degree25Frame.output (Char2Degree25Coordinates.raw a)

theorem polynomial_monic (a : Fin 25 → F) : IsMonicOfDegree (polynomial a) 25 :=
  Char2Degree25Frame.output_monic _

theorem polynomial_coeff (a : Fin 25 → F) (i : Fin 25) :
    (polynomial a).coeff i.val = coefficientEquiv a i :=
  (coefficientEquiv_apply a i).symm

/-- A named preprocessing expression, not existentially chosen offsets. -/
noncomputable def decoder (c : Fin 25 → F) : ℕ → F :=
  Char2Degree25Coordinates.raw (coefficientEquiv.symm c)

theorem decoder_correct (c : Fin 25 → F) :
    Char2Degree25Frame.output (decoder c) = monicOfCoefficients c :=
  ExplicitCircuitConstruction.polynomial_inverse polynomial coefficientEquiv
    polynomial_monic polynomial_coeff c

/-- The counted program evaluates exactly the polynomial decoded above. -/
noncomputable def construction : Construction F 25 13 :=
  ExplicitCircuitConstruction.construction Char2Degree25Program.program
    Char2Degree25Coordinates.raw polynomial
    (fun a => Char2Degree25Program.program_eval (Char2Degree25Coordinates.raw a))
    coefficientEquiv polynomial_monic polynomial_coeff

theorem construction_decoder (c : Fin 25 → F) :
    construction.decoder c = decoder c := rfl

theorem monic_evaluation (P : F[X]) (hP : P.Monic) (hn : P.natDegree = 25) :
    (construction (F := F)).program.circuit.eval
      (inputEnv (decoder (fun i => P.coeff i))) 0 = P :=
  (construction (F := F)).correct_polynomial P hP hn

theorem polynomial_eq_monic (a : Fin 25 → F) :
    polynomial a = monicOfCoefficients (coefficientEquiv a) :=
  ExplicitCircuitConstruction.eq_monicOfCoefficients _ (polynomial_monic a)
    _ (polynomial_coeff a)

/-- Interpolate the requested values, then run the displayed raw-key inverse. -/
noncomputable def evaluationEquiv (x : Fin 25 → F) (hx : Function.Injective x) :
    (Fin 25 → F) ≃ (Fin 25 → F) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv coefficientEquiv (by omega) x hx

theorem evaluationEquiv_apply (x : Fin 25 → F) (hx : Function.Injective x)
    (a : Fin 25 → F) :
    evaluationEquiv x hx a = fun i => (polynomial a).eval (x i) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_apply coefficientEquiv (by omega)
    x hx polynomial polynomial_eq_monic a

theorem evaluationEquiv_symm_apply (x : Fin 25 → F) (hx : Function.Injective x)
    (values : Fin 25 → F) :
    (evaluationEquiv x hx).symm values =
      coefficientEquiv.symm (ExplicitEvaluationInverse.decode x values) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_inverse coefficientEquiv (by omega) x hx values

end FastPoly.Char2Degree25Realization
