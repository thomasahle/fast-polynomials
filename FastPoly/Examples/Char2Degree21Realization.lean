import FastPoly.Examples.Char2Degree21Program
import FastPoly.Examples.Char2Degree21Inverse
import FastPoly.Examples.ExplicitCircuitConstruction
import FastPoly.Examples.ExplicitEvaluationInverse

/-!
# The existing eleven-product degree-21 construction and its explicit inverse

The raw-key coefficient equivalence is the supplied key-coordinate inverse,
followed by certified prefix back-substitution and row reversal. This file
connects that exact inverse to the literal program and arbitrary monic targets.
The evaluation inverse is Lagrange interpolation followed by the same decoder.
-/

namespace FastPoly.Char2Degree21Realization

set_option maxHeartbeats 20000

open Polynomial Char2Certificate Char2Degree21Inverse

variable {F : Type*} [Field F] [CharP F 2]

/-- The actual circuit polynomial in the original twenty-one raw offsets. -/
noncomputable def polynomial (a : Fin 21 → F) : F[X] :=
  Char2Degree21Frame.output (extendFin a)

theorem polynomial_monic (a : Fin 21 → F) : IsMonicOfDegree (polynomial a) 21 :=
  Char2Degree21Frame.output_monic _

theorem polynomial_coeff (a : Fin 21 → F) (i : Fin 21) :
    (polynomial a).coeff i.val = coefficientEquiv a i :=
  (coefficientEquiv_apply a i).symm

/-- The named preprocessing expression; no parameters are chosen existentially. -/
noncomputable def decoder (c : Fin 21 → F) : ℕ → F :=
  extendFin (coefficientEquiv.symm c)

theorem decoder_correct (c : Fin 21 → F) :
    Char2Degree21Frame.output (decoder c) = monicOfCoefficients c :=
  ExplicitCircuitConstruction.polynomial_inverse polynomial coefficientEquiv
    polynomial_monic polynomial_coeff c

/-- The counted program evaluates the very same polynomial as the inverse. -/
noncomputable def construction : Construction F 21 11 :=
  ExplicitCircuitConstruction.construction Char2Degree21Program.program
    extendFin polynomial (fun a => Char2Degree21Program.program_eval (extendFin a))
    coefficientEquiv polynomial_monic polynomial_coeff

theorem construction_decoder (c : Fin 21 → F) :
    construction.decoder c = decoder c := rfl

theorem monic_evaluation (P : F[X]) (hP : P.Monic) (hn : P.natDegree = 21) :
    (construction (F := F)).program.circuit.eval
      (inputEnv (decoder (fun i => P.coeff i))) 0 = P :=
  (construction (F := F)).correct_polynomial P hP hn

theorem polynomial_eq_monic (a : Fin 21 → F) :
    polynomial a = monicOfCoefficients (coefficientEquiv a) :=
  ExplicitCircuitConstruction.eq_monicOfCoefficients _ (polynomial_monic a)
    _ (polynomial_coeff a)

/-- Interpolate the requested values, then execute the supplied raw-key inverse. -/
noncomputable def evaluationEquiv (x : Fin 21 → F) (hx : Function.Injective x) :
    (Fin 21 → F) ≃ (Fin 21 → F) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv coefficientEquiv (by omega) x hx

theorem evaluationEquiv_apply (x : Fin 21 → F) (hx : Function.Injective x)
    (a : Fin 21 → F) :
    evaluationEquiv x hx a = fun i => (polynomial a).eval (x i) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_apply coefficientEquiv (by omega)
    x hx polynomial polynomial_eq_monic a

theorem evaluationEquiv_symm_apply (x : Fin 21 → F) (hx : Function.Injective x)
    (values : Fin 21 → F) :
    (evaluationEquiv x hx).symm values =
      coefficientEquiv.symm (ExplicitEvaluationInverse.decode x values) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_inverse coefficientEquiv (by omega) x hx values

end FastPoly.Char2Degree21Realization
