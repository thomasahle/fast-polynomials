import FastPoly.Examples.Char2Degree17Inverse
import FastPoly.Examples.Char2Degree17Program
import FastPoly.Examples.ExplicitCircuitConstruction
import FastPoly.Examples.ExplicitEvaluationInverse

/-! The existing nine-product degree17 circuit, with the supplied explicit
coefficient and evaluation inverses on its original raw offsets. -/
namespace FastPoly.Char2Degree17Realization

open Polynomial Char2Certificate Char2Degree17Inverse
set_option maxHeartbeats 20000
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

noncomputable def polynomial (a : Fin 17 → F) : F[X] :=
  Char2Degree17Wires.output a

theorem polynomial_monic (a : Fin 17 → F) : IsMonicOfDegree (polynomial a) 17 :=
  Char2Degree17Wires.output_monic a

theorem polynomial_coeff (a : Fin 17 → F) (i : Fin 17) :
    (polynomial a).coeff i.val = coefficientEquiv a i :=
  (coefficientEquiv_apply a i).symm

/-- Literal prefix back-substitution and the displayed raw-key inverse. -/
noncomputable def decoder (c : Fin 17 → F) : ℕ → F :=
  extendFin (coefficientEquiv.symm c)

theorem decoder_polynomial (c : Fin 17 → F) :
    polynomial (coefficientEquiv.symm c) = monicOfCoefficients c :=
  ExplicitCircuitConstruction.polynomial_inverse polynomial coefficientEquiv
    polynomial_monic polynomial_coeff c

/-- The nine-product ledger and the exact two-sided inverse refer to one circuit. -/
noncomputable def construction : Construction F 17 9 :=
  ExplicitCircuitConstruction.construction Char2Degree17Program.program
    extendFin polynomial Char2Degree17Program.program_eval
    coefficientEquiv polynomial_monic polynomial_coeff

theorem construction_decoder (c : Fin 17 → F) :
    construction.decoder c = decoder c := rfl

theorem monic_evaluation (P : F[X]) (hP : P.Monic) (hn : P.natDegree = 17) :
    (construction (F := F)).program.circuit.eval
      (inputEnv (decoder (fun i => P.coeff i))) 0 = P :=
  (construction (F := F)).correct_polynomial P hP hn

theorem polynomial_eq_monic (a : Fin 17 → F) :
    polynomial a = monicOfCoefficients (coefficientEquiv a) :=
  ExplicitCircuitConstruction.eq_monicOfCoefficients _ (polynomial_monic a)
    _ (polynomial_coeff a)

/-- Interpolate the requested values, then run the same raw-key decoder. -/
noncomputable def evaluationEquiv (x : Fin 17 → F) (hx : Function.Injective x) :
    (Fin 17 → F) ≃ (Fin 17 → F) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv coefficientEquiv (by omega) x hx

theorem evaluationEquiv_apply (x : Fin 17 → F) (hx : Function.Injective x)
    (a : Fin 17 → F) :
    evaluationEquiv x hx a = fun i => (polynomial a).eval (x i) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_apply coefficientEquiv (by omega)
    x hx polynomial polynomial_eq_monic a

theorem evaluationEquiv_symm_apply (x : Fin 17 → F) (hx : Function.Injective x)
    (values : Fin 17 → F) :
    (evaluationEquiv x hx).symm values =
      coefficientEquiv.symm (ExplicitEvaluationInverse.decode x values) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_inverse coefficientEquiv (by omega) x hx values

end FastPoly.Char2Degree17Realization

