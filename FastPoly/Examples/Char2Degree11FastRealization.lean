import FastPoly.Examples.Char2Degree11FastInverse
import FastPoly.Examples.Char2Degree11FastProgram
import FastPoly.Examples.ExplicitCircuitConstruction
import FastPoly.Examples.ExplicitEvaluationInverse

/-! The original degree-11 six-product circuit, with its fast explicit inverse.
Preprocessing uses literal descending back-substitution at named prefix baselines.
No existential choice of gate offsets or expanded coefficient formula is used. -/

namespace FastPoly.Char2Degree11Fast

set_option maxHeartbeats 20000

open Polynomial Char2Certificate

variable {F : Type*} [Field F] [CharP F 2]

/-- The normalized-coordinate solve, followed by the supplied raw-key formulas. -/
noncomputable def decoder (c : Fin 11 → F) : ℕ → F :=
  keys (ascendingEquiv.symm c)

theorem decoder_polynomial (c : Fin 11 → F) :
    output (ascendingEquiv.symm c) = monicOfCoefficients c :=
  ExplicitCircuitConstruction.polynomial_inverse output ascendingEquiv
    output_monic output_coefficient c

/-- The fixed multiplication ledger and the explicitly supplied decoder. -/
noncomputable def construction : Construction F 11 6 :=
  ExplicitCircuitConstruction.construction program keys output program_eval
    ascendingEquiv output_monic output_coefficient

theorem construction_decoder (c : Fin 11 → F) :
    construction.decoder c = decoder c := rfl

theorem program_decode_correct (c : Fin 11 → F) :
    (program (F := F)).circuit.eval (inputEnv (decoder c)) 0 = monicOfCoefficients c :=
  (construction (F := F)).correct c

theorem monic_evaluation (P : F[X]) (hP : P.Monic) (hn : P.natDegree = 11) :
    (construction (F := F)).program.circuit.eval
      (inputEnv (decoder (fun i => P.coeff i))) 0 = P :=
  (construction (F := F)).correct_polynomial P hP hn

theorem output_eq_monic (q : Keys F) :
    output q = monicOfCoefficients (ascendingEquiv q) :=
  ExplicitCircuitConstruction.eq_monicOfCoefficients _ (output_monic q)
    _ (output_coefficient q)

/-- Lagrange interpolation of the requested values, followed by the actual
coefficient inverse. The domain is the supplied normalized coordinate vector. -/
noncomputable def evaluationEquiv (x : Fin 11 → F) (hx : Function.Injective x) :
    Keys F ≃ (Fin 11 → F) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv ascendingEquiv (by omega) x hx

theorem evaluationEquiv_apply (x : Fin 11 → F) (hx : Function.Injective x) (q : Keys F) :
    evaluationEquiv x hx q = fun i => (output q).eval (x i) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_apply ascendingEquiv (by omega)
    x hx output output_eq_monic q

theorem evaluationEquiv_symm_apply (x : Fin 11 → F) (hx : Function.Injective x)
    (values : Fin 11 → F) :
    (evaluationEquiv x hx).symm values =
      ascendingEquiv.symm (ExplicitEvaluationInverse.decode x values) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_inverse ascendingEquiv (by omega) x hx values

end FastPoly.Char2Degree11Fast

