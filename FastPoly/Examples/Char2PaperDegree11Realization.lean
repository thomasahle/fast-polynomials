import FastPoly.Examples.Char2PaperDegree11Inverse
import FastPoly.Examples.Char2PaperDegree11Program
import FastPoly.Examples.ExplicitCircuitConstruction
import FastPoly.Examples.ExplicitEvaluationInverse

/-! The complete retained appendix degree-eleven result: the original raw-key
coefficient bijection, the literal six-product circuit, and the explicit
interpolation-then-decoding evaluation inverse. Perfectness is used only by
the two named inverse-Frobenius operations in the high-row decoder. -/
namespace FastPoly.Char2PaperDegree11Realization

open Polynomial Char2Certificate Char2PaperDegree11Coordinates
open Char2PaperDegree11Inverse (coefficientEquiv)
set_option maxHeartbeats 20000
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

noncomputable def polynomial (a : Fin 11 → F) : F[X] :=
  Char2PaperDegree11.output (keys (rawInput a))
theorem polynomial_monic (a : Fin 11 → F) : IsMonicOfDegree (polynomial a) 11 :=
  Char2PaperDegree11.output_monic _
theorem polynomial_coeff (a : Fin 11 → F) (i : Fin 11) :
    (polynomial a).coeff i.val = coefficientEquiv a i := rfl

/-- Exactly equations (11.2)--(11.4), followed by the displayed raw-key map. -/
noncomputable def decoder (c : Fin 11 → F) : ℕ → F :=
  keys (Char2PaperDegree11Inverse.decode c)

theorem decoder_correct (c : Fin 11 → F) :
    Char2PaperDegree11.output (decoder c) = monicOfCoefficients c := by
  have he := ExplicitCircuitConstruction.polynomial_inverse polynomial coefficientEquiv
    polynomial_monic polynomial_coeff c
  change Char2PaperDegree11.output
    (keys (rawInput (rawKeys (Char2PaperDegree11Inverse.decode c)))) = _ at he
  rw [rawInput_rawKeys] at he
  exact he

noncomputable def construction : Construction F 11 6 :=
  ExplicitCircuitConstruction.construction Char2PaperDegree11Program.program
    (fun a => keys (rawInput a)) polynomial
    (fun a => Char2PaperDegree11Program.program_eval (keys (rawInput a)))
    coefficientEquiv polynomial_monic polynomial_coeff

theorem construction_decoder (c : Fin 11 → F) : construction.decoder c = decoder c := by
  change keys (rawInput (rawKeys (Char2PaperDegree11Inverse.decode c))) = _
  rw [rawInput_rawKeys]
  rfl

theorem monic_evaluation (P : F[X]) (hP : P.Monic) (hn : P.natDegree = 11) :
    (construction (F := F)).program.circuit.eval
      (inputEnv (decoder (fun i => P.coeff i))) 0 = P := by
  have he := (construction (F := F)).correct_polynomial P hP hn
  rw [construction_decoder] at he
  exact he

theorem polynomial_eq_monic (a : Fin 11 → F) :
    polynomial a = monicOfCoefficients (coefficientEquiv a) :=
  ExplicitCircuitConstruction.eq_monicOfCoefficients _ (polynomial_monic a)
    _ (polynomial_coeff a)

noncomputable def evaluationEquiv (x : Fin 11 → F) (hx : Function.Injective x) :
    (Fin 11 → F) ≃ (Fin 11 → F) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv coefficientEquiv (by omega) x hx

theorem evaluationEquiv_apply (x : Fin 11 → F) (hx : Function.Injective x)
    (a : Fin 11 → F) :
    evaluationEquiv x hx a = fun i => (polynomial a).eval (x i) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_apply coefficientEquiv (by omega)
    x hx polynomial polynomial_eq_monic a

theorem evaluationEquiv_symm_apply (x : Fin 11 → F) (hx : Function.Injective x)
    (values : Fin 11 → F) :
    (evaluationEquiv x hx).symm values =
      rawKeys (Char2PaperDegree11Inverse.decode (ExplicitEvaluationInverse.decode x values)) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_inverse coefficientEquiv (by omega) x hx values

end FastPoly.Char2PaperDegree11Realization
