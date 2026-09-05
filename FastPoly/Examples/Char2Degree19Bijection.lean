import FastPoly.Examples.Char2Degree19Realization
import FastPoly.Examples.ExplicitEvaluationInverse

/-!
# The original degree-19 raw-key bijection and its explicit inverse

The realization decoder also recovers the original raw keys.  First split
the already invertible normalized coordinates into shell, inner, and outer
slots.  The inner inverse recovers the thirteen inner slots, and installation
of the three decoded remainder offsets restores the whole raw-key vector.
No gate polynomial or recursive coefficient baseline is expanded.

The public coefficient equivalence uses that very decoder in both directions.
Its composition with the named Lagrange inverse gives an evaluation equivalence
at any nineteen distinct points of any characteristic-two field.
-/

namespace FastPoly.Char2Degree19Bijection

set_option maxHeartbeats 20000

open Polynomial Char2Degree19Coordinates Char2Degree19KeyUpdates
open Char2Degree19InnerInverse Char2Degree19Realization Char2Degree19Crown

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The first three normalized coordinates, kept as the fixed shell. -/
def shellOf (q : Fin 19 → R) (i : Fin 3) : R := q ⟨i.val, by omega⟩

/-- The thirteen normalized inner coordinates, in decoding order. -/
def innerOf (q : Fin 19 → R) (i : Fin 13) : R := q (innerIndex i)

/-- The three separately installed normalized outer coordinates. -/
def tailOf (q : Fin 19 → R) : Char2Degree19Shell.Triple R := (q 16, q 17, q 18)

omit [CharP R 2] in
/-- Splitting and restoring the coordinate vector is the displayed key inverse.
Only the nineteen fixed index cases are checked; no field values are enumerated. -/
theorem restoreEmbedding (q : Fin 19 → R) :
    withRemainder (rawKeys (embed (shellOf q) (innerOf q))) (tailOf q) = rawKeys q := by
  funext i
  by_cases hi : i < 19
  · interval_cases i <;> rfl
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
    have hk : ¬ k + 19 < 19 := by omega
    simp only [withRemainder, rawKeys, dif_neg hk]

variable [Nontrivial R]

omit [CharP R 2] [Nontrivial R] in
/-- The zeroed outer slots do not occur in the named crown. -/
theorem crown_embedding (q : Fin 19 → R) :
    crown (rawKeys (embed (shellOf q) (innerOf q))) = crown (rawKeys q) := by
  have he := congrArg crown (restoreEmbedding q)
  rw [crown_withRemainder] at he
  exact he

/-- The explicit outer decoder reads precisely the canonical shell. -/
theorem targetShell_output (q : Fin 19 → R) :
    targetShell (output (rawKeys q)) = shellOf q := by
  rw [targetShell, decode_output]
  funext i
  fin_cases i <;> rfl

/-- The crown rows in the outer decoder are the canonical inner forward map. -/
theorem targetRows_output (q : Fin 19 → R) :
    targetRows (output (rawKeys q)) = innerRows (shellOf q) (innerOf q) := by
  funext i
  rw [targetRows, decode_output]
  change (crown (rawKeys q)).coeff (12 - i.val) =
    (crown (rawKeys (embed (shellOf q) (innerOf q)))).coeff (12 - i.val)
  rw [crown_embedding]

/-- The left composition of the supplied inner inverse recovers every inner key. -/
theorem decodeInner_output (q : Fin 19 → R) :
    decodeInner (output (rawKeys q)) = innerOf q := by
  rw [decodeInner, targetShell_output, targetRows_output]
  exact (innerEquiv (shellOf q)).symm_apply_apply (innerOf q)

theorem innerKeys_output (q : Fin 19 → R) :
    innerKeys (output (rawKeys q)) = rawKeys (embed (shellOf q) (innerOf q)) := by
  rw [innerKeys, targetShell_output, decodeInner_output]

/-- The named full decoder restores the raw inverse of every coordinate vector. -/
theorem decodePolynomial_output_rawKeys (q : Fin 19 → R) :
    decodePolynomial (output (rawKeys q)) = rawKeys q := by
  rw [decodePolynomial, innerKeys_output, decode_output]
  change withRemainder (rawKeys (embed (shellOf q) (innerOf q))) (tailOf q) = rawKeys q
  exact restoreEmbedding q

/-- Degree follows from the opaque crown and the two named cubic factors. -/
theorem output_monic (a : ℕ → R) : IsMonicOfDegree (output a) 19 := by
  rw [output_eq_encode]
  change IsMonicOfDegree
    (Char2Degree19Shell.cubic (a 10, a 11, a 16) * crown a +
      Char2Degree19Shell.cubic (a 12, a 13, a 18)) 19
  have hprod : IsMonicOfDegree
      (Char2Degree19Shell.cubic (a 10, a 11, a 16) * crown a) 19 :=
    (Char2Degree19Shell.cubic_monic _).mul (crown_monic a)
  apply hprod.add_right
  rw [(Char2Degree19Shell.cubic_monic (a 12, a 13, a 18)).natDegree_eq]
  omega

section Field

variable {F : Type*} [Field F] [CharP F 2]

/-- Use the already checked two-sided coordinate inverse, not a new solve. -/
theorem rawKeys_coordinates (a : Fin 19 → F) :
    rawKeys (coordinates a) = extendFin a := by
  funext i
  simp only [rawKeys, keys_coordinates, extendFin]

/-- Decoding the output recovers the original nineteen raw offsets, extended by zero. -/
theorem decodePolynomial_output (a : Fin 19 → F) :
    decodePolynomial (output (extendFin a)) = extendFin a := by
  rw [← rawKeys_coordinates a]
  exact decodePolynomial_output_rawKeys (coordinates a)

/-- The concrete raw-key left inverse, at every genuine circuit input slot. -/
theorem decodePolynomial_output_at (a : Fin 19 → F) (i : Fin 19) :
    decodePolynomial (output (extendFin a)) i = a i := by
  rw [decodePolynomial_output]
  exact dif_pos i.isLt

/-- Restrict the very same polynomial decoder to its nineteen actual input slots. -/
noncomputable def decodeFin (p : F[X]) (i : Fin 19) : F := decodePolynomial p i

/-- The full decoder has no extra unspecified offsets outside its nineteen keys. -/
theorem decodePolynomial_above (p : F[X]) (i : ℕ) (hi : 19 ≤ i) :
    decodePolynomial p i = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 19 := ⟨i - 19, by omega⟩
  have hk : ¬ k + 19 < 19 := by omega
  simp only [decodePolynomial, withRemainder, innerKeys, rawKeys, dif_neg hk]

theorem extend_decodeFin (p : F[X]) : extendFin (decodeFin p) = decodePolynomial p := by
  funext i
  by_cases hi : i < 19
  · simp only [extendFin, dif_pos hi, decodeFin]
  · rw [extendFin, dif_neg hi, decodePolynomial_above p i (by omega)]

/-- Read the low coefficients of the actual raw-key circuit output. -/
noncomputable def coefficients (a : Fin 19 → F) (i : Fin 19) : F :=
  (output (extendFin a)).coeff i

/-- The supplied coefficient inverse: construct the monic target and decode it. -/
noncomputable def decodeCoefficients (c : Fin 19 → F) : Fin 19 → F :=
  decodeFin (monicOfCoefficients c)

theorem output_eq_monic (a : Fin 19 → F) :
    output (extendFin a) = monicOfCoefficients (coefficients a) :=
  Char2Certificate.monic_eq_coefficients _ (output_monic _).monic
    (output_monic _).natDegree_eq

/-- First composition: the original raw keys, not only some realizing keys. -/
theorem decodeCoefficients_coefficients (a : Fin 19 → F) :
    decodeCoefficients (coefficients a) = a := by
  funext i
  change decodePolynomial (monicOfCoefficients (coefficients a)) i = a i
  rw [← output_eq_monic]
  exact decodePolynomial_output_at a i

omit [CharP F 2] in
theorem coefficientTarget_coeff (c : Fin 19 → F) (i : Fin 19) :
    (monicOfCoefficients c).coeff i = c i := by
  have hi : i.val ≠ 19 := by omega
  rw [ExplicitEvaluationInverse.monic_eq, coeff_add,
    ExplicitEvaluationInverse.low_coeff, coeff_X_pow, if_neg hi, zero_add]

/-- Second composition: the already checked realization decoder reaches every target. -/
theorem coefficients_decodeCoefficients (c : Fin 19 → F) :
    coefficients (decodeCoefficients c) = c := by
  funext i
  change (output (extendFin (decodeFin (monicOfCoefficients c)))).coeff i = c i
  rw [extend_decodeFin, decodePolynomial_correct _ (coefficientTarget_monic c)]
  exact coefficientTarget_coeff c i

/-- Original raw keys and all nineteen low coefficients are explicitly equivalent. -/
noncomputable def coefficientEquiv : (Fin 19 → F) ≃ (Fin 19 → F) where
  toFun := coefficients
  invFun := decodeCoefficients
  left_inv := decodeCoefficients_coefficients
  right_inv := coefficients_decodeCoefficients

theorem coefficientEquiv_apply (a : Fin 19 → F) :
    coefficientEquiv a = coefficients a := rfl

theorem coefficientEquiv_symm_apply (c : Fin 19 → F) :
    coefficientEquiv.symm c = decodeCoefficients c := rfl

/-- Explicit Lagrange interpolation followed by the original circuit decoder. -/
noncomputable def evaluationEquiv (x : Fin 19 → F) (hx : Function.Injective x) :
    (Fin 19 → F) ≃ (Fin 19 → F) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv coefficientEquiv (by omega) x hx

theorem evaluationEquiv_apply (x : Fin 19 → F) (hx : Function.Injective x)
    (a : Fin 19 → F) :
    evaluationEquiv x hx a = fun i => (output (extendFin a)).eval (x i) :=
  ExplicitEvaluationInverse.familyEvaluationEquiv_apply coefficientEquiv (by omega)
    x hx (fun a => output (extendFin a)) output_eq_monic a

theorem evaluationEquiv_symm_apply (x : Fin 19 → F) (hx : Function.Injective x)
    (values : Fin 19 → F) :
    (evaluationEquiv x hx).symm values =
      decodeCoefficients (ExplicitEvaluationInverse.decode x values) :=
  (ExplicitEvaluationInverse.familyEvaluationEquiv_inverse coefficientEquiv
    (by omega) x hx values).trans (coefficientEquiv_symm_apply _)

/-- Both explicit compositions imply the raw-key evaluation map is bijective. -/
theorem evaluation_bijective (x : Fin 19 → F) (hx : Function.Injective x) :
    Function.Bijective (fun a : Fin 19 → F => fun i : Fin 19 =>
      (output (extendFin a)).eval (x i)) := by
  have he : (fun a : Fin 19 → F => fun i : Fin 19 =>
      (output (extendFin a)).eval (x i)) = evaluationEquiv x hx := by
    funext a
    exact (evaluationEquiv_apply x hx a).symm
  rw [he]
  exact (evaluationEquiv x hx).bijective

end Field

end FastPoly.Char2Degree19Bijection
