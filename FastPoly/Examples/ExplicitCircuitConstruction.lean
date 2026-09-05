import FastPoly.Examples.Char2Construction
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# From a supplied coefficient inverse to a counted polynomial construction

Keep the circuit polynomial and its preprocessing map named. Its monic degree,
the low coefficient identities, and an explicitly supplied equivalence suffice
to check the decoder. The proof never expands the circuit into a coefficient
formula or chooses parameters from an existential surjectivity result.
-/

namespace FastPoly.ExplicitCircuitConstruction

set_option maxHeartbeats 20000

open Polynomial Char2Certificate

variable {F : Type*} [Field F] {n m : ℕ} {Q : Type*}

/-- Two monic polynomials of the same degree agree once all lower rows agree. -/
theorem monic_ext {P S : F[X]} (hP : IsMonicOfDegree P n)
    (hS : IsMonicOfDegree S n)
    (h : ∀ i : Fin n, P.coeff i.val = S.coeff i.val) : P = S := by
  ext j
  by_cases hj : j < n
  · exact h ⟨j, hj⟩
  · exact hP.coeff_eq hS (by omega)

/-- The target representation is proved once, not by re-expanding each circuit. -/
theorem eq_monicOfCoefficients (P : F[X]) (hP : IsMonicOfDegree P n)
    (c : Fin n → F) (hc : ∀ i : Fin n, P.coeff i.val = c i) :
    P = monicOfCoefficients c := by
  have h := Char2Certificate.monic_eq_coefficients P hP.monic hP.natDegree_eq
  have he : (fun i : Fin n => P.coeff i) = c := funext hc
  rw [he] at h
  exact h

/-- The explicitly supplied equivalence is the whole decoder; the polynomial
is only inspected through its already-certified degree and coefficient rows. -/
theorem polynomial_inverse (P : Q → F[X]) (e : Q ≃ (Fin n → F))
    (hP : ∀ q, IsMonicOfDegree (P q) n)
    (hc : ∀ q (i : Fin n), (P q).coeff i.val = e q i) (c : Fin n → F) :
    P (e.symm c) = monicOfCoefficients c := by
  apply eq_monicOfCoefficients _ (hP _)
  intro i
  rw [hc, e.apply_symm_apply]

/-- Counted realization with a literal inverse, not a choice from bijectivity. -/
noncomputable def construction (program : Cost.MultiplicationProgram F ℕ 1 m)
    (offsets : Q → ℕ → F) (P : Q → F[X])
    (hp : ∀ q, program.circuit.eval (inputEnv (offsets q)) 0 = P q)
    (e : Q ≃ (Fin n → F)) (hP : ∀ q, IsMonicOfDegree (P q) n)
    (hc : ∀ q (i : Fin n), (P q).coeff i.val = e q i) : Construction F n m where
  program := program
  decoder c := offsets (e.symm c)
  correct c := (hp _).trans (polynomial_inverse P e hP hc c)

end FastPoly.ExplicitCircuitConstruction
