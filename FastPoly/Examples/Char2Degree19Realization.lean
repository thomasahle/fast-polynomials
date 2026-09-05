import FastPoly.Examples.Char2Degree19Targets
import FastPoly.Examples.Char2Degree19Crown
import FastPoly.Examples.Char2Degree19InnerInverse
import FastPoly.Examples.Char2Degree19Program
import FastPoly.Examples.Char2Construction

/-!
# Assembling the existing degree-19 explicit inverse

The outer inverse first recovers the cubic shell, the inner crown, and the
final three offsets. The crown's explicit thirteen-row inverse can then be
used with that fixed shell. Finally, offsets 12, 13, and 18 are installed;
they do not occur in the crown, so this last step preserves the inner solve.

Every intermediate polynomial is kept named. The assembly uses the checked
component inverses and equality of the thirteen low rows, not expansion of
the full circuit or its preprocessed keys.
-/

namespace FastPoly.Char2Degree19Realization

set_option maxHeartbeats 20000

open Polynomial Char2Degree19Shell Char2Degree19Crown

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- Install the separately decoded low cubic's three offsets. -/
def withRemainder (a : ℕ → R) (tail : Triple R) : ℕ → R
  | 12 => tail.1
  | 13 => tail.2.1
  | 18 => tail.2.2
  | j => a j

omit [CharP R 2] [Nontrivial R] in
/-- These three outer offsets are absent from every gate of the inner crown. -/
theorem crown_withRemainder (a : ℕ → R) (tail : Triple R) :
    crown (withRemainder a tail) = crown a := rfl

/-- The assembled offsets preserve the shell and install the low cubic. -/
theorem output_withRemainder (a : ℕ → R) (tail : Triple R) :
    output (withRemainder a tail) =
      encode ((a 10, a 11, a 16), crown a, tail) := by
  rw [output_eq_encode]
  rfl

/-- Once the inner solve matches the decoded shell and crown, the existing
outer right inverse gives the desired target polynomial literally. -/
theorem output_eq_target (p : R[X]) (a : ℕ → R)
    (hshell : (a 10, a 11, a 16) = (decode p).1)
    (hcrown : crown a = (decode p).2.1) :
    output (withRemainder a (decode p).2.2) = p := by
  rw [output_withRemainder, hshell, hcrown]
  exact encode_decode p

omit [CharP R 2] [Nontrivial R] in
/-- The thirteen remaining coefficients determine a crown with the fixed
signature. The inverse's row order is descending, from 12 to 0. -/
theorem signature_ext {p q : R[X]} (hp : Signature p) (hq : Signature q)
    (hrows : ∀ i : Fin 13, p.coeff (12 - i.val) = q.coeff (12 - i.val)) :
    p = q := by
  ext j
  by_cases hj : j < 13
  · let i : Fin 13 := ⟨12 - j, by omega⟩
    have he : 12 - i.val = j := by dsimp only [i]; omega
    simpa only [he] using hrows i
  by_cases h13 : j = 13
  · subst j
    exact hp.row13.trans hq.row13.symm
  by_cases h14 : j = 14
  · subst j
    exact hp.row14.trans hq.row14.symm
  by_cases h15 : j = 15
  · subst j
    exact hp.row15.trans hq.row15.symm
  exact hp.monic.coeff_eq hq.monic (by omega)

/-- The three outer shell parameters, in the inner inverse's vector order. -/
def shellVector (shell : Triple R) (i : Fin 3) : R :=
  match i.val with
  | 0 => shell.1
  | 1 => shell.2.1
  | _ => shell.2.2

/-- Fix the shell read by the explicit monic-division inverse. -/
noncomputable def targetShell (p : R[X]) : Fin 3 → R :=
  shellVector (decode p).1

/-- The thirteen free crown rows, from coefficient twelve down to zero. -/
noncomputable def targetRows (p : R[X]) (i : Fin 13) : R :=
  (decode p).2.1.coeff (12 - i.val)

/-- Literal inner back-substitution at the already decoded shell. -/
noncomputable def decodeInner (p : R[X]) : Fin 13 → R :=
  (Char2Degree19InnerInverse.innerEquiv (targetShell p)).symm (targetRows p)

/-- Convert the decoded inner coordinates to the original circuit's raw keys. -/
noncomputable def innerKeys (p : R[X]) : ℕ → R :=
  Char2Degree19KeyUpdates.rawKeys
    (Char2Degree19InnerInverse.embed (targetShell p) (decodeInner p))

/-- The inner embedding retains precisely the three decoded shell parameters. -/
theorem innerKeys_shell (p : R[X]) :
    (innerKeys p 10, innerKeys p 11, innerKeys p 16) = (decode p).1 := rfl

/-- The explicit inner inverse matches all free rows; both crowns have the
same fixed signature, so no expansion of either polynomial is needed. -/
theorem innerKeys_crown (p : R[X]) (hp : IsMonicOfDegree p 19) :
    crown (innerKeys p) = (decode p).2.1 := by
  apply signature_ext (crown_signature (innerKeys p)) (decode_signature p hp)
  intro i
  change Char2Degree19InnerInverse.innerRows (targetShell p) (decodeInner p) i =
    targetRows p i
  exact congrFun
    ((Char2Degree19InnerInverse.innerEquiv (targetShell p)).apply_symm_apply
      (targetRows p)) i

/-- The complete degree-19 decoder: monic division, explicit inner
back-substitution, then the three independent outer offsets. -/
noncomputable def decodePolynomial (p : R[X]) : ℕ → R :=
  withRemainder (innerKeys p) (decode p).2.2

/-- Every monic degree-19 target is computed by the original fixed circuit
at the keys produced by this explicit decoder. -/
theorem decodePolynomial_correct (p : R[X]) (hp : IsMonicOfDegree p 19) :
    output (decodePolynomial p) = p :=
  output_eq_target p (innerKeys p) (innerKeys_shell p) (innerKeys_crown p hp)

section CoefficientTargets

variable {F : Type*} [Field F]

/-- The coefficient-vector interface really supplies a monic degree-19 target;
the low sum is bounded by its term degrees, without coefficient expansion. -/
theorem coefficientTarget_monic (c : Fin 19 → F) :
    IsMonicOfDegree (monicOfCoefficients c) 19 := by
  have hlow : (∑ j ∈ Finset.range 19, C (extendFin c j) * X ^ j).natDegree ≤ 18 := by
    refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
    simp only [Finset.fold_max_le]
    refine ⟨by omega, ?_⟩
    intro j hj
    apply (natDegree_C_mul_X_pow_le _ _).trans
    have hj' : j < 19 := Finset.mem_range.mp hj
    omega
  exact (isMonicOfDegree_X_pow F 19).add_right (hlow.trans_lt (by omega))

variable [CharP F 2]

/-- The same explicit decoder, with the public coefficient-vector interface. -/
noncomputable def decoder (c : Fin 19 → F) : ℕ → F :=
  decodePolynomial (monicOfCoefficients c)

/-- A fixed ten-multiplication circuit with its explicit degree-19 right
inverse, valid over every characteristic-two field. -/
noncomputable def construction : Char2Certificate.Construction F 19 10 where
  program := Char2Degree19Program.program
  decoder := decoder
  correct c := (Char2Degree19Program.program_eval _).trans
    (decodePolynomial_correct _ (coefficientTarget_monic c))

end CoefficientTargets

end FastPoly.Char2Degree19Realization
