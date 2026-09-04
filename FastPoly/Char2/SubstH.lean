import FastPoly.Recover.Context
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

/-!
# The Artin–Schreier substitution bridge

Seed lemmas for the characteristic-two lane (coordination notes n+25/n+26).
The carrier is `H = X² + X`.  Three facts drive the final cap of the
punctured-pair interface (`char2_static_patterns.md` §27):

* `coeff_mem_of_comp_H` — the substitution `z ↦ H` is monic-triangular by
  degree, so the coefficients of `F` are recoverable, into any subalgebra,
  from the coefficients of `F(H)`.  Characteristic-free, unit pivots only.
* `comp_H_comp_add_one` — `H(x+1) = H(x)` in characteristic two, so every
  polynomial in `H` is invariant under the Artin–Schreier translation.
* `cap_difference` / `cap_gamma` — the finite difference of the cap
  `P = (x+β)(B(H)+γ) + A(H) + c` is exactly `B(H)+γ`, and the puncture
  `B(0) = 0` exposes `γ` at the constant row.
-/

namespace FastPoly.Char2

open Polynomial Algebra

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The Artin–Schreier quadratic. -/
noncomputable def H : A[X] := X ^ 2 + X

theorem H_monic : (H (A := A)).Monic := by
  rw [H]
  have hX : ((X : A[X])).degree < (2 : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_X_le (by exact_mod_cast one_lt_two)
  exact Polynomial.monic_X_pow_add hX

theorem H_natDegree_le : (H (A := A)).natDegree ≤ 2 := by
  rw [H]
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans natDegree_pow_le
      (by simpa using Nat.mul_le_mul_left 2 natDegree_X_le)
  · exact le_trans natDegree_X_le (by omega)

/-- Every coefficient of `H` is prime (zero or one), hence visible everywhere. -/
theorem H_coeff_mem (V : Subalgebra R A) (k : ℕ) : (H (A := A)).coeff k ∈ V := by
  rw [H, coeff_add, coeff_X_pow, coeff_X]
  split_ifs <;> (try simp only [add_zero, zero_add]) <;>
    first
      | exact add_mem V.one_mem V.one_mem
      | exact V.one_mem
      | exact V.zero_mem

/-- Every coefficient of `H ^ d` is visible everywhere. -/
theorem H_pow_coeff_mem (V : Subalgebra R A) (d : ℕ) :
    ∀ k, ((H (A := A)) ^ d).coeff k ∈ V := by
  induction d with
  | zero =>
    intro k
    rw [pow_zero, coeff_one]
    split_ifs
    · exact V.one_mem
    · exact V.zero_mem
  | succ d ih =>
    intro k
    rw [pow_succ, coeff_mul]
    exact Subalgebra.sum_mem _ fun p _ => mul_mem (ih p.1) (H_coeff_mem V p.2)

/-- **The substitution bridge** (characteristic-free): the coefficients of `F`
lie in any subalgebra containing the coefficients of `F(H)`. -/
theorem coeff_mem_of_comp_H [Nontrivial A] (V : Subalgebra R A) :
    ∀ F : A[X], (∀ m, (F.comp (H (A := A))).coeff m ∈ V) →
      ∀ j, F.coeff j ∈ V := by
  have main : ∀ fuel (F : A[X]), F.natDegree ≤ fuel →
      (∀ m, (F.comp (H (A := A))).coeff m ∈ V) → ∀ j, F.coeff j ∈ V := by
    intro fuel
    induction fuel with
    | zero =>
      intro F hdeg hcomp j
      have hF : F = C (F.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
      match j with
      | 0 =>
        have h0 := hcomp 0
        rw [hF] at h0 ⊢
        simpa using h0
      | j + 1 =>
        rw [hF, coeff_C, if_neg (by omega)]
        exact V.zero_mem
    | succ fuel ih =>
      intro F hdeg hcomp j
      by_cases hFf : F.natDegree ≤ fuel
      · exact ih F hFf hcomp j
      have hd : F.natDegree = fuel + 1 := by omega
      have hF0 : F ≠ 0 := fun h => by simp [h] at hd
      -- the top pivot: row `2·natDegree` of `F(H)` is the leading coefficient
      have hpivot : (F.comp (H (A := A))).coeff (2 * (fuel + 1))
          = F.coeff (fuel + 1) := by
        rw [comp_eq_sum_left, Polynomial.sum_def, finset_sum_coeff]
        rw [Finset.sum_eq_single (fuel + 1)]
        · rw [coeff_C_mul]
          have hm : ((H (A := A)) ^ (fuel + 1)).natDegree = 2 * (fuel + 1) := by
            rw [(H_monic (A := A)).natDegree_pow]
            have h2 : (H (A := A)).natDegree = 2 := by
              refine le_antisymm H_natDegree_le (le_natDegree_of_ne_zero ?_)
              rw [H, coeff_add, coeff_X_pow, if_pos rfl, coeff_X,
                if_neg (by omega), add_zero]
              exact one_ne_zero
            rw [h2, Nat.mul_comm]
          rw [show 2 * (fuel + 1) = ((H (A := A)) ^ (fuel + 1)).natDegree
              from hm.symm]
          rw [((H_monic (A := A)).pow _).coeff_natDegree, mul_one]
        · intro b hb hbne
          rw [coeff_C_mul]
          have hble : b ≤ fuel + 1 := hd ▸ le_natDegree_of_mem_supp b hb
          have hlt : ((H (A := A)) ^ b).natDegree < 2 * (fuel + 1) := by
            refine lt_of_le_of_lt (le_trans natDegree_pow_le
              (Nat.mul_le_mul_left b H_natDegree_le)) ?_
            omega
          rw [coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
        · intro hns
          exact absurd (hd ▸ natDegree_mem_support_of_nonzero hF0) hns
      have hlead : F.coeff (fuel + 1) ∈ V := hpivot ▸ hcomp _
      -- erase the lead and recurse
      have hFsplit : F.eraseLead + C (F.coeff (fuel + 1)) * X ^ (fuel + 1) = F := by
        have h := F.eraseLead_add_C_mul_X_pow
        rwa [Polynomial.leadingCoeff, hd] at h
      have hcomp_erase : ∀ m, (F.eraseLead.comp (H (A := A))).coeff m ∈ V := by
        intro m
        have hsplit : F.eraseLead.comp (H (A := A))
            = F.comp (H (A := A))
              - C (F.coeff (fuel + 1)) * (H (A := A)) ^ (fuel + 1) := by
          have h := congrArg (fun p : A[X] => p.comp (H (A := A))) hFsplit
          simp only [add_comp, mul_comp, C_comp, X_pow_comp] at h
          rw [← h]
          ring
        rw [hsplit, coeff_sub, coeff_C_mul]
        exact sub_mem (hcomp m) (mul_mem hlead (H_pow_coeff_mem V _ _))
      have herase := ih F.eraseLead
        (by have := F.eraseLead_natDegree_le; omega) hcomp_erase
      have hcoeff : F.coeff j = F.eraseLead.coeff j
          + F.coeff (fuel + 1) * ((X : A[X]) ^ (fuel + 1)).coeff j := by
        conv_lhs => rw [← hFsplit]
        rw [coeff_add, coeff_C_mul]
      rw [hcoeff]
      refine add_mem (herase j) (mul_mem hlead ?_)
      rw [coeff_X_pow]
      split_ifs
      · exact V.one_mem
      · exact V.zero_mem
  intro F
  exact main F.natDegree F le_rfl

/-! ## Characteristic two: translation invariance and the cap -/

theorem two_eq_zero_poly [CharP A 2] : (2 : A[X]) = 0 := by
  have h : C (2 : A) = (2 : A[X]) := map_ofNat C 2
  rw [← h, CharTwo.two_eq_zero, map_zero]

theorem H_comp_add_one [CharP A 2] : (H (A := A)).comp (X + 1) = H := by
  have h2 := two_eq_zero_poly (A := A)
  rw [H]
  simp only [add_comp, pow_comp, X_comp]
  linear_combination ((X : A[X]) + 1) * h2

/-- Every polynomial in `H` is Artin–Schreier translation-invariant. -/
theorem comp_H_comp_add_one [CharP A 2] (F : A[X]) :
    (F.comp (H (A := A))).comp (X + 1) = F.comp H := by
  rw [Polynomial.comp_assoc, H_comp_add_one]

/-- **The cap difference** (`char2_static_patterns.md` (27.2)): the finite
difference of `P = (x+β)(B(H)+γ) + A(H) + c` is `B(H)+γ`. -/
theorem cap_difference [CharP A 2] (B A' : A[X]) (β γ c : A) :
    ((X + C β) * (B.comp (H (A := A)) + C γ) + A'.comp H + C c).comp (X + 1)
      + ((X + C β) * (B.comp (H (A := A)) + C γ) + A'.comp H + C c)
      = B.comp H + C γ := by
  have h2 := two_eq_zero_poly (A := A)
  simp only [add_comp, mul_comp, X_comp, C_comp, comp_H_comp_add_one]
  linear_combination (((X : A[X]) + C β) * (B.comp (H (A := A)) + C γ)
    + A'.comp (H (A := A)) + C c) * h2

/-- The puncture `B(0) = 0` exposes `γ` at the constant row of the difference. -/
theorem cap_gamma (B : A[X]) (γ : A) (hB0 : B.coeff 0 = 0) :
    (B.comp (H (A := A)) + C γ).coeff 0 = γ := by
  rw [coeff_add, coeff_C, if_pos rfl]
  have hH0 : (H (A := A)).eval 0 = 0 := by simp [H]
  rw [show (B.comp (H (A := A))).coeff 0 = B.eval ((H (A := A)).eval 0) from by
    rw [coeff_zero_eq_eval_zero, eval_comp]]
  rw [hH0, ← coeff_zero_eq_eval_zero, hB0, zero_add]

end FastPoly.Char2
