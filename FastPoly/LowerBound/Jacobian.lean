/-
The degree-six lower bound (`sections/lower.tex`): the Jacobian obstruction.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination

/-!
# The Jacobian obstruction

This file is independent of the circuit model.  It collects

* the two singularity criteria and the three explicit solvers of small linear systems that
  the case analysis of `sections/lower.tex` uses (shared by `CaseDNonzero.lean`,
  `CaseDZero.lean` and `Defs.lean`), and
* the "bridge" step, about an arbitrary polynomial map
  `Q : Fin n → MvPolynomial (Fin n) F` over an infinite field `F`.

The main result, `RationalInverse.isEmpty_of_det_eq_zero`, is the "bridge" step of
`sections/lower.tex`:

> if the Jacobian determinant of `Q` vanishes at **some** parameter point, then `Q` admits
> no everywhere-defined rational inverse.

## Deviation from the paper

The paper argues "the denominator vanishes nowhere, hence (over an infinite field) it is a
nonzero constant, hence the inverse is polynomial", and then differentiates.  The middle
step is false over a non-algebraically-closed field (`x² + 1` vanishes nowhere on `ℚ`).
We avoid it entirely: we differentiate the *cleared-denominator* identity

`num_i(Q(p)) = p_i · den_i(Q(p))`

directly.  Contracting the resulting identity with a kernel vector `v ≠ 0` of the Jacobian
at `p₀` kills every term containing a Jacobian factor and leaves
`v_i · den_i(Q(p₀)) = 0`; since `den_i` does not vanish at the point `Q(p₀) ∈ Fⁿ` this
forces `v = 0`, a contradiction.  Only `Infinite F` is used (to pass from a pointwise
identity to a polynomial identity).
-/

namespace FastPoly.LowerBound

open MvPolynomial

/-! ## Chain rule for polynomial substitution -/

section ChainRule

variable {R : Type*} [CommRing R] {σ τ : Type*} [Fintype σ] [DecidableEq σ]

/-- **Chain rule.**  The partial derivative of a substituted polynomial. -/
theorem pderiv_bind₁ (j : τ) (Q : σ → MvPolynomial τ R) (f : MvPolynomial σ R) :
    pderiv j (bind₁ Q f) = ∑ k : σ, bind₁ Q (pderiv k f) * pderiv j (Q k) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
      simp only [map_add, hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f n hf =>
      have key : ∀ k : σ, (bind₁ Q) ((pderiv k) (f * X n)) * (pderiv j) (Q k)
          = (bind₁ Q) ((pderiv k) f) * (pderiv j) (Q k) * Q n
            + (if n = k then (bind₁ Q) f * (pderiv j) (Q k) else 0) := by
        intro k
        rw [pderiv_mul, pderiv_X, Pi.single_apply]
        split_ifs with h
        · simp only [map_add, map_mul, bind₁_X_right, mul_one]
          ring
        · simp only [map_mul, bind₁_X_right, mul_zero, add_zero]
          ring
      rw [Finset.sum_congr rfl fun k _ => key k, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_ite_eq Finset.univ n fun k => (bind₁ Q) f * (pderiv j) (Q k),
        map_mul, bind₁_X_right, pderiv_mul, hf]
      simp only [Finset.mem_univ, if_true]

end ChainRule

/-! ## Two ways for a square matrix to be singular -/

section Singular

variable {F : Type*} [Field F] {n : ℕ}

/-- Two equal rows make the determinant vanish.  This is the criterion used in
Case `D ≠ 0` of `sections/lower.tex`. -/
theorem det_eq_zero_of_rows_eq {M : Matrix (Fin n) (Fin n) F} {k l : Fin n} (hkl : k ≠ l)
    (h : ∀ i, M k i = M l i) : M.det = 0 :=
  Matrix.det_zero_of_row_eq hkl (funext h)

/-- A nonzero linear dependence among the rows makes the determinant vanish.  This is the
criterion used in Case `D = 0` of `sections/lower.tex`, with `w` supported on three of the
six rows and equal there to the weights of the functional `⟨·⟩`. -/
theorem det_eq_zero_of_rows_dep {M : Matrix (Fin n) (Fin n) F} (w : Fin n → F) (hw : w ≠ 0)
    (h : ∀ i, ∑ k, w k * M k i = 0) : M.det = 0 := by
  rw [← Matrix.det_transpose]
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, funext fun i => ?_⟩
  show ∑ k, M k i * w k = 0
  rw [← h i]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- A nonzero linear dependence among the *columns* makes the determinant vanish.  This is
the criterion behind the degenerate branches `s₃ = 0` and `E = 0` of `sections/lower.tex`,
where two Jacobian *columns* (parameter slots) are proportional. -/
theorem det_eq_zero_of_cols_dep {M : Matrix (Fin n) (Fin n) F} (v : Fin n → F) (hv : v ≠ 0)
    (h : ∀ k, ∑ i, M k i * v i = 0) : M.det = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, funext h⟩

end Singular

/-! ## Explicit solvers for the small linear systems

Every parameter choice in `sections/lower.tex` is made by solving an explicit linear
system, never by an abstract existence argument.  These three lemmas
are the only solvers used, and each of them *exhibits* its solution: a pivot, Cramer's
rule, or the nonvanishing adjugate column. -/

section SmallSystems

variable {F : Type*} [Field F]

/-- One linear equation `aS + bT = t` in two unknowns, with `(S,T) ≠ (0,0)`: pivot on
whichever of `S`, `T` is nonzero.  (Case `D ≠ 0`, Step 1b.) -/
theorem exists_solve_one {S T : F} (h : ¬(S = 0 ∧ T = 0)) (t : F) :
    ∃ a b : F, a * S + b * T = t := by
  by_cases hS : S = 0
  · have hT : T ≠ 0 := fun hT => h ⟨hS, hT⟩
    obtain ⟨e, he⟩ : ∃ e : F, T * e = 1 := ⟨T⁻¹, mul_inv_cancel₀ hT⟩
    exact ⟨0, t * e, by linear_combination t * he⟩
  · obtain ⟨e, he⟩ : ∃ e : F, S * e = 1 := ⟨S⁻¹, mul_inv_cancel₀ hS⟩
    exact ⟨t * e, 0, by linear_combination t * he⟩

/-- Cramer's rule for a `2 × 2` system with nonzero determinant, written with an explicitly
supplied inverse `e` of the determinant.  (Case `D ≠ 0`, Steps 0 and 2; Case `D = 0`,
Step 1.) -/
theorem exists_solve_two (m₁₁ m₁₂ m₂₁ m₂₂ : F) (hdet : m₁₁ * m₂₂ - m₁₂ * m₂₁ ≠ 0) (c₁ c₂ : F) :
    ∃ y z : F, m₁₁ * y + m₁₂ * z = c₁ ∧ m₂₁ * y + m₂₂ * z = c₂ := by
  obtain ⟨e, he⟩ : ∃ e : F, (m₁₁ * m₂₂ - m₁₂ * m₂₁) * e = 1 :=
    ⟨(m₁₁ * m₂₂ - m₁₂ * m₂₁)⁻¹, mul_inv_cancel₀ hdet⟩
  exact ⟨(c₁ * m₂₂ - m₁₂ * c₂) * e, (m₁₁ * c₂ - c₁ * m₂₁) * e,
    by linear_combination c₁ * he, by linear_combination c₂ * he⟩

/-- An explicit nonzero kernel vector of a singular `2 × 2` matrix `[[a, b], [s, d]]`: the
adjugate column that does not vanish.  (Degenerate branch `E = 0`.) -/
theorem exists_kernel_two {a b s d : F} (h : a * d - b * s = 0) :
    ∃ lam mu : F, (lam ≠ 0 ∨ mu ≠ 0) ∧ a * lam + b * mu = 0 ∧ s * lam + d * mu = 0 := by
  by_cases hsd : s = 0 ∧ d = 0
  · obtain ⟨hs, hd⟩ := hsd
    by_cases hab : a = 0 ∧ b = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by rw [hab.1, hab.2]; ring, by rw [hs, hd]; ring⟩
    · refine ⟨b, -a, ?_, by ring, by rw [hs, hd]; ring⟩
      rcases not_and_or.mp hab with h' | h'
      · exact Or.inr (neg_ne_zero.mpr h')
      · exact Or.inl h'
  · refine ⟨d, -s, ?_, by linear_combination h, by ring⟩
    rcases not_and_or.mp hsd with h' | h'
    · exact Or.inr (neg_ne_zero.mpr h')
    · exact Or.inl h'

end SmallSystems

/-! ## Polynomial maps, their Jacobians, and rational inverses -/

section Bridge

variable {F : Type*} [Field F] {n : ℕ}

/-- The map `Fⁿ → Fⁿ` determined by `n` polynomials in `n` variables. -/
noncomputable def polyMap (Q : Fin n → MvPolynomial (Fin n) F) (p : Fin n → F) : Fin n → F :=
  fun k => eval p (Q k)

/-- The Jacobian matrix `∂Q_k/∂p_i` of `Q`, evaluated at the point `p`. -/
noncomputable def polyJacobian (Q : Fin n → MvPolynomial (Fin n) F) (p : Fin n → F) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of fun k i => eval p (pderiv i (Q k))

@[simp] theorem polyJacobian_apply (Q : Fin n → MvPolynomial (Fin n) F) (p : Fin n → F)
    (k i : Fin n) : polyJacobian Q p k i = eval p (pderiv i (Q k)) := rfl

/-- An **everywhere-defined rational inverse** of the polynomial map `Q`: `n` rational
functions `num i / den i` whose denominators vanish nowhere on `Fⁿ`, and which invert `Q`
at every point.  The inversion equation is stated with the denominator cleared, so that no
division appears. -/
structure RationalInverse (Q : Fin n → MvPolynomial (Fin n) F) where
  /-- Numerators of the `n` coordinates of the inverse. -/
  num : Fin n → MvPolynomial (Fin n) F
  /-- Denominators of the `n` coordinates of the inverse. -/
  den : Fin n → MvPolynomial (Fin n) F
  /-- The inverse is defined everywhere: no denominator has a zero in `Fⁿ`. -/
  den_ne_zero : ∀ (i : Fin n) (q : Fin n → F), eval q (den i) ≠ 0
  /-- `(num i / den i) ∘ Q = pᵢ`, with the denominator cleared. -/
  inv_eq : ∀ (p : Fin n → F) (i : Fin n),
    eval (polyMap Q p) (num i) = p i * eval (polyMap Q p) (den i)

theorem eval_bind₁ (Q : Fin n → MvPolynomial (Fin n) F) (q : Fin n → F)
    (f : MvPolynomial (Fin n) F) : eval q (bind₁ Q f) = eval (polyMap Q q) f := by
  simpa [polyMap] using aeval_bind₁ (R := F) q Q f

/-- **The Jacobian obstruction.**  If the Jacobian determinant of `Q` vanishes at some
point, then `Q` has no everywhere-defined rational inverse. -/
theorem RationalInverse.isEmpty_of_det_eq_zero [Infinite F]
    (Q : Fin n → MvPolynomial (Fin n) F) (p₀ : Fin n → F)
    (hdet : (polyJacobian Q p₀).det = 0) : IsEmpty (RationalInverse Q) := by
  constructor
  intro inv
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  -- Clearing denominators gives a polynomial identity, because `F` is infinite.
  have hpoly : ∀ i, bind₁ Q (inv.num i) = X i * bind₁ Q (inv.den i) := by
    intro i
    apply MvPolynomial.funext
    intro q
    rw [eval_bind₁, map_mul, eval_X, eval_bind₁]
    exact inv.inv_eq q i
  -- Differentiate it.
  have hder : ∀ i j : Fin n,
      ∑ k, bind₁ Q (pderiv k (inv.num i)) * pderiv j (Q k)
        = (if i = j then (1 : MvPolynomial (Fin n) F) else 0) * bind₁ Q (inv.den i)
          + X i * ∑ k, bind₁ Q (pderiv k (inv.den i)) * pderiv j (Q k) := by
    intro i j
    have h := congrArg (fun t : MvPolynomial (Fin n) F => (pderiv j) t) (hpoly i)
    simp only [pderiv_mul, pderiv_X, Pi.single_apply] at h
    rw [pderiv_bind₁, pderiv_bind₁] at h
    exact h
  -- Evaluate at `p₀`.
  set A : Matrix (Fin n) (Fin n) F :=
    Matrix.of fun i k => eval p₀ (bind₁ Q (pderiv k (inv.num i))) with hA
  set B : Matrix (Fin n) (Fin n) F :=
    Matrix.of fun i k => eval p₀ (bind₁ Q (pderiv k (inv.den i))) with hB
  set J : Matrix (Fin n) (Fin n) F := polyJacobian Q p₀ with hJ
  have hentry : ∀ i j : Fin n,
      (A * J) i j
        = (if i = j then eval p₀ (bind₁ Q (inv.den i)) else 0) + p₀ i * (B * J) i j := by
    intro i j
    have h := congrArg (fun t : MvPolynomial (Fin n) F => eval p₀ t) (hder i j)
    simp only [map_sum, map_mul, map_add, eval_X, apply_ite (eval p₀), map_one,
      map_zero] at h
    simp only [Matrix.mul_apply, hA, hB, hJ, Matrix.of_apply, polyJacobian_apply]
    rw [h, Finset.mul_sum]
    congr 1
    · split_ifs <;> simp
  -- Contract with the kernel vector `v`.
  have hAJ : (A * J).mulVec v = 0 := by
    rw [← Matrix.mulVec_mulVec, hJ, hmul, Matrix.mulVec_zero]
  have hBJ : (B * J).mulVec v = 0 := by
    rw [← Matrix.mulVec_mulVec, hJ, hmul, Matrix.mulVec_zero]
  have hcoord : ∀ i : Fin n, v i = 0 := by
    intro i
    have h1 : ∑ j, (A * J) i j * v j = 0 := congrFun hAJ i
    have h2 : ∑ j, (B * J) i j * v j = 0 := congrFun hBJ i
    rw [Finset.sum_congr rfl fun j _ => by rw [hentry i j]] at h1
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, mul_assoc, ← Finset.mul_sum, h2, mul_zero, add_zero] at h1
    have hd : eval (polyMap Q p₀) (inv.den i) ≠ 0 := inv.den_ne_zero i _
    have hd' : eval p₀ (bind₁ Q (inv.den i)) ≠ 0 := by rwa [eval_bind₁]
    exact (mul_eq_zero.mp h1).resolve_left hd'
  exact hv (funext hcoord)

end Bridge

end FastPoly.LowerBound
