/-
The degree-six lower bound (`sections/lower.tex`): the main theorem.
-/
import FastPoly.LowerBound.CaseDNonzero
import FastPoly.LowerBound.CaseDZero
import FastPoly.LowerBound.Normalform
import Mathlib.Algebra.CharP.Basic

/-!
# Degree-six lower bound

This is the Lean counterpart of the Lemma (`6` parameters) of `sections/lower.tex`:

> Let `F` be an infinite field with `char F ≠ 2`, fix six **distinct** evaluation points
> `x₀, …, x₅ ∈ F`, and fix a straight-line program that uses **three** nonscalar
> multiplications and has **six** scalar parameters `p ∈ F⁶`, computing `P_p(x)`.  Then
> `F(p) = (P_p(x₀), …, P_p(x₅))` admits no everywhere-defined rational inverse.

The two statements below are `no_rationalInverse` (the normal form itself) and
`no_rationalInverse_affine` (the normal form with the six constant slots an arbitrary
affine image `M p + m₀` of the parameter vector, which is the shape the paper's reduction
produces).  `no_rationalInverse_affine_of_ringChar_ne_two` restates the latter with the
characteristic hypothesis written as `ringChar F ≠ 2`.

## Where each step of `sections/lower.tex` lives

| `sections/lower.tex` | Lean |
| --- | --- |
| "Straight-line programs"; the normal form `u₁ = x(R₁₀x+a₁)`, `u₂ = ℓ₂r₂`, `u₃ = ℓ₃r₃`, `P = s₃u₃+s₂u₂+s₁u₁+s₀x+b₁` | `Circuit`, `u1`, `ell2`, `r2`, `u2`, `ell3`, `r3`, `u3`, `out` (`Defs.lean`) |
| the chain rule `ū₃ = s₃`, `ū₂ = s₂ + ū₃(L₃₂r₃+R₃₂ℓ₃)`, `ū₁ = …` | `ubar3`, `ubar2`, `ubar1` (`Defs.lean`) |
| the sensitivity display `∂P/∂b₁ = 1`, `∂P/∂b₃ = s₃ℓ₃`, `∂P/∂a₃ = s₃r₃`, `∂P/∂b₂ = ū₂ℓ₂`, `∂P/∂a₂ = ū₂r₂`, `∂P/∂a₁ = ū₁x` | `sens`, proved to be the partial derivatives by `derivation_out` and `pderiv_outPoly` (`Defs.lean`) |
| `J_{k,i}(p) = ∂P_p(x_k)/∂p_i` | `jacobian` (`Defs.lean`), `polyJacobian` (`Jacobian.lean`), tied together by `polyJacobian_outPoly` (`Normalform.lean`) |
| "Proof method (Jacobian obstruction)": an everywhere-defined rational inverse forces `det J` to be a nonzero constant | `RationalInverse` and `RationalInverse.isEmpty_of_det_eq_zero` (`Jacobian.lean`) |
| "Reduction to a normal form", first two paragraphs (topological order, `(Ax+a)(Bx+b) = A·x(Bx+b) + a(Bx+b)`) | **not formalized**: this is the modelling step, encoded in the definitions of `Circuit`/`out` rather than proved — see "What is *not* formalized" below |
| "Reduction to a normal form", last paragraph (`(a₁,a₂,b₂,a₃,b₃,b₁) = Mp`, including `det M = 0`) | `slotPoly`, `outPolyAffine`, `polyJacobian_outPolyAffine` (`J_p = J·M`), `exists_singular_polyJacobian_affine` (`Normalform.lean`) |
| "it suffices to make two of its rows equal, or three of its rows linearly dependent" | `det_eq_zero_of_rows_eq`, `det_eq_zero_of_rows_dep` (`Jacobian.lean`) |
| "If `s₃ = 0` … the Jacobian is singular" (both cases) | `jacobian_det_eq_zero_of_s3_eq_zero` (`Defs.lean`) |
| "If `|L₂₀ L₂₁; R₂₀ R₂₁| = 0` then `r₂ = αℓ₂` … the Jacobian is singular" (both cases) | `exists_singular_jacobian_of_E_eq_zero` (`Defs.lean`) |
| Case `D ≠ 0`, Step 0 (the two slopes), Step 1a (`a₁`), Step 1b (`a₂,b₂`), Step 2 (`a₃,b₃`), Conclusion | `exists_singular_jacobian_of_D_ne_zero` (`CaseDNonzero.lean`), with the Conclusion display isolated as `sens_eq_of_ubar_vanish` |
| Case `D = 0`, subcase `L₃₂R₃₂ = 0`, and the branch `R₁₀ = 0` ("all six sensitivity polynomials have degree at most `4`") | `det_eq_zero_of_sens_natDegree_le` together with `sensPoly_natDegree_le_four_of_L32_R32`, `…_of_L32_L31`, `…_of_R32_R31`, `…_of_R10` (`CaseDZero.lean`) |
| Case `D = 0`, main construction: `f = L₃₂r₃+R₃₂ℓ₃` constant on `{x₀,x₁,x₂}`, then `ū₂ ≡ 0` there, then `⟨ℓ₃⟩ = ⟨r₃⟩ = 0` (the char `≠ 2` step) and `ū₁` constant | `exists_dependent_rows` (`CaseDZero.lean`) |
| Case `D = 0`, Conclusion (`⟨∂P/∂pᵢ⟩ = 0` for all six `i`) | `exists_singular_jacobian_of_D_eq_zero` (`CaseDZero.lean`) |
| the case split on `D = L₃₂R₃₁ - R₃₂L₃₁` | `exists_singular_jacobian` (this file) |
| the Lemma itself | `no_rationalInverse`, `no_rationalInverse_affine` (this file) |

## Deviations from the paper (each is a *weakening* of a hypothesis or a repair)

* **A one-sided inverse is enough.**  `RationalInverse Q` only asks that the rational map
  be a *left* inverse of `Q` (`(num i / den i) ∘ Q = pᵢ`, with the denominator cleared), so
  what is ruled out is weaker — hence the theorem stronger — than the paper's two-sided
  "rational inverse".
* **`Infinite F` instead of `algebraically closed`.**  The paper passes through "the
  denominator vanishes nowhere, hence by the Nullstellensatz it is a nonzero constant,
  hence the inverse is polynomial".  We never need that step: `RationalInverse` states the
  inversion equation with denominators cleared and `isEmpty_of_det_eq_zero` differentiates
  *that* identity, contracting it with a kernel vector of the singular Jacobian.  Only
  `Infinite F` is used (to turn a pointwise identity into a polynomial identity).  Since an
  algebraically closed field is infinite, the Lean statement implies the paper's.
* **The `E = 0` branch.**  The paper writes `(R₂₀,R₂₁) = α(L₂₀,L₂₁)`, which does not exist
  when `(L₂₀,L₂₁) = (0,0)`.  `exists_singular_jacobian_of_E_eq_zero` uses instead the
  explicit nonvanishing adjugate column of `[[R₂₁,L₂₁],[R₂₀,L₂₀]]`, covering both
  sub-cases uniformly.
* **Case `D ≠ 0`, Step 2.**  Imposing `ū₂(x₀) = 0` *before* solving for `(a₃,b₃)` removes
  the paper's `T = (L₂₁r₂ + R₂₁ℓ₂)(x₀)` from the `2 × 2` system; the determinant is the
  same `-s₃²D`.
* **Case `D = 0`, degree branches.**  Instead of the paper's divided-difference argument we
  use the plain rank bound: six polynomials of degree `≤ 4` evaluated at six points span at
  most `5` dimensions (`det_eq_zero_of_sens_natDegree_le`), which needs no distinctness of
  the points.

## What is *not* formalized

The first two paragraphs of "Reduction to a normal form" — topologically ordering the three
nonscalar multiplications of an arbitrary straight-line program, observing that every
multiplicand is then an affine form in `x` and the earlier gate outputs with *fixed*
coefficients, and absorbing the affine correction of the first multiplication — are
**modelling**, not a theorem: they are what the definitions `Circuit` and `out` of
`Defs.lean` and `outPolyAffine` of `Normalform.lean` encode.  There is no Lean datatype of
straight-line programs here, so "for every three-multiplication program" is not quantified
over inside Lean; the theorems below quantify over every circuit in the normal form and
every affine parameterization of its six constant slots.  Everything after that point in
the paper *is* proved, with no `sorry` anywhere in `FastPoly/LowerBound/`.
-/

namespace FastPoly.LowerBound

variable {F : Type*} [Field F]

/-- **The Jacobian of a normal-form three-multiplication program is singular somewhere.**
This is the whole content of the case analysis of `sections/lower.tex`: the split on
`D = L₃₂R₃₁ - R₃₂L₃₁`, with `exists_singular_jacobian_of_D_ne_zero` making two rows of the
Jacobian equal and `exists_singular_jacobian_of_D_eq_zero` making three rows linearly
dependent. -/
theorem exists_singular_jacobian (h2 : (2 : F) ≠ 0) (c : Circuit F) (xs : Fin 6 → F)
    (hxs : Function.Injective xs) : ∃ p : Fin 6 → F, (jacobian c xs p).det = 0 := by
  by_cases hD : c.D = 0
  · exact exists_singular_jacobian_of_D_eq_zero h2 c hD xs hxs
  · exact exists_singular_jacobian_of_D_ne_zero c hD xs hxs

/-- **Degree-six lower bound, normal form.**  Over an infinite field of characteristic
`≠ 2` (`h2 : (2 : F) ≠ 0`), and for six distinct evaluation points `xs`, the evaluation map
`p ↦ (P_p(x₀), …, P_p(x₅))` of a normal-form three-multiplication program with six
parameters has no everywhere-defined rational inverse. -/
theorem no_rationalInverse [Infinite F] (h2 : (2 : F) ≠ 0) (c : Circuit F) (xs : Fin 6 → F)
    (hxs : Function.Injective xs) : IsEmpty (RationalInverse (outPoly c xs)) := by
  obtain ⟨p, hp⟩ := exists_singular_jacobian h2 c xs hxs
  refine RationalInverse.isEmpty_of_det_eq_zero _ p ?_
  rw [polyJacobian_outPoly]
  exact hp

/-- **Degree-six lower bound.**  The same statement for an arbitrary affine
reparameterization `(a₁,a₂,b₂,a₃,b₃,b₁) = M p + m₀` of the six normal-form slots, which is
the output of the reduction in `sections/lower.tex`.  No invertibility of `M` is assumed:
when `det M = 0` the composite Jacobian is singular at every point. -/
theorem no_rationalInverse_affine [Infinite F] (h2 : (2 : F) ≠ 0) (c : Circuit F)
    (xs : Fin 6 → F) (hxs : Function.Injective xs) (M : Matrix (Fin 6) (Fin 6) F)
    (m₀ : Fin 6 → F) : IsEmpty (RationalInverse (outPolyAffine c xs M m₀)) := by
  obtain ⟨p, hp⟩ :=
    exists_singular_polyJacobian_affine c xs M m₀ (exists_singular_jacobian h2 c xs hxs)
  exact RationalInverse.isEmpty_of_det_eq_zero _ p hp

/-- **Degree-six lower bound**, with the characteristic hypothesis in the form
`ringChar F ≠ 2` used by the statement of the Lemma in `sections/lower.tex`. -/
theorem no_rationalInverse_affine_of_ringChar_ne_two [Infinite F] (hchar : ringChar F ≠ 2)
    (c : Circuit F) (xs : Fin 6 → F) (hxs : Function.Injective xs)
    (M : Matrix (Fin 6) (Fin 6) F) (m₀ : Fin 6 → F) :
    IsEmpty (RationalInverse (outPolyAffine c xs M m₀)) :=
  no_rationalInverse_affine (Ring.two_ne_zero hchar) c xs hxs M m₀

end FastPoly.LowerBound
