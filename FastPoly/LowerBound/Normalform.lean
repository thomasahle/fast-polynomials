/-
The degree-six lower bound (`sections/lower.tex`): the reduction to the normal form.
-/
import FastPoly.LowerBound.Defs
import FastPoly.LowerBound.Jacobian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Reduction to the normal form

`sections/lower.tex` reduces an arbitrary three-multiplication straight-line program with
six parameters to the normal form of `Defs.lean` in two steps.

1. *Shape.*  Topologically order the three nonscalar multiplications; every multiplicand is
   an affine form in `x` and the earlier gate outputs, with **fixed** coefficients on `x`
   and the `u_j` (multiplying a gate value by a parameter would cost a nonscalar
   multiplication) and a constant slot that is an affine form in the parameters.  The first
   multiplication `(Ax+a)(Bx+b)` with `A ≠ 0` is rewritten as `A·x(Bx+b) + a(Bx+b)`,
   absorbing the correction into the later affine uses, which normalizes it to
   `u₁ = x(R₁₀x + a₁)`.  This step is *modelling*: it is what the definition
   `outPolyAffine` below encodes, and it is not formalized as a theorem.

2. *Reparameterization.*  The six constant slots are then affine images
   `(a₁,a₂,b₂,a₃,b₃,b₁) = M p + m₀` of the actual parameter vector `p`.  This step **is**
   formalized here: `polyJacobian_outPolyAffine` shows the Jacobian of the reparameterized
   map is `J · M`, and `exists_singular_polyJacobian_affine` transfers the singularity
   statement.  In particular no invertibility assumption on `M` is needed: if `det M = 0`
   the composite Jacobian is singular everywhere.
-/

namespace FastPoly.LowerBound

open Matrix MvPolynomial

variable {F : Type*} [Field F]

/-- The six normal-form slots `(a₁,a₂,b₂,a₃,b₃,b₁) = M p + m₀` as affine functions of the
underlying parameter vector `p`. -/
def slotsOf (M : Matrix (Fin 6) (Fin 6) F) (m₀ p : Fin 6 → F) : Fin 6 → F := M *ᵥ p + m₀

/-- The six normal-form slots as polynomials in the parameters. -/
noncomputable def slotPoly (M : Matrix (Fin 6) (Fin 6) F) (m₀ : Fin 6 → F) :
    Fin 6 → MvPolynomial (Fin 6) F :=
  fun j => (∑ i, C (M j i) * X i) + C (m₀ j)

@[simp] theorem eval_slotPoly (M : Matrix (Fin 6) (Fin 6) F) (m₀ p : Fin 6 → F) (j : Fin 6) :
    eval p (slotPoly M m₀ j) = slotsOf M m₀ p j := by
  simp [slotPoly, slotsOf, Matrix.mulVec, dotProduct]

@[simp] theorem pderiv_slotPoly (M : Matrix (Fin 6) (Fin 6) F) (m₀ : Fin 6 → F) (i j : Fin 6) :
    pderiv i (slotPoly M m₀ j) = C (M j i) := by
  rw [slotPoly]
  simp only [map_add, pderiv_C, add_zero, map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The six output polynomials of the *reparameterized* program: the parameters enter the
six normal-form slots through the affine map `p ↦ M p + m₀`. -/
noncomputable def outPolyAffine (c : Circuit F) (xs : Fin 6 → F)
    (M : Matrix (Fin 6) (Fin 6) F) (m₀ : Fin 6 → F) : Fin 6 → MvPolynomial (Fin 6) F :=
  fun k => out (c.map C) (C (xs k)) (slotPoly M m₀)

@[simp] theorem polyMap_outPolyAffine (c : Circuit F) (xs : Fin 6 → F)
    (M : Matrix (Fin 6) (Fin 6) F) (m₀ p : Fin 6 → F) (k : Fin 6) :
    polyMap (outPolyAffine c xs M m₀) p k = out c (xs k) (slotsOf M m₀ p) := by
  have hmapC : (c.map (C : F → MvPolynomial (Fin 6) F)).map (eval p) = c := by
    rw [Circuit.map_map, Circuit.map_congr c (g := id) (fun y => by simp), Circuit.map_id]
  have hslot : (fun j => (eval p) (slotPoly M m₀ j)) = slotsOf M m₀ p := by
    funext j; exact eval_slotPoly M m₀ p j
  simp only [polyMap, outPolyAffine]
  rw [map_out (eval p) (c.map C) (C (xs k)) (slotPoly M m₀), hmapC, eval_C, hslot]

/-- The Jacobian of the reparameterized program is `J · M`: the chain rule for the affine
substitution `p ↦ M p + m₀`. -/
theorem polyJacobian_outPolyAffine (c : Circuit F) (xs : Fin 6 → F)
    (M : Matrix (Fin 6) (Fin 6) F) (m₀ p : Fin 6 → F) :
    polyJacobian (outPolyAffine c xs M m₀) p = jacobian c xs (slotsOf M m₀ p) * M := by
  funext k i
  have hmapC : (c.map (algebraMap F (MvPolynomial (Fin 6) F))).map (eval p) = c := by
    rw [Circuit.map_map, Circuit.map_congr c (g := id) (fun y => by simp), Circuit.map_id]
  have hslot : (fun j => (eval p) (slotPoly M m₀ j)) = slotsOf M m₀ p := by
    funext j; exact eval_slotPoly M m₀ p j
  simp only [polyJacobian_apply, outPolyAffine]
  rw [map_C_eq_map_algebraMap,
    derivation_out (pderiv i) c (C (xs k)) (by simp) (slotPoly M m₀), map_sum,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, pderiv_slotPoly, eval_C,
    map_sens (eval p) (c.map (algebraMap F (MvPolynomial (Fin 6) F))) (C (xs k))
      (slotPoly M m₀) j,
    hmapC, eval_C, hslot, jacobian_apply]

/-- The Jacobian of the program with the identity reparameterization is the closed-form
Jacobian of `Defs.lean`. -/
theorem polyJacobian_outPoly (c : Circuit F) (xs : Fin 6 → F) (p : Fin 6 → F) :
    polyJacobian (outPoly c xs) p = jacobian c xs p := by
  funext k i
  exact eval_pderiv_outPoly c xs p k i

/-- **The reparameterization step of the reduction.**  Singularity of the normal-form
Jacobian somewhere transfers to the reparameterized program, for *every* affine
reparameterization `p ↦ M p + m₀` — including the singular ones, where the composite
Jacobian is singular at every point. -/
theorem exists_singular_polyJacobian_affine (c : Circuit F) (xs : Fin 6 → F)
    (M : Matrix (Fin 6) (Fin 6) F) (m₀ : Fin 6 → F)
    (h : ∃ q : Fin 6 → F, (jacobian c xs q).det = 0) :
    ∃ p : Fin 6 → F, (polyJacobian (outPolyAffine c xs M m₀) p).det = 0 := by
  by_cases hM : M.det = 0
  · exact ⟨0, by rw [polyJacobian_outPolyAffine, Matrix.det_mul, hM, mul_zero]⟩
  · obtain ⟨q, hq⟩ := h
    refine ⟨M⁻¹ *ᵥ (q - m₀), ?_⟩
    have hs : slotsOf M m₀ (M⁻¹ *ᵥ (q - m₀)) = q := by
      rw [slotsOf, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
        Matrix.one_mulVec]
      abel
    rw [polyJacobian_outPolyAffine, hs, Matrix.det_mul, hq, zero_mul]

end FastPoly.LowerBound
