/-
The degree-six lower bound: the Jacobian of `Q = ν ∘ H`, its kernel direction, and
case (i) of the case split.
-/
import FastPoly.LowerBound.General.Affine
import Mathlib.Algebra.BigOperators.Fin

/-!
# The Jacobian of `Q = ν ∘ H`

`dnu b c z w` is the directional derivative `Dν(z) w` of the quadratic slot map `ν`; no
`6 × 7` matrix is ever built, because every singularity argument only needs `Dν(z)`
applied to a vector.  `xi b c z = (1, −b, −λ(v₁ − b u₁))` spans its kernel (`dnu_xi`).

The chain rule for `Q = ν ∘ H` at the vector level is `polyJacobian_Qpoly_mulVec`:
`DQ(p) v = Dν(H p) (M v)`.  Together with `polyJacobian_outPolyGeneral` this gives the two
singularity criteria `det_polyJacobian_Qpoly_eq_zero` and `det_eq_zero_of_dnu_kernel`, and
**case (i)**: a kernel vector of `M` makes `J_F` singular at every parameter point
(`det_eq_zero_of_mulVec_eq_zero`).
-/

namespace FastPoly.LowerBound.General

open Matrix MvPolynomial

section Dnu

variable {A : Type*} [CommRing A]

/-- The directional derivative `Dν(z) w` of the slot map `ν`. -/
def dnu (b : A) (c : GCircuit A) (z w : Fin 7 → A) : Fin 6 → A :=
  Matrix.vecCons (w 1 + b * w 0) fun j : Fin 5 =>
    w j.succ.succ + c.lam j * (w 0 * z 1 + z 0 * w 1)

/-- The gauge direction `ξ(z) = (1, −b, −λ(v₁ − b u₁))`, spanning `ker Dν(z)`. -/
def xi (b : A) (c : GCircuit A) (z : Fin 7 → A) : Fin 7 → A :=
  Matrix.vecCons 1 (Matrix.vecCons (-b) fun j : Fin 5 => -(c.lam j * (z 1 - b * z 0)))

variable (b : A) (c : GCircuit A) (z w : Fin 7 → A)

@[simp] theorem dnu_zero_apply : dnu b c z w 0 = w 1 + b * w 0 := rfl
@[simp] theorem dnu_succ_apply (j : Fin 5) :
    dnu b c z w j.succ = w j.succ.succ + c.lam j * (w 0 * z 1 + z 0 * w 1) := by
  simp only [dnu, Matrix.cons_val_succ]

@[simp] theorem xi_zero : xi b c z 0 = 1 := rfl
@[simp] theorem xi_one : xi b c z 1 = -b := rfl
@[simp] theorem xi_succ_succ (j : Fin 5) :
    xi b c z j.succ.succ = -(c.lam j * (z 1 - b * z 0)) := by
  simp only [xi, Matrix.cons_val_succ]
@[simp] theorem xi_two : xi b c z 2 = -(c.p21 * (z 1 - b * z 0)) := rfl
@[simp] theorem xi_three : xi b c z 3 = -(c.q21 * (z 1 - b * z 0)) := rfl
@[simp] theorem xi_four : xi b c z 4 = -(c.p31 * (z 1 - b * z 0)) := rfl
@[simp] theorem xi_five : xi b c z 5 = -(c.q31 * (z 1 - b * z 0)) := rfl
@[simp] theorem xi_six : xi b c z 6 = -(c.r1 * (z 1 - b * z 0)) := rfl

theorem dnu_zero : dnu b c z 0 = 0 := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [dnu_zero_apply, Pi.zero_apply, mul_zero, add_zero]
  · simp only [dnu_succ_apply, Pi.zero_apply, mul_zero, zero_mul, add_zero]

/-- `ξ(z) ∈ ker Dν(z)`. -/
theorem dnu_xi : dnu b c z (xi b c z) = 0 := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [dnu_zero_apply, xi_zero, xi_one, Pi.zero_apply]
    ring
  · simp only [dnu_succ_apply, xi_zero, xi_one, xi_succ_succ, Pi.zero_apply]
    ring

end Dnu

section Field

variable {F : Type*} [Field F] (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
  (h₀ : Fin 7 → F)

theorem pderiv_Qpoly_zero (i : Fin 6) :
    pderiv i (Qpoly b c M h₀ 0) = C (M 1 i + b * M 0 i) := by
  simp only [Qpoly, nuSlots_zero, map_add, pderiv_C_mul, pderiv_affineSlotPoly, C_mul]

theorem pderiv_Qpoly_succ (j : Fin 5) (i : Fin 6) :
    pderiv i (Qpoly b c M h₀ j.succ)
      = C (M j.succ.succ i)
        + C (c.lam j) * (C (M 0 i) * affineSlotPoly M h₀ 1 + affineSlotPoly M h₀ 0 * C (M 1 i)) := by
  simp only [Qpoly, nuSlots_succ, GCircuit.lam_map, map_add, pderiv_mul, pderiv_C,
    pderiv_affineSlotPoly, zero_mul, zero_add]

theorem polyJacobian_Qpoly_zero (p : Fin 6 → F) (i : Fin 6) :
    polyJacobian (Qpoly b c M h₀) p 0 i = M 1 i + b * M 0 i := by
  rw [polyJacobian_apply, pderiv_Qpoly_zero, eval_C]

theorem polyJacobian_Qpoly_succ (p : Fin 6 → F) (j : Fin 5) (i : Fin 6) :
    polyJacobian (Qpoly b c M h₀) p j.succ i
      = M j.succ.succ i
        + c.lam j * (M 0 i * affineSlots M h₀ p 1 + affineSlots M h₀ p 0 * M 1 i) := by
  rw [polyJacobian_apply, pderiv_Qpoly_succ]
  simp only [map_add, map_mul, eval_C, eval_affineSlotPoly]

/-- **Chain rule for `Q = ν ∘ H` at the vector level:** `DQ(p) v = Dν(H p) (M v)`. -/
theorem polyJacobian_Qpoly_mulVec (p v : Fin 6 → F) :
    polyJacobian (Qpoly b c M h₀) p *ᵥ v = dnu b c (affineSlots M h₀ p) (M *ᵥ v) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.mulVec, dotProduct, polyJacobian_Qpoly_zero, dnu_zero_apply,
      Fin.sum_univ_six]
    ring
  · simp only [Matrix.mulVec, dotProduct, polyJacobian_Qpoly_succ, dnu_succ_apply,
      Fin.sum_univ_six]
    ring

/-- Singularity criterion for `DQ`: a nonzero `v` with `Dν(H p) (M v) = 0`. -/
theorem det_polyJacobian_Qpoly_eq_zero (p v : Fin 6 → F) (hv : v ≠ 0)
    (h : dnu b c (affineSlots M h₀ p) (M *ᵥ v) = 0) :
    (polyJacobian (Qpoly b c M h₀) p).det = 0 := by
  refine det_eq_zero_of_cols_dep v hv fun k => ?_
  have hk := congrFun (polyJacobian_Qpoly_mulVec b c M h₀ p v) k
  rw [h, Pi.zero_apply] at hk
  exact hk

/-- Singularity criterion for `J_F`. -/
theorem det_eq_zero_of_dnu_kernel (hb : c.β₁ = c.α₁ * b) (xs : Fin 6 → F) (p v : Fin 6 → F)
    (hv : v ≠ 0) (h : dnu b c (affineSlots M h₀ p) (M *ᵥ v) = 0) :
    (polyJacobian (outPolyGeneral c xs M h₀) p).det = 0 := by
  rw [polyJacobian_outPolyGeneral c hb, Matrix.det_mul,
    det_polyJacobian_Qpoly_eq_zero b c M h₀ p v hv h, mul_zero]

/-- **Case (i).**  A kernel vector of `M` makes `J_F` singular at every parameter point. -/
theorem det_eq_zero_of_mulVec_eq_zero (hb : c.β₁ = c.α₁ * b) (xs : Fin 6 → F) (p : Fin 6 → F)
    (v : Fin 6 → F) (hv : v ≠ 0) (hMv : M *ᵥ v = 0) :
    (polyJacobian (outPolyGeneral c xs M h₀) p).det = 0 :=
  det_eq_zero_of_dnu_kernel b c M h₀ hb xs p v hv (by rw [hMv, dnu_zero])

end Field

end FastPoly.LowerBound.General
