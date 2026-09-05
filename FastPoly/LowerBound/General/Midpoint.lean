/-
The degree-six lower bound: the midpoint identity for the quadratic map `Q = ν ∘ H` and
case (ii) of the case split (route B).
-/
import FastPoly.LowerBound.General.DQ

/-!
# The midpoint identity and case (ii)

For the quadratic map `Q = ν ∘ H`, and in characteristic `≠ 2`,

`Q(p) − Q(p') = DQ((p + p')/2) (p − p')`   (`Qval_sub_eq_mulVec`),

so two distinct parameter points with the same normal-form slots make `J_F` singular at
their rational midpoint (`det_eq_zero_of_Qval_eq`).  This is case (ii) of the repaired
reduction (`sections/lower_char_p_draft.tex`, `rem:charp-lower-gap`); the
characteristic-free assembly in `Main.lean` does not use it, but the statement is proved
so that the remark can cite it.
-/

namespace FastPoly.LowerBound.General

open Matrix MvPolynomial

variable {F : Type*} [Field F]

/-- The rational midpoint of two parameter points. -/
def mid (p p' : Fin 6 → F) : Fin 6 → F := fun i => (p i + p' i) / 2

/-- **Midpoint identity for `ν`.** -/
theorem nuSlots_sub_eq_dnu (h2 : (2 : F) ≠ 0) (b : F) (c : GCircuit F) (z z' : Fin 7 → F) :
    nuSlots b c z - nuSlots b c z' = dnu b c (fun i => (z i + z' i) / 2) (z - z') := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Pi.sub_apply, nuSlots_zero, dnu_zero_apply]
    ring
  · simp only [Pi.sub_apply, nuSlots_succ, dnu_succ_apply, div_eq_mul_inv]
    linear_combination (-(c.lam j * (z 0 * z 1 - z' 0 * z' 1))) * h

theorem affineSlots_mid (h2 : (2 : F) ≠ 0) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F)
    (p p' : Fin 6 → F) :
    affineSlots M h₀ (mid p p')
      = fun i => (affineSlots M h₀ p i + affineSlots M h₀ p' i) / 2 := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  funext i
  simp only [affineSlots, mid, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
    div_eq_mul_inv]
  linear_combination (-(h₀ i)) * h

/-- **Midpoint identity for `Q = ν ∘ H`:** `Q p − Q p' = DQ((p + p')/2) (p − p')`. -/
theorem Qval_sub_eq_mulVec (h2 : (2 : F) ≠ 0) (b : F) (c : GCircuit F)
    (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) (p p' : Fin 6 → F) :
    Qval b c M h₀ p - Qval b c M h₀ p'
      = polyJacobian (Qpoly b c M h₀) (mid p p') *ᵥ (p - p') := by
  rw [polyJacobian_Qpoly_mulVec, ← affineSlots_sub M h₀, affineSlots_mid h2, Qval, Qval,
    nuSlots_sub_eq_dnu h2]

/-- **Case (ii).**  Two distinct parameter points with the same normal-form slots make `J_F`
singular at their midpoint. -/
theorem det_eq_zero_of_Qval_eq (h2 : (2 : F) ≠ 0) (b : F) (c : GCircuit F)
    (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) (hb : c.β₁ = c.α₁ * b) (xs : Fin 6 → F)
    (p p' : Fin 6 → F) (hne : p ≠ p') (hQ : Qval b c M h₀ p = Qval b c M h₀ p') :
    (polyJacobian (outPolyGeneral c xs M h₀) (mid p p')).det = 0 :=
  det_eq_zero_of_dnu_kernel b c M h₀ hb xs (mid p p') (p - p') (sub_ne_zero.mpr hne)
    (by rw [← polyJacobian_Qpoly_mulVec, ← Qval_sub_eq_mulVec h2, hQ, sub_self])

end FastPoly.LowerBound.General
