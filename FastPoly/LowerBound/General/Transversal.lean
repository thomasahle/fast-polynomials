/-
The degree-six lower bound: case (iv), the explicit inverse `Θ` of `Q = ν ∘ H`.
-/
import FastPoly.LowerBound.General.Orbit

/-!
# Case (iv): the transversal case

When `κ = 0 ≠ c₁°` the orbit polynomial `ℓ · (O_q(u) − h₀) = c₁° u + c₀(q)` has the single
root `u(q) = −c₀(q)/c₁°` (`uOf`), so the fibre of `ν` over `q` meets `im H` in exactly one
point, `O_q(u(q))`, with the explicit preimage `Θ(q) = M⁺(O_q(u(q)) − h₀)` (`Theta`).  The
only fact about `Θ` the main theorem uses is `Q ∘ Θ = id` (`Qval_Theta`): the singular
point `q₀` of the normal-form Jacobian pulls back to `Θ(q₀)`.  No "the Jacobian of `Q` is
invertible, hence `Q` is bijective" step is needed.
-/

namespace FastPoly.LowerBound.General

open Matrix

variable {F : Type*} [Field F]

/-- The root of the orbit polynomial when `κ = 0`: `u(q) = −c₀(q)/c₁°`. -/
noncomputable def uOf (b : F) (ℓ h₀ : Fin 7 → F) (q : Fin 6 → F) : F := -(c0 ℓ h₀ q) / c1o b ℓ

/-- The inverse of `Q` in the transversal case: `Θ(q) = M⁺(O_q(u(q)) − h₀)`. -/
noncomputable def Theta (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) (i₀ : Fin 7) (q : Fin 6 → F) : Fin 6 → F :=
  MplusVec M i₀ (orbit b c q (uOf b (lker M i₀) h₀ q) - h₀)

theorem dot_orbit_uOf (b : F) (c : GCircuit F) (ℓ h₀ : Fin 7 → F) (hκ : kappa c ℓ = 0)
    (hc : c1o b ℓ ≠ 0) (q : Fin 6 → F) :
    ℓ ⬝ᵥ (orbit b c q (uOf b ℓ h₀ q) - h₀) = 0 := by
  rw [dot_orbit_sub, hκ, uOf]
  simp only [mul_zero, zero_mul, sub_zero, zero_add]
  rw [mul_div_cancel₀ _ hc, neg_add_cancel]

theorem affineSlots_Theta (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) {i₀ : Fin 7} (hd : (minor M i₀).det ≠ 0) (hκ : kappa c (lker M i₀) = 0)
    (hc : c1o b (lker M i₀) ≠ 0) (q : Fin 6 → F) :
    affineSlots M h₀ (Theta b c M h₀ i₀ q) = orbit b c q (uOf b (lker M i₀) h₀ q) := by
  rw [affineSlots, Theta,
    mulVec_MplusVec_of_dot_eq_zero M hd _ (dot_orbit_uOf b c (lker M i₀) h₀ hκ hc q),
    sub_add_cancel]

/-- **`Q ∘ Θ = id`** in the transversal case. -/
theorem Qval_Theta (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) {i₀ : Fin 7} (hd : (minor M i₀).det ≠ 0) (hκ : kappa c (lker M i₀) = 0)
    (hc : c1o b (lker M i₀) ≠ 0) (q : Fin 6 → F) :
    Qval b c M h₀ (Theta b c M h₀ i₀ q) = q := by
  rw [Qval, affineSlots_Theta b c M h₀ hd hκ hc q, nuSlots_orbit]

end FastPoly.LowerBound.General
