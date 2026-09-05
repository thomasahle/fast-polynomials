/-
The degree-six lower bound: the gauge identity and the reduction to the normal form.
-/
import FastPoly.LowerBound.General.Defs
import Mathlib.Tactic.LinearCombination

/-!
# The reduction identity

The first-gate absorption of the appendix's "Reduction to a normal form" paragraph, in
its repaired form (`sections/lower_char_p_draft.tex`, `rem:charp-lower-gap`; the
`x`-free correction).  With a scalar `b` such that `β₁ = α₁ b`,

`(α₁ x + u₁)(β₁ x + v₁) = α₁ · x (β₁ x + v₁ + b u₁) + u₁ v₁`  (`g1_eq`),

and the correction `u₁ v₁` is `x`-free, so it goes into the constant slots of every later
use of `G₁`.  Consequently the general program *is* the normal-form program with constants
`c.toNormal` and slots `nuSlots b c z` (`gout_eq`).  The scalar first gate (`α₁ = β₁ = 0`)
needs no separate treatment: `hb` holds with `b = 0`, and the resulting normal form has
`L₂₁ = R₂₁ = L₃₁ = R₃₁ = s₁ = 0`.  When `α₁ = 0 ≠ β₁` the two factors are interchanged
first (`gout_swap`).

The gate lemmas rewrite only the previous gate lemmas and unfold one normal-form gate each,
so every `ring` goal is small (the atoms are `u1 …`, `u2 …`, `u3 …`).
-/

namespace FastPoly.LowerBound.General

variable {A : Type*} [CommRing A]

section Gauge

variable (c : GCircuit A) {b : A} (hb : c.β₁ = c.α₁ * b) (x : A) (z : Fin 7 → A)
include hb

/-- **The gauge identity.**  `G₁ = α₁ · u₁'(ν z) + u₁ v₁`, where `u₁' = x (R₁₀ x + a₁)` is
the normal-form first gate with `R₁₀ = β₁` and `a₁ = v₁ + b u₁`. -/
theorem g1_eq : g1 c x z = c.α₁ * u1 c.toNormal x (nuSlots b c z) + z 0 * z 1 := by
  simp only [g1, u1, GCircuit.toNormal_R10, nuSlots_zero]
  linear_combination (z 0 * x) * hb

theorem gl2_eq : gl2 c x z = ell2 c.toNormal x (nuSlots b c z) := by
  rw [gl2, g1_eq c hb, ell2]
  simp only [GCircuit.toNormal_L21, GCircuit.toNormal_L20, nuSlots_one]
  ring

theorem gr2_eq : gr2 c x z = r2 c.toNormal x (nuSlots b c z) := by
  rw [gr2, g1_eq c hb, r2]
  simp only [GCircuit.toNormal_R21, GCircuit.toNormal_R20, nuSlots_two]
  ring

theorem g2_eq : g2 c x z = u2 c.toNormal x (nuSlots b c z) := by
  rw [g2, gl2_eq c hb, gr2_eq c hb]
  rfl

theorem gl3_eq : gl3 c x z = ell3 c.toNormal x (nuSlots b c z) := by
  rw [gl3, g1_eq c hb, g2_eq c hb, ell3]
  simp only [GCircuit.toNormal_L32, GCircuit.toNormal_L31, GCircuit.toNormal_L30,
    nuSlots_three]
  ring

theorem gr3_eq : gr3 c x z = r3 c.toNormal x (nuSlots b c z) := by
  rw [gr3, g1_eq c hb, g2_eq c hb, r3]
  simp only [GCircuit.toNormal_R32, GCircuit.toNormal_R31, GCircuit.toNormal_R30,
    nuSlots_four]
  ring

theorem g3_eq : g3 c x z = u3 c.toNormal x (nuSlots b c z) := by
  rw [g3, gl3_eq c hb, gr3_eq c hb]
  rfl

/-- **The reduction identity.**  A general program with `β₁ = α₁ b` computes exactly the
normal-form program `c.toNormal` on the slots `ν(z)`.  This is the first-gate absorption
of the appendix, as a theorem. -/
theorem gout_eq : gout c x z = out c.toNormal x (nuSlots b c z) := by
  rw [gout, g1_eq c hb, g2_eq c hb, g3_eq c hb, out]
  simp only [GCircuit.toNormal_s3, GCircuit.toNormal_s2, GCircuit.toNormal_s1,
    GCircuit.toNormal_s0, nuSlots_five]
  ring

end Gauge

/-! ## Interchanging the two factors of the first gate -/

section Swap

variable (c : GCircuit A) (x : A) (z : Fin 7 → A)

theorem g1_swap : g1 c.swap x (swapSlots z) = g1 c x z := by
  simp only [g1, GCircuit.swap_α₁, GCircuit.swap_β₁, swapSlots_zero, swapSlots_one]
  ring

theorem gl2_swap : gl2 c.swap x (swapSlots z) = gl2 c x z := by
  simp only [gl2, g1_swap, GCircuit.swap_α₂, GCircuit.swap_p21, swapSlots_two]

theorem gr2_swap : gr2 c.swap x (swapSlots z) = gr2 c x z := by
  simp only [gr2, g1_swap, GCircuit.swap_β₂, GCircuit.swap_q21, swapSlots_three]

theorem g2_swap : g2 c.swap x (swapSlots z) = g2 c x z := by
  simp only [g2, gl2_swap, gr2_swap]

theorem gl3_swap : gl3 c.swap x (swapSlots z) = gl3 c x z := by
  simp only [gl3, g1_swap, g2_swap, GCircuit.swap_α₃, GCircuit.swap_p31, GCircuit.swap_p32,
    swapSlots_four]

theorem gr3_swap : gr3 c.swap x (swapSlots z) = gr3 c x z := by
  simp only [gr3, g1_swap, g2_swap, GCircuit.swap_β₃, GCircuit.swap_q31, GCircuit.swap_q32,
    swapSlots_five]

theorem g3_swap : g3 c.swap x (swapSlots z) = g3 c x z := by
  simp only [g3, gl3_swap, gr3_swap]

/-- The two factors of the first gate commute: swapping them (and the two slots `u₁, v₁`)
does not change the output. -/
theorem gout_swap : gout c.swap x (swapSlots z) = gout c x z := by
  simp only [gout, g1_swap, g2_swap, g3_swap, GCircuit.swap_γ, GCircuit.swap_r1,
    GCircuit.swap_r2, GCircuit.swap_r3, swapSlots_six]

end Swap

/-! ## Normal-form circuits as general circuits -/

section OfNormal

variable (c' : Circuit A) (x : A) (z : Fin 7 → A) (hz : z 0 = 0)
include hz

theorem g1_ofNormal : g1 (GCircuit.ofNormal c') x z = u1 c' x (tailSlots z) := by
  simp only [g1, u1, GCircuit.ofNormal_α₁, GCircuit.ofNormal_β₁, hz, tailSlots_zero]
  ring

theorem gl2_ofNormal : gl2 (GCircuit.ofNormal c') x z = ell2 c' x (tailSlots z) := by
  rw [gl2, g1_ofNormal c' x z hz, ell2]
  simp only [GCircuit.ofNormal_α₂, GCircuit.ofNormal_p21, tailSlots_one]
  ring

theorem gr2_ofNormal : gr2 (GCircuit.ofNormal c') x z = r2 c' x (tailSlots z) := by
  rw [gr2, g1_ofNormal c' x z hz, r2]
  simp only [GCircuit.ofNormal_β₂, GCircuit.ofNormal_q21, tailSlots_two]
  ring

theorem g2_ofNormal : g2 (GCircuit.ofNormal c') x z = u2 c' x (tailSlots z) := by
  rw [g2, gl2_ofNormal c' x z hz, gr2_ofNormal c' x z hz]
  rfl

theorem gl3_ofNormal : gl3 (GCircuit.ofNormal c') x z = ell3 c' x (tailSlots z) := by
  rw [gl3, g1_ofNormal c' x z hz, g2_ofNormal c' x z hz, ell3]
  simp only [GCircuit.ofNormal_α₃, GCircuit.ofNormal_p31, GCircuit.ofNormal_p32,
    tailSlots_three]
  ring

theorem gr3_ofNormal : gr3 (GCircuit.ofNormal c') x z = r3 c' x (tailSlots z) := by
  rw [gr3, g1_ofNormal c' x z hz, g2_ofNormal c' x z hz, r3]
  simp only [GCircuit.ofNormal_β₃, GCircuit.ofNormal_q31, GCircuit.ofNormal_q32,
    tailSlots_four]
  ring

theorem g3_ofNormal : g3 (GCircuit.ofNormal c') x z = u3 c' x (tailSlots z) := by
  rw [g3, gl3_ofNormal c' x z hz, gr3_ofNormal c' x z hz]
  rfl

/-- `ofNormal` computes the normal form when the `u₁` slot is `0`. -/
theorem gout_ofNormal : gout (GCircuit.ofNormal c') x z = out c' x (tailSlots z) := by
  rw [gout, g1_ofNormal c' x z hz, g2_ofNormal c' x z hz, g3_ofNormal c' x z hz, out]
  simp only [GCircuit.ofNormal_γ, GCircuit.ofNormal_r1, GCircuit.ofNormal_r2,
    GCircuit.ofNormal_r3, tailSlots_five]
  ring

end OfNormal

end FastPoly.LowerBound.General
