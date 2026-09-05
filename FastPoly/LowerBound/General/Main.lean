/-
The degree-six lower bound for general three-multiplication programs: the assembly.
-/
import FastPoly.LowerBound.General.Transversal
import FastPoly.LowerBound.General.Midpoint
import FastPoly.LowerBound.Main
import Mathlib.Algebra.CharP.Basic

/-!
# Degree-six lower bound, general programs

`FastPoly/LowerBound/Main.lean` proves the lower bound for the *normal form* of
`sections/appendix_lower.tex` (`no_rationalInverse_affine`), and its docstring records
that the first-gate absorption `(Ax+a)(Bx+b) = A·x(Bx+b) + a(Bx+b)` of the paragraph
"Reduction to a normal form" is modelling, not a theorem.  That absorption is in fact
*wrong* as stated: the correction `a(Bx+b)` is not `x`-free, so it changes the
`x`-coefficients of all later uses of `G₁` by amounts depending on the parameter `a`,
whereas the normal form treats those coefficients as fixed.  The repair
(`sections/lower_char_p_draft.tex`, `rem:charp-lower-gap`; `notes/lower_char_p.md`,
section (d)) uses the gauge identity `(Ax+a)(Bx+b) = A·x(Bx + b + aB/A) + ab`, whose
correction `ab` is `x`-free; the normal-form slots then depend *quadratically* on the
parameters.

This tree (`FastPoly/LowerBound/General/`) formalizes the repaired reduction and closes
the gap: the theorem `no_rationalInverse_general` below quantifies over **every** program
`(c, M, h₀)` of the model of `General/Defs.lean` — sixteen arbitrary fixed constants (both
first-gate constant terms are parameter slots; `α₁ = β₁ = 0` and `α₁ = 0 ≠ β₁` are
allowed) and an arbitrary affine map `H p = M p + h₀` from the six parameters to the seven
constant slots — and the only remaining modelling statement is that every multiplicand is
a fixed affine form in `x` and the earlier gates plus a parameter-affine constant.

## Where each step of the repaired paragraph lives

| repaired reduction | Lean |
| --- | --- |
| the model: sixteen constants, seven slots `(u₁, v₁, u₂, v₂, u₃, v₃, w)`, `H p = M p + h₀` | `GCircuit`, `g1 … gout` (`Defs.lean`), `affineSlots`, `outPolyGeneral` (`Affine.lean`) |
| the gauge identity `(α₁x+u₁)(β₁x+v₁) = α₁·x(β₁x + v₁ + b u₁) + u₁v₁`, `β₁ = α₁ b` | `g1_eq` (`Gauge.lean`) |
| `f_z = f'_{ν z}` for the normal form `c.toNormal` and the quadratic slot map `ν` | `gout_eq` (`Gauge.lean`), `outPolyGeneral_eq_outPolyOf` (`Affine.lean`) |
| `J_F(p) = J(Q p) · DQ(p)`, `Q = ν ∘ H` | `polyJacobian_outPolyOf`, `polyJacobian_outPolyGeneral` (`Affine.lean`) |
| `ker Dν(z) ∋ ξ(z) = (1, −b, −λ(v₁ − b u₁))` | `dnu_xi` (`DQ.lean`) |
| `DQ(p) v = Dν(H p)(M v)` | `polyJacobian_Qpoly_mulVec` (`DQ.lean`) |
| case (i): `M` not injective ⇒ `J_F` singular everywhere | `det_eq_zero_of_mulVec_eq_zero` (`DQ.lean`) |
| case (ii): two points on one fibre ⇒ singular at their midpoint (char `≠ 2`) | `Qval_sub_eq_mulVec`, `det_eq_zero_of_Qval_eq` (`Midpoint.lean`) |
| `im H` is the hyperplane `ℓ · (z − h₀) = 0`, `ℓ` = the left-kernel vector (the appendix's cofactor vector, normalized at the pivot row `i₀`) | `lker`, `lker_vecMul`, `mulVec_MplusVec_of_dot_eq_zero`, `eq_smul_lker_of_vecMul_eq_zero` (`LinAlg.lean`) |
| `ℓ · ξ(H p) = c₁° − κ τ(p)`; the orbit polynomial | `dot_xi`, `dot_orbit_sub` (`Orbit.lean`) |
| `ℓ · ξ(H p₀) = 0 ⇒ J_F(p₀)` singular | `det_eq_zero_of_dot_xi_eq_zero` (`Orbit.lean`) |
| `κ ≠ 0`: one pivot gives `τ(p₀) = c₁°/κ` | `exists_tau_eq` (`Orbit.lean`) |
| case (iii): a fibre inside `im H` ⇒ singular along it | `det_eq_zero_along_orbit` (`Orbit.lean`) |
| case (iv): `κ = 0 ≠ c₁°`, the explicit inverse `Θ` with `Q ∘ Θ = id` | `Theta`, `Qval_Theta` (`Transversal.lean`) |
| the normal-form theorem (existing) | `exists_singular_jacobian` (`LowerBound/Main.lean`) |
| the assembly | `exists_singular_of_gauge`, `exists_singular_polyJacobian_general`, `no_rationalInverse_general` (this file) |

## The case split actually used (route A, characteristic-free)

`exists_singular_of_gauge` splits on: a kernel vector of `M` (case (i)); otherwise some
`6 × 6` minor `minor M i₀` is nonzero (`exists_mulVec_eq_zero_of_forall_minor`),
`ℓ = lker M i₀` spans the left kernel, and with `κ = ℓ_s · λ`, `c₁° = ℓ_u − b ℓ_v`:

* `κ ≠ 0`: a pivot gives `p₀` with `ℓ · ξ(H p₀) = 0`, so `ξ(H p₀) ∈ im M` and `DQ(p₀)` is
  singular (this is the Jacobian-level form of case (ii));
* `κ = 0 = c₁°`: `ℓ · ξ(H p) = 0` for every `p` (the Jacobian-level form of case (iii));
* `κ = 0 ≠ c₁°`: case (iv), the normal-form singular point `q₀` pulls back to `Θ(q₀)`.

The hypothesis `2 ≠ 0` enters only through the normal-form theorem
`exists_singular_jacobian` (and, separately, through `Midpoint.lean`); `Infinite F` only
through `RationalInverse.isEmpty_of_det_eq_zero`; `hxs` only through
`exists_singular_jacobian`.  Every witness is explicit: a kernel vector, a `Pi.single`
pivot, the inverse of a nonzero minor, the closed form `Θ`, and the existing `q₀`.

The two first-gate degeneracies are dispatched in `exists_singular_polyJacobian_general`:
`α₁ ≠ 0` uses `b = β₁/α₁`; `α₁ = β₁ = 0` uses `b = 0` (the normal form then has
`L₂₁ = R₂₁ = L₃₁ = R₃₁ = s₁ = 0`); `α₁ = 0 ≠ β₁` interchanges the two factors
(`outPolyGeneral_swap`).  The existing `no_rationalInverse_affine` is recovered as the
instance `c = ofNormal c'`, `M = liftM M6`, `h₀ = lifth m₀`
(`no_rationalInverse_affine_of_general`).
-/

namespace FastPoly.LowerBound.General

open Matrix

variable {F : Type*} [Field F]

/-- **Route A core.**  For a gauge scalar `b` with `β₁ = α₁ b`, the Jacobian of the general
program is singular somewhere. -/
theorem exists_singular_of_gauge (h2 : (2 : F) ≠ 0) (c : GCircuit F) (xs : Fin 6 → F)
    (hxs : Function.Injective xs) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F)
    (b : F) (hb : c.β₁ = c.α₁ * b) :
    ∃ p : Fin 6 → F, (polyJacobian (outPolyGeneral c xs M h₀) p).det = 0 := by
  by_cases hker : ∃ v : Fin 6 → F, v ≠ 0 ∧ M *ᵥ v = 0
  · obtain ⟨v, hv, hMv⟩ := hker
    exact ⟨0, det_eq_zero_of_mulVec_eq_zero b c M h₀ hb xs 0 v hv hMv⟩
  · obtain ⟨i₀, hd⟩ : ∃ i₀ : Fin 7, (minor M i₀).det ≠ 0 := by
      by_contra hall
      exact hker (exists_mulVec_eq_zero_of_forall_minor M
        fun i => of_not_not fun hne => hall ⟨i, hne⟩)
    by_cases hκ : kappa c (lker M i₀) = 0
    · by_cases hc : c1o b (lker M i₀) = 0
      · -- `ℓ · ξ(H p) = 0` at every `p`
        refine ⟨0, det_eq_zero_of_dot_xi_eq_zero b c M h₀ hb xs hd 0 ?_⟩
        rw [dot_xi, hκ, hc, zero_mul, sub_zero]
      · -- case (iv): pull back the normal-form singular point along `Θ`
        obtain ⟨q₀, hq₀⟩ := exists_singular_jacobian h2 c.toNormal xs hxs
        refine ⟨Theta b c M h₀ i₀ q₀, ?_⟩
        rw [polyJacobian_outPolyGeneral c hb, Matrix.det_mul, Qval_Theta b c M h₀ hd hκ hc,
          hq₀, zero_mul]
    · -- `κ ≠ 0`: one pivot puts `ξ(H p₀)` into `im M`
      obtain ⟨p₀, hp₀⟩ := exists_tau_eq b c M h₀ hd hκ (c1o b (lker M i₀) / kappa c (lker M i₀))
      refine ⟨p₀, det_eq_zero_of_dot_xi_eq_zero b c M h₀ hb xs hd p₀ ?_⟩
      have htau : affineSlots M h₀ p₀ 1 - b * affineSlots M h₀ p₀ 0
          = c1o b (lker M i₀) / kappa c (lker M i₀) := hp₀
      rw [dot_xi, htau, mul_div_cancel₀ _ hκ, sub_self]

/-- **The Jacobian of every general three-multiplication program is singular somewhere.**
The first-gate degeneracies are dispatched here: `α₁ ≠ 0` uses `b = β₁/α₁`;
`α₁ = β₁ = 0` uses `b = 0`; `α₁ = 0 ≠ β₁` interchanges the two factors. -/
theorem exists_singular_polyJacobian_general (h2 : (2 : F) ≠ 0) (c : GCircuit F)
    (xs : Fin 6 → F) (hxs : Function.Injective xs) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) :
    ∃ p : Fin 6 → F, (polyJacobian (outPolyGeneral c xs M h₀) p).det = 0 := by
  by_cases hα : c.α₁ = 0
  · by_cases hβ : c.β₁ = 0
    · exact exists_singular_of_gauge h2 c xs hxs M h₀ 0 (by rw [hβ, hα, mul_zero])
    · rw [← outPolyGeneral_swap c xs M h₀]
      exact exists_singular_of_gauge h2 c.swap xs hxs _ _ 0
        (by rw [GCircuit.swap_β₁, GCircuit.swap_α₁, hα, mul_zero])
  · exact exists_singular_of_gauge h2 c xs hxs M h₀ (c.β₁ / c.α₁) (mul_div_cancel₀ _ hα).symm

/-- **Degree-six lower bound, general programs.**  Over an infinite field with `2 ≠ 0`, for
six distinct evaluation points, and for *every* three-multiplication program `(c, M, h₀)` —
sixteen arbitrary fixed constants and an arbitrary affine map from the six parameters to
the seven constant slots — the evaluation map `p ↦ (f_{H p}(x₀), …, f_{H p}(x₅))` has no
everywhere-defined rational inverse. -/
theorem no_rationalInverse_general [Infinite F] (h2 : (2 : F) ≠ 0) (c : GCircuit F)
    (xs : Fin 6 → F) (hxs : Function.Injective xs) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) : IsEmpty (RationalInverse (outPolyGeneral c xs M h₀)) := by
  obtain ⟨p, hp⟩ := exists_singular_polyJacobian_general h2 c xs hxs M h₀
  exact RationalInverse.isEmpty_of_det_eq_zero _ p hp

/-- The same with the characteristic hypothesis written as `ringChar F ≠ 2`. -/
theorem no_rationalInverse_general_of_ringChar_ne_two [Infinite F] (hchar : ringChar F ≠ 2)
    (c : GCircuit F) (xs : Fin 6 → F) (hxs : Function.Injective xs)
    (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) :
    IsEmpty (RationalInverse (outPolyGeneral c xs M h₀)) :=
  no_rationalInverse_general (Ring.two_ne_zero hchar) c xs hxs M h₀

/-- **Specialization check.**  The existing normal-form statement `no_rationalInverse_affine`
is the instance `c = ofNormal c'`, `M = liftM M6`, `h₀ = lifth m₀` of the general theorem. -/
theorem no_rationalInverse_affine_of_general [Infinite F] (h2 : (2 : F) ≠ 0) (c' : Circuit F)
    (xs : Fin 6 → F) (hxs : Function.Injective xs) (M6 : Matrix (Fin 6) (Fin 6) F)
    (m₀ : Fin 6 → F) : IsEmpty (RationalInverse (outPolyAffine c' xs M6 m₀)) := by
  rw [← outPolyGeneral_ofNormal c' xs M6 m₀]
  exact no_rationalInverse_general h2 (GCircuit.ofNormal c') xs hxs (liftM M6) (lifth m₀)

end FastPoly.LowerBound.General
