/-
The degree-six lower bound: the fibres of the slot map `ν`, the three scalars of the case
split, and cases (ii′) and (iii).
-/
import FastPoly.LowerBound.General.DQ
import FastPoly.LowerBound.General.LinAlg

/-!
# Fibres of `ν` and the case split

The fibre of `ν` over `q = (v*, s*)` is the curve `O_q(u) = (u, v* − b u, s* − λ u (v* − b u))`
(`orbit`, with `nuSlots_orbit`).  Its intersection with the affine image `im H = h₀ + im M`
is governed, when the `6 × 6` minor `minor M i₀` is nonzero and `ℓ = lker M i₀` spans the
left kernel, by the *orbit polynomial*

`ℓ · (O_q(u) − h₀) = b κ u² + (c₁° − κ q₀) u + c₀(q)`   (`dot_orbit_sub`),

with `κ = ℓ_s · λ` (`kappa`), `c₁° = ℓ_u − b ℓ_v` (`c1o`), `c₀(q)` (`c0`).  The gauge
direction satisfies `ℓ · ξ(z) = c₁° − κ (v₁ − b u₁)` (`dot_xi`), so `J_F` is singular at
every `p` with `ℓ · ξ(H p) = 0` (`det_eq_zero_of_dot_xi_eq_zero`: then `ξ(H p) ∈ im M`).

* **Case (ii′)** (`exists_tau_eq`): if `κ ≠ 0` the affine function `τ(p) = v₁(H p) − b u₁(H p)`
  is not constant, and one pivot solves `τ(p₀) = c₁°/κ`.
* **Case (iii)** (`det_eq_zero_along_orbit`): if a whole fibre lies in `im H`, `J_F` is
  singular along the curve `p(u) = M⁺(O_q(u) − h₀)`.
-/

namespace FastPoly.LowerBound.General

open Matrix

section Orbit

variable {A : Type*} [CommRing A]

/-- The fibre of `ν` over `q`: `O_q(u) = (u, v* − b u, s* − λ u (v* − b u))`. -/
def orbit (b : A) (c : GCircuit A) (q : Fin 6 → A) (u : A) : Fin 7 → A :=
  Matrix.vecCons u (Matrix.vecCons (q 0 - b * u) fun j : Fin 5 =>
    q j.succ - c.lam j * (u * (q 0 - b * u)))

variable (b : A) (c : GCircuit A) (q : Fin 6 → A) (u : A)

@[simp] theorem orbit_zero : orbit b c q u 0 = u := rfl
@[simp] theorem orbit_one : orbit b c q u 1 = q 0 - b * u := rfl
@[simp] theorem orbit_succ_succ (j : Fin 5) :
    orbit b c q u j.succ.succ = q j.succ - c.lam j * (u * (q 0 - b * u)) := by
  simp only [orbit, Matrix.cons_val_succ]
@[simp] theorem orbit_two : orbit b c q u 2 = q 1 - c.p21 * (u * (q 0 - b * u)) := rfl
@[simp] theorem orbit_three : orbit b c q u 3 = q 2 - c.q21 * (u * (q 0 - b * u)) := rfl
@[simp] theorem orbit_four : orbit b c q u 4 = q 3 - c.p31 * (u * (q 0 - b * u)) := rfl
@[simp] theorem orbit_five : orbit b c q u 5 = q 4 - c.q31 * (u * (q 0 - b * u)) := rfl
@[simp] theorem orbit_six : orbit b c q u 6 = q 5 - c.r1 * (u * (q 0 - b * u)) := rfl

/-- `O_q(u)` lies in the fibre of `ν` over `q`. -/
theorem nuSlots_orbit : nuSlots b c (orbit b c q u) = q := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [nuSlots_zero, orbit_zero, orbit_one]
    ring
  · simp only [nuSlots_succ, orbit_zero, orbit_one, orbit_succ_succ]
    ring

/-- Every slot vector lies on the fibre through it. -/
theorem orbit_nuSlots (z : Fin 7 → A) : orbit b c (nuSlots b c z) (z 0) = z := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) k
  · rfl
  · simp only [Fin.succ_zero_eq_one, orbit_one, nuSlots_zero]
    ring
  · simp only [orbit_succ_succ, nuSlots_succ, nuSlots_zero]
    ring

end Orbit

section Scalars

variable {F : Type*} [Field F]

/-- `κ = ℓ_s · λ = ℓ₂ p₂₁ + ℓ₃ q₂₁ + ℓ₄ p₃₁ + ℓ₅ q₃₁ + ℓ₆ r₁`. -/
def kappa (c : GCircuit F) (ℓ : Fin 7 → F) : F :=
  ℓ 2 * c.p21 + ℓ 3 * c.q21 + ℓ 4 * c.p31 + ℓ 5 * c.q31 + ℓ 6 * c.r1

/-- `c₁° = ℓ_u − b ℓ_v`. -/
def c1o (b : F) (ℓ : Fin 7 → F) : F := ℓ 0 - b * ℓ 1

/-- The constant term `c₀(q) = ℓ_v v* + ℓ_s · s* − ℓ · h₀` of the orbit polynomial. -/
def c0 (ℓ h₀ : Fin 7 → F) (q : Fin 6 → F) : F :=
  ℓ 1 * q 0 + ℓ 2 * q 1 + ℓ 3 * q 2 + ℓ 4 * q 3 + ℓ 5 * q 4 + ℓ 6 * q 5 - ℓ ⬝ᵥ h₀

/-- `τ(p) = v₁(H p) − b u₁(H p)`. -/
def tau (b : F) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) (p : Fin 6 → F) : F :=
  affineSlots M h₀ p 1 - b * affineSlots M h₀ p 0

/-- `ℓ · ξ(z) = c₁° − κ (v₁ − b u₁)`. -/
theorem dot_xi (b : F) (c : GCircuit F) (ℓ z : Fin 7 → F) :
    ℓ ⬝ᵥ xi b c z = c1o b ℓ - kappa c ℓ * (z 1 - b * z 0) := by
  simp only [dotProduct, Fin.sum_univ_seven, xi_zero, xi_one, xi_two, xi_three, xi_four,
    xi_five, xi_six, c1o, kappa]
  ring

/-- **The orbit polynomial.** -/
theorem dot_orbit_sub (b : F) (c : GCircuit F) (ℓ h₀ : Fin 7 → F) (q : Fin 6 → F) (u : F) :
    ℓ ⬝ᵥ (orbit b c q u - h₀)
      = b * kappa c ℓ * u ^ 2 + (c1o b ℓ - kappa c ℓ * q 0) * u + c0 ℓ h₀ q := by
  simp only [dotProduct, Fin.sum_univ_seven, Pi.sub_apply, orbit_zero, orbit_one, orbit_two,
    orbit_three, orbit_four, orbit_five, orbit_six, c1o, kappa, c0]
  ring

theorem tau_eq (b : F) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) (p : Fin 6 → F) :
    tau b M h₀ p = ∑ i, (M 1 i - b * M 0 i) * p i + (h₀ 1 - b * h₀ 0) := by
  simp only [tau, affineSlots, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  ring

/-- **The singular point from `ℓ · ξ(H p) = 0`:** then `ξ(H p) ∈ ker ℓᵀ = im M`, so
`DQ(p)` has the kernel vector `M⁺ ξ(H p)`. -/
theorem det_eq_zero_of_dot_xi_eq_zero (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) (hb : c.β₁ = c.α₁ * b) (xs : Fin 6 → F) {i₀ : Fin 7}
    (hd : (minor M i₀).det ≠ 0) (p : Fin 6 → F)
    (h : lker M i₀ ⬝ᵥ xi b c (affineSlots M h₀ p) = 0) :
    (polyJacobian (outPolyGeneral c xs M h₀) p).det = 0 := by
  have hMv : M *ᵥ MplusVec M i₀ (xi b c (affineSlots M h₀ p)) = xi b c (affineSlots M h₀ p) :=
    mulVec_MplusVec_of_dot_eq_zero M hd _ h
  have hv : MplusVec M i₀ (xi b c (affineSlots M h₀ p)) ≠ 0 := by
    intro hv0
    have h0 := congrFun hMv 0
    rw [hv0, Matrix.mulVec_zero, Pi.zero_apply, xi_zero] at h0
    exact zero_ne_one h0
  exact det_eq_zero_of_dnu_kernel b c M h₀ hb xs p _ hv (by rw [hMv, dnu_xi])

/-- **Case (ii′).**  If `κ ≠ 0` then `τ` is a non-constant affine function of `p`, and one
pivot solves `τ(p) = t`. -/
theorem exists_tau_eq (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F)
    {i₀ : Fin 7} (hd : (minor M i₀).det ≠ 0) (hκ : kappa c (lker M i₀) ≠ 0) (t : F) :
    ∃ p : Fin 6 → F, tau b M h₀ p = t := by
  have hw : (fun i => M 1 i - b * M 0 i) ≠ 0 := by
    intro hw0
    obtain ⟨e, he0, he1, he2, he3, he4, he5, he6⟩ : ∃ e : Fin 7 → F,
        e 0 = -b ∧ e 1 = 1 ∧ e 2 = 0 ∧ e 3 = 0 ∧ e 4 = 0 ∧ e 5 = 0 ∧ e 6 = 0 :=
      ⟨![-b, 1, 0, 0, 0, 0, 0], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have heM : e ᵥ* M = 0 := by
      funext j
      have hj := congrFun hw0 j
      simp only [Pi.zero_apply] at hj
      simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_seven, he0, he1, he2, he3, he4, he5,
        he6, zero_mul, add_zero, Pi.zero_apply]
      linear_combination hj
    have hsm := eq_smul_lker_of_vecMul_eq_zero M hd e heM
    have h1 := congrFun hsm 1
    rw [he1, Pi.smul_apply, smul_eq_mul] at h1
    have hs : e i₀ ≠ 0 := fun hs0 => by
      rw [hs0, zero_mul] at h1
      exact one_ne_zero h1
    have hk : ∀ k, e k = 0 → lker M i₀ k = 0 := fun k hek => by
      have hj := congrFun hsm k
      rw [hek, Pi.smul_apply, smul_eq_mul] at hj
      exact (mul_eq_zero.mp hj.symm).resolve_left hs
    apply hκ
    simp only [kappa, hk 2 he2, hk 3 he3, hk 4 he4, hk 5 he5, hk 6 he6, zero_mul, add_zero]
  obtain ⟨p, hp⟩ := exists_solve_affine (fun i => M 1 i - b * M 0 i) hw (h₀ 1 - b * h₀ 0) t
  refine ⟨p, ?_⟩
  rw [tau_eq]
  exact hp

/-! ## Case (iii): a whole fibre inside `im H` -/

/-- The curve `p(u) = M⁺(O_q(u) − h₀)` in parameter space. -/
noncomputable def pcurve (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) (i₀ : Fin 7) (q : Fin 6 → F) (u : F) : Fin 6 → F :=
  MplusVec M i₀ (orbit b c q u - h₀)

theorem affineSlots_pcurve (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) {i₀ : Fin 7} (hd : (minor M i₀).det ≠ 0) (q : Fin 6 → F)
    (hin : ∀ u, lker M i₀ ⬝ᵥ (orbit b c q u - h₀) = 0) (u : F) :
    affineSlots M h₀ (pcurve b c M h₀ i₀ q u) = orbit b c q u := by
  rw [affineSlots, pcurve, mulVec_MplusVec_of_dot_eq_zero M hd _ (hin u), sub_add_cancel]

theorem Qval_pcurve (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) {i₀ : Fin 7} (hd : (minor M i₀).det ≠ 0) (q : Fin 6 → F)
    (hin : ∀ u, lker M i₀ ⬝ᵥ (orbit b c q u - h₀) = 0) (u : F) :
    Qval b c M h₀ (pcurve b c M h₀ i₀ q u) = q := by
  rw [Qval, affineSlots_pcurve b c M h₀ hd q hin u, nuSlots_orbit]

/-- **Case (iii).**  If the orbit polynomial of `q` vanishes identically (the fibre `O_q`
lies in `im H`), `J_F` is singular at every point of the curve `p(u)`. -/
theorem det_eq_zero_along_orbit (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) (hb : c.β₁ = c.α₁ * b) (xs : Fin 6 → F) {i₀ : Fin 7}
    (hd : (minor M i₀).det ≠ 0) (q : Fin 6 → F) (hc2 : b * kappa c (lker M i₀) = 0)
    (hc1 : c1o b (lker M i₀) - kappa c (lker M i₀) * q 0 = 0) (hc0 : c0 (lker M i₀) h₀ q = 0) (u : F) :
    (polyJacobian (outPolyGeneral c xs M h₀) (pcurve b c M h₀ i₀ q u)).det = 0 := by
  have hin : ∀ u, lker M i₀ ⬝ᵥ (orbit b c q u - h₀) = 0 := fun u => by
    rw [dot_orbit_sub, hc2, hc1, hc0]
    ring
  refine det_eq_zero_of_dot_xi_eq_zero b c M h₀ hb xs hd _ ?_
  rw [affineSlots_pcurve b c M h₀ hd q hin u, dot_xi, orbit_one, orbit_zero]
  linear_combination hc1 + 2 * u * hc2

/-- Two distinct points of the curve (route B, Lemma 5.4.4). -/
theorem pcurve_zero_ne_one (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) {i₀ : Fin 7} (hd : (minor M i₀).det ≠ 0) (q : Fin 6 → F)
    (hin : ∀ u, lker M i₀ ⬝ᵥ (orbit b c q u - h₀) = 0) :
    pcurve b c M h₀ i₀ q 0 ≠ pcurve b c M h₀ i₀ q 1 := by
  intro heq
  have h := congrArg (fun p => affineSlots M h₀ p 0) heq
  simp only [affineSlots_pcurve b c M h₀ hd q hin, orbit_zero] at h
  exact zero_ne_one h

end Scalars

end FastPoly.LowerBound.General
