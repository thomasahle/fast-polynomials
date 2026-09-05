/-
The degree-six lower bound (`sections/appendix_lower.tex`, "Reduction to a normal form"):
the general three-multiplication program and its slot map.
-/
import FastPoly.LowerBound.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The general three-multiplication program

This file sets up the *general* model behind the reduction paragraph of the lower-bound
appendix (`sections/appendix_lower.tex`, "Reduction to a normal form"; repaired version in
`sections/lower_char_p_draft.tex`, `rem:charp-lower-gap`).  A program is given by sixteen
fixed constants `c : GCircuit F` and seven constant slots `z = (u₁, v₁, u₂, v₂, u₃, v₃, w)`,
indexed by `Fin 7`:

```
G₁ = (α₁ x + u₁)(β₁ x + v₁)
G₂ = (α₂ x + p₂₁ G₁ + u₂)(β₂ x + q₂₁ G₁ + v₂)
G₃ = (α₃ x + p₃₁ G₁ + p₃₂ G₂ + u₃)(β₃ x + q₃₁ G₁ + q₃₂ G₂ + v₃)
f  = γ x + r₁ G₁ + r₂ G₂ + r₃ G₃ + w
```

Compared with the normal form of `FastPoly/LowerBound/Defs.lean` the first multiplication
is an arbitrary product of two affine forms in `x` (both constant terms are slots, and
`α₁ = β₁ = 0`, i.e. a scalar first gate, is allowed).  The dictionary to the appendix is
`α₁ = A, β₁ = B, u₁ = a, v₁ = b, α₂ = L₂₀, p₂₁ = L₂₁, β₂ = R₂₀, q₂₁ = R₂₁, α₃ = L₃₀,
p₃₁ = L₃₁, p₃₂ = L₃₂, β₃ = R₃₀, q₃₁ = R₃₁, q₃₂ = R₃₂, γ = s₀, rᵢ = sᵢ`.

* `GCircuit.toNormal` is the normal-form circuit of the repair (`R₁₀ = β₁`, `L₂₁ = α₁ p₂₁`,
  `s₁ = α₁ r₁`, …; no division).
* `nuSlots b c z` is the quadratic slot map `ν(u₁, v₁, s) = (v₁ + b u₁, s + λ u₁ v₁)` with
  `λ = (p₂₁, q₂₁, p₃₁, q₃₁, r₁)`, in the normal-form slot order `(a₁, a₂, b₂, a₃, b₃, b₁)`.
* `Gauge.lean` proves `gout c x z = out c.toNormal x (nuSlots b c z)` whenever
  `β₁ = α₁ b`: the first-gate absorption is a theorem, not modelling.

Slot vectors are `Matrix.vecCons` heads with a `Fin 5`-function tail, so that proofs can
split a `Fin 6`/`Fin 7` index into `0` and `j.succ` (`Fin.cases`) instead of six or seven
literal cases; the literal `rfl` lemmas (`nuSlots_one`, …) serve the gate lemmas.
-/

namespace FastPoly.LowerBound.General

open MvPolynomial

variable {F A B : Type*}

/-! ## The sixteen circuit constants -/

/-- The fixed constants of a general three-multiplication program. -/
@[ext] structure GCircuit (F : Type*) where
  /-- Coefficient of `x` in the first factor of `G₁`. -/
  α₁ : F
  /-- Coefficient of `x` in the second factor of `G₁`. -/
  β₁ : F
  /-- Coefficient of `x` in the first factor of `G₂`. -/
  α₂ : F
  /-- Coefficient of `x` in the second factor of `G₂`. -/
  β₂ : F
  /-- Coefficient of `x` in the first factor of `G₃`. -/
  α₃ : F
  /-- Coefficient of `x` in the second factor of `G₃`. -/
  β₃ : F
  /-- Coefficient of `G₁` in the first factor of `G₂`. -/
  p21 : F
  /-- Coefficient of `G₁` in the second factor of `G₂`. -/
  q21 : F
  /-- Coefficient of `G₁` in the first factor of `G₃`. -/
  p31 : F
  /-- Coefficient of `G₂` in the first factor of `G₃`. -/
  p32 : F
  /-- Coefficient of `G₁` in the second factor of `G₃`. -/
  q31 : F
  /-- Coefficient of `G₂` in the second factor of `G₃`. -/
  q32 : F
  /-- Coefficient of `x` in the output. -/
  γ : F
  /-- Coefficient of `G₁` in the output. -/
  r1 : F
  /-- Coefficient of `G₂` in the output. -/
  r2 : F
  /-- Coefficient of `G₃` in the output. -/
  r3 : F

namespace GCircuit

/-- Transport the constants along a map of coefficients. -/
def map (f : F → A) (c : GCircuit F) : GCircuit A where
  α₁ := f c.α₁
  β₁ := f c.β₁
  α₂ := f c.α₂
  β₂ := f c.β₂
  α₃ := f c.α₃
  β₃ := f c.β₃
  p21 := f c.p21
  q21 := f c.q21
  p31 := f c.p31
  p32 := f c.p32
  q31 := f c.q31
  q32 := f c.q32
  γ := f c.γ
  r1 := f c.r1
  r2 := f c.r2
  r3 := f c.r3

@[simp] theorem map_α₁ (f : F → A) (c : GCircuit F) : (c.map f).α₁ = f c.α₁ := rfl
@[simp] theorem map_β₁ (f : F → A) (c : GCircuit F) : (c.map f).β₁ = f c.β₁ := rfl
@[simp] theorem map_α₂ (f : F → A) (c : GCircuit F) : (c.map f).α₂ = f c.α₂ := rfl
@[simp] theorem map_β₂ (f : F → A) (c : GCircuit F) : (c.map f).β₂ = f c.β₂ := rfl
@[simp] theorem map_α₃ (f : F → A) (c : GCircuit F) : (c.map f).α₃ = f c.α₃ := rfl
@[simp] theorem map_β₃ (f : F → A) (c : GCircuit F) : (c.map f).β₃ = f c.β₃ := rfl
@[simp] theorem map_p21 (f : F → A) (c : GCircuit F) : (c.map f).p21 = f c.p21 := rfl
@[simp] theorem map_q21 (f : F → A) (c : GCircuit F) : (c.map f).q21 = f c.q21 := rfl
@[simp] theorem map_p31 (f : F → A) (c : GCircuit F) : (c.map f).p31 = f c.p31 := rfl
@[simp] theorem map_p32 (f : F → A) (c : GCircuit F) : (c.map f).p32 = f c.p32 := rfl
@[simp] theorem map_q31 (f : F → A) (c : GCircuit F) : (c.map f).q31 = f c.q31 := rfl
@[simp] theorem map_q32 (f : F → A) (c : GCircuit F) : (c.map f).q32 = f c.q32 := rfl
@[simp] theorem map_γ (f : F → A) (c : GCircuit F) : (c.map f).γ = f c.γ := rfl
@[simp] theorem map_r1 (f : F → A) (c : GCircuit F) : (c.map f).r1 = f c.r1 := rfl
@[simp] theorem map_r2 (f : F → A) (c : GCircuit F) : (c.map f).r2 = f c.r2 := rfl
@[simp] theorem map_r3 (f : F → A) (c : GCircuit F) : (c.map f).r3 = f c.r3 := rfl

@[simp] theorem map_id (c : GCircuit F) : c.map id = c := rfl

theorem map_congr {f g : F → A} (c : GCircuit F) (h : ∀ y, f y = g y) : c.map f = c.map g := by
  simp only [GCircuit.map, h]

theorem map_map (g : A → B) (f : F → A) (c : GCircuit F) :
    (c.map f).map g = c.map (g ∘ f) := rfl

/-- Interchange the two factors of the first gate. -/
def swap (c : GCircuit F) : GCircuit F := { c with α₁ := c.β₁, β₁ := c.α₁ }

@[simp] theorem swap_α₁ (c : GCircuit F) : c.swap.α₁ = c.β₁ := rfl
@[simp] theorem swap_β₁ (c : GCircuit F) : c.swap.β₁ = c.α₁ := rfl
@[simp] theorem swap_α₂ (c : GCircuit F) : c.swap.α₂ = c.α₂ := rfl
@[simp] theorem swap_β₂ (c : GCircuit F) : c.swap.β₂ = c.β₂ := rfl
@[simp] theorem swap_α₃ (c : GCircuit F) : c.swap.α₃ = c.α₃ := rfl
@[simp] theorem swap_β₃ (c : GCircuit F) : c.swap.β₃ = c.β₃ := rfl
@[simp] theorem swap_p21 (c : GCircuit F) : c.swap.p21 = c.p21 := rfl
@[simp] theorem swap_q21 (c : GCircuit F) : c.swap.q21 = c.q21 := rfl
@[simp] theorem swap_p31 (c : GCircuit F) : c.swap.p31 = c.p31 := rfl
@[simp] theorem swap_p32 (c : GCircuit F) : c.swap.p32 = c.p32 := rfl
@[simp] theorem swap_q31 (c : GCircuit F) : c.swap.q31 = c.q31 := rfl
@[simp] theorem swap_q32 (c : GCircuit F) : c.swap.q32 = c.q32 := rfl
@[simp] theorem swap_γ (c : GCircuit F) : c.swap.γ = c.γ := rfl
@[simp] theorem swap_r1 (c : GCircuit F) : c.swap.r1 = c.r1 := rfl
@[simp] theorem swap_r2 (c : GCircuit F) : c.swap.r2 = c.r2 := rfl
@[simp] theorem swap_r3 (c : GCircuit F) : c.swap.r3 = c.r3 := rfl

theorem swap_map (f : F → A) (c : GCircuit F) : (c.map f).swap = c.swap.map f := rfl

/-- The coefficients of `G₁` in the five later slots: `λ = (p₂₁, q₂₁, p₃₁, q₃₁, r₁)`. -/
def lam (c : GCircuit F) : Fin 5 → F := ![c.p21, c.q21, c.p31, c.q31, c.r1]

@[simp] theorem lam_zero (c : GCircuit F) : c.lam 0 = c.p21 := rfl
@[simp] theorem lam_one (c : GCircuit F) : c.lam 1 = c.q21 := rfl
@[simp] theorem lam_two (c : GCircuit F) : c.lam 2 = c.p31 := rfl
@[simp] theorem lam_three (c : GCircuit F) : c.lam 3 = c.q31 := rfl
@[simp] theorem lam_four (c : GCircuit F) : c.lam 4 = c.r1 := rfl

@[simp] theorem lam_map (f : F → A) (c : GCircuit F) (j : Fin 5) :
    (c.map f).lam j = f (c.lam j) := by
  fin_cases j <;> rfl

@[simp] theorem lam_swap (c : GCircuit F) : c.swap.lam = c.lam := rfl

/-- The normalized constants of the repair (no division): `R₁₀ = β₁`, `L₂₁ = α₁ p₂₁`,
`L₂₀ = α₂`, `R₂₁ = α₁ q₂₁`, `R₂₀ = β₂`, `L₃₂ = p₃₂`, `L₃₁ = α₁ p₃₁`, `L₃₀ = α₃`,
`R₃₂ = q₃₂`, `R₃₁ = α₁ q₃₁`, `R₃₀ = β₃`, `s₃ = r₃`, `s₂ = r₂`, `s₁ = α₁ r₁`, `s₀ = γ`. -/
def toNormal [Mul F] (c : GCircuit F) : Circuit F where
  R10 := c.β₁
  L21 := c.α₁ * c.p21
  L20 := c.α₂
  R21 := c.α₁ * c.q21
  R20 := c.β₂
  L32 := c.p32
  L31 := c.α₁ * c.p31
  L30 := c.α₃
  R32 := c.q32
  R31 := c.α₁ * c.q31
  R30 := c.β₃
  s3 := c.r3
  s2 := c.r2
  s1 := c.α₁ * c.r1
  s0 := c.γ

section toNormal
variable [Mul F] (c : GCircuit F)
@[simp] theorem toNormal_R10 : c.toNormal.R10 = c.β₁ := rfl
@[simp] theorem toNormal_L21 : c.toNormal.L21 = c.α₁ * c.p21 := rfl
@[simp] theorem toNormal_L20 : c.toNormal.L20 = c.α₂ := rfl
@[simp] theorem toNormal_R21 : c.toNormal.R21 = c.α₁ * c.q21 := rfl
@[simp] theorem toNormal_R20 : c.toNormal.R20 = c.β₂ := rfl
@[simp] theorem toNormal_L32 : c.toNormal.L32 = c.p32 := rfl
@[simp] theorem toNormal_L31 : c.toNormal.L31 = c.α₁ * c.p31 := rfl
@[simp] theorem toNormal_L30 : c.toNormal.L30 = c.α₃ := rfl
@[simp] theorem toNormal_R32 : c.toNormal.R32 = c.q32 := rfl
@[simp] theorem toNormal_R31 : c.toNormal.R31 = c.α₁ * c.q31 := rfl
@[simp] theorem toNormal_R30 : c.toNormal.R30 = c.β₃ := rfl
@[simp] theorem toNormal_s3 : c.toNormal.s3 = c.r3 := rfl
@[simp] theorem toNormal_s2 : c.toNormal.s2 = c.r2 := rfl
@[simp] theorem toNormal_s1 : c.toNormal.s1 = c.α₁ * c.r1 := rfl
@[simp] theorem toNormal_s0 : c.toNormal.s0 = c.γ := rfl
end toNormal

theorem toNormal_map [CommRing F] [CommRing A] (f : F →+* A) (c : GCircuit F) :
    (c.map f).toNormal = c.toNormal.map f := by
  simp only [toNormal, GCircuit.map, Circuit.map, map_mul]

/-- A normal-form circuit as a general one: the first factor of `G₁` is exactly `x`
(`α₁ = 1`, and the `u₁` slot is meant to be `0`). -/
def ofNormal [One F] (c' : Circuit F) : GCircuit F where
  α₁ := 1
  β₁ := c'.R10
  α₂ := c'.L20
  β₂ := c'.R20
  α₃ := c'.L30
  β₃ := c'.R30
  p21 := c'.L21
  q21 := c'.R21
  p31 := c'.L31
  p32 := c'.L32
  q31 := c'.R31
  q32 := c'.R32
  γ := c'.s0
  r1 := c'.s1
  r2 := c'.s2
  r3 := c'.s3

section ofNormal
variable [One F] (c' : Circuit F)
@[simp] theorem ofNormal_α₁ : (ofNormal c').α₁ = 1 := rfl
@[simp] theorem ofNormal_β₁ : (ofNormal c').β₁ = c'.R10 := rfl
@[simp] theorem ofNormal_α₂ : (ofNormal c').α₂ = c'.L20 := rfl
@[simp] theorem ofNormal_β₂ : (ofNormal c').β₂ = c'.R20 := rfl
@[simp] theorem ofNormal_α₃ : (ofNormal c').α₃ = c'.L30 := rfl
@[simp] theorem ofNormal_β₃ : (ofNormal c').β₃ = c'.R30 := rfl
@[simp] theorem ofNormal_p21 : (ofNormal c').p21 = c'.L21 := rfl
@[simp] theorem ofNormal_q21 : (ofNormal c').q21 = c'.R21 := rfl
@[simp] theorem ofNormal_p31 : (ofNormal c').p31 = c'.L31 := rfl
@[simp] theorem ofNormal_p32 : (ofNormal c').p32 = c'.L32 := rfl
@[simp] theorem ofNormal_q31 : (ofNormal c').q31 = c'.R31 := rfl
@[simp] theorem ofNormal_q32 : (ofNormal c').q32 = c'.R32 := rfl
@[simp] theorem ofNormal_γ : (ofNormal c').γ = c'.s0 := rfl
@[simp] theorem ofNormal_r1 : (ofNormal c').r1 = c'.s1 := rfl
@[simp] theorem ofNormal_r2 : (ofNormal c').r2 = c'.s2 := rfl
@[simp] theorem ofNormal_r3 : (ofNormal c').r3 = c'.s3 := rfl
end ofNormal

theorem ofNormal_map [CommRing F] [CommRing A] (f : F →+* A) (c' : Circuit F) :
    (ofNormal c').map f = ofNormal (c'.map f) := by
  ext <;> simp [ofNormal, GCircuit.map, Circuit.map]

end GCircuit

/-! ## Slot vectors: swapping the two first-gate slots, dropping the `u₁` slot -/

/-- Interchange the slots `u₁` and `v₁` (indices `0` and `1`) of a seven-slot vector. -/
def swapSlots {α : Type*} (z : Fin 7 → α) : Fin 7 → α :=
  Matrix.vecCons (z 1) (Matrix.vecCons (z 0) fun j : Fin 5 => z j.succ.succ)

section swapSlots
variable {α : Type*} (z : Fin 7 → α)
@[simp] theorem swapSlots_zero : swapSlots z 0 = z 1 := rfl
@[simp] theorem swapSlots_one : swapSlots z 1 = z 0 := rfl
@[simp] theorem swapSlots_succ_succ (j : Fin 5) : swapSlots z j.succ.succ = z j.succ.succ := by
  simp only [swapSlots, Matrix.cons_val_succ]
@[simp] theorem swapSlots_two : swapSlots z 2 = z 2 := rfl
@[simp] theorem swapSlots_three : swapSlots z 3 = z 3 := rfl
@[simp] theorem swapSlots_four : swapSlots z 4 = z 4 := rfl
@[simp] theorem swapSlots_five : swapSlots z 5 = z 5 := rfl
@[simp] theorem swapSlots_six : swapSlots z 6 = z 6 := rfl
end swapSlots

/-- Drop the `u₁` slot: the six normal-form slots `(v₁, u₂, v₂, u₃, v₃, w)`. -/
def tailSlots {α : Type*} (z : Fin 7 → α) : Fin 6 → α := fun j => z j.succ

section tailSlots
variable {α : Type*} (z : Fin 7 → α)
@[simp] theorem tailSlots_zero : tailSlots z 0 = z 1 := rfl
@[simp] theorem tailSlots_one : tailSlots z 1 = z 2 := rfl
@[simp] theorem tailSlots_two : tailSlots z 2 = z 3 := rfl
@[simp] theorem tailSlots_three : tailSlots z 3 = z 4 := rfl
@[simp] theorem tailSlots_four : tailSlots z 4 = z 5 := rfl
@[simp] theorem tailSlots_five : tailSlots z 5 = z 6 := rfl
end tailSlots

/-! ## Program semantics -/

section Semantics

variable [CommRing A]

/-- `G₁ = (α₁ x + u₁)(β₁ x + v₁)`. -/
def g1 (c : GCircuit A) (x : A) (z : Fin 7 → A) : A := (c.α₁ * x + z 0) * (c.β₁ * x + z 1)

/-- The first factor of `G₂`: `α₂ x + p₂₁ G₁ + u₂`. -/
def gl2 (c : GCircuit A) (x : A) (z : Fin 7 → A) : A := c.α₂ * x + c.p21 * g1 c x z + z 2

/-- The second factor of `G₂`: `β₂ x + q₂₁ G₁ + v₂`. -/
def gr2 (c : GCircuit A) (x : A) (z : Fin 7 → A) : A := c.β₂ * x + c.q21 * g1 c x z + z 3

/-- `G₂`. -/
def g2 (c : GCircuit A) (x : A) (z : Fin 7 → A) : A := gl2 c x z * gr2 c x z

/-- The first factor of `G₃`: `α₃ x + p₃₁ G₁ + p₃₂ G₂ + u₃`. -/
def gl3 (c : GCircuit A) (x : A) (z : Fin 7 → A) : A :=
  c.α₃ * x + c.p31 * g1 c x z + c.p32 * g2 c x z + z 4

/-- The second factor of `G₃`: `β₃ x + q₃₁ G₁ + q₃₂ G₂ + v₃`. -/
def gr3 (c : GCircuit A) (x : A) (z : Fin 7 → A) : A :=
  c.β₃ * x + c.q31 * g1 c x z + c.q32 * g2 c x z + z 5

/-- `G₃`. -/
def g3 (c : GCircuit A) (x : A) (z : Fin 7 → A) : A := gl3 c x z * gr3 c x z

/-- The output `f = γ x + r₁ G₁ + r₂ G₂ + r₃ G₃ + w`. -/
def gout (c : GCircuit A) (x : A) (z : Fin 7 → A) : A :=
  c.γ * x + c.r1 * g1 c x z + c.r2 * g2 c x z + c.r3 * g3 c x z + z 6

/-- The slot map `ν(u₁, v₁, s) = (v₁ + b u₁, s + λ u₁ v₁)`, in the normal-form slot order
`(a₁, a₂, b₂, a₃, b₃, b₁)`. -/
def nuSlots (b : A) (c : GCircuit A) (z : Fin 7 → A) : Fin 6 → A :=
  Matrix.vecCons (z 1 + b * z 0) fun j : Fin 5 => z j.succ.succ + c.lam j * (z 0 * z 1)

variable (b : A) (c : GCircuit A) (z : Fin 7 → A)

@[simp] theorem nuSlots_zero : nuSlots b c z 0 = z 1 + b * z 0 := rfl
@[simp] theorem nuSlots_succ (j : Fin 5) :
    nuSlots b c z j.succ = z j.succ.succ + c.lam j * (z 0 * z 1) := by
  simp only [nuSlots, Matrix.cons_val_succ]
@[simp] theorem nuSlots_one : nuSlots b c z 1 = z 2 + c.p21 * (z 0 * z 1) := rfl
@[simp] theorem nuSlots_two : nuSlots b c z 2 = z 3 + c.q21 * (z 0 * z 1) := rfl
@[simp] theorem nuSlots_three : nuSlots b c z 3 = z 4 + c.p31 * (z 0 * z 1) := rfl
@[simp] theorem nuSlots_four : nuSlots b c z 4 = z 5 + c.q31 * (z 0 * z 1) := rfl
@[simp] theorem nuSlots_five : nuSlots b c z 5 = z 6 + c.r1 * (z 0 * z 1) := rfl

end Semantics

/-! ## Compatibility with ring homomorphisms -/

section Hom

variable [CommRing A] [CommRing B]

@[simp] theorem map_g1 (f : A →+* B) (c : GCircuit A) (x : A) (z : Fin 7 → A) :
    f (g1 c x z) = g1 (c.map f) (f x) (fun i => f (z i)) := by
  simp [g1]

@[simp] theorem map_gl2 (f : A →+* B) (c : GCircuit A) (x : A) (z : Fin 7 → A) :
    f (gl2 c x z) = gl2 (c.map f) (f x) (fun i => f (z i)) := by
  simp [gl2]

@[simp] theorem map_gr2 (f : A →+* B) (c : GCircuit A) (x : A) (z : Fin 7 → A) :
    f (gr2 c x z) = gr2 (c.map f) (f x) (fun i => f (z i)) := by
  simp [gr2]

@[simp] theorem map_g2 (f : A →+* B) (c : GCircuit A) (x : A) (z : Fin 7 → A) :
    f (g2 c x z) = g2 (c.map f) (f x) (fun i => f (z i)) := by
  simp [g2]

@[simp] theorem map_gl3 (f : A →+* B) (c : GCircuit A) (x : A) (z : Fin 7 → A) :
    f (gl3 c x z) = gl3 (c.map f) (f x) (fun i => f (z i)) := by
  simp [gl3]

@[simp] theorem map_gr3 (f : A →+* B) (c : GCircuit A) (x : A) (z : Fin 7 → A) :
    f (gr3 c x z) = gr3 (c.map f) (f x) (fun i => f (z i)) := by
  simp [gr3]

@[simp] theorem map_g3 (f : A →+* B) (c : GCircuit A) (x : A) (z : Fin 7 → A) :
    f (g3 c x z) = g3 (c.map f) (f x) (fun i => f (z i)) := by
  simp [g3]

@[simp] theorem map_gout (f : A →+* B) (c : GCircuit A) (x : A) (z : Fin 7 → A) :
    f (gout c x z) = gout (c.map f) (f x) (fun i => f (z i)) := by
  simp [gout]

theorem map_nuSlots (f : A →+* B) (b : A) (c : GCircuit A) (z : Fin 7 → A) (j : Fin 6) :
    f (nuSlots b c z j) = nuSlots (f b) (c.map f) (fun i => f (z i)) j := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [nuSlots_zero, map_add, map_mul]
  · simp only [nuSlots_succ, GCircuit.lam_map, map_add, map_mul]

end Hom

end FastPoly.LowerBound.General
