/-
The degree-six lower bound (`sections/lower.tex`): the normal-form model.
-/
import FastPoly.LowerBound.Jacobian
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Degree-six lower bound: the normal-form program and its Jacobian

This file sets up the *model* used by the lower bound of `sections/lower.tex`:
a straight-line program with three nonscalar multiplications, six parameter slots, and
fixed circuit constants, written in the paper's normal form

```
u₀ = x
u₁ = x (R₁₀ x + a₁)
u₂ = ℓ₂ r₂ = (L₂₁ u₁ + L₂₀ x + a₂)(R₂₁ u₁ + R₂₀ x + b₂)
u₃ = ℓ₃ r₃ = (L₃₂ u₂ + L₃₁ u₁ + L₃₀ x + a₃)(R₃₂ u₂ + R₃₁ u₁ + R₃₀ x + b₃)
P  = s₃ u₃ + s₂ u₂ + s₁ u₁ + s₀ x + b₁
```

## Design decisions

* The fixed constants `R₁₀, L₂₁, …, s₀` are bundled into `Circuit F` (a plain data
  structure).  `Circuit.map` transports them along any map of coefficients; this lets a
  *single* definition of the program semantics be reused in every ring we care about.

* The semantics `u1, ell2, r2, u2, ell3, r3, u3, out` are defined over an arbitrary
  commutative ring `A`, with the input `x : A` and the six parameter slots
  `p : Fin 6 → A` both taken in `A`.  Two instantiations are used:

  - `A = F`, `x = xₖ`, `p = ` the actual parameters — the *value* of the program;
  - `A = MvPolynomial (Fin 6) F`, `x = C xₖ`, `p = X` — the program output as a
    polynomial in the six parameters, whose `pderiv`s are the Jacobian entries.

  (A third instantiation, `A = Polynomial F`, `x = Polynomial.X`, `p = C ∘ p₀`, gives the
  output as a polynomial in `x` and is what the degree arguments of Case `D = 0` will use.)

* **Slot numbering.**  The six parameter slots are indexed by `Fin 6` in the order of the
  paper's tuple `(a₁, a₂, b₂, a₃, b₃, b₁)`:

  | index | `0`  | `1`  | `2`  | `3`  | `4`  | `5`  |
  |-------|------|------|------|------|------|------|
  | slot  | `a₁` | `a₂` | `b₂` | `a₃` | `b₃` | `b₁` |

* The six *sensitivities* `∂P/∂pᵢ` are **defined** by the paper's closed forms (`sens`,
  built from the barred quantities `ubar1`, `ubar2`); `derivation_out` and
  `pderiv_outPoly` prove that these closed forms really are the partial derivatives.

* The two degenerate branches that *both* halves of the case analysis begin with —
  `s₃ = 0` and `E = 0` — are proved once here
  (`jacobian_det_eq_zero_of_s3_eq_zero`, `exists_singular_jacobian_of_E_eq_zero`) and used
  by `CaseDNonzero.lean` and `CaseDZero.lean` alike.
-/

namespace FastPoly.LowerBound

open MvPolynomial

variable {F A B : Type*}

/-! ## Circuit constants -/

/-- The fixed scalar constants of a three-multiplication straight-line program in normal
form.  These are *not* parameters: they are hard-wired in the circuit. -/
structure Circuit (F : Type*) where
  /-- Coefficient of `x` in the second factor of the first multiplication. -/
  R10 : F
  /-- Coefficient of `u₁` in `ℓ₂`. -/
  L21 : F
  /-- Coefficient of `x` in `ℓ₂`. -/
  L20 : F
  /-- Coefficient of `u₁` in `r₂`. -/
  R21 : F
  /-- Coefficient of `x` in `r₂`. -/
  R20 : F
  /-- Coefficient of `u₂` in `ℓ₃`. -/
  L32 : F
  /-- Coefficient of `u₁` in `ℓ₃`. -/
  L31 : F
  /-- Coefficient of `x` in `ℓ₃`. -/
  L30 : F
  /-- Coefficient of `u₂` in `r₃`. -/
  R32 : F
  /-- Coefficient of `u₁` in `r₃`. -/
  R31 : F
  /-- Coefficient of `x` in `r₃`. -/
  R30 : F
  /-- Coefficient of `u₃` in the output. -/
  s3 : F
  /-- Coefficient of `u₂` in the output. -/
  s2 : F
  /-- Coefficient of `u₁` in the output. -/
  s1 : F
  /-- Coefficient of `x` in the output. -/
  s0 : F

namespace Circuit

/-- Transport the circuit constants along a map of coefficients. -/
def map (f : F → A) (c : Circuit F) : Circuit A where
  R10 := f c.R10
  L21 := f c.L21
  L20 := f c.L20
  R21 := f c.R21
  R20 := f c.R20
  L32 := f c.L32
  L31 := f c.L31
  L30 := f c.L30
  R32 := f c.R32
  R31 := f c.R31
  R30 := f c.R30
  s3 := f c.s3
  s2 := f c.s2
  s1 := f c.s1
  s0 := f c.s0

@[simp] theorem map_R10 (f : F → A) (c : Circuit F) : (c.map f).R10 = f c.R10 := rfl
@[simp] theorem map_L21 (f : F → A) (c : Circuit F) : (c.map f).L21 = f c.L21 := rfl
@[simp] theorem map_L20 (f : F → A) (c : Circuit F) : (c.map f).L20 = f c.L20 := rfl
@[simp] theorem map_R21 (f : F → A) (c : Circuit F) : (c.map f).R21 = f c.R21 := rfl
@[simp] theorem map_R20 (f : F → A) (c : Circuit F) : (c.map f).R20 = f c.R20 := rfl
@[simp] theorem map_L32 (f : F → A) (c : Circuit F) : (c.map f).L32 = f c.L32 := rfl
@[simp] theorem map_L31 (f : F → A) (c : Circuit F) : (c.map f).L31 = f c.L31 := rfl
@[simp] theorem map_L30 (f : F → A) (c : Circuit F) : (c.map f).L30 = f c.L30 := rfl
@[simp] theorem map_R32 (f : F → A) (c : Circuit F) : (c.map f).R32 = f c.R32 := rfl
@[simp] theorem map_R31 (f : F → A) (c : Circuit F) : (c.map f).R31 = f c.R31 := rfl
@[simp] theorem map_R30 (f : F → A) (c : Circuit F) : (c.map f).R30 = f c.R30 := rfl
@[simp] theorem map_s3 (f : F → A) (c : Circuit F) : (c.map f).s3 = f c.s3 := rfl
@[simp] theorem map_s2 (f : F → A) (c : Circuit F) : (c.map f).s2 = f c.s2 := rfl
@[simp] theorem map_s1 (f : F → A) (c : Circuit F) : (c.map f).s1 = f c.s1 := rfl
@[simp] theorem map_s0 (f : F → A) (c : Circuit F) : (c.map f).s0 = f c.s0 := rfl

@[simp] theorem map_id (c : Circuit F) : c.map id = c := rfl

theorem map_congr {f g : F → A} (c : Circuit F) (h : ∀ y, f y = g y) : c.map f = c.map g := by
  simp only [Circuit.map, h]

theorem map_map (g : A → B) (f : F → A) (c : Circuit F) :
    (c.map f).map g = c.map (g ∘ f) := rfl

/-- The determinant `D = L₃₂ R₃₁ - R₃₂ L₃₁` governing the case split of the proof. -/
def D [Mul F] [Sub F] (c : Circuit F) : F := c.L32 * c.R31 - c.R32 * c.L31

/-- The determinant `|L₂₀ L₂₁ ; R₂₀ R₂₁|` of the second multiplication.  When it vanishes
the two `u₂`-slot columns of the Jacobian are proportional. -/
def E [Mul F] [Sub F] (c : Circuit F) : F := c.L20 * c.R21 - c.L21 * c.R20

end Circuit

/-! ## Program semantics

All of these are stated over an arbitrary commutative ring `A`; the circuit constants are
already elements of `A` (use `Circuit.map` to put them there). -/

section Semantics

variable [CommRing A]

/-- `u₁ = x (R₁₀ x + a₁)`, the first nonscalar multiplication. -/
def u1 (c : Circuit A) (x : A) (p : Fin 6 → A) : A := x * (c.R10 * x + p 0)

/-- `ℓ₂ = L₂₁ u₁ + L₂₀ x + a₂`, the left factor of the second multiplication. -/
def ell2 (c : Circuit A) (x : A) (p : Fin 6 → A) : A := c.L21 * u1 c x p + c.L20 * x + p 1

/-- `r₂ = R₂₁ u₁ + R₂₀ x + b₂`, the right factor of the second multiplication. -/
def r2 (c : Circuit A) (x : A) (p : Fin 6 → A) : A := c.R21 * u1 c x p + c.R20 * x + p 2

/-- `u₂ = ℓ₂ r₂`, the second nonscalar multiplication. -/
def u2 (c : Circuit A) (x : A) (p : Fin 6 → A) : A := ell2 c x p * r2 c x p

/-- `ℓ₃ = L₃₂ u₂ + L₃₁ u₁ + L₃₀ x + a₃`, the left factor of the third multiplication. -/
def ell3 (c : Circuit A) (x : A) (p : Fin 6 → A) : A :=
  c.L32 * u2 c x p + c.L31 * u1 c x p + c.L30 * x + p 3

/-- `r₃ = R₃₂ u₂ + R₃₁ u₁ + R₃₀ x + b₃`, the right factor of the third multiplication. -/
def r3 (c : Circuit A) (x : A) (p : Fin 6 → A) : A :=
  c.R32 * u2 c x p + c.R31 * u1 c x p + c.R30 * x + p 4

/-- `u₃ = ℓ₃ r₃`, the third nonscalar multiplication. -/
def u3 (c : Circuit A) (x : A) (p : Fin 6 → A) : A := ell3 c x p * r3 c x p

/-- The program output `P = s₃ u₃ + s₂ u₂ + s₁ u₁ + s₀ x + b₁`. -/
def out (c : Circuit A) (x : A) (p : Fin 6 → A) : A :=
  c.s3 * u3 c x p + c.s2 * u2 c x p + c.s1 * u1 c x p + c.s0 * x + p 5

/-- `ū₃ = ∂P/∂u₃ = s₃`. -/
def ubar3 (c : Circuit A) : A := c.s3

/-- `ū₂ = ∂P/∂u₂ = s₂ + ū₃ (L₃₂ r₃ + R₃₂ ℓ₃)`. -/
def ubar2 (c : Circuit A) (x : A) (p : Fin 6 → A) : A :=
  c.s2 + ubar3 c * (c.L32 * r3 c x p + c.R32 * ell3 c x p)

/-- `ū₁ = ∂P/∂u₁ = s₁ + ū₂ (L₂₁ r₂ + R₂₁ ℓ₂) + ū₃ (L₃₁ r₃ + R₃₁ ℓ₃)`. -/
def ubar1 (c : Circuit A) (x : A) (p : Fin 6 → A) : A :=
  c.s1 + ubar2 c x p * (c.L21 * r2 c x p + c.R21 * ell2 c x p)
    + ubar3 c * (c.L31 * r3 c x p + c.R31 * ell3 c x p)

/-- The six sensitivities `∂P/∂pᵢ` in the closed form of `sections/lower.tex`,
in slot order `(a₁, a₂, b₂, a₃, b₃, b₁)`. -/
def sens (c : Circuit A) (x : A) (p : Fin 6 → A) : Fin 6 → A :=
  ![ubar1 c x p * x,
    ubar2 c x p * r2 c x p,
    ubar2 c x p * ell2 c x p,
    ubar3 c * r3 c x p,
    ubar3 c * ell3 c x p,
    1]

@[simp] theorem sens_zero (c : Circuit A) (x : A) (p : Fin 6 → A) :
    sens c x p 0 = ubar1 c x p * x := rfl
@[simp] theorem sens_one (c : Circuit A) (x : A) (p : Fin 6 → A) :
    sens c x p 1 = ubar2 c x p * r2 c x p := rfl
@[simp] theorem sens_two (c : Circuit A) (x : A) (p : Fin 6 → A) :
    sens c x p 2 = ubar2 c x p * ell2 c x p := rfl
@[simp] theorem sens_three (c : Circuit A) (x : A) (p : Fin 6 → A) :
    sens c x p 3 = ubar3 c * r3 c x p := rfl
@[simp] theorem sens_four (c : Circuit A) (x : A) (p : Fin 6 → A) :
    sens c x p 4 = ubar3 c * ell3 c x p := rfl
@[simp] theorem sens_five (c : Circuit A) (x : A) (p : Fin 6 → A) :
    sens c x p 5 = 1 := rfl

end Semantics

/-! ## Compatibility with ring homomorphisms -/

section Hom

variable [CommRing A] [CommRing B]

@[simp] theorem map_u1 (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (u1 c x p) = u1 (c.map f) (f x) (fun i => f (p i)) := by
  simp [u1]

@[simp] theorem map_ell2 (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (ell2 c x p) = ell2 (c.map f) (f x) (fun i => f (p i)) := by
  simp [ell2]

@[simp] theorem map_r2 (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (r2 c x p) = r2 (c.map f) (f x) (fun i => f (p i)) := by
  simp [r2]

@[simp] theorem map_u2 (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (u2 c x p) = u2 (c.map f) (f x) (fun i => f (p i)) := by
  simp [u2]

@[simp] theorem map_ell3 (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (ell3 c x p) = ell3 (c.map f) (f x) (fun i => f (p i)) := by
  simp [ell3]

@[simp] theorem map_r3 (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (r3 c x p) = r3 (c.map f) (f x) (fun i => f (p i)) := by
  simp [r3]

@[simp] theorem map_u3 (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (u3 c x p) = u3 (c.map f) (f x) (fun i => f (p i)) := by
  simp [u3]

@[simp] theorem map_out (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (out c x p) = out (c.map f) (f x) (fun i => f (p i)) := by
  simp [out]

@[simp] theorem map_ubar3 (f : A →+* B) (c : Circuit A) :
    f (ubar3 c) = ubar3 (c.map f) := rfl

@[simp] theorem map_ubar2 (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (ubar2 c x p) = ubar2 (c.map f) (f x) (fun i => f (p i)) := by
  simp [ubar2]

@[simp] theorem map_ubar1 (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) :
    f (ubar1 c x p) = ubar1 (c.map f) (f x) (fun i => f (p i)) := by
  simp [ubar1]

theorem map_sens (f : A →+* B) (c : Circuit A) (x : A) (p : Fin 6 → A) (i : Fin 6) :
    f (sens c x p i) = sens (c.map f) (f x) (fun i => f (p i)) i := by
  fin_cases i <;> simp

end Hom

/-! ## The sensitivities are the partial derivatives

The proof is a chain-rule computation valid for *any* derivation `D` that kills the
circuit constants and the input `x`; `pderiv_outPoly` then specializes it. -/

section Chain

variable [CommRing F] [CommRing A] [Algebra F A]

/-- **Chain rule / total derivative.**  For any `F`-derivation `D` of `A` that kills the
input `x`, the derivative of the program output is the sum of the six sensitivities times
the derivatives of the six parameter slots.  This is the formal content of the display
in `sections/lower.tex` giving `∂P/∂b₁ = 1`, `∂P/∂b₃ = s₃ ℓ₃`, … -/
theorem derivation_out (D : Derivation F A A) (c : Circuit F) (x : A) (hx : D x = 0)
    (p : Fin 6 → A) :
    D (out (c.map (algebraMap F A)) x p)
      = ∑ j : Fin 6, sens (c.map (algebraMap F A)) x p j * D (p j) := by
  have hsm : ∀ (y : F) (a : A), D (algebraMap F A y * a) = algebraMap F A y * D a := by
    intro y a
    rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero, smul_eq_mul]
  have hu1 : D (u1 (c.map (algebraMap F A)) x p) = x * D (p 0) := by
    have h : u1 (c.map (algebraMap F A)) x p
        = x * (algebraMap F A c.R10 * x + p 0) := rfl
    rw [h, Derivation.leibniz, map_add, hsm, hx, smul_zero, add_zero, mul_zero, zero_add,
      smul_eq_mul]
  have hell2 : D (ell2 (c.map (algebraMap F A)) x p)
      = algebraMap F A c.L21 * (x * D (p 0)) + D (p 1) := by
    have h : ell2 (c.map (algebraMap F A)) x p
        = algebraMap F A c.L21 * u1 (c.map (algebraMap F A)) x p
          + algebraMap F A c.L20 * x + p 1 := rfl
    rw [h, map_add, map_add, hsm, hsm, hu1, hx, mul_zero, add_zero]
  have hr2 : D (r2 (c.map (algebraMap F A)) x p)
      = algebraMap F A c.R21 * (x * D (p 0)) + D (p 2) := by
    have h : r2 (c.map (algebraMap F A)) x p
        = algebraMap F A c.R21 * u1 (c.map (algebraMap F A)) x p
          + algebraMap F A c.R20 * x + p 2 := rfl
    rw [h, map_add, map_add, hsm, hsm, hu1, hx, mul_zero, add_zero]
  have hu2 : D (u2 (c.map (algebraMap F A)) x p)
      = ell2 (c.map (algebraMap F A)) x p * D (r2 (c.map (algebraMap F A)) x p)
        + r2 (c.map (algebraMap F A)) x p * D (ell2 (c.map (algebraMap F A)) x p) := by
    have h : u2 (c.map (algebraMap F A)) x p
        = ell2 (c.map (algebraMap F A)) x p * r2 (c.map (algebraMap F A)) x p := rfl
    rw [h, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hell3 : D (ell3 (c.map (algebraMap F A)) x p)
      = algebraMap F A c.L32 * D (u2 (c.map (algebraMap F A)) x p)
        + algebraMap F A c.L31 * (x * D (p 0)) + D (p 3) := by
    have h : ell3 (c.map (algebraMap F A)) x p
        = algebraMap F A c.L32 * u2 (c.map (algebraMap F A)) x p
          + algebraMap F A c.L31 * u1 (c.map (algebraMap F A)) x p
          + algebraMap F A c.L30 * x + p 3 := rfl
    rw [h, map_add, map_add, map_add, hsm, hsm, hsm, hu1, hx, mul_zero, add_zero]
  have hr3 : D (r3 (c.map (algebraMap F A)) x p)
      = algebraMap F A c.R32 * D (u2 (c.map (algebraMap F A)) x p)
        + algebraMap F A c.R31 * (x * D (p 0)) + D (p 4) := by
    have h : r3 (c.map (algebraMap F A)) x p
        = algebraMap F A c.R32 * u2 (c.map (algebraMap F A)) x p
          + algebraMap F A c.R31 * u1 (c.map (algebraMap F A)) x p
          + algebraMap F A c.R30 * x + p 4 := rfl
    rw [h, map_add, map_add, map_add, hsm, hsm, hsm, hu1, hx, mul_zero, add_zero]
  have hu3 : D (u3 (c.map (algebraMap F A)) x p)
      = ell3 (c.map (algebraMap F A)) x p * D (r3 (c.map (algebraMap F A)) x p)
        + r3 (c.map (algebraMap F A)) x p * D (ell3 (c.map (algebraMap F A)) x p) := by
    have h : u3 (c.map (algebraMap F A)) x p
        = ell3 (c.map (algebraMap F A)) x p * r3 (c.map (algebraMap F A)) x p := rfl
    rw [h, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hout : D (out (c.map (algebraMap F A)) x p)
      = algebraMap F A c.s3 * D (u3 (c.map (algebraMap F A)) x p)
        + algebraMap F A c.s2 * D (u2 (c.map (algebraMap F A)) x p)
        + algebraMap F A c.s1 * D (u1 (c.map (algebraMap F A)) x p) + D (p 5) := by
    have h : out (c.map (algebraMap F A)) x p
        = algebraMap F A c.s3 * u3 (c.map (algebraMap F A)) x p
          + algebraMap F A c.s2 * u2 (c.map (algebraMap F A)) x p
          + algebraMap F A c.s1 * u1 (c.map (algebraMap F A)) x p
          + algebraMap F A c.s0 * x + p 5 := rfl
    rw [h, map_add, map_add, map_add, map_add, hsm, hsm, hsm, hsm, hx, mul_zero, add_zero]
  rw [hout, hu3, hell3, hr3, hu2, hell2, hr2, hu1, Fin.sum_univ_six]
  simp only [sens_zero, sens_one, sens_two, sens_three, sens_four, sens_five, ubar1, ubar2,
    ubar3, Circuit.map_s3, Circuit.map_s2, Circuit.map_s1, Circuit.map_L32, Circuit.map_R32,
    Circuit.map_L31, Circuit.map_R31, Circuit.map_L21, Circuit.map_R21]
  ring

end Chain

/-! ## The polynomial family and its Jacobian -/

section Jacobian

variable [CommRing F]

/-- The six output polynomials `p ↦ P_p(x_k)`, as elements of `MvPolynomial (Fin 6) F`.
These are the coordinates of the map `F` of `sections/lower.tex`. -/
noncomputable def outPoly (c : Circuit F) (xs : Fin 6 → F) : Fin 6 → MvPolynomial (Fin 6) F :=
  fun k => out (c.map C) (C (xs k)) X

/-- The Jacobian of `p ↦ (P_p(x₀), …, P_p(x₅))` at the parameter point `p`,
in the closed form of `sections/lower.tex`: rows are evaluation points, columns are
parameter slots. -/
def jacobian (c : Circuit F) (xs : Fin 6 → F) (p : Fin 6 → F) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun k i => sens c (xs k) p i

@[simp] theorem jacobian_apply (c : Circuit F) (xs : Fin 6 → F) (p : Fin 6 → F) (k i : Fin 6) :
    jacobian c xs p k i = sens c (xs k) p i := rfl

theorem map_C_eq_map_algebraMap (c : Circuit F) :
    c.map (C : F → MvPolynomial (Fin 6) F)
      = c.map (algebraMap F (MvPolynomial (Fin 6) F)) := by
  rw [MvPolynomial.algebraMap_eq]

/-- **The six sensitivities are the six partial derivatives.**  This is the display
`∂P/∂b₁ = 1`, `∂P/∂b₃ = s₃ℓ₃`, `∂P/∂a₃ = s₃r₃`, `∂P/∂b₂ = ū₂ℓ₂`, `∂P/∂a₂ = ū₂r₂`,
`∂P/∂a₁ = ū₁x` of `sections/lower.tex`. -/
theorem pderiv_outPoly (c : Circuit F) (xs : Fin 6 → F) (k i : Fin 6) :
    pderiv i (outPoly c xs k) = sens (c.map C) (C (xs k)) X i := by
  classical
  rw [outPoly, map_C_eq_map_algebraMap,
    derivation_out (pderiv i) c (C (xs k)) (by simp) X]
  have hterm : ∀ j : Fin 6,
      sens (c.map (algebraMap F (MvPolynomial (Fin 6) F))) (C (xs k)) X j *
          (pderiv i) (X j : MvPolynomial (Fin 6) F)
        = if j = i then
            sens (c.map (algebraMap F (MvPolynomial (Fin 6) F))) (C (xs k)) X j else 0 := by
    intro j
    rw [pderiv_X, Pi.single_apply]
    split_ifs with h
    · rw [mul_one]
    · rw [mul_zero]
  rw [Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_ite_eq' Finset.univ i
      (fun j => sens (c.map (algebraMap F (MvPolynomial (Fin 6) F))) (C (xs k)) X j)]
  simp [map_C_eq_map_algebraMap]

/-- Evaluating the polynomial Jacobian at a parameter point gives the closed-form
Jacobian. -/
theorem eval_pderiv_outPoly (c : Circuit F) (xs : Fin 6 → F) (p : Fin 6 → F) (k i : Fin 6) :
    eval p (pderiv i (outPoly c xs k)) = jacobian c xs p k i := by
  have h1 : (c.map (C : F → MvPolynomial (Fin 6) F)).map (eval p) = c := by
    rw [Circuit.map_map, Circuit.map_congr c (g := id) (fun y => by simp), Circuit.map_id]
  have h2 : (eval p) (C (xs k) : MvPolynomial (Fin 6) F) = xs k := by simp
  have h3 : (fun i => (eval p) (X i : MvPolynomial (Fin 6) F)) = p := by funext j; simp
  rw [pderiv_outPoly, jacobian_apply, map_sens (eval p) (c.map C) (C (xs k)) X i, h1, h2, h3]

/-- Evaluating the six output polynomials at a parameter point gives the six values
`P_p(x_k)`. -/
theorem eval_outPoly (c : Circuit F) (xs : Fin 6 → F) (p : Fin 6 → F) (k : Fin 6) :
    eval p (outPoly c xs k) = out c (xs k) p := by
  have h1 : (c.map (C : F → MvPolynomial (Fin 6) F)).map (eval p) = c := by
    rw [Circuit.map_map, Circuit.map_congr c (g := id) (fun y => by simp), Circuit.map_id]
  have h2 : (eval p) (C (xs k) : MvPolynomial (Fin 6) F) = xs k := by simp
  have h3 : (fun i => (eval p) (X i : MvPolynomial (Fin 6) F)) = p := by funext j; simp
  rw [outPoly, map_out (eval p) (c.map C) (C (xs k)) X, h1, h2, h3]

/-- If the output does not use the third multiplication (`s₃ = 0`) then the `a₃` column of
the Jacobian is identically zero, so the Jacobian is singular at every parameter point.
(`sections/lower.tex`, Case `D ≠ 0`, Step 2 and Case `D = 0`.) -/
theorem jacobian_det_eq_zero_of_s3_eq_zero (c : Circuit F) (hs3 : c.s3 = 0)
    (xs : Fin 6 → F) (p : Fin 6 → F) : (jacobian c xs p).det = 0 := by
  refine Matrix.det_eq_zero_of_column_eq_zero 3 fun k => ?_
  rw [jacobian_apply, sens_three, ubar3, hs3, zero_mul]

end Jacobian

/-! ## The degenerate branch `E = 0`

Both halves of the case analysis open with the same two degenerate branches, so they are
proved once, here.  The `s₃ = 0` branch is `jacobian_det_eq_zero_of_s3_eq_zero` above; the
`E = 0` branch is the following. -/

section DegenerateE

variable [Field F]

/-- **Degenerate branch `E = 0`.**  If `E = L₂₀R₂₁ - L₂₁R₂₀ = 0` then already at the
parameter point `p = 0` the two `u₂`-slot columns `∂P/∂a₂ = ū₂r₂` and `∂P/∂b₂ = ū₂ℓ₂` of
the Jacobian are linearly dependent, because `r₂` and `ℓ₂` are then (with `a₂ = b₂ = 0`)
two dependent linear forms in `u₁` and `x`.

`sections/lower.tex` states this in Case `D ≠ 0`, Step 1b, as: if the determinant
`|L₂₀ L₂₁; R₂₀ R₂₁|` vanishes then `(R₂₀,R₂₁) = α(L₂₀,L₂₁)`, so `r₂ = αℓ₂` and
`∂P/∂a₂ = α ∂P/∂b₂`; Case `D = 0` invokes the same fact ("we can assume … `≠ 0`, as
otherwise the rows `∂P/∂a₂` and `∂P/∂b₂` would be linearly dependent").

**Deviation from the paper.**  No such `α` exists when `(L₂₀, L₂₁) = (0,0)`.  We replace it
by the explicit kernel vector `(λ, μ) ≠ (0,0)` of `[[R₂₁, L₂₁], [R₂₀, L₂₀]]`
(`exists_kernel_two`), which gives `λr₂ + μℓ₂ = 0` identically at `p = 0` and hence the
column dependence `λ ∂P/∂a₂ + μ ∂P/∂b₂ = ū₂(λr₂ + μℓ₂) = 0` in all cases. -/
theorem exists_singular_jacobian_of_E_eq_zero (c : Circuit F) (hE : c.E = 0)
    (xs : Fin 6 → F) : ∃ p : Fin 6 → F, (jacobian c xs p).det = 0 := by
  obtain ⟨lam, mu, hlm, hk1, hk2⟩ :
      ∃ lam mu : F, (lam ≠ 0 ∨ mu ≠ 0) ∧ c.R21 * lam + c.L21 * mu = 0
        ∧ c.R20 * lam + c.L20 * mu = 0 := by
    refine exists_kernel_two (a := c.R21) (b := c.L21) (s := c.R20) (d := c.L20) ?_
    have hE' : c.L20 * c.R21 - c.L21 * c.R20 = 0 := hE
    linear_combination hE'
  obtain ⟨w, hw0, hw1, hw2, hw3, hw4, hw5⟩ : ∃ w : Fin 6 → F,
      w 0 = 0 ∧ w 1 = lam ∧ w 2 = mu ∧ w 3 = 0 ∧ w 4 = 0 ∧ w 5 = 0 :=
    ⟨![0, lam, mu, 0, 0, 0], by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨0, det_eq_zero_of_cols_dep w ?_ ?_⟩
  · rcases hlm with h | h
    · exact fun hcon => h (by rw [← hw1, hcon]; rfl)
    · exact fun hcon => h (by rw [← hw2, hcon]; rfl)
  · intro k
    have hr : r2 c (xs k) (0 : Fin 6 → F) = c.R21 * u1 c (xs k) 0 + c.R20 * xs k := by
      show c.R21 * u1 c (xs k) 0 + c.R20 * xs k + (0 : Fin 6 → F) 2 = _
      rw [Pi.zero_apply, add_zero]
    have he : ell2 c (xs k) (0 : Fin 6 → F) = c.L21 * u1 c (xs k) 0 + c.L20 * xs k := by
      show c.L21 * u1 c (xs k) 0 + c.L20 * xs k + (0 : Fin 6 → F) 1 = _
      rw [Pi.zero_apply, add_zero]
    rw [Fin.sum_univ_six, hw0, hw1, hw2, hw3, hw4, hw5]
    simp only [jacobian_apply, sens_zero, sens_one, sens_two, sens_three, sens_four,
      sens_five, hr, he]
    linear_combination (ubar2 c (xs k) 0 * u1 c (xs k) 0) * hk1
      + (ubar2 c (xs k) 0 * xs k) * hk2

end DegenerateE

end FastPoly.LowerBound
