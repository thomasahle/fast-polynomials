/-
The characteristic-two lower bound (`sections/lower_char2.md`): the model.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sum

/-!
# Characteristic-two lower bound: the strict straight-line model

This file sets up the model of `sections/lower_char2.md`.  A family of polynomials with
`2n` scalar parameters computed by `n` multiplication gates, in the *strict* straight-line
model (additions and multiplications by fixed field constants are free), is written in the
normal form

```
Gᵢ = (αᵢ x + ∑_{j<i} pᵢⱼ Gⱼ + uᵢ) (βᵢ x + ∑_{j<i} qᵢⱼ Gⱼ + vᵢ)
f  = γ x + ∑ⱼ rⱼ Gⱼ + w
```

where `α, β, p, q, γ, r` are the *fixed* circuit constants (`Circuit`) and the `2n+1`
**slots** `u₁, v₁, …, uₙ, vₙ, w` are affine-linear forms in the `2n` parameters
(`ParamMap`).

## Design decisions

* **Slot space is a plain function type.**  `Slots F n = SlotIdx n → F` with
  `SlotIdx n = Fin n ⊕ Fin n ⊕ Unit`.  This buys the `AddCommGroup`/`Module`/`Fintype`
  structure for free, so the gauge and translation maps of §3 are literally
  `z ↦ z + t • d` for explicit slot vectors `d`, and the counting steps are
  `Fintype.card_fun` computations.  The three slot indices are `U i`, `V i`, `W`.

* **Evaluation is a function `F → F`, not a `Polynomial F`.**  Every step of the argument
  (gauge invariance, translation, the fixed-point count, the final conjugacy) is a
  statement about *values* at field points, so no polynomial API is needed.

* **The gate recursion is well-founded on `i.val`**, with the `j < i` guard supplied by a
  `dite` inside the sum; `gate_eq` repackages it through `leftFactor`/`rightFactor`.

* **Indexing.**  Gates are indexed by `Fin n`, so the paper's first gate `G₁` is
  `gate c z x 0` here, its constants are `c.α 0, c.β 0`, and the paper's `s`-block is
  everything except the two slots `U 0`, `V 0`.

* **"At most `n` gates" versus "exactly `n` gates".**  The model below has exactly `n`
  gates, which is no loss: a circuit with `m < n` multiplications is padded to `n` by
  appending gates with `α = β = 0`, `p = q = 0`, output coefficient `r = 0`, and the two
  new slots pinned to the constant `0` (`cu = 0`, `du = 0`, …).  The padded circuit
  computes the same family from the same `2n` parameters.

* **`λ` and `ε` are slot vectors.**  `lamVec c` records, in the slot indexed by a factor,
  the coefficient of `G₁` in that factor (`0` in the two first-gate slots, since `G₁` does
  not feed itself); `epsVec c` records the coefficient of `x`.  With this convention the
  translation `𝒯_c` of §3 is *uniformly* `z ↦ z + c • epsVec`, including on the two
  first-gate slots where it acts by `(αc, βc)`.
-/

namespace FastPoly.LowerBoundChar2

/-! ## Slot space -/

/-- Indices of the `2n+1` scalar slots: `uᵢ`, `vᵢ` (`i : Fin n`), and `w`. -/
abbrev SlotIdx (n : ℕ) := Fin n ⊕ Fin n ⊕ Unit

/-- Slot space `F^{2n+1}`. -/
abbrev Slots (F : Type*) (n : ℕ) := SlotIdx n → F

variable {F : Type*} {n : ℕ}

/-- The slot index of `uᵢ` (the additive slot of the left factor of gate `i`). -/
def U (i : Fin n) : SlotIdx n := Sum.inl i

/-- The slot index of `vᵢ` (the additive slot of the right factor of gate `i`). -/
def V (i : Fin n) : SlotIdx n := Sum.inr (Sum.inl i)

/-- The slot index of the output constant `w`. -/
def W : SlotIdx n := Sum.inr (Sum.inr ())

@[simp] theorem U_inj {i j : Fin n} : (U i : SlotIdx n) = U j ↔ i = j := by
  simp [U]

@[simp] theorem V_inj {i j : Fin n} : (V i : SlotIdx n) = V j ↔ i = j := by
  simp [V]

@[simp] theorem U_ne_V {i j : Fin n} : (U i : SlotIdx n) ≠ V j := by simp [U, V]

@[simp] theorem U_ne_W {i : Fin n} : (U i : SlotIdx n) ≠ W := by simp [U, W]

@[simp] theorem V_ne_W {i : Fin n} : (V i : SlotIdx n) ≠ W := by simp [V, W]

/-- Assemble a slot vector from its `u`-part, its `v`-part and its `w`-entry. -/
def slotVec (a b : Fin n → F) (t : F) : Slots F n := Sum.elim a (Sum.elim b fun _ => t)

@[simp] theorem slotVec_U (a b : Fin n → F) (t : F) (i : Fin n) :
    slotVec a b t (U i) = a i := rfl
@[simp] theorem slotVec_V (a b : Fin n → F) (t : F) (i : Fin n) :
    slotVec a b t (V i) = b i := rfl
@[simp] theorem slotVec_W (a b : Fin n → F) (t : F) : slotVec a b t W = t := rfl

/-- Slot vectors are determined by their three families of entries. -/
theorem slots_ext {z z' : Slots F n} (hu : ∀ i, z (U i) = z' (U i))
    (hv : ∀ i, z (V i) = z' (V i)) (hw : z W = z' W) : z = z' := by
  funext k
  match k with
  | Sum.inl i => exact hu i
  | Sum.inr (Sum.inl i) => exact hv i
  | Sum.inr (Sum.inr ()) => exact hw

theorem card_slotIdx (n : ℕ) : Fintype.card (SlotIdx n) = 2 * n + 1 := by
  simp [SlotIdx, Fintype.card_sum]
  ring

theorem card_slots (F : Type*) [Fintype F] (n : ℕ) :
    Fintype.card (Slots F n) = Fintype.card F ^ (2 * n + 1) := by
  rw [Fintype.card_fun, card_slotIdx]

/-! ## Circuits -/

/-- The fixed constants of an `n`-multiplication straight-line program in the normal form
of `sections/lower_char2.md`.  These are *not* parameters: they are hard-wired.  Only the
entries `p i j`, `q i j` with `j < i` are ever used. -/
structure Circuit (F : Type*) (n : ℕ) where
  /-- Coefficient of `x` in the left factor of gate `i`. -/
  α : Fin n → F
  /-- Coefficient of `x` in the right factor of gate `i`. -/
  β : Fin n → F
  /-- Coefficient of `Gⱼ` in the left factor of gate `i` (used only for `j < i`). -/
  p : Fin n → Fin n → F
  /-- Coefficient of `Gⱼ` in the right factor of gate `i` (used only for `j < i`). -/
  q : Fin n → Fin n → F
  /-- Coefficient of `x` in the output. -/
  γ : F
  /-- Coefficient of `Gⱼ` in the output. -/
  r : Fin n → F

variable [Field F]

/-- The value of gate `i` at the field point `x`, with slots `z`:
`Gᵢ = (αᵢ x + ∑_{j<i} pᵢⱼ Gⱼ + uᵢ)(βᵢ x + ∑_{j<i} qᵢⱼ Gⱼ + vᵢ)`. -/
def gate (c : Circuit F n) (z : Slots F n) (x : F) : Fin n → F
  | i =>
      (c.α i * x + (∑ j : Fin n, if h : j < i then c.p i j * gate c z x j else 0) + z (U i)) *
      (c.β i * x + (∑ j : Fin n, if h : j < i then c.q i j * gate c z x j else 0) + z (V i))
  termination_by i => i.val
  decreasing_by all_goals exact h

/-- The left factor `αᵢ x + ∑_{j<i} pᵢⱼ Gⱼ + uᵢ` of gate `i`. -/
def leftFactor (c : Circuit F n) (z : Slots F n) (x : F) (i : Fin n) : F :=
  c.α i * x + (∑ j : Fin n, if j < i then c.p i j * gate c z x j else 0) + z (U i)

/-- The right factor `βᵢ x + ∑_{j<i} qᵢⱼ Gⱼ + vᵢ` of gate `i`. -/
def rightFactor (c : Circuit F n) (z : Slots F n) (x : F) (i : Fin n) : F :=
  c.β i * x + (∑ j : Fin n, if j < i then c.q i j * gate c z x j else 0) + z (V i)

theorem gate_eq (c : Circuit F n) (z : Slots F n) (x : F) (i : Fin n) :
    gate c z x i = leftFactor c z x i * rightFactor c z x i := by
  rw [gate]
  simp only [leftFactor, rightFactor, dite_eq_ite]

/-- The output `f = γ x + ∑ⱼ rⱼ Gⱼ + w`. -/
def eval (c : Circuit F n) (z : Slots F n) (x : F) : F :=
  c.γ * x + (∑ j : Fin n, c.r j * gate c z x j) + z W

section FirstGate

variable [NeZero n]

/-- The first gate has no earlier gates to sum over. -/
theorem leftFactor_zero (c : Circuit F n) (z : Slots F n) (x : F) :
    leftFactor c z x 0 = c.α 0 * x + z (U 0) := by
  have : (∑ j : Fin n, if j < (0 : Fin n) then c.p 0 j * gate c z x j else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (by exact Nat.not_lt_zero j.val)]
  rw [leftFactor, this, add_zero]

theorem rightFactor_zero (c : Circuit F n) (z : Slots F n) (x : F) :
    rightFactor c z x 0 = c.β 0 * x + z (V 0) := by
  have : (∑ j : Fin n, if j < (0 : Fin n) then c.q 0 j * gate c z x j else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (by exact Nat.not_lt_zero j.val)]
  rw [rightFactor, this, add_zero]

/-- `G₁ = (α x + u)(β x + v)`. -/
theorem gate_zero (c : Circuit F n) (z : Slots F n) (x : F) :
    gate c z x 0 = (c.α 0 * x + z (U 0)) * (c.β 0 * x + z (V 0)) := by
  rw [gate_eq, leftFactor_zero, rightFactor_zero]

end FirstGate

/-! ## Parameters

The `2n+1` slots are affine-linear forms in the `2n` parameters. -/

/-- An affine map from the `2n` parameters to the `2n+1` slots. -/
structure ParamMap (F : Type*) (n : ℕ) where
  /-- Linear part of the slot `uᵢ`. -/
  cu : Fin n → Fin (2 * n) → F
  /-- Constant term of the slot `uᵢ`. -/
  du : Fin n → F
  /-- Linear part of the slot `vᵢ`. -/
  cv : Fin n → Fin (2 * n) → F
  /-- Constant term of the slot `vᵢ`. -/
  dv : Fin n → F
  /-- Linear part of the slot `w`. -/
  cw : Fin (2 * n) → F
  /-- Constant term of the slot `w`. -/
  dw : F

/-- The slot vector produced by the parameter tuple `a`. -/
def ParamMap.slots (P : ParamMap F n) (a : Fin (2 * n) → F) : Slots F n :=
  slotVec (fun i => (∑ k, P.cu i k * a k) + P.du i)
     (fun i => (∑ k, P.cv i k * a k) + P.dv i)
     ((∑ k, P.cw k * a k) + P.dw)

/-- The polynomial family: the output as a function of the parameters and of `x`. -/
def family (c : Circuit F n) (P : ParamMap F n) (a : Fin (2 * n) → F) (x : F) : F :=
  eval c (P.slots a) x

/-- Evaluation of the family at the `2n` points `X`. -/
def evalAt (c : Circuit F n) (P : ParamMap F n) (X : Fin (2 * n) → F)
    (a : Fin (2 * n) → F) : Fin (2 * n) → F :=
  fun k => family c P a (X k)

/-- **The property the theorem rules out**: a `(2n, n)` construction, i.e. evaluation at
every `2n` distinct points is a bijection `F^{2n} → F^{2n}`. -/
def IsConstruction (c : Circuit F n) (P : ParamMap F n) : Prop :=
  ∀ X : Fin (2 * n) → F, Function.Injective X → Function.Bijective (evalAt c P X)

/-! ## Linear forms and the parameter hyperplane (§1) -/

/-- The linear form on slot space with coefficient vector `L`. -/
def form (L z : Slots F n) : F := ∑ k, L k * z k

theorem form_add (L z z' : Slots F n) : form L (z + z') = form L z + form L z' := by
  simp only [form, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

theorem form_smul (L : Slots F n) (t : F) (z : Slots F n) :
    form L (t • z) = t * form L z := by
  simp only [form, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The affine hyperplane `{z | ℓ(z) = h}` of §1. -/
def Hyperplane (L : Slots F n) (h : F) : Set (Slots F n) := {z | form L z = h}

@[simp] theorem mem_hyperplane {L : Slots F n} {h : F} {z : Slots F n} :
    z ∈ Hyperplane L h ↔ form L z = h := Iff.rfl

/-! ## The derived quantities of §3–§4 -/

section Derived

variable [NeZero n]

/-- The `G₁`-coefficient vector `λ`: in the slot of a later factor (or of the output), the
coefficient with which `G₁` enters that factor.  The two first-gate slots carry `0`,
because `G₁` does not occur in its own factors. -/
def lamVec (c : Circuit F n) : Slots F n :=
  slotVec (fun i => if i = 0 then 0 else c.p i 0) (fun i => if i = 0 then 0 else c.q i 0) (c.r 0)

/-- The `x`-coefficient vector `ε`: in the slot of a factor (or of the output), the
coefficient of `x` in that factor. -/
def epsVec (c : Circuit F n) : Slots F n := slotVec c.α c.β c.γ

/-- The `(u₁, v₁)`-part of a slot vector. -/
def headPart (d : Slots F n) : Slots F n :=
  slotVec (fun i => if i = 0 then d (U 0) else 0) (fun i => if i = 0 then d (V 0) else 0) 0

/-- The `s`-part of a slot vector: everything except the two first-gate slots. -/
def tailPart (d : Slots F n) : Slots F n :=
  slotVec (fun i => if i = 0 then 0 else d (U i)) (fun i => if i = 0 then 0 else d (V i)) (d W)

theorem headPart_add_tailPart (d : Slots F n) : headPart d + tailPart d = d := by
  refine slots_ext (fun i => ?_) (fun i => ?_) ?_
  · simp only [Pi.add_apply, headPart, tailPart, slotVec_U]
    by_cases h : i = 0 <;> simp [h]
  · simp only [Pi.add_apply, headPart, tailPart, slotVec_V]
    by_cases h : i = 0 <;> simp [h]
  · simp [headPart, tailPart]

theorem headPart_lamVec (c : Circuit F n) : headPart (lamVec c) = 0 := by
  refine slots_ext (fun i => ?_) (fun i => ?_) ?_
  · by_cases h : i = 0 <;> simp [headPart, lamVec, h]
  · by_cases h : i = 0 <;> simp [headPart, lamVec, h]
  · simp [headPart]

/-- `σ = α v + β u`, the coefficient of `x` in `G₁`. -/
def sigma (c : Circuit F n) (z : Slots F n) : F := c.α 0 * z (V 0) + c.β 0 * z (U 0)

/-- `d_t = σ t + α β t²`, the scalar by which the gauge changes `G₁`. -/
def dShift (c : Circuit F n) (z : Slots F n) (t : F) : F :=
  sigma c z * t + c.α 0 * c.β 0 * t ^ 2

/-- `A = ℓ_u α + ℓ_v β`. -/
def Acoef (c : Circuit F n) (L : Slots F n) : F := form L (headPart (epsVec c))

/-- `B = ℓ(λ)`. -/
def Bcoef (c : Circuit F n) (L : Slots F n) : F := form L (lamVec c)

/-- `E = ℓ(ε)`. -/
def Ecoef (c : Circuit F n) (L : Slots F n) : F := form L (tailPart (epsVec c))

theorem form_epsVec (c : Circuit F n) (L : Slots F n) :
    form L (epsVec c) = Acoef c L + Ecoef c L := by
  rw [Acoef, Ecoef, ← form_add, headPart_add_tailPart]

/-! ## The two slot-space maps of §3 -/

/-- The gauge transformation `𝒢_t(u, v, s) = (u + α t, v + β t, s + λ d_t)`. -/
def gauge (c : Circuit F n) (t : F) (z : Slots F n) : Slots F n :=
  z + t • headPart (epsVec c) + dShift c z t • lamVec c

/-- The translation `𝒯_b(u, v, s) = (u + α b, v + β b, s + ε b)`. -/
def transl (c : Circuit F n) (b : F) (z : Slots F n) : Slots F n := z + b • epsVec c

/-- The corrected translation `𝒯̂_b = 𝒢_{t_b} ∘ 𝒯_b` with `t_b = ((A + E)/A) b` (§5). -/
def tHat (c : Circuit F n) (L : Slots F n) (b : F) (z : Slots F n) : Slots F n :=
  gauge c (((Acoef c L + Ecoef c L) / Acoef c L) * b) (transl c b z)

end Derived

end FastPoly.LowerBoundChar2
