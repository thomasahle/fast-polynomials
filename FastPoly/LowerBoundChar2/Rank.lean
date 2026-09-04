/-
The characteristic-two lower bound (`sections/lower_char2.md` §1): parameter space is an
affine hyperplane in slot space.
-/
import FastPoly.LowerBoundChar2.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Step 1: the parameter hyperplane

The `2n+1` slots `u₁, v₁, …, uₙ, vₙ, w` are affine-linear in the `2n` parameters, so the
image of the parameter map `P.slots : F^{2n} → F^{2n+1}` is an affine subspace of dimension
at most `2n` inside a space of dimension `2n+1`.  Hence it is contained in an affine
hyperplane

```
H = {z | ℓ(z) = h},    ℓ ≠ 0.
```

**The existence of `ℓ` is proved by pure counting, not by rank/duality.**  The transpose
`L ↦ (ℓ_L(colₖ))ₖ` maps `F^{2n+1}` to `F^{2n}`; as `Q^{2n} < Q^{2n+1}` it cannot be
injective, and a difference of two colliding forms is a nonzero `ℓ` annihilating every
column of the linear part (`exists_ann`).  Then `form L (P.slots a)` is the constant
`ℓ(const)` (`exists_hyperplane`).

The second half of §1 is the *equality* `image = H`.  If `P.slots` is injective — which is
forced by injectivity of evaluation — the image has `Q^{2n}` points, and a hyperplane with
`ℓ ≠ 0` has exactly `Q^{2n}` points (`card_hyperplane_of_ne_zero`, proved by solving the
defining equation for one coordinate whose coefficient is nonzero).  Two finite sets of
the same size, one inside the other, are equal, which is `slots_surjective`: **every**
point of `H` is realised by a parameter tuple.  That is what lets §4 quantify over all of
`H`.

Nothing in this file uses characteristic `2`.
-/

namespace FastPoly.LowerBoundChar2

variable {F : Type*} [Field F] {n : ℕ}

/-! ## `form` is linear in the coefficient vector as well -/

@[simp] theorem form_zero_right (L : Slots F n) : form L (0 : Slots F n) = 0 := by
  simp [form]

theorem form_add_left (L L' z : Slots F n) : form (L + L') z = form L z + form L' z := by
  simp only [form, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

theorem form_sub_left (L L' z : Slots F n) : form (L - L') z = form L z - form L' z := by
  simp only [form, Pi.sub_apply, sub_mul]
  exact Finset.sum_sub_distrib _ _

theorem form_sum {ι : Type*} (L : Slots F n) (s : Finset ι) (v : ι → Slots F n) :
    form L (∑ k ∈ s, v k) = ∑ k ∈ s, form L (v k) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro k s hk ih
  rw [Finset.sum_insert hk, form_add, ih, Finset.sum_insert hk]

/-- Split off one coordinate of a linear form. -/
theorem form_split (L z : Slots F n) (k₀ : SlotIdx n) :
    form L z = L k₀ * z k₀ + ∑ k ∈ Finset.univ.erase k₀, L k * z k := by
  rw [form]
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ k₀)).symm

/-! ## The affine parameter map in column form -/

namespace ParamMap

/-- The `k`-th column of the linear part of the affine parameter map: the slot vector of
the coefficients of the parameter `aₖ`. -/
def col (P : ParamMap F n) (k : Fin (2 * n)) : Slots F n :=
  slotVec (fun i => P.cu i k) (fun i => P.cv i k) (P.cw k)

/-- The constant term of the affine parameter map. -/
def const (P : ParamMap F n) : Slots F n := slotVec P.du P.dv P.dw

omit [Field F] in
@[simp] theorem col_U (P : ParamMap F n) (k : Fin (2 * n)) (i : Fin n) :
    P.col k (U i) = P.cu i k := rfl

omit [Field F] in
@[simp] theorem col_V (P : ParamMap F n) (k : Fin (2 * n)) (i : Fin n) :
    P.col k (V i) = P.cv i k := rfl

omit [Field F] in
@[simp] theorem col_W (P : ParamMap F n) (k : Fin (2 * n)) :
    P.col k (W : SlotIdx n) = P.cw k := rfl

/-- The parameter map is `a ↦ ∑ₖ aₖ · colₖ + const`. -/
theorem slots_eq_sum (P : ParamMap F n) (a : Fin (2 * n) → F) :
    P.slots a = (∑ k, a k • P.col k) + P.const := by
  refine slots_ext (fun i => ?_) (fun i => ?_) ?_
  · simp only [ParamMap.slots, slotVec_U, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, col_U, const, slotVec_U]
    rw [show (∑ k, P.cu i k * a k) = ∑ k, a k * P.cu i k from
      Finset.sum_congr rfl fun k _ => mul_comm _ _]
  · simp only [ParamMap.slots, slotVec_V, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, col_V, const, slotVec_V]
    rw [show (∑ k, P.cv i k * a k) = ∑ k, a k * P.cv i k from
      Finset.sum_congr rfl fun k _ => mul_comm _ _]
  · simp only [ParamMap.slots, slotVec_W, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, col_W, const, slotVec_W]
    rw [show (∑ k, P.cw k * a k) = ∑ k, a k * P.cw k from
      Finset.sum_congr rfl fun k _ => mul_comm _ _]

end ParamMap

/-- A linear form evaluated along the parameter map. -/
theorem form_slots (L : Slots F n) (P : ParamMap F n) (a : Fin (2 * n) → F) :
    form L (P.slots a) = (∑ k, a k * form L (P.col k)) + form L P.const := by
  rw [P.slots_eq_sum a, form_add, form_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => form_smul L (a k) (P.col k)

/-! ## §1: the image of the parameter map lies in a hyperplane -/

/-- **Counting instead of rank.**  There is a *nonzero* linear form annihilating all `2n`
columns of the linear part of the parameter map: the transpose map
`L ↦ (ℓ_L(colₖ))ₖ : F^{2n+1} → F^{2n}` cannot be injective, because `Q^{2n} < Q^{2n+1}`. -/
theorem exists_ann [Fintype F] (P : ParamMap F n) :
    ∃ L : Slots F n, L ≠ 0 ∧ ∀ k, form L (P.col k) = 0 := by
  have hlt : Fintype.card (Fin (2 * n) → F) < Fintype.card (Slots F n) := by
    rw [Fintype.card_fun, Fintype.card_fin, card_slots]
    exact Nat.pow_lt_pow_right Fintype.one_lt_card (by omega)
  obtain ⟨L, L', hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun L : Slots F n => fun k => form L (P.col k)) hlt
  refine ⟨L - L', sub_ne_zero.mpr hne, fun k => ?_⟩
  have hk : form L (P.col k) = form L' (P.col k) := congrFun heq k
  rw [form_sub_left, hk, sub_self]

/-- **Step 1.**  All parameter tuples land on one affine hyperplane `{z | ℓ(z) = h}` with
`ℓ ≠ 0`. -/
theorem exists_hyperplane [Fintype F] (P : ParamMap F n) :
    ∃ (L : Slots F n) (h : F), L ≠ 0 ∧ ∀ a, form L (P.slots a) = h := by
  obtain ⟨L, hL, hann⟩ := exists_ann P
  refine ⟨L, form L P.const, hL, fun a => ?_⟩
  rw [form_slots]
  simp [hann]

/-! ## §1: a hyperplane has `Q^{2n}` points -/

/-- **`|H| = Q^{2n}`** for any nonzero `ℓ`.  Solve the defining equation for a coordinate
`k₀` with `ℓ_{k₀} ≠ 0`: the remaining `2n` coordinates are free. -/
theorem card_hyperplane_of_ne_zero [Fintype F] {L : Slots F n} (hL : L ≠ 0) (h : F) :
    Nat.card {z : Slots F n // form L z = h} = Fintype.card F ^ (2 * n) := by
  classical
  obtain ⟨k₀, hk₀⟩ : ∃ k, L k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hL (funext fun k => hcon k)
  have key : Function.Bijective
      (fun z : {z : Slots F n // form L z = h} =>
        fun k : {k : SlotIdx n // k ≠ k₀} => z.1 k.1) := by
    constructor
    · rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
      have hrest : ∀ k : SlotIdx n, k ≠ k₀ → z k = z' k := fun k hk => congrFun hzz ⟨k, hk⟩
      have hsum : (∑ k ∈ Finset.univ.erase k₀, L k * z k)
          = ∑ k ∈ Finset.univ.erase k₀, L k * z' k :=
        Finset.sum_congr rfl fun k hk => by rw [hrest k (Finset.mem_erase.mp hk).1]
      have e1 := form_split L z k₀
      have e2 := form_split L z' k₀
      rw [hz, hsum] at e1
      rw [hz'] at e2
      have h0 : L k₀ * z k₀ = L k₀ * z' k₀ := by linear_combination e2 - e1
      refine Subtype.ext (funext fun k => ?_)
      by_cases hk : k = k₀
      · subst hk; exact mul_left_cancel₀ hk₀ h0
      · exact hrest k hk
    · intro g
      obtain ⟨y, hy0, hyg⟩ :
          ∃ y : Slots F n, y k₀ = 0 ∧ ∀ (k : SlotIdx n) (hk : k ≠ k₀), y k = g ⟨k, hk⟩ :=
        ⟨fun k => if hk : k = k₀ then 0 else g ⟨k, hk⟩, dif_pos rfl, fun k hk => dif_neg hk⟩
      obtain ⟨z, hz0, hzy⟩ :
          ∃ z : Slots F n, z k₀ = (h - form L y) / L k₀ ∧ ∀ k : SlotIdx n, k ≠ k₀ → z k = y k :=
        ⟨fun k => if hk : k = k₀ then (h - form L y) / L k₀ else y k, dif_pos rfl,
          fun k hk => dif_neg hk⟩
      have hS : form L y = ∑ k ∈ Finset.univ.erase k₀, L k * y k := by
        rw [form_split L y k₀, hy0, mul_zero, zero_add]
      have hzsum : (∑ k ∈ Finset.univ.erase k₀, L k * z k)
          = ∑ k ∈ Finset.univ.erase k₀, L k * y k :=
        Finset.sum_congr rfl fun k hk => by rw [hzy k (Finset.mem_erase.mp hk).1]
      have hcancel : L k₀ * ((h - form L y) / L k₀) = h - form L y := by
        field_simp
      have hzform : form L z = h := by
        rw [form_split L z k₀, hz0, hzsum, ← hS, hcancel]
        ring
      exact ⟨⟨z, hzform⟩, funext fun k => (hzy k.1 k.2).trans (hyg k.1 k.2)⟩
  have hcard : Fintype.card {k : SlotIdx n // k ≠ k₀} = 2 * n := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, card_slotIdx]
    omega
  rw [Nat.card_eq_of_bijective _ key, Nat.card_eq_fintype_card, Fintype.card_fun, hcard]

/-! ## §1: the parameter map is *onto* the hyperplane -/

/-- **Step 1, second half.**  An injective parameter map whose image lies in a hyperplane
`{ℓ = h}` with `ℓ ≠ 0` is onto that hyperplane: both sides have `Q^{2n}` points. -/
theorem slots_surjective [Fintype F] {P : ParamMap F n} {L : Slots F n} {h : F} (hL : L ≠ 0)
    (hinj : Function.Injective P.slots) (himg : ∀ a, form L (P.slots a) = h) {z : Slots F n}
    (hz : form L z = h) : ∃ a, P.slots a = z := by
  classical
  have hbij : Function.Bijective
      (fun a : Fin (2 * n) → F => (⟨P.slots a, himg a⟩ : {z : Slots F n // form L z = h})) := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a a' haa => hinj (congrArg Subtype.val haa), ?_⟩
    rw [Fintype.card_fun, Fintype.card_fin, ← card_hyperplane_of_ne_zero hL h]
    exact Nat.card_eq_fintype_card
  obtain ⟨a, ha⟩ := hbij.2 ⟨z, hz⟩
  exact ⟨a, congrArg Subtype.val ha⟩

end FastPoly.LowerBoundChar2
