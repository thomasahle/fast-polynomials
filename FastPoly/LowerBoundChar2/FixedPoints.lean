/-
The characteristic-two lower bound (`sections/lower_char2.md` §5–§6): the fixed-point
count of the corrected translation, and the conjugacy contradiction.
-/
import FastPoly.LowerBoundChar2.FirstGate
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Steps 5–6: counting fixed points, and the conjugacy contradiction

This file is the **counting half** of `sections/lower_char2.md`.  It is deliberately
independent of the *algebra* of §3–§4 (that `𝒢_t` preserves the output polynomial, that
`𝒯_c` shifts the variable, and that injectivity forces `B = 0`, `A ≠ 0`): everything those
steps produce enters here as a hypothesis.  What is proved here is:

* **§5, the trichotomy** (`card_fix_tHat`):
  `|Fix(𝒯̂_b) ∩ H| ∈ {0, Q^{2n-1}, Q^{2n}}`, by the case analysis of the write-up.
  `E ≠ 0` moves the two head slots `(u₁, v₁)` by `(E/A)b·(α, β) ≠ 0`, so there is no fixed
  point at all.  `E = 0` makes `𝒯̂_b` act by `z ↦ z + b·ε' + b(σ(z) + αβb)·λ` on the tail
  slots, so `z` is fixed exactly when `ε' + (σ(z) + αβb)·λ = 0`: either that vector
  equation is unsolvable (`0` points), or `λ = 0 = ε'` and every point is fixed (`Q^{2n}`),
  or it pins `σ(z)` to a single value and the fixed locus is a fibre of the *nonconstant*
  affine function `σ` on `H` (`Q^{2n-1}`).

* **§6, the conjugacy** (`card_fixed_eq_of_semiconj`): a bijection `Φ` with
  `Φ ∘ T = π ∘ Φ` transports fixed points, so `|Fix T| = |Fix π|`; and
  (`card_fixed_pairSwap`) the pair-swap `π` of `F^{2n} = F^{n×2}` has exactly `Q^n` fixed
  points.  `card_pow_not_mem` is the arithmetic contradiction, and
  `not_bijective_of_pairing` assembles the three.

## Where `n > 1` and characteristic `2` are used

`n > 1` enters **only** in `card_pow_not_mem`: `Q^n = Q^{2n-1}` forces `n = 2n-1`, i.e.
`n = 1`.  For `n = 1` the exponents genuinely agree, which is exactly why the theorem is
false there (`f_{a,b}(x) = a x + b`).

Characteristic `2` is used twice.  In `splitMap_injective`: the determinant of the `2 × 2`
block of `(ℓ, σ)` on the two head slots is `ℓ_u α - ℓ_v β`, which in characteristic `2` is
`ℓ_u α + ℓ_v β = A`, so `A ≠ 0` says exactly that `(ℓ, σ)` is a coordinate system there —
this is the "`σ` is nonconstant on `H`" of §4–§5, and it is what makes the fibres of `σ`
on `H` have `Q^{2n-1}` points.  And in `tHat_U_zero`/`tHat_eq_of_Ecoef_zero`: the head
slots move by `(b + t_b)·(α, β)` with `t_b = ((A+E)/A) b`, and `b + t_b = (E/A) b` only
because `2 = 0`.

## Namespace

Everything lives in `FastPoly.LowerBoundChar2.FixedPoints`, so that it cannot collide with
the §1/§3/§4 lemmas being developed in parallel in `Gauge.lean`.  Several small helpers
here (`form_of_head`, `Acoef_eq`, `smul_slots_eq_zero_iff`, …) are natural candidates to be
hoisted into `Defs.lean` when the development is sealed.
-/

namespace FastPoly.LowerBoundChar2

namespace FixedPoints

/-! ## Transport of fixed points along a semiconjugacy (§6)

The write-up says "`𝒯̂_c` and `π` are conjugate permutations, hence have the same number
of fixed points".  Conjugacy is not needed: a bijection intertwining the two maps
transports the fixed-point sets directly. -/

/-- **Fixed points transport along a semiconjugacy.**  If `Φ` is a bijection with
`Φ ∘ T = π ∘ Φ`, then `T` and `π` have the same number of fixed points. -/
theorem card_fixed_eq_of_semiconj {A B : Type*} (Φ : A → B) (hΦ : Function.Bijective Φ)
    (T : A → A) (π : B → B) (hsemi : ∀ a, Φ (T a) = π (Φ a)) :
    Nat.card {a : A // T a = a} = Nat.card {b : B // π b = b} := by
  refine Nat.card_eq_of_bijective (fun a => ⟨Φ a.1, by rw [← hsemi, a.2]⟩) ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    exact Subtype.ext (hΦ.1 (by simpa using hxy))
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := hΦ.2 b
    exact ⟨⟨a, hΦ.1 (by rw [hsemi, hb])⟩, rfl⟩

/-! ## The pair-swap permutation and its `Q^n` fixed points (§6) -/

section PairSwap

variable {K : Type*}

/-- The permutation `π` of `F^{2n} = F^{n × 2}` which swaps the two entries of every pair.
(On `Fin 2` the swap is `j ↦ j + 1`.) -/
def pairSwap {n : ℕ} (g : Fin n × Fin 2 → K) : Fin n × Fin 2 → K := fun p => g (p.1, p.2 + 1)

@[simp] theorem pairSwap_apply {n : ℕ} (g : Fin n × Fin 2 → K) (i : Fin n) (j : Fin 2) :
    pairSwap g (i, j) = g (i, j + 1) := rfl

/-- **`|Fix π| = Q^n`.**  A vector is fixed by the pair swap exactly when the two entries
of each of the `n` pairs agree, so the fixed vectors are parametrised by `F^n`. -/
theorem card_fixed_pairSwap (K : Type*) [Fintype K] (n : ℕ) :
    Nat.card {g : Fin n × Fin 2 → K // pairSwap g = g} = Fintype.card K ^ n := by
  have e : {g : Fin n × Fin 2 → K // pairSwap g = g} ≃ (Fin n → K) :=
    { toFun := fun g i => g.1 (i, 0)
      invFun := fun a => ⟨fun p => a p.1, by funext p; rfl⟩
      left_inv := by
        rintro ⟨g, hg⟩
        refine Subtype.ext (funext fun p => ?_)
        obtain ⟨i, j⟩ := p
        show g (i, 0) = g (i, j)
        revert j
        rw [Fin.forall_fin_two]
        exact ⟨rfl, by simpa using congrFun hg (i, 1)⟩
      right_inv := fun a => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

/-- The same count for an arbitrary index type `I` carrying a pairing `e : I ≃ Fin n × Fin 2`:
this is the shape in which §6 uses it, with `I = Fin (2n)` the index set of the evaluation
points `r₁, r₁+c, …, rₙ, rₙ+c`. -/
theorem card_fixed_of_pairing [Fintype K] {n : ℕ} {I : Type*} (e : I ≃ Fin n × Fin 2)
    (π : (I → K) → (I → K)) (hπ : ∀ g k, π g k = g (e.symm ((e k).1, (e k).2 + 1))) :
    Nat.card {g : I → K // π g = g} = Fintype.card K ^ n := by
  rw [← card_fixed_pairSwap K n]
  refine card_fixed_eq_of_semiconj (fun g => g ∘ e.symm) ⟨?_, ?_⟩ π pairSwap ?_
  · intro f g hfg
    funext k
    simpa using congrFun hfg (e k)
  · exact fun f => ⟨f ∘ e, by funext p; simp⟩
  · intro g
    funext p
    simp only [Function.comp_apply, hπ, pairSwap, Equiv.apply_symm_apply]

/-- The pairing of the `2n` evaluation points of §6 into `n` translation orbits. -/
def pairIdx (n : ℕ) : Fin (2 * n) ≃ Fin n × Fin 2 :=
  (finCongr (Nat.mul_comm 2 n)).trans (finProdFinEquiv (m := n) (n := 2)).symm

end PairSwap

/-! ## The arithmetic obstruction -/

/-- **`Q^n ∉ {0, Q^{2n-1}, Q^{2n}}` for `n > 1`.**  This is the only place `n > 1` is used:
`Q^n = Q^{2n-1}` forces `n = 2n - 1`, i.e. `n = 1`, and for `n = 1` the middle equality is
in fact *true* — which is exactly why the theorem fails for `n = 1`. -/
theorem card_pow_not_mem {Q n : ℕ} (hQ : 2 ≤ Q) (hn : 1 < n) :
    Q ^ n ≠ 0 ∧ Q ^ n ≠ Q ^ (2 * n - 1) ∧ Q ^ n ≠ Q ^ (2 * n) := by
  refine ⟨pow_ne_zero _ (by omega), fun h => ?_, fun h => ?_⟩
  · -- `n = 2n - 1` means `n = 1`
    have := Nat.pow_right_injective hQ h
    omega
  · -- `n = 2n` means `n = 0`
    have := Nat.pow_right_injective hQ h
    omega

/-! ## Slot-space counting

The two counts `|H| = Q^{2n}` and `|{z ∈ H : σ(z) = k}| = Q^{2n-1}` both come from a
single change of coordinates: since the `2 × 2` matrix of `(ℓ, σ)` on the head slots
`(u₁, v₁)` has determinant `A ≠ 0` (in characteristic `2`), the map
`z ↦ (ℓ(z), σ(z), z|ₛ)` is a bijection of `F^{2n+1}` with `F × F × F^{2n-1}`. -/

section Slots

variable {F : Type*} [Field F] {n : ℕ} [NeZero n]

@[simp] theorem headPart_apply_U (d : Slots F n) (i : Fin n) :
    headPart d (U i) = if i = 0 then d (U 0) else 0 := rfl

@[simp] theorem headPart_apply_V (d : Slots F n) (i : Fin n) :
    headPart d (V i) = if i = 0 then d (V 0) else 0 := rfl

@[simp] theorem headPart_apply_W (d : Slots F n) : headPart d (W : SlotIdx n) = 0 := rfl

theorem headPart_eq_zero_of_ne (d : Slots F n) {k : SlotIdx n} (h1 : k ≠ U 0) (h2 : k ≠ V 0) :
    headPart d k = 0 := by
  rcases k with i | i | u
  · rw [show (Sum.inl i : SlotIdx n) = U i from rfl, headPart_apply_U, if_neg]
    rintro rfl
    exact h1 rfl
  · rw [show (Sum.inr (Sum.inl i) : SlotIdx n) = V i from rfl, headPart_apply_V, if_neg]
    rintro rfl
    exact h2 rfl
  · rfl

omit [Field F] in
@[simp] theorem epsVec_U_zero (c : Circuit F n) : epsVec c (U 0) = c.α 0 := rfl

omit [Field F] in
@[simp] theorem epsVec_V_zero (c : Circuit F n) : epsVec c (V 0) = c.β 0 := rfl

@[simp] theorem lamVec_U_zero (c : Circuit F n) : lamVec c (U 0) = 0 := by simp [lamVec]

@[simp] theorem lamVec_V_zero (c : Circuit F n) : lamVec c (V 0) = 0 := by simp [lamVec]

@[simp] theorem headPart_epsVec_U (c : Circuit F n) : headPart (epsVec c) (U 0) = c.α 0 := by
  simp

@[simp] theorem headPart_epsVec_V (c : Circuit F n) : headPart (epsVec c) (V 0) = c.β 0 := by
  simp

/-- A linear form evaluated on a vector supported on the two head slots. -/
theorem form_of_head (L d : Slots F n) (hd : ∀ k, k ≠ U 0 → k ≠ V 0 → d k = 0) :
    form L d = L (U 0) * d (U 0) + L (V 0) * d (V 0) := by
  rw [form, ← Finset.sum_subset (Finset.subset_univ ({U 0, V 0} : Finset (SlotIdx n)))]
  · rw [Finset.sum_pair U_ne_V]
  · intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [hd k hk.1 hk.2, mul_zero]

/-- `A = ℓ_u α + ℓ_v β` in coordinates. -/
theorem Acoef_eq (c : Circuit F n) (L : Slots F n) :
    Acoef c L = L (U 0) * c.α 0 + L (V 0) * c.β 0 := by
  rw [Acoef, form_of_head L _ fun k h1 h2 => headPart_eq_zero_of_ne _ h1 h2]
  simp

omit [NeZero n] in
/-- Scaling a slot vector by a nonzero scalar cannot make it vanish. -/
theorem smul_slots_eq_zero_iff {b : F} (hb : b ≠ 0) (v : Slots F n) : b • v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext k
    have hk := congrFun h k
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk
    simpa using (mul_eq_zero.mp hk).resolve_left hb
  · rintro rfl
    funext k
    simp

omit [NeZero n] in
theorem smul_slots_eq_zero_of_ne {a : F} {v : Slots F n} (hv : v ≠ 0) (h : a • v = 0) : a = 0 := by
  by_contra ha
  exact hv ((smul_slots_eq_zero_iff ha v).mp h)

section Counting

variable [Fintype F] [CharP F 2]

/-- The change of coordinates `z ↦ (ℓ(z), σ(z), z|ₛ)`: the two head slots `(u₁, v₁)` are
traded for the two values `ℓ(z)` and `σ(z)`. -/
def splitMap (c : Circuit F n) (L : Slots F n) (z : Slots F n) : F × F × (↥(sIdx n) → F) :=
  (form L z, sigma c z, fun k => z (k : SlotIdx n))

omit [Fintype F] in
/-- **The determinant computation.**  On the two head slots the pair `(ℓ, σ)` has matrix
`[[ℓ_u, ℓ_v], [β, α]]`, of determinant `ℓ_u α - ℓ_v β = A` in characteristic `2`.  So
`A ≠ 0` makes the change of coordinates injective; in particular `σ` is nonconstant on
every fibre of `ℓ`, which is the "`σ` is nonconstant on `H`" of §4–§5. -/
theorem splitMap_injective (c : Circuit F n) (L : Slots F n) (hA : Acoef c L ≠ 0) :
    Function.Injective (splitMap c L) := by
  intro z z' hzz
  simp only [splitMap, Prod.mk.injEq] at hzz
  obtain ⟨h1, h2, h3⟩ := hzz
  have hrest : ∀ k : SlotIdx n, k ≠ U 0 → k ≠ V 0 → z k = z' k := by
    intro k hk1 hk2
    exact congrFun h3 ⟨k, mem_sIdx hk1 hk2⟩
  -- the linear form vanishes on the difference …
  have hdiff : form L (fun k => z k - z' k) = 0 := by
    have hs : (∑ k, (L k * z k - L k * z' k)) = (∑ k, L k * z k) - ∑ k, L k * z' k :=
      Finset.sum_sub_distrib (fun k => L k * z k) fun k => L k * z' k
    simp only [form, mul_sub] at h1 ⊢
    rw [hs, h1, sub_self]
  -- … which is supported on the two head slots
  have hform : L (U 0) * (z (U 0) - z' (U 0)) + L (V 0) * (z (V 0) - z' (V 0)) = 0 := by
    have hh := form_of_head L (fun k => z k - z' k)
      fun k hk1 hk2 => sub_eq_zero_of_eq (hrest k hk1 hk2)
    rw [hdiff] at hh
    exact hh.symm
  have hsig : c.α 0 * (z (V 0) - z' (V 0)) + c.β 0 * (z (U 0) - z' (U 0)) = 0 := by
    rw [sigma, sigma] at h2
    linear_combination h2
  -- solve the `2 × 2` system: its determinant is `A ≠ 0`
  have hu : z (U 0) = z' (U 0) := by
    have hkey : Acoef c L * (z (U 0) - z' (U 0)) = 0 := by
      rw [Acoef_eq]
      linear_combination c.α 0 * hform + L (V 0) * hsig
        - (c.α 0 * L (V 0) * (z (V 0) - z' (V 0))) * (CharTwo.two_eq_zero : (2 : F) = 0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_left hA)
  have hv : z (V 0) = z' (V 0) := by
    have hkey : Acoef c L * (z (V 0) - z' (V 0)) = 0 := by
      rw [Acoef_eq]
      linear_combination c.β 0 * hform + L (U 0) * hsig
        - (c.β 0 * L (U 0) * (z (U 0) - z' (U 0))) * (CharTwo.two_eq_zero : (2 : F) = 0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_left hA)
  funext k
  by_cases hk1 : k = U 0
  · rw [hk1]; exact hu
  by_cases hk2 : k = V 0
  · rw [hk2]; exact hv
  · exact hrest k hk1 hk2

omit [Field F] [CharP F 2] in
theorem card_split_domain :
    Fintype.card (Slots F n) = Fintype.card (F × F × (↥(sIdx n) → F)) := by
  classical
  have hn : n ≠ 0 := NeZero.ne n
  have h1 : 2 * n + 1 = 2 * n - 1 + 1 + 1 := by omega
  rw [card_slots, Fintype.card_prod, Fintype.card_prod, card_sIdx_fun, h1, pow_succ, pow_succ]
  ring

theorem splitMap_bijective (c : Circuit F n) (L : Slots F n) (hA : Acoef c L ≠ 0) :
    Function.Bijective (splitMap c L) :=
  (Fintype.bijective_iff_injective_and_card _).mpr ⟨splitMap_injective c L hA, card_split_domain⟩

/-- **`|H| = Q^{2n}`**: the parameter hyperplane of §1 has `Q^{2n}` points. -/
theorem card_hyperplane (c : Circuit F n) (L : Slots F n) (hA : Acoef c L ≠ 0) (h : F) :
    Nat.card {z : Slots F n // form L z = h} = Fintype.card F ^ (2 * n) := by
  have hb := splitMap_bijective c L hA
  have key : Function.Bijective fun z : {z : Slots F n // form L z = h} =>
      (sigma c z.1, fun k : ↥(sIdx n) => z.1 (k : SlotIdx n)) := by
    constructor
    · rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
      simp only [Prod.mk.injEq] at hzz
      refine Subtype.ext (hb.1 ?_)
      show (form L z, sigma c z, fun k : ↥(sIdx n) => z (k : SlotIdx n))
        = (form L z', sigma c z', fun k : ↥(sIdx n) => z' (k : SlotIdx n))
      rw [hz, hz', hzz.1, hzz.2]
    · rintro ⟨s, g⟩
      obtain ⟨z, hz⟩ := hb.2 (h, s, g)
      simp only [splitMap, Prod.mk.injEq] at hz
      exact ⟨⟨z, hz.1⟩, by simp only [hz.2.1, hz.2.2]⟩
  have hn : n ≠ 0 := NeZero.ne n
  have h2 : Fintype.card F ^ (2 * n - 1 + 1) = Fintype.card F ^ (2 * n) := by
    congr 1
    omega
  rw [Nat.card_eq_of_bijective _ key, Nat.card_eq_fintype_card, Fintype.card_prod,
    card_sIdx_fun, ← h2, pow_succ]
  ring

/-- **`|{z ∈ H : σ(z) = k}| = Q^{2n-1}`**: since `A ≠ 0`, the affine function `σ` is
nonconstant on `H`, so each of its fibres in `H` has `Q^{2n-1}` points. -/
theorem card_sigma_fibre (c : Circuit F n) (L : Slots F n) (hA : Acoef c L ≠ 0) (h k : F) :
    Nat.card {z : Slots F n // form L z = h ∧ sigma c z = k} = Fintype.card F ^ (2 * n - 1) := by
  have hb := splitMap_bijective c L hA
  have key : Function.Bijective fun z : {z : Slots F n // form L z = h ∧ sigma c z = k} =>
      fun i : ↥(sIdx n) => z.1 (i : SlotIdx n) := by
    constructor
    · rintro ⟨z, hz1, hz2⟩ ⟨z', hz1', hz2'⟩ hzz
      replace hzz : (fun i : ↥(sIdx n) => z (i : SlotIdx n))
          = fun i : ↥(sIdx n) => z' (i : SlotIdx n) := hzz
      refine Subtype.ext (hb.1 ?_)
      show (form L z, sigma c z, fun i : ↥(sIdx n) => z (i : SlotIdx n))
        = (form L z', sigma c z', fun i : ↥(sIdx n) => z' (i : SlotIdx n))
      rw [hz1, hz1', hz2, hz2', hzz]
    · intro g
      obtain ⟨z, hz⟩ := hb.2 (h, k, g)
      simp only [splitMap, Prod.mk.injEq] at hz
      exact ⟨⟨z, hz.1, hz.2.1⟩, by simp only [hz.2.2]⟩
  rw [Nat.card_eq_of_bijective _ key, Nat.card_eq_fintype_card, card_sIdx_fun]

end Counting

/-! ## The corrected translation `𝒯̂_b` slot by slot (§5) -/

omit [NeZero n] in
theorem transl_slot_apply (c : Circuit F n) (b : F) (z : Slots F n) (k : SlotIdx n) :
    transl c b z k = z k + b * epsVec c k := by
  simp only [transl, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem gauge_slot_apply (c : Circuit F n) (t : F) (y : Slots F n) (k : SlotIdx n) :
    gauge c t y k = y k + t * headPart (epsVec c) k + dShift c y t * lamVec c k := by
  simp only [gauge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

section THat

variable [CharP F 2]

/-- The head slots move by `(E/A) b · (α, β)`: the translation contributes `b` and the
gauge correction `t_b = ((A+E)/A) b`, and in characteristic `2` the two combine to
`(E/A) b`. -/
theorem tHat_U_zero (c : Circuit F n) (L : Slots F n) (hA : Acoef c L ≠ 0) (b : F)
    (z : Slots F n) :
    tHat c L b z (U 0) = z (U 0) + Ecoef c L / Acoef c L * b * c.α 0 := by
  rw [tHat, gauge_slot_apply, transl_slot_apply, lamVec_U_zero, mul_zero, add_zero,
    headPart_epsVec_U, epsVec_U_zero]
  rw [show (Acoef c L + Ecoef c L) / Acoef c L = 1 + Ecoef c L / Acoef c L by
    rw [add_div, div_self hA]]
  linear_combination (b * c.α 0) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem tHat_V_zero (c : Circuit F n) (L : Slots F n) (hA : Acoef c L ≠ 0) (b : F)
    (z : Slots F n) :
    tHat c L b z (V 0) = z (V 0) + Ecoef c L / Acoef c L * b * c.β 0 := by
  rw [tHat, gauge_slot_apply, transl_slot_apply, lamVec_V_zero, mul_zero, add_zero,
    headPart_epsVec_V, epsVec_V_zero]
  rw [show (Acoef c L + Ecoef c L) / Acoef c L = 1 + Ecoef c L / Acoef c L by
    rw [add_div, div_self hA]]
  linear_combination (b * c.β 0) * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- `σ` is invariant under the translation `𝒯_b`: the two cross terms `αβb` cancel. -/
theorem sigma_transl (c : Circuit F n) (b : F) (z : Slots F n) :
    sigma c (transl c b z) = sigma c z := by
  simp only [sigma, transl_slot_apply, epsVec_U_zero, epsVec_V_zero]
  linear_combination (c.α 0 * c.β 0 * b) * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- **`𝒯̂_b` when `E = 0`.**  The head slots return to their original values (`t_b = b`),
and the tail slots move by `b·ε' + b(σ(z) + αβb)·λ`. -/
theorem tHat_eq_of_Ecoef_zero (c : Circuit F n) (L : Slots F n) (hA : Acoef c L ≠ 0)
    (hE : Ecoef c L = 0) (b : F) (z : Slots F n) :
    tHat c L b z
      = z + (b • tailPart (epsVec c) + (b * (sigma c z + c.α 0 * c.β 0 * b)) • lamVec c) := by
  have ht : (Acoef c L + Ecoef c L) / Acoef c L * b = b := by
    rw [hE, add_zero, div_self hA, one_mul]
  have hD : dShift c (transl c b z) b = b * (sigma c z + c.α 0 * c.β 0 * b) := by
    rw [dShift, sigma_transl]
    ring
  funext k
  rw [tHat, ht, gauge_slot_apply, transl_slot_apply, hD]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hk : epsVec c k = headPart (epsVec c) k + tailPart (epsVec c) k := by
    simpa using (congrFun (headPart_add_tailPart (epsVec c)) k).symm
  linear_combination b * hk
    + (b * headPart (epsVec c) k) * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- **The fixed-point equation of §5.**  For `E = 0` and `b ≠ 0`, a slot vector is fixed by
`𝒯̂_b` exactly when `ε' + (σ(z) + αβb)·λ = 0`. -/
theorem tHat_fix_iff (c : Circuit F n) (L : Slots F n) (hA : Acoef c L ≠ 0)
    (hE : Ecoef c L = 0) {b : F} (hb : b ≠ 0) (z : Slots F n) :
    tHat c L b z = z ↔
      tailPart (epsVec c) + (sigma c z + c.α 0 * c.β 0 * b) • lamVec c = 0 := by
  rw [tHat_eq_of_Ecoef_zero c L hA hE b z, add_eq_left]
  constructor
  · intro h0
    funext j
    have e := congrFun h0 j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    have e2 : b * (tailPart (epsVec c) j + (sigma c z + c.α 0 * c.β 0 * b) * lamVec c j) = 0 := by
      linear_combination e
    exact (mul_eq_zero.mp e2).resolve_left hb
  · intro h0
    funext j
    have e := congrFun h0 j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    linear_combination b * e

/-! ## The trichotomy (§5) -/

variable [Fintype F]

/-- **`|Fix(𝒯̂_b) ∩ H| ∈ {0, Q^{2n-1}, Q^{2n}}`.**

The four branches of the write-up:
* `E ≠ 0`: the head slots move by the nonzero vector `(E/A)b·(α, β)` — no fixed point;
* `E = 0` and `ε' + k·λ = 0` has no solution `k`: no fixed point;
* `E = 0`, `λ = 0 = ε'`: every point of `H` is fixed — `Q^{2n}` points;
* `E = 0`, `λ ≠ 0`, `ε' = -k·λ`: the fixed locus is the fibre `σ = k - αβb` — `Q^{2n-1}`. -/
theorem card_fix_tHat (c : Circuit F n) (L : Slots F n) (hA : Acoef c L ≠ 0)
    (hfirst : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) {b : F} (hb : b ≠ 0) (h : F) :
    Nat.card {z : Slots F n // form L z = h ∧ tHat c L b z = z} = 0 ∨
      Nat.card {z : Slots F n // form L z = h ∧ tHat c L b z = z} =
        Fintype.card F ^ (2 * n - 1) ∨
      Nat.card {z : Slots F n // form L z = h ∧ tHat c L b z = z} =
        Fintype.card F ^ (2 * n) := by
  by_cases hE : Ecoef c L = 0
  · by_cases hsol : ∃ k : F, tailPart (epsVec c) + k • lamVec c = 0
    · obtain ⟨k, hk⟩ := hsol
      by_cases hlam : lamVec c = 0
      · -- `λ = 0 = ε'`: every point of `H` is fixed
        right; right
        have heps : tailPart (epsVec c) = 0 := by
          funext j
          have e1 := congrFun hk j
          have e2 := congrFun hlam j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
          linear_combination e1 - k * e2
        have hall : ∀ z : Slots F n, tHat c L b z = z := fun z => by
          rw [tHat_fix_iff c L hA hE hb z]
          funext j
          have e1 := congrFun heps j
          have e2 := congrFun hlam j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
          linear_combination e1 + (sigma c z + c.α 0 * c.β 0 * b) * e2
        rw [Nat.card_congr (Equiv.subtypeEquivRight fun z => and_iff_left (hall z))]
        exact card_hyperplane c L hA h
      · -- `λ ≠ 0`: the fixed locus is a fibre of `σ`
        right; left
        have hiff : ∀ z : Slots F n, (form L z = h ∧ tHat c L b z = z) ↔
            (form L z = h ∧ sigma c z = k - c.α 0 * c.β 0 * b) := by
          intro z
          refine and_congr_right fun _ => ?_
          rw [tHat_fix_iff c L hA hE hb z]
          constructor
          · intro hz
            have h1 : (sigma c z + c.α 0 * c.β 0 * b - k) • lamVec c = 0 := by
              funext j
              have e1 := congrFun hz j
              have e2 := congrFun hk j
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
              linear_combination e1 - e2
            have h2 := smul_slots_eq_zero_of_ne hlam h1
            linear_combination h2
          · intro hz
            have h1 : sigma c z + c.α 0 * c.β 0 * b = k := by linear_combination hz
            rw [h1]
            exact hk
        rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
        exact card_sigma_fibre c L hA h _
    · -- the vector equation is inconsistent: no fixed point
      left
      haveI : IsEmpty {z : Slots F n // form L z = h ∧ tHat c L b z = z} := by
        constructor
        rintro ⟨z, -, hz⟩
        exact hsol ⟨sigma c z + c.α 0 * c.β 0 * b, (tHat_fix_iff c L hA hE hb z).mp hz⟩
      exact Nat.card_of_isEmpty
  · -- `E ≠ 0`: the head slots move, so there is no fixed point
    left
    have hne : Ecoef c L / Acoef c L * b ≠ 0 := mul_ne_zero (div_ne_zero hE hA) hb
    haveI : IsEmpty {z : Slots F n // form L z = h ∧ tHat c L b z = z} := by
      constructor
      rintro ⟨z, -, hz⟩
      refine hfirst ⟨?_, ?_⟩
      · have h1 := congrFun hz (U 0)
        rw [tHat_U_zero c L hA b z, add_eq_left] at h1
        exact (mul_eq_zero.mp h1).resolve_left hne
      · have h1 := congrFun hz (V 0)
        rw [tHat_V_zero c L hA b z, add_eq_left] at h1
        exact (mul_eq_zero.mp h1).resolve_left hne
    exact Nat.card_of_isEmpty

/-! ## The contradiction (§6) -/

/-- **The counting half of the theorem.**  Suppose the corrected translation `𝒯̂_b`
restricts to a map `T` of the parameter hyperplane `H`, and that evaluation at the `2n`
translation-paired points is a *bijection* `Φ : H → F^{2n}` intertwining `T` with the pair
swap `π`.  Then `|Fix T| = |Fix π| = Q^n`, contradicting `|Fix T| ∈ {0, Q^{2n-1}, Q^{2n}}`
when `n > 1`.

The hypotheses `hA` (`A ≠ 0`, from §4), `hfirst` (§2), the existence of `T` (i.e.
`𝒯̂_b(H) = H`, from §5, which needs `B = 0`) and of `Φ` with `hsemi` (from §3 and §6) are
supplied by the other steps. -/
theorem not_bijective_of_pairing {I : Type*} (hn : 1 < n) (c : Circuit F n) (L : Slots F n) (h : F) {b : F} (hb : b ≠ 0)
    (hA : Acoef c L ≠ 0) (hfirst : ¬(c.α 0 = 0 ∧ c.β 0 = 0))
    (T : {z : Slots F n // form L z = h} → {z : Slots F n // form L z = h})
    (hT : ∀ z, (T z).1 = tHat c L b z.1)
    (e : I ≃ Fin n × Fin 2) (π : (I → F) → (I → F))
    (hπ : ∀ g k, π g k = g (e.symm ((e k).1, (e k).2 + 1)))
    (Φ : {z : Slots F n // form L z = h} → (I → F)) (hΦ : Function.Bijective Φ)
    (hsemi : ∀ z, Φ (T z) = π (Φ z)) : False := by
  have hQ : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have h1 : Nat.card {z : {z : Slots F n // form L z = h} // T z = z} = Fintype.card F ^ n := by
    rw [card_fixed_eq_of_semiconj Φ hΦ T π hsemi, card_fixed_of_pairing e π hπ]
  have h2 : Nat.card {z : {z : Slots F n // form L z = h} // T z = z}
      = Nat.card {z : Slots F n // form L z = h ∧ tHat c L b z = z} := by
    refine Nat.card_congr ((Equiv.subtypeEquivRight ?_).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _))
    intro z
    rw [Subtype.ext_iff, hT]
  have h3 := card_fix_tHat c L hA hfirst hb h
  rw [← h2, h1] at h3
  obtain ⟨hz, hm, hM⟩ := card_pow_not_mem hQ hn
  rcases h3 with h3 | h3 | h3
  · exact hz h3
  · exact hm h3
  · exact hM h3

/-- The same statement with the stability of `H` under `𝒯̂_b` (§5) as a hypothesis rather
than a packaged map `T`. -/
theorem not_bijective_of_pairing' {I : Type*} (hn : 1 < n) (c : Circuit F n) (L : Slots F n) (h : F) {b : F} (hb : b ≠ 0)
    (hA : Acoef c L ≠ 0) (hfirst : ¬(c.α 0 = 0 ∧ c.β 0 = 0))
    (hstab : ∀ z : Slots F n, form L z = h → form L (tHat c L b z) = h)
    (e : I ≃ Fin n × Fin 2) (π : (I → F) → (I → F))
    (hπ : ∀ g k, π g k = g (e.symm ((e k).1, (e k).2 + 1)))
    (Φ : {z : Slots F n // form L z = h} → (I → F)) (hΦ : Function.Bijective Φ)
    (hsemi : ∀ z : {z : Slots F n // form L z = h},
      Φ ⟨tHat c L b z.1, hstab z.1 z.2⟩ = π (Φ z)) : False :=
  not_bijective_of_pairing hn c L h hb hA hfirst
    (fun z => ⟨tHat c L b z.1, hstab z.1 z.2⟩) (fun _ => rfl) e π hπ Φ hΦ hsemi

end THat

end Slots

end FixedPoints

end FastPoly.LowerBoundChar2
