/-
The characteristic-two lower bound (`sections/lower_char2.tex`, fibre-counting form):
no preprocessing map of any kind — affine, rational, or arbitrary — makes evaluation at
`2n` points surjective from slot space.
-/
import FastPoly.LowerBoundChar2.Main

/-!
# No `(2n, n)` construction in characteristic `2`, without the affine hypothesis

`Main.lean` proves `no_construction` for an *affine* parameter map `P : F^{2n} → F^{2n+1}`,
by restricting the evaluation map to the affine hyperplane `H = P(F^{2n})`.  The paper's
fibre-counting proof (`thm:char2-lower`) needs no parameter map at all: it shows that for
`n > 1` and `Q = |F| ≥ 2n` there are `2n` distinct points `X` at which the evaluation map

```
E_X : F^{2n+1} → F^{2n},   E_X(z) = (f_z(x₁), …, f_z(x_{2n}))
```

on the *whole* slot space is not surjective.  Since any `(2n, n)` construction, whatever
its preprocessing map, makes `E_X` surjective, none exists.

## The argument (`sections/lower_char2.tex`)

* **Scalar first gate** (`not_surjective_of_scalar_first_gate`): if `α₁ = β₁ = 0` the
  output factors through the `2n-1` absorbed slots (`FirstGate.eval_eq_of_absorb`), so
  `E_X` takes at most `Q^{2n-1} < Q^{2n}` values.
* **The gauge action is free** (`gauge_injective`): `t ↦ 𝒢_t z` is injective when
  `(α₁, β₁) ≠ (0, 0)`, so every orbit has exactly `Q` elements (`card_orbit`).  The group
  law and the commutation with translation (`gauge_gauge`, `transl_gauge`) are recorded
  for completeness but not needed by the count.
* **Fibres are orbits** (`eval_eq_iff_gauge`): `E_X` is constant on gauge orbits
  (`Gauge.eval_gauge`), so each of its `Q^{2n}` fibres is a union of `Q`-element orbits;
  if `E_X` is surjective, the pure counting lemma `card_fibre_eq_of_le` forces every fibre
  to have exactly `Q` elements, hence to be a single orbit.
* **Counting `𝒜` in two ways.**  Let `X` list `n` disjoint orbits `{r, r+1}` of the
  translation `x ↦ x + 1` (`Points.exists_paired_points`), and let
  `𝒜 = {z : 𝒯₁ z = 𝒢_t z for some t}` (`coincide`).  Because
  `E_X ∘ 𝒯₁ = π ∘ E_X` for the pair swap `π` (`evalSlots_transl`), `𝒜` is exactly the
  preimage of `Fix(π)` under `E_X`, so `|𝒜| = Q · |Fix(π)| = Q^{n+1}`
  (`card_coincide_eq_pow`, using `FixedPoints.card_fixed_pairSwap`).  Directly from the
  formulas, `𝒜 = {z : ε' + (σ(z) + α₁β₁)·λ = 0}` (`transl_eq_gauge_iff`), whose size is
  `0`, `Q^{2n}` or `Q^{2n+1}` (`card_coincide_mem`).  For `n > 1` these are incompatible
  (`pow_succ_not_mem`).

## Relation to the affine development

`eval_gauge`, `eval_transl`, `exists_paired_points`, `card_fixed_pairSwap`, the slot-wise
formulas `transl_slot_apply`/`gauge_slot_apply`, and the first-gate absorption are reused
verbatim.  The hyperplane `H`, the transversality lemma, the corrected translation `𝒯̂_b`
and its fixed-point trichotomy are *not* needed: the trichotomy here is the analogous
case analysis on all of slot space.  `no_construction'` re-derives the affine statement
`no_construction` from the general one.
-/

namespace FastPoly.LowerBoundChar2

open Finset

variable {F : Type*} [Field F] {n : ℕ}

/-- The evaluation map `E_X` of the write-up on slot space: `z ↦ (f_z(X k))_k`. -/
def evalSlots (c : Circuit F n) {I : Type*} (X : I → F) (z : Slots F n) : I → F :=
  fun k => eval c z (X k)

@[simp] theorem evalSlots_apply (c : Circuit F n) {I : Type*} (X : I → F) (z : Slots F n)
    (k : I) : evalSlots c X z k = eval c z (X k) := rfl

/-- `E_X` intertwines the translation `𝒯₁` with the pair swap `π`
(`eq:char2-conjugacy`). -/
theorem evalSlots_transl (c : Circuit F n) {X : Fin n × Fin 2 → F}
    (hXb : ∀ (i : Fin n) (j : Fin 2), X (i, j + 1) = X (i, j) + 1) (z : Slots F n) :
    evalSlots c X (transl c 1 z) = FixedPoints.pairSwap (evalSlots c X z) := by
  funext k
  obtain ⟨i, j⟩ := k
  show eval c (transl c 1 z) (X (i, j)) = eval c z (X (i, j + 1))
  rw [eval_transl, hXb i j]

/-! ## A pure counting lemma -/

/-- **Equal fibres by counting.**  If every fibre of `f : α → β` has at least `Q` elements
and `|α| = |β| · Q`, then every fibre has exactly `Q` elements. -/
theorem card_fibre_eq_of_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) {Q : ℕ} (hcard : Fintype.card α = Fintype.card β * Q)
    (hlow : ∀ b, Q ≤ (univ.filter fun a => f a = b).card) (b : β) :
    (univ.filter fun a => f a = b).card = Q := by
  by_contra hne
  have hlt : Q < (univ.filter fun a => f a = b).card := lt_of_le_of_ne (hlow b) (Ne.symm hne)
  have hsum : (univ : Finset α).card
      = ∑ b ∈ (univ : Finset β), (univ.filter fun a => f a = b).card :=
    card_eq_sum_card_fiberwise fun a _ => mem_coe.2 (mem_univ (f a))
  have hstrict : ∑ _b ∈ (univ : Finset β), Q
      < ∑ b ∈ (univ : Finset β), (univ.filter fun a => f a = b).card :=
    sum_lt_sum (fun b _ => hlow b) ⟨b, mem_univ b, hlt⟩
  rw [sum_const, card_univ, smul_eq_mul, ← hsum, card_univ, hcard] at hstrict
  exact lt_irrefl _ hstrict

/-- `Q^{n+1} ∉ {0, Q^{2n}, Q^{2n+1}}` for `n > 1` and `Q ≥ 2`: the only place `n > 1`
enters.  For `n = 1` the middle equality holds, as it must (`ax + b` is a construction). -/
theorem pow_succ_not_mem {Q : ℕ} (hQ : 2 ≤ Q) (hn : 1 < n) :
    Q ^ (n + 1) ≠ 0 ∧ Q ^ (n + 1) ≠ Q ^ (2 * n) ∧ Q ^ (n + 1) ≠ Q ^ (2 * n + 1) := by
  refine ⟨pow_ne_zero _ (by omega), fun h => ?_, fun h => ?_⟩
  · have := Nat.pow_right_injective hQ h
    omega
  · have := Nat.pow_right_injective hQ h
    omega

/-! ## The gauge action is free and commutes with translation -/

section Action

variable [NeZero n]

/-- **Freeness.**  With a nonscalar first gate, `t ↦ 𝒢_t z` is injective: the two head
slots move by `(α₁ t, β₁ t)`. -/
theorem gauge_injective {c : Circuit F n} (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) (z : Slots F n) :
    Function.Injective fun t : F => gauge c t z := by
  intro t s hts
  have hU : gauge c t z (U 0) = gauge c s z (U 0) := congrFun hts (U 0)
  have hV : gauge c t z (V 0) = gauge c s z (V 0) := congrFun hts (V 0)
  rw [gauge_U_zero, gauge_U_zero] at hU
  rw [gauge_V_zero, gauge_V_zero] at hV
  have hU' : c.α 0 * (t - s) = 0 := by linear_combination hU
  have hV' : c.β 0 * (t - s) = 0 := by linear_combination hV
  by_cases hα : c.α 0 = 0
  · have hβ : c.β 0 ≠ 0 := fun hβ => hαβ ⟨hα, hβ⟩
    exact sub_eq_zero.mp ((mul_eq_zero.mp hV').resolve_left hβ)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hU').resolve_left hα)

theorem gauge_zero (c : Circuit F n) (z : Slots F n) : gauge c 0 z = z := by
  funext k
  rw [FixedPoints.gauge_slot_apply, dShift]
  ring

/-- `σ` is gauge invariant in characteristic `2`: the change `2 α₁ β₁ t` vanishes. -/
theorem sigma_gauge [CharP F 2] (c : Circuit F n) (t : F) (z : Slots F n) :
    sigma c (gauge c t z) = sigma c z := by
  simp only [sigma, gauge_U_zero, gauge_V_zero]
  linear_combination (c.α 0 * c.β 0 * t) * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- **The group law** `𝒢_s ∘ 𝒢_t = 𝒢_{s+t}` (characteristic `2`: `d_s + d_t = d_{s+t}`). -/
theorem gauge_gauge [CharP F 2] (c : Circuit F n) (s t : F) (z : Slots F n) :
    gauge c s (gauge c t z) = gauge c (s + t) z := by
  funext k
  simp only [FixedPoints.gauge_slot_apply, dShift, sigma_gauge]
  linear_combination (-(c.α 0 * c.β 0 * s * t * lamVec c k)) *
    (CharTwo.two_eq_zero : (2 : F) = 0)

/-- **Commutation** `𝒯_b ∘ 𝒢_t = 𝒢_t ∘ 𝒯_b` (characteristic `2`: `σ` is translation
invariant). -/
theorem transl_gauge [CharP F 2] (c : Circuit F n) (b t : F) (z : Slots F n) :
    transl c b (gauge c t z) = gauge c t (transl c b z) := by
  funext k
  simp only [FixedPoints.transl_slot_apply, FixedPoints.gauge_slot_apply, dShift,
    FixedPoints.sigma_transl]
  ring

/-- `d_1 = σ(z) + α₁ β₁`. -/
theorem dShift_one (c : Circuit F n) (z : Slots F n) :
    dShift c z 1 = sigma c z + c.α 0 * c.β 0 := by
  rw [dShift]; ring

/-- **The set `𝒜`, slot by slot.**  `𝒯₁ z` lies on the gauge orbit of `z` exactly when
`ε' + (σ(z) + α₁β₁)·λ = 0`: the head slots force the gauge parameter to be `t = 1`, and
then the tail slots compare `ε'` with `d_1 λ`. -/
theorem transl_eq_gauge_iff [CharP F 2] {c : Circuit F n} (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0))
    (z : Slots F n) :
    (∃ t : F, transl c 1 z = gauge c t z) ↔
      tailPart (epsVec c) + (sigma c z + c.α 0 * c.β 0) • lamVec c = 0 := by
  constructor
  · rintro ⟨t, ht⟩
    have ht1 : t = 1 := by
      have hU : transl c 1 z (U 0) = gauge c t z (U 0) := congrFun ht (U 0)
      have hV : transl c 1 z (V 0) = gauge c t z (V 0) := congrFun ht (V 0)
      rw [transl_U, gauge_U_zero] at hU
      rw [transl_V, gauge_V_zero] at hV
      have hU' : c.α 0 * (t - 1) = 0 := by linear_combination -hU
      have hV' : c.β 0 * (t - 1) = 0 := by linear_combination -hV
      by_cases hα : c.α 0 = 0
      · have hβ : c.β 0 ≠ 0 := fun hβ => hαβ ⟨hα, hβ⟩
        exact sub_eq_zero.mp ((mul_eq_zero.mp hV').resolve_left hβ)
      · exact sub_eq_zero.mp ((mul_eq_zero.mp hU').resolve_left hα)
    subst ht1
    funext k
    have hk : transl c 1 z k = gauge c 1 z k := congrFun ht k
    rw [FixedPoints.transl_slot_apply, FixedPoints.gauge_slot_apply, dShift_one] at hk
    have hsplit : epsVec c k = headPart (epsVec c) k + tailPart (epsVec c) k :=
      (congrFun (headPart_add_tailPart (epsVec c)) k).symm
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination hk - hsplit
      + ((sigma c z + c.α 0 * c.β 0) * lamVec c k) * (CharTwo.two_eq_zero : (2 : F) = 0)
  · intro h
    refine ⟨1, ?_⟩
    funext k
    have hk : tailPart (epsVec c) k + (sigma c z + c.α 0 * c.β 0) * lamVec c k = 0 := by
      have e := congrFun h k
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using e
    rw [FixedPoints.transl_slot_apply, FixedPoints.gauge_slot_apply, dShift_one]
    have hsplit : epsVec c k = headPart (epsVec c) k + tailPart (epsVec c) k :=
      (congrFun (headPart_add_tailPart (epsVec c)) k).symm
    linear_combination hsplit + hk
      - ((sigma c z + c.α 0 * c.β 0) * lamVec c k) * (CharTwo.two_eq_zero : (2 : F) = 0)

end Action

/-! ## Fibres of a surjective `E_X` are gauge orbits -/

section Fibres

variable [Fintype F] [DecidableEq F] [NeZero n]

/-- The gauge orbit of `z`. -/
def orbit (c : Circuit F n) (z : Slots F n) : Finset (Slots F n) :=
  univ.image fun t : F => gauge c t z

theorem card_orbit {c : Circuit F n} (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) (z : Slots F n) :
    (orbit c z).card = Fintype.card F := by
  rw [orbit, card_image_of_injective _ (gauge_injective hαβ z), card_univ]

/-- `E_X` is constant on gauge orbits (`Gauge.eval_gauge`). -/
theorem orbit_subset_fibre [CharP F 2] {I : Type*} [Fintype I] (c : Circuit F n)
    (X : I → F) (z : Slots F n) :
    orbit c z ⊆ univ.filter fun y => evalSlots c X y = evalSlots c X z := by
  intro y hy
  obtain ⟨t, -, rfl⟩ := mem_image.mp hy
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  funext k
  exact eval_gauge c z (X k) t

/-- If `E_X` is surjective onto `F^{2n}`, every fibre has exactly `Q` elements. -/
theorem card_fibre_eq [CharP F 2] {I : Type*} [Fintype I] [DecidableEq I] {c : Circuit F n}
    (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) (X : I → F) (hI : Fintype.card I = 2 * n)
    (hsurj : Function.Surjective (evalSlots c X)) (g : I → F) :
    (univ.filter fun z => evalSlots c X z = g).card = Fintype.card F := by
  refine card_fibre_eq_of_le (evalSlots c X) ?_ ?_ g
  · rw [card_slots, Fintype.card_fun, hI, pow_succ]
  · intro b
    obtain ⟨z, rfl⟩ := hsurj b
    calc Fintype.card F = (orbit c z).card := (card_orbit hαβ z).symm
      _ ≤ _ := card_le_card (orbit_subset_fibre c X z)

/-- **Fibres are orbits** (`eq:char2-fibres`): for a surjective `E_X`,
`E_X(z') = E_X(z)` exactly when `z' = 𝒢_t z` for some `t`. -/
theorem eval_eq_iff_gauge [CharP F 2] {I : Type*} [Fintype I] [DecidableEq I]
    {c : Circuit F n}
    (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) (X : I → F) (hI : Fintype.card I = 2 * n)
    (hsurj : Function.Surjective (evalSlots c X)) (z z' : Slots F n) :
    evalSlots c X z' = evalSlots c X z ↔ ∃ t : F, z' = gauge c t z := by
  constructor
  · intro h
    have hsub := orbit_subset_fibre c X z
    have hcard : (univ.filter fun y => evalSlots c X y = evalSlots c X z).card
        ≤ (orbit c z).card := by
      rw [card_orbit hαβ z, card_fibre_eq hαβ X hI hsurj]
    have heq := eq_of_subset_of_card_le hsub hcard
    have hz' : z' ∈ univ.filter fun y => evalSlots c X y = evalSlots c X z :=
      mem_filter.mpr ⟨mem_univ _, h⟩
    rw [← heq, orbit, mem_image] at hz'
    obtain ⟨t, -, ht⟩ := hz'
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, rfl⟩
    funext k
    exact eval_gauge c z (X k) t

/-! ## The set `𝒜`, counted in two ways -/

/-- `𝒜 = {z : 𝒯₁ z = 𝒢_t z for some t}`. -/
def coincide (c : Circuit F n) : Finset (Slots F n) :=
  univ.filter fun z => ∃ t : F, transl c 1 z = gauge c t z

/-- **First count: `|𝒜| = Q^{n+1}`.**  `𝒜` is the preimage of `Fix(π)` under a surjective
`E_X` whose fibres are `Q`-element orbits, and `|Fix(π)| = Q^n`. -/
theorem card_coincide_eq_pow [CharP F 2] {c : Circuit F n}
    (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) {X : Fin n × Fin 2 → F}
    (hXb : ∀ (i : Fin n) (j : Fin 2), X (i, j + 1) = X (i, j) + 1)
    (hsurj : Function.Surjective (evalSlots c X)) :
    (coincide c).card = Fintype.card F ^ (n + 1) := by
  have hI : Fintype.card (Fin n × Fin 2) = 2 * n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; ring
  have hmem : ∀ z : Slots F n, (∃ t : F, transl c 1 z = gauge c t z) ↔
      FixedPoints.pairSwap (evalSlots c X z) = evalSlots c X z := by
    intro z
    rw [← evalSlots_transl c hXb z]
    exact (eval_eq_iff_gauge hαβ X hI hsurj z (transl c 1 z)).symm
  set Fixπ : Finset (Fin n × Fin 2 → F) :=
    univ.filter fun g => FixedPoints.pairSwap g = g with hFixπ
  have hFix : Fixπ.card = Fintype.card F ^ n := by
    rw [← FixedPoints.card_fixed_pairSwap F n, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard : (coincide c).card
      = ∑ g ∈ Fixπ, ((coincide c).filter fun z => evalSlots c X z = g).card :=
    card_eq_sum_card_fiberwise fun z hz => by
      rw [mem_coe] at hz ⊢
      exact mem_filter.mpr ⟨mem_univ _, (hmem z).1 (mem_filter.mp hz).2⟩
  have hfib : ∀ g ∈ Fixπ,
      ((coincide c).filter fun z => evalSlots c X z = g).card = Fintype.card F := by
    intro g hg
    rw [← card_fibre_eq hαβ X hI hsurj g]
    congr 1
    ext z
    simp only [coincide, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨-, hz⟩
      exact hz
    · intro hz
      refine ⟨(hmem z).2 ?_, hz⟩
      rw [hz]
      exact (mem_filter.mp hg).2
  rw [hcard, sum_congr rfl hfib, sum_const, smul_eq_mul, hFix, pow_succ]

/-- Every fibre of the nonconstant linear form `σ` has `Q^{2n}` points. -/
theorem card_sigma_fibre_univ {c : Circuit F n} (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) (k : F) :
    (univ.filter fun z : Slots F n => sigma c z = k).card = Fintype.card F ^ (2 * n) := by
  obtain ⟨e, he⟩ := exists_sigma_eq_one hαβ
  have hfib : ∀ k : F, (univ.filter fun z : Slots F n => sigma c z = k).card
      = (univ.filter fun z : Slots F n => sigma c z = 0).card := by
    intro k
    refine card_bij' (fun z _ => z - k • e) (fun z _ => z + k • e) ?_ ?_ ?_ ?_
    · intro z hz
      rw [mem_filter] at hz ⊢
      refine ⟨mem_univ _, ?_⟩
      have h1 : c.α 0 * z (V 0) + c.β 0 * z (U 0) = k := hz.2
      have he' : c.α 0 * e (V 0) + c.β 0 * e (U 0) = 1 := he
      show c.α 0 * (z - k • e) (V 0) + c.β 0 * (z - k • e) (U 0) = 0
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination h1 - k * he'
    · intro z hz
      rw [mem_filter] at hz ⊢
      refine ⟨mem_univ _, ?_⟩
      have h1 : c.α 0 * z (V 0) + c.β 0 * z (U 0) = 0 := hz.2
      have he' : c.α 0 * e (V 0) + c.β 0 * e (U 0) = 1 := he
      show c.α 0 * (z + k • e) (V 0) + c.β 0 * (z + k • e) (U 0) = k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination h1 + k * he'
    · intro z _
      simp
    · intro z _
      simp
  have hsum : (univ : Finset (Slots F n)).card
      = ∑ k ∈ (univ : Finset F), (univ.filter fun z : Slots F n => sigma c z = k).card :=
    card_eq_sum_card_fiberwise fun z _ => mem_coe.2 (mem_univ _)
  rw [sum_congr rfl (fun k _ => hfib k), sum_const, card_univ, smul_eq_mul, card_univ,
    card_slots, pow_succ'] at hsum
  have hQ : 0 < Fintype.card F := Fintype.card_pos
  rw [hfib k]
  exact (Nat.eq_of_mul_eq_mul_left hQ hsum).symm

/-- **Second count: `|𝒜| ∈ {0, Q^{2n}, Q^{2n+1}}`** (`eq:char2-fix`), by the case analysis
of the write-up on `ε' + (σ(z) + α₁β₁)·λ = 0`. -/
theorem card_coincide_mem [CharP F 2] {c : Circuit F n}
    (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) :
    (coincide c).card = 0 ∨ (coincide c).card = Fintype.card F ^ (2 * n) ∨
      (coincide c).card = Fintype.card F ^ (2 * n + 1) := by
  have hdesc : coincide c = univ.filter fun z =>
      tailPart (epsVec c) + (sigma c z + c.α 0 * c.β 0) • lamVec c = 0 := by
    ext z
    simp only [coincide, mem_filter, mem_univ, true_and]
    exact transl_eq_gauge_iff hαβ z
  rw [hdesc]
  by_cases hlam : lamVec c = 0
  · by_cases heps : tailPart (epsVec c) = 0
    · -- `λ = 0 = ε'`: every slot vector lies in `𝒜`
      right; right
      have hall : ∀ z : Slots F n,
          tailPart (epsVec c) + (sigma c z + c.α 0 * c.β 0) • lamVec c = 0 := by
        intro z
        funext j
        have e1 := congrFun heps j
        have e2 := congrFun hlam j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
        rw [e1, e2]
        ring
      rw [filter_true_of_mem fun z _ => hall z, card_univ, card_slots]
    · -- `λ = 0 ≠ ε'`: `𝒜` is empty
      left
      rw [card_eq_zero, filter_eq_empty_iff]
      intro z _ hz
      apply heps
      funext j
      have e1 := congrFun hz j
      have e2 := congrFun hlam j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
      rw [e2] at e1
      linear_combination e1
  · by_cases hsol : ∃ k : F, tailPart (epsVec c) + k • lamVec c = 0
    · -- `λ ≠ 0`, `ε' = -k λ`: `𝒜` is the fibre `σ = k - α₁β₁`
      obtain ⟨k, hk⟩ := hsol
      right; left
      rw [← card_sigma_fibre_univ hαβ (k - c.α 0 * c.β 0)]
      congr 1
      apply filter_congr
      intro z _
      constructor
      · intro hz
        have h1 : (sigma c z + c.α 0 * c.β 0 - k) • lamVec c = 0 := by
          funext j
          have e1 := congrFun hz j
          have e2 := congrFun hk j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
          linear_combination e1 - e2
        have h2 := FixedPoints.smul_slots_eq_zero_of_ne hlam h1
        linear_combination h2
      · intro hz
        have h1 : sigma c z + c.α 0 * c.β 0 = k := by linear_combination hz
        rw [h1]
        exact hk
    · -- the vector equation is inconsistent: `𝒜` is empty
      left
      rw [card_eq_zero, filter_eq_empty_iff]
      intro z _ hz
      exact hsol ⟨_, hz⟩

end Fibres

/-! ## The theorem -/

section Char2

variable [Fintype F] [CharP F 2]

omit [CharP F 2] in
/-- **Scalar first gate.**  If `α₁ = β₁ = 0`, the output depends on `z` only through the
`2n-1` absorbed slots, so `E_X` takes at most `Q^{2n-1} < Q^{2n}` values. -/
theorem not_surjective_of_scalar_first_gate {I : Type*} [Fintype I] [NeZero n]
    {c : Circuit F n} (hα : c.α 0 = 0) (hβ : c.β 0 = 0) (X : I → F)
    (hI : Fintype.card I = 2 * n) : ¬ Function.Surjective (evalSlots c X) := by
  intro hsurj
  classical
  set Θ : Slots F n → (↥(sIdx n) → F) := fun z k => absorb c z (k : SlotIdx n) with hΘ
  have hΘinj : Function.Injective (Θ ∘ Function.surjInv hsurj) := by
    intro g g' hgg
    have habs : absorb c (Function.surjInv hsurj g) = absorb c (Function.surjInv hsurj g') := by
      funext k
      by_cases h1 : k = U 0
      · rw [h1, absorb_U_zero, absorb_U_zero]
      by_cases h2 : k = V 0
      · rw [h2, absorb_V_zero, absorb_V_zero]
      · exact congrFun hgg ⟨k, mem_sIdx h1 h2⟩
    rw [← Function.surjInv_eq hsurj g, ← Function.surjInv_eq hsurj g']
    funext k
    exact eval_eq_of_absorb hα hβ habs (X k)
  have hle := Fintype.card_le_of_injective _ hΘinj
  rw [card_sIdx_fun, Fintype.card_fun, hI] at hle
  have hn : n ≠ 0 := NeZero.ne n
  have hlt : Fintype.card F ^ (2 * n - 1) < Fintype.card F ^ (2 * n) :=
    Nat.pow_lt_pow_right Fintype.one_lt_card (by omega)
  omega

/-- **The whole argument at one tuple of paired points.**  If `X` lists `n` disjoint
orbits `{X(i,0), X(i,1) = X(i,0) + 1}` of `x ↦ x + 1`, then evaluation at those `2n`
points is not surjective from slot space `F^{2n+1}` onto `F^{2n}`. -/
theorem not_surjective_paired (hn : 1 < n) (c : Circuit F n) {X : Fin n × Fin 2 → F}
    (hXb : ∀ (i : Fin n) (j : Fin 2), X (i, j + 1) = X (i, j) + 1) :
    ¬ Function.Surjective (evalSlots c X) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hI : Fintype.card (Fin n × Fin 2) = 2 * n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; ring
  intro hsurj
  by_cases hαβ : c.α 0 = 0 ∧ c.β 0 = 0
  · exact not_surjective_of_scalar_first_gate hαβ.1 hαβ.2 X hI hsurj
  · have h1 := card_coincide_eq_pow hαβ hXb hsurj
    have h2 := card_coincide_mem hαβ
    obtain ⟨hz, hm, hM⟩ := pow_succ_not_mem (Fintype.one_lt_card : 1 < Fintype.card F) hn
    rw [h1] at h2
    rcases h2 with h2 | h2 | h2
    · exact hz h2
    · exact hm h2
    · exact hM h2

/-- **`thm:char2-lower`, evaluation form.**  For a finite field `F` of characteristic `2`
with `|F| ≥ 2n` and `n > 1`, every `n`-gate chain `c` has `2n` distinct points `X` at which
the evaluation map `E_X : F^{2n+1} → F^{2n}` on slot space is not surjective.  No
hypothesis on the preprocessing map, the degree, or the leading coefficient is made. -/
theorem no_surjective_eval (hn : 1 < n) (hQ : 2 * n ≤ Fintype.card F) (c : Circuit F n) :
    ∃ X : Fin (2 * n) → F, Function.Injective X ∧
      ¬ Function.Surjective (fun z : Slots F n => evalSlots c X z) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨X, hXinj, hXb⟩ := exists_paired_points (F := F) (n := n) hQ (b := 1) one_ne_zero
  refine ⟨fun m => X (FixedPoints.pairIdx n m),
    hXinj.comp (FixedPoints.pairIdx n).injective,
    fun hsurj => not_surjective_paired hn c hXb ?_⟩
  intro g
  obtain ⟨z, hz⟩ := hsurj fun m => g (FixedPoints.pairIdx n m)
  refine ⟨z, funext fun k => ?_⟩
  have h := congrFun hz ((FixedPoints.pairIdx n).symm k)
  simpa [evalSlots] using h

/-- **`thm:char2-lower`, construction form.**  No preprocessing map `pre` from any parameter
type `Λ` — affine, rational, or an arbitrary function — makes evaluation at every `2n`
distinct points surjective (a fortiori, bijective). -/
theorem no_construction_general {Λ : Type*} (hn : 1 < n) (hQ : 2 * n ≤ Fintype.card F)
    (c : Circuit F n) (pre : Λ → Slots F n) :
    ¬ ∀ X : Fin (2 * n) → F, Function.Injective X →
        Function.Surjective fun a : Λ => evalSlots c X (pre a) := by
  intro hall
  obtain ⟨X, hXinj, hX⟩ := no_surjective_eval hn hQ c
  refine hX fun g => ?_
  obtain ⟨a, ha⟩ := hall X hXinj g
  exact ⟨pre a, ha⟩

/-- The affine statement `no_construction` of `Main.lean`, re-derived from the general
theorem: an affine parameter map is a particular preprocessing map. -/
theorem no_construction' (hn : 1 < n) (hQ : 2 * n ≤ Fintype.card F) (c : Circuit F n)
    (P : ParamMap F n) : ¬IsConstruction c P :=
  fun hcon => no_construction_general hn hQ c P.slots fun X hX => (hcon X hX).2

end Char2

end FastPoly.LowerBoundChar2
