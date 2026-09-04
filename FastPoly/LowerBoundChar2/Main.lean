/-
The characteristic-two lower bound (`sections/lower_char2.md`): the theorem.
-/
import FastPoly.LowerBoundChar2.FirstGate
import FastPoly.LowerBoundChar2.Rank
import FastPoly.LowerBoundChar2.Gauge
import FastPoly.LowerBoundChar2.FixedPoints
import FastPoly.LowerBoundChar2.Points

/-!
# There is no `(2n, n)` construction in characteristic `2`

**Theorem** (`sections/lower_char2.md`).  Let `F = F_Q` be a finite field of characteristic
`2` with `Q ≥ 2n` and `n > 1`.  In the strict straight-line model, no polynomial family
with `2n` scalar parameters and at most `n` multiplication gates has the property that
evaluation at every `2n` distinct points is a bijection `F^{2n} → F^{2n}`.

No assumption on the degree or on the leading coefficient of the output is needed.  The
case `n = 1` is genuinely exceptional: `f_{a,b}(x) = a x + b` uses one multiplication and
*is* bijective on evaluations at any two distinct points.

## Map from the write-up to the formalisation

| write-up | Lean |
| --- | --- |
| the model: `Gᵢ = (αᵢx + ∑p Gⱼ + uᵢ)(βᵢx + ∑q Gⱼ + vᵢ)`, `f = γx + ∑ rⱼGⱼ + w` | `Defs.gate`, `Defs.eval`, `Defs.Circuit` |
| slots `u₁,v₁,…,uₙ,vₙ,w` are affine in the `2n` parameters | `Defs.ParamMap`, `Defs.ParamMap.slots` |
| "evaluation at `2n` distinct points is a bijection" | `Defs.IsConstruction`, `Defs.evalAt` |
| §1 the `2n+1` slot forms have rank `2n`, so parameter space is a hyperplane `H` | `Rank.exists_hyperplane` (nonzero `ℓ` annihilating the linear part, by counting) |
| §1 `H` has `Q^{2n}` points, so the parameter map is *onto* `H` | `Rank.card_hyperplane_of_ne_zero`, `Rank.slots_surjective` |
| §2 the first gate cannot be scalar | `FirstGate.eval_eq_of_absorb`, `FirstGate.exists_collision_of_scalar_first_gate`, `FirstGate.first_gate_not_scalar` |
| §3 gauge `𝒢_t`, and `f_{𝒢_t z} = f_z` | `Defs.gauge`, `Gauge.gauge_factor_char2`, `Gauge.gate_zero_gauge`, `Gauge.gate_gauge_of_ne`, `Gauge.eval_gauge` |
| §3 translation `𝒯_b`, and `f_{𝒯_b z}(x) = f_z(x+b)` | `Defs.transl`, `Gauge.gate_transl`, `Gauge.eval_transl` |
| §4 injectivity forces `B = ℓ(λ) = 0` and `A = ℓ_uα + ℓ_vβ ≠ 0` | `Gauge.Bcoef_eq_zero`, `Gauge.Acoef_ne_zero`, `Gauge.transverse` |
| §5 `𝒯̂_b = 𝒢_{t_b} ∘ 𝒯_b` preserves `H` and shifts `x` by `b` | `Defs.tHat`, `Gauge.tHat_mem_hyperplane`, `Gauge.eval_tHat` |
| §5 `|Fix 𝒯̂_b| ∈ {0, Q^{2n-1}, Q^{2n}}` | `FixedPoints.card_fix_tHat` (with `FixedPoints.card_hyperplane`, `FixedPoints.card_sigma_fibre`) |
| §6 `n` disjoint translation orbits (`Q ≥ 2n`) | `Points.exists_paired_points` |
| §6 `Φ_X ∘ 𝒯̂_c = π ∘ Φ_X` and `|Fix π| = Q^n` | `FixedPoints.card_fixed_eq_of_semiconj`, `FixedPoints.card_fixed_pairSwap`, `FixedPoints.card_fixed_of_pairing` |
| §6 `Q^n ∉ {0, Q^{2n-1}, Q^{2n}}` for `n > 1` | `FixedPoints.card_pow_not_mem` |
| the contradiction | `FixedPoints.not_bijective_of_pairing'`, assembled in `not_bijective_paired` below |

## Status

Complete and unconditional: `not_bijective_paired`, `exists_not_bijective` and
`no_construction` contain **no `sorry`**, and neither does any file they depend on.
`#print axioms` on each reports only `[propext, Classical.choice, Quot.sound]`.

## Faithfulness of the statement

* `F` is an arbitrary finite field (`Field F`, `Fintype F`) of characteristic `2`
  (`CharP F 2`), with `2 * n ≤ Fintype.card F` and `1 < n`.
* The family has exactly `2n` scalar parameters: `ParamMap` is an *affine* map
  `F^{2n} → F^{2n+1}` onto the slots, and `family c P a x = eval c (P.slots a) x`.
* The circuit has exactly `n` multiplication gates.  This is no loss of generality for
  the "at most `n`" statement of the write-up: a circuit with `m < n` multiplications is
  padded to `n` gates by appending gates with `α = β = 0`, `p = q = 0`, output coefficient
  `r = 0` and the two new slots pinned to the constant `0`; the padded circuit computes
  the same family from the same `2n` parameters.  (This padding is a remark, not a Lean
  theorem: the model here quantifies over `n`-gate circuits.)
* The conclusion `¬ IsConstruction c P` is exactly "it is **not** the case that evaluation
  at every `2n` distinct points is a bijection".  `exists_not_bijective` is sharper and is
  what is actually proved: it exhibits `2n` distinct points — `n` orbits `{r, r+1}` of the
  translation `x ↦ x + 1` — at which evaluation already fails to be a bijection.
-/

namespace FastPoly.LowerBoundChar2

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

section Char2

variable [CharP F 2]

/-- **The whole argument, at one tuple of evaluation points.**

Let `X : Fin n × Fin 2 → F` list `n` disjoint orbits `{X(i,0), X(i,1) = X(i,0) + 1}` of the
translation `x ↦ x + 1`.  Then evaluation of the family at those `2n` points is *not* a
bijection `F^{2n} → F^{2n}`.

The proof runs through the write-up in order:

* §2 (`exists_collision_of_scalar_first_gate`): a scalar first gate collapses the family to
  `2n-1` slots, so injectivity of evaluation already forbids `α₁ = β₁ = 0`;
* §1 (`exists_hyperplane`, `slots_surjective`): the `Q^{2n}` slot vectors reachable from
  the parameters are *exactly* an affine hyperplane `H = {ℓ = h}` with `ℓ ≠ 0`;
* §3–§4 (`transverse`): on `H` the parameter-to-polynomial map is injective, which forces
  `B = ℓ(λ) = 0` and `A ≠ 0`, because a gauge move inside `H` would be a collision;
* §5 (`tHat_mem_hyperplane`, `eval_tHat`): `𝒯̂₁` is then a self-map of `H` realising the
  substitution `x ↦ x + 1`;
* §6 (`FixedPoints.not_bijective_of_pairing'`): evaluation at `X` intertwines `𝒯̂₁` with
  the pair swap `π`, so a bijection would give `|Fix 𝒯̂₁| = |Fix π| = Q^n`, contradicting
  `|Fix 𝒯̂₁| ∈ {0, Q^{2n-1}, Q^{2n}}` for `n > 1`. -/
theorem not_bijective_paired (hn : 1 < n) (c : Circuit F n) (P : ParamMap F n)
    {X : Fin n × Fin 2 → F}
    (hXb : ∀ (i : Fin n) (j : Fin 2), X (i, j + 1) = X (i, j) + 1)
    (hbij : Function.Bijective (evalAt c P fun m => X (FixedPoints.pairIdx n m))) : False := by
  haveI : NeZero n := ⟨by omega⟩
  -- Evaluation at `X` already separates parameter tuples with the same output function.
  have hsep : ∀ a a' : Fin (2 * n) → F,
      (∀ x : F, family c P a x = family c P a' x) → a = a' := fun a a' hcoll =>
    hbij.1 (funext fun m => hcoll (X (FixedPoints.pairIdx n m)))
  -- §2: the first gate is not scalar.
  have hfirst : ¬(c.α 0 = 0 ∧ c.β 0 = 0) := by
    rintro ⟨hα, hβ⟩
    obtain ⟨a, a', hne, hcoll⟩ := exists_collision_of_scalar_first_gate (by omega) hα hβ P
    exact hne (hsep a a' hcoll)
  -- §1: parameter space *is* an affine hyperplane `H = {ℓ = h}`.
  obtain ⟨L, h, hL, himg⟩ := exists_hyperplane P
  have hslotsinj : Function.Injective P.slots := fun a a' haa =>
    hsep a a' fun x => by simp only [family, haa]
  have hsurj : ∀ z : Slots F n, form L z = h → ∃ a, P.slots a = z := fun z hz =>
    slots_surjective hL hslotsinj himg hz
  have hHne : (Hyperplane L h).Nonempty := ⟨P.slots fun _ => 0, himg _⟩
  have hinjOn : Set.InjOn (outMap c) (Hyperplane L h) := by
    intro z hz z' hz' hEq
    obtain ⟨a, rfl⟩ := hsurj z hz
    obtain ⟨a', rfl⟩ := hsurj z' hz'
    exact congrArg P.slots (hsep a a' fun x => congrFun hEq x)
  -- §4: the hyperplane is transverse to the gauge orbits.
  obtain ⟨hB, hA⟩ := transverse hfirst hHne hinjOn
  -- §5–§6: the corrected translation `𝒯̂₁` and the pair swap.
  refine FixedPoints.not_bijective_of_pairing' hn c L h (b := 1) one_ne_zero hA hfirst
    (fun z hz => tHat_mem_hyperplane hA hB 1 hz) (Equiv.refl (Fin n × Fin 2))
    (fun g k => g (k.1, k.2 + 1)) (fun g k => rfl)
    (fun z k => eval c z.1 (X k)) ⟨?_, ?_⟩ ?_
  · -- `Φ` is injective: it is evaluation at `X`, read through `H ≃ F^{2n}`
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ hEq
    obtain ⟨a, rfl⟩ := hsurj z hz
    obtain ⟨a', rfl⟩ := hsurj z' hz'
    exact Subtype.ext (congrArg P.slots
      (hbij.1 (funext fun m => congrFun hEq (FixedPoints.pairIdx n m))))
  · -- `Φ` is surjective, because evaluation at `X` is
    intro g
    obtain ⟨a, ha⟩ := hbij.2 fun m => g (FixedPoints.pairIdx n m)
    refine ⟨⟨P.slots a, himg a⟩, funext fun k => ?_⟩
    simpa [evalAt, family] using congrFun ha ((FixedPoints.pairIdx n).symm k)
  · -- `Φ ∘ 𝒯̂₁ = π ∘ Φ`: the corrected translation shifts the variable by `1`
    intro z
    funext k
    obtain ⟨i, j⟩ := k
    show eval c (tHat c L 1 z.1) (X (i, j)) = eval c z.1 (X (i, j + 1))
    rw [eval_tHat, hXb i j]

/-- **The theorem, in its sharpest form.**  There are `2n` *distinct* points of `F` — the
`n` orbits `{r, r+1}` of the translation `x ↦ x + 1`, which exist because `Q ≥ 2n` — at
which evaluation of the family is not a bijection `F^{2n} → F^{2n}`. -/
theorem exists_not_bijective (hn : 1 < n) (hQ : 2 * n ≤ Fintype.card F) (c : Circuit F n)
    (P : ParamMap F n) :
    ∃ X : Fin (2 * n) → F, Function.Injective X ∧ ¬Function.Bijective (evalAt c P X) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨X, hXinj, hXb⟩ := exists_paired_points (F := F) (n := n) hQ (b := 1) one_ne_zero
  exact ⟨fun m => X (FixedPoints.pairIdx n m), hXinj.comp (FixedPoints.pairIdx n).injective,
    fun hbij => not_bijective_paired hn c P hXb hbij⟩

/-- **No `(2n, n)` construction in characteristic `2`.**

For a finite field `F` of characteristic `2` with `Fintype.card F ≥ 2n` and `n > 1`, no
`n`-gate strict straight-line circuit `c` together with an affine parameter map `P` on
`2n` parameters can have the property that evaluation at every `2n` distinct points is a
bijection `F^{2n} → F^{2n}`. -/
theorem no_construction (hn : 1 < n) (hQ : 2 * n ≤ Fintype.card F) (c : Circuit F n)
    (P : ParamMap F n) : ¬IsConstruction c P := by
  intro hcon
  obtain ⟨X, hXinj, hXbad⟩ := exists_not_bijective hn hQ c P
  exact hXbad (hcon X hXinj)

/-- The theorem with `IsConstruction` unfolded, in the exact shape of the write-up: for
every tuple `X` of `2n` distinct points of `F`, the evaluation map
`a ↦ (f_a(X₁), …, f_a(X_{2n}))` from `F^{2n}` to `F^{2n}` fails to be a bijection for at
least one such `X`. -/
theorem no_construction_explicit (hn : 1 < n) (hQ : 2 * n ≤ Fintype.card F) (c : Circuit F n)
    (P : ParamMap F n) :
    ¬∀ X : Fin (2 * n) → F, Function.Injective X →
        Function.Bijective fun (a : Fin (2 * n) → F) (k : Fin (2 * n)) =>
          eval c (P.slots a) (X k) :=
  no_construction hn hQ c P

end Char2

/-!
## Why `n > 1` cannot be dropped

The case `n = 1` really is a construction: `f_{a,b}(x) = a x + b`.  The circuit computes
`G₁ = (0 · x + a)(x + 0) = a x` — one multiplication — and the output is `G₁ + b`, so
evaluation at two distinct points is the invertible map `(a, b) ↦ (a x₀ + b, a x₁ + b)`.
Nothing above is claimed for `n = 1`, and the final contradiction genuinely fails there:
`Q^n = Q^{2n-1}` when `n = 1` (`FixedPoints.card_pow_not_mem` is exactly where `1 < n`
enters).

This is not only prose: `Sharpness.lean` (which imports this file) builds that circuit and
parameter map inside the present model and proves `IsConstruction` for them
(`oneGate_isConstruction`, `exists_isConstruction_one`).  So the hypothesis `1 < n` is
necessary, and `IsConstruction` is satisfiable — the impossibility proved here is not an
artefact of a model no circuit could meet.
-/

end FastPoly.LowerBoundChar2
