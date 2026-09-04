/-
The characteristic-two lower bound (`sections/lower_char2.md` §3–§5): the gauge
transformation, the translation, transversality, and the corrected translation.
-/
import FastPoly.LowerBoundChar2.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The two slot-space maps, transversality, and the corrected translation

The heart of the whole argument is the following identity in characteristic `2`:

```
(α x + u + α t)(β x + v + β t) = (α x + u)(β x + v) + d_t,   d_t = σ t + α β t²,
```

with `σ = α v + β u`.  Expanding the left side produces the two cross terms `α β t x`
*twice*; in characteristic `2` they cancel, so the coefficient of `x` is unchanged and the
whole change is the **scalar** `d_t`.  Hence the gauge move
`(u, v, s) ↦ (u + α t, v + β t, s + λ d_t)` shifts `G₁` by a constant that the later slot
corrections `λ d_t` absorb exactly, leaving the output polynomial untouched.

## Contents

* §3, gauge (`gauge_factor_char2`, `gate_zero_gauge`, `gate_gauge_of_ne`, `eval_gauge`):
  the characteristic-`2` identity, its effect on the first gate, and — by induction
  through the circuit — the fact that `𝒢_t` changes **no** later gate and hence preserves
  the output function exactly.  Characteristic `2` is used twice: once for the cancellation
  of the cross terms in `G₁`, and once again in every later factor, where the `G₁`-shift
  `p_{i1} d_t` and the slot correction `d_t p_{i1}` add up to `2 p_{i1} d_t = 0`.

* §3, translation (`gate_transl`, `eval_transl`): `𝒯_b` shifts the variable,
  `f_{𝒯_b z}(x) = f_z(x + b)`, gate by gate.  This half is characteristic-free.

* §4, transversality (`Bcoef_eq_zero`, `Acoef_ne_zero`, `transverse`): if the output map is
  injective on the hyperplane `H`, then `B = ℓ(λ) = 0` and `A = ℓ_u α + ℓ_v β ≠ 0`.  The
  three sub-cases of the write-up are driven by `exists_mem_hyperplane_sigma_eq`: when
  `B ≠ 0` the function `σ` is *surjective* on `H`, because
  `D = e − (ℓ(e)/B) λ` is a direction inside `H` with `σ(D) = 1`.  Each sub-case then
  exhibits an explicit `t ≠ 0` with `𝒢_t(H) ∋ 𝒢_t z`, i.e. a collision.

* §5, the corrected translation (`tHat_mem_hyperplane`, `eval_tHat`): with `B = 0` and
  `A ≠ 0`, the map `𝒯̂_b = 𝒢_{t_b} ∘ 𝒯_b` with `t_b = ((A + E)/A) b` preserves `H` (the two
  changes `(A+E)b` and `A t_b` of the defining form are equal, hence cancel in
  characteristic `2`) and still shifts the variable by `b`.

The fixed-point count of `𝒯̂_b` and the final conjugacy argument are §5–§6, and are not in
this file.
-/

namespace FastPoly.LowerBoundChar2

variable {F : Type*} [Field F] {n : ℕ}

/-! ## The characteristic-two cancellation

`gauge_factor_char2` is the *only* place where characteristic `2` is used in the first
gate; the `linear_combination` certificate below multiplies `(2 : F) = 0` by exactly the
coefficient `α β t x` of the surviving cross term. -/

/-- **The gauge identity.**  In characteristic `2`, shifting the two additive slots of a
product of two affine forms by `α t` and `β t` changes the product by the *constant*
`d_t = (α v + β u) t + α β t²`: the `x`-coefficient is unchanged because the two cross
terms `α β t x` cancel.

Outside characteristic `2` the left-hand side carries an extra `2 α β t x`, which is why
the argument is special to characteristic `2`. -/
theorem gauge_factor_char2 [CharP F 2] (a b u v t x : F) :
    (a * x + (u + a * t)) * (b * x + (v + b * t))
      = (a * x + u) * (b * x + v) + ((a * v + b * u) * t + a * b * t ^ 2) := by
  linear_combination (a * b * t * x) * (CharTwo.two_eq_zero : (2 : F) = 0)

/-- The discrepancy in the absence of the characteristic-`2` hypothesis: over any field the
two sides of `gauge_factor_char2` differ exactly by the cross term `2 α β t x`. -/
theorem gauge_factor_general (a b u v t x : F) :
    (a * x + (u + a * t)) * (b * x + (v + b * t))
      = (a * x + u) * (b * x + v) + ((a * v + b * u) * t + a * b * t ^ 2)
        + 2 * (a * b * t * x) := by
  ring

/-! ## §3: translation of the variable

`𝒯_b(u, v, s) = (u + α b, v + β b, s + ε b)` adds to *every* slot `b` times the
`x`-coefficient of the factor that slot belongs to, so each factor of each gate turns into
the same factor evaluated at `x + b`.  Nothing here uses characteristic `2`. -/

omit [Field F] in
@[simp] theorem epsVec_U (c : Circuit F n) (i : Fin n) : epsVec c (U i) = c.α i := rfl

omit [Field F] in
@[simp] theorem epsVec_V (c : Circuit F n) (i : Fin n) : epsVec c (V i) = c.β i := rfl

omit [Field F] in
@[simp] theorem epsVec_W (c : Circuit F n) : epsVec c (W : SlotIdx n) = c.γ := rfl

theorem transl_U (c : Circuit F n) (b : F) (z : Slots F n) (i : Fin n) :
    transl c b z (U i) = z (U i) + b * c.α i := by simp [transl]

theorem transl_V (c : Circuit F n) (b : F) (z : Slots F n) (i : Fin n) :
    transl c b z (V i) = z (V i) + b * c.β i := by simp [transl]

theorem transl_W (c : Circuit F n) (b : F) (z : Slots F n) :
    transl c b z (W : SlotIdx n) = z W + b * c.γ := by simp [transl]

/-- **Step 3, translation.**  `Gᵢ^{𝒯_b z}(x) = Gᵢ^{z}(x + b)` for every gate, by induction
on `i`: in the left factor the slot gains `b αᵢ`, which is exactly what turns `αᵢ x` into
`αᵢ (x + b)`, while the earlier gates are handled by the induction hypothesis. -/
theorem gate_transl (c : Circuit F n) (z : Slots F n) (x b : F) :
    ∀ i : Fin n, gate c (transl c b z) x i = gate c z (x + b) i := by
  have main : ∀ m : ℕ, ∀ i : Fin n, i.val = m →
      gate c (transl c b z) x i = gate c z (x + b) i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hm
      have hsum : ∀ co : Fin n → F,
          (∑ j : Fin n, if j < i then co j * gate c (transl c b z) x j else 0)
            = ∑ j : Fin n, if j < i then co j * gate c z (x + b) j else 0 := by
        intro co
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hlt : j < i
        · rw [if_pos hlt, if_pos hlt, ih j.val (by omega) j rfl]
        · rw [if_neg hlt, if_neg hlt]
      rw [gate_eq, gate_eq]
      simp only [leftFactor, rightFactor]
      rw [hsum (c.p i), hsum (c.q i), transl_U, transl_V]
      ring
  exact fun i => main i.val i rfl

/-- **Step 3, translation, for the output.**  `f_{𝒯_b z}(x) = f_z(x + b)`. -/
theorem eval_transl (c : Circuit F n) (z : Slots F n) (x b : F) :
    eval c (transl c b z) x = eval c z (x + b) := by
  have hsum : (∑ j : Fin n, c.r j * gate c (transl c b z) x j)
      = ∑ j : Fin n, c.r j * gate c z (x + b) j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gate_transl]
  rw [eval, eval, hsum, transl_W]
  ring

section Derived

variable [NeZero n]

/-! ## The slot-wise description of the gauge map -/

@[simp] theorem headPart_epsVec_U_zero (c : Circuit F n) :
    headPart (epsVec c) (U 0) = c.α 0 := by simp [headPart, epsVec]

@[simp] theorem headPart_epsVec_V_zero (c : Circuit F n) :
    headPart (epsVec c) (V 0) = c.β 0 := by simp [headPart, epsVec]

@[simp] theorem lamVec_U_zero (c : Circuit F n) : lamVec c (U 0) = 0 := by simp [lamVec]

@[simp] theorem lamVec_V_zero (c : Circuit F n) : lamVec c (V 0) = 0 := by simp [lamVec]

theorem gauge_U_zero (c : Circuit F n) (t : F) (z : Slots F n) :
    gauge c t z (U 0) = z (U 0) + c.α 0 * t := by
  simp [gauge, mul_comm]

theorem gauge_V_zero (c : Circuit F n) (t : F) (z : Slots F n) :
    gauge c t z (V 0) = z (V 0) + c.β 0 * t := by
  simp [gauge, mul_comm]

/-- On a later `u`-slot the gauge adds `p_{i1} d_t`. -/
theorem gauge_U_of_ne (c : Circuit F n) (t : F) (z : Slots F n) {i : Fin n} (hi : i ≠ 0) :
    gauge c t z (U i) = z (U i) + dShift c z t * c.p i 0 := by
  simp [gauge, headPart, epsVec, lamVec, hi]

/-- On a later `v`-slot the gauge adds `q_{i1} d_t`. -/
theorem gauge_V_of_ne (c : Circuit F n) (t : F) (z : Slots F n) {i : Fin n} (hi : i ≠ 0) :
    gauge c t z (V i) = z (V i) + dShift c z t * c.q i 0 := by
  simp [gauge, headPart, epsVec, lamVec, hi]

/-- On the output slot the gauge adds `r₁ d_t`. -/
theorem gauge_W (c : Circuit F n) (t : F) (z : Slots F n) :
    gauge c t z (W : SlotIdx n) = z W + dShift c z t * c.r 0 := by
  simp [gauge, headPart, epsVec, lamVec]

/-! ## §3: the gauge preserves the output polynomial -/

/-- **Step 3 for the first gate.**  In characteristic `2`,
`G₁^{𝒢_t z} = G₁^{z} + d_t`, with no `x`-dependence in the correction. -/
theorem gate_zero_gauge [CharP F 2] (c : Circuit F n) (z : Slots F n) (x t : F) :
    gate c (gauge c t z) x 0 = gate c z x 0 + dShift c z t := by
  rw [gate_zero, gate_zero, gauge_U_zero, gauge_V_zero, dShift, sigma]
  exact gauge_factor_char2 (c.α 0) (c.β 0) (z (U 0)) (z (V 0)) t x

/-- Split the first-gate term off a guarded gate sum: since `i ≠ 0` the guard `j < i` holds
at `j = 0`.  (Same splitting as `FirstGate.sum_split_zero`, restated so that §3 does not
depend on §2.) -/
theorem sum_split_first {i : Fin n} (hi : i ≠ 0) (co g : Fin n → F) :
    (∑ j : Fin n, if j < i then co j * g j else 0)
      = co 0 * g 0 + ∑ j ∈ Finset.univ.erase (0 : Fin n), (if j < i then co j * g j else 0) := by
  have h0 : (0 : Fin n) < i := (Fin.pos_iff_ne_zero' i).mpr hi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n)), if_pos h0]

/-- **Step 3, later gates.**  Every gate after the first is *unchanged* by the gauge: the
first gate contributes `p_{i1} d_t` more to the left factor, and the slot correction adds
another `d_t p_{i1}`, so in characteristic `2` the two cancel. -/
theorem gate_gauge_of_ne [CharP F 2] (c : Circuit F n) (z : Slots F n) (x t : F) :
    ∀ i : Fin n, i ≠ 0 → gate c (gauge c t z) x i = gate c z x i := by
  have main : ∀ m : ℕ, ∀ i : Fin n, i.val = m → i ≠ 0 →
      gate c (gauge c t z) x i = gate c z x i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hm hi
      have hprev : ∀ j : Fin n, j < i → j ≠ 0 →
          gate c (gauge c t z) x j = gate c z x j := by
        intro j hj hj0
        exact ih j.val (by omega) j rfl hj0
      have hsum : ∀ co : Fin n → F,
          (∑ j ∈ Finset.univ.erase (0 : Fin n),
              (if j < i then co j * gate c (gauge c t z) x j else 0))
            = ∑ j ∈ Finset.univ.erase (0 : Fin n),
                (if j < i then co j * gate c z x j else 0) := by
        intro co
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
        by_cases hlt : j < i
        · rw [if_pos hlt, if_pos hlt, hprev j hlt hj0]
        · rw [if_neg hlt, if_neg hlt]
      have hleft : leftFactor c (gauge c t z) x i = leftFactor c z x i := by
        rw [leftFactor, leftFactor, sum_split_first hi (c.p i), sum_split_first hi (c.p i),
          hsum (c.p i), gate_zero_gauge, gauge_U_of_ne c t z hi]
        linear_combination (c.p i 0 * dShift c z t) * (CharTwo.two_eq_zero : (2 : F) = 0)
      have hright : rightFactor c (gauge c t z) x i = rightFactor c z x i := by
        rw [rightFactor, rightFactor, sum_split_first hi (c.q i), sum_split_first hi (c.q i),
          hsum (c.q i), gate_zero_gauge, gauge_V_of_ne c t z hi]
        linear_combination (c.q i 0 * dShift c z t) * (CharTwo.two_eq_zero : (2 : F) = 0)
      rw [gate_eq, gate_eq, hleft, hright]
  exact fun i hi => main i.val i rfl hi

/-- **Step 3.**  `f_{𝒢_t z}(x) = f_z(x)`: the gauge preserves the output polynomial
exactly.  The output slot `w` gains `r₁ d_t`, the first gate gains `d_t`, and the two
contributions `r₁ d_t` cancel in characteristic `2`. -/
theorem eval_gauge [CharP F 2] (c : Circuit F n) (z : Slots F n) (x t : F) :
    eval c (gauge c t z) x = eval c z x := by
  have hsplit : ∀ y : Slots F n, (∑ j : Fin n, c.r j * gate c y x j)
      = c.r 0 * gate c y x 0
        + ∑ j ∈ Finset.univ.erase (0 : Fin n), c.r j * gate c y x j := fun y =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n))).symm
  have hsum : (∑ j ∈ Finset.univ.erase (0 : Fin n), c.r j * gate c (gauge c t z) x j)
      = ∑ j ∈ Finset.univ.erase (0 : Fin n), c.r j * gate c z x j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [gate_gauge_of_ne c z x t j (Finset.mem_erase.mp hj).1]
  rw [eval, eval, hsplit (gauge c t z), hsplit z, hsum, gate_zero_gauge, gauge_W]
  linear_combination (c.r 0 * dShift c z t) * (CharTwo.two_eq_zero : (2 : F) = 0)

/-! ## §4: the hyperplane must be transverse to the gauge orbits -/

/-- The gauge changes the defining form of `H` by `t A + d_t B`. -/
theorem form_gauge (c : Circuit F n) (L : Slots F n) (t : F) (z : Slots F n) :
    form L (gauge c t z) = form L z + (t * Acoef c L + dShift c z t * Bcoef c L) := by
  simp only [gauge, form_add, form_smul, Acoef, Bcoef]
  ring

/-- The write-up's factored form of that change: `t (A + B σ + B α β t)`. -/
theorem gauge_cond_eq (c : Circuit F n) (L : Slots F n) (t : F) (z : Slots F n) :
    t * Acoef c L + dShift c z t * Bcoef c L
      = t * (Acoef c L + Bcoef c L * sigma c z + Bcoef c L * (c.α 0 * c.β 0) * t) := by
  simp only [dShift]
  ring

/-- `𝒢_t` keeps `z` inside `H` as soon as the *second* factor `A + B σ + B α β t` vanishes
(the first factor is `t`, which is nonzero in every application below). -/
theorem gauge_mem_hyperplane {c : Circuit F n} {L : Slots F n} {h t : F} {z : Slots F n}
    (hz : z ∈ Hyperplane L h)
    (hcond : Acoef c L + Bcoef c L * sigma c z + Bcoef c L * (c.α 0 * c.β 0) * t = 0) :
    gauge c t z ∈ Hyperplane L h := by
  simp only [mem_hyperplane] at hz ⊢
  rw [form_gauge, gauge_cond_eq, hcond, mul_zero, add_zero, hz]

/-- A nonzero gauge really moves the point: it shifts `(u₁, v₁)` by `(α t, β t)`, and by §2
not both of `α, β` vanish. -/
theorem gauge_ne_self {c : Circuit F n} {t : F} (ht : t ≠ 0)
    (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) (z : Slots F n) : gauge c t z ≠ z := by
  intro hEq
  refine hαβ ⟨?_, ?_⟩
  · have h := congrFun hEq (U 0)
    rw [gauge_U_zero] at h
    have h0 : c.α 0 * t = 0 := by linear_combination h
    exact (mul_eq_zero.mp h0).resolve_right ht
  · have h := congrFun hEq (V 0)
    rw [gauge_V_zero] at h
    have h0 : c.β 0 * t = 0 := by linear_combination h
    exact (mul_eq_zero.mp h0).resolve_right ht

theorem sigma_add (c : Circuit F n) (z z' : Slots F n) :
    sigma c (z + z') = sigma c z + sigma c z' := by
  simp only [sigma, Pi.add_apply]; ring

theorem sigma_smul (c : Circuit F n) (μ : F) (z : Slots F n) :
    sigma c (μ • z) = μ * sigma c z := by
  simp only [sigma, Pi.smul_apply, smul_eq_mul]; ring

/-- `σ` ignores the `λ`-direction: `λ` has no first-gate slots. -/
@[simp] theorem sigma_lamVec (c : Circuit F n) : sigma c (lamVec c) = 0 := by
  simp [sigma]

/-- Since not both of `α, β` vanish, some slot vector has `σ = 1`. -/
theorem exists_sigma_eq_one {c : Circuit F n} (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) :
    ∃ e : Slots F n, sigma c e = 1 := by
  by_cases hα : c.α 0 = 0
  · have hβ : c.β 0 ≠ 0 := fun hβ => hαβ ⟨hα, hβ⟩
    refine ⟨slotVec (fun i => if i = 0 then (c.β 0)⁻¹ else 0) (fun _ => 0) 0, ?_⟩
    simp [sigma, hα, mul_inv_cancel₀ hβ]
  · refine ⟨slotVec (fun _ => 0) (fun i => if i = 0 then (c.α 0)⁻¹ else 0) 0, ?_⟩
    simp [sigma, mul_inv_cancel₀ hα]

/-- **The write-up's "σ is nonconstant on `H`", in constructive form.**  If `B ≠ 0` there is
a direction `D` inside `H` (i.e. `ℓ(D) = 0`) along which `σ` moves at unit speed: correct
any `e` with `σ(e) = 1` by the multiple `(ℓ(e)/B) λ` of the `λ`-direction, which `σ` does
not see. -/
theorem exists_dir_of_Bcoef_ne {c : Circuit F n} {L : Slots F n} (hB : Bcoef c L ≠ 0)
    (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) :
    ∃ D : Slots F n, form L D = 0 ∧ sigma c D = 1 := by
  obtain ⟨e, he⟩ := exists_sigma_eq_one hαβ
  refine ⟨e + (-(form L e / Bcoef c L)) • lamVec c, ?_, ?_⟩
  · rw [form_add, form_smul, ← Bcoef]
    field_simp
    ring
  · rw [sigma_add, sigma_smul, sigma_lamVec, mul_zero, add_zero, he]

/-- Consequently, when `B ≠ 0` the affine function `σ` is *surjective* on `H`. -/
theorem exists_mem_hyperplane_sigma_eq {c : Circuit F n} {L : Slots F n} {h : F}
    (hB : Bcoef c L ≠ 0) (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0))
    (hne : (Hyperplane L h).Nonempty) (τ : F) :
    ∃ z ∈ Hyperplane L h, sigma c z = τ := by
  obtain ⟨D, hD0, hD1⟩ := exists_dir_of_Bcoef_ne hB hαβ
  obtain ⟨z0, hz0⟩ := hne
  simp only [mem_hyperplane] at hz0
  refine ⟨z0 + (τ - sigma c z0) • D, ?_, ?_⟩
  · simp only [mem_hyperplane, form_add, form_smul, hD0, mul_zero, add_zero]
    exact hz0
  · rw [sigma_add, sigma_smul, hD1, mul_one]
    ring

/-- The map sending a slot vector to the output *function* `x ↦ f_z(x)`.  §1's rank
normalisation says exactly that this map is injective on the parameter hyperplane. -/
def outMap (c : Circuit F n) (z : Slots F n) : F → F := fun x => eval c z x

/-- **Step 4, first half: `B = ℓ(λ) = 0`.**  Otherwise `σ` is surjective on `H`
(`exists_mem_hyperplane_sigma_eq`) and one can solve `A + B σ + B α β t = 0` with `t ≠ 0`:

* if `α β = 0`, pick `σ = A / B`, so that `A + B σ = 2A = 0` and any `t` — say `t = 1` —
  works;
* if `α β ≠ 0`, pick `σ = (A + 1) / B`, so that `A + B σ = 1`, and take
  `t = (B α β)⁻¹`, so that `B α β t = 1` and the sum is `1 + 1 = 0`.

Either way `𝒢_t z` and `z` are two *distinct* points of `H` with the same output
polynomial, contradicting injectivity. -/
theorem Bcoef_eq_zero [CharP F 2] {c : Circuit F n} {L : Slots F n} {h : F}
    (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) (hne : (Hyperplane L h).Nonempty)
    (hinj : Set.InjOn (outMap c) (Hyperplane L h)) : Bcoef c L = 0 := by
  by_contra hB
  obtain ⟨z, hz, t, ht, hcond⟩ :
      ∃ z ∈ Hyperplane L h, ∃ t : F, t ≠ 0 ∧
        Acoef c L + Bcoef c L * sigma c z + Bcoef c L * (c.α 0 * c.β 0) * t = 0 := by
    by_cases hab : c.α 0 * c.β 0 = 0
    · obtain ⟨z, hz, hσ⟩ :=
        exists_mem_hyperplane_sigma_eq hB hαβ hne (Acoef c L / Bcoef c L)
      refine ⟨z, hz, 1, one_ne_zero, ?_⟩
      have h1 : Bcoef c L * (Acoef c L / Bcoef c L) = Acoef c L := by
        field_simp
      rw [hσ, h1, hab, mul_zero, zero_mul, add_zero]
      exact CharTwo.add_self_eq_zero _
    · obtain ⟨z, hz, hσ⟩ :=
        exists_mem_hyperplane_sigma_eq hB hαβ hne ((Acoef c L + 1) / Bcoef c L)
      refine ⟨z, hz, (Bcoef c L * (c.α 0 * c.β 0))⁻¹, inv_ne_zero (mul_ne_zero hB hab), ?_⟩
      have h1 : Bcoef c L * ((Acoef c L + 1) / Bcoef c L) = Acoef c L + 1 := by
        field_simp
      have h2 : Bcoef c L * (c.α 0 * c.β 0) * (Bcoef c L * (c.α 0 * c.β 0))⁻¹ = 1 :=
        mul_inv_cancel₀ (mul_ne_zero hB hab)
      rw [hσ, h1, h2]
      linear_combination (Acoef c L + 1) * (CharTwo.two_eq_zero : (2 : F) = 0)
  refine gauge_ne_self ht hαβ z (hinj (gauge_mem_hyperplane hz hcond) hz ?_)
  funext x
  exact eval_gauge c z x t

/-- **Step 4, second half: `A = ℓ_u α + ℓ_v β ≠ 0`.**  If `A = B = 0` then *every* gauge
preserves `H`, and `𝒢_1 z ≠ z` is again a collision. -/
theorem Acoef_ne_zero [CharP F 2] {c : Circuit F n} {L : Slots F n} {h : F}
    (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) (hne : (Hyperplane L h).Nonempty)
    (hinj : Set.InjOn (outMap c) (Hyperplane L h)) (hB : Bcoef c L = 0) :
    Acoef c L ≠ 0 := by
  intro hA
  obtain ⟨z, hz⟩ := hne
  have hcond : Acoef c L + Bcoef c L * sigma c z + Bcoef c L * (c.α 0 * c.β 0) * 1 = 0 := by
    rw [hA, hB]; ring
  refine gauge_ne_self one_ne_zero hαβ z (hinj (gauge_mem_hyperplane hz hcond) hz ?_)
  funext x
  exact eval_gauge c z x 1

/-- **Step 4.**  Injectivity of the parameter-to-polynomial map on `H` forces `B = 0` and
`A ≠ 0`: the hyperplane is transverse to the gauge orbits. -/
theorem transverse [CharP F 2] {c : Circuit F n} {L : Slots F n} {h : F}
    (hαβ : ¬(c.α 0 = 0 ∧ c.β 0 = 0)) (hne : (Hyperplane L h).Nonempty)
    (hinj : Set.InjOn (outMap c) (Hyperplane L h)) :
    Bcoef c L = 0 ∧ Acoef c L ≠ 0 :=
  ⟨Bcoef_eq_zero hαβ hne hinj,
   Acoef_ne_zero hαβ hne hinj (Bcoef_eq_zero hαβ hne hinj)⟩

/-! ## §5: projecting the translation back onto the parameter hyperplane -/

/-- The translation changes the defining form of `H` by `b (A + E)`. -/
theorem form_transl (c : Circuit F n) (L : Slots F n) (b : F) (z : Slots F n) :
    form L (transl c b z) = form L z + b * (Acoef c L + Ecoef c L) := by
  rw [transl, form_add, form_smul, form_epsVec]

/-- **Step 5, first half.**  With `B = 0` and `A ≠ 0`, the corrected translation
`𝒯̂_b = 𝒢_{t_b} ∘ 𝒯_b`, `t_b = ((A + E)/A) b`, maps `H` to `H`: the translation changes the
defining form by `b (A + E)` and the gauge changes it by `t_b A = b (A + E)`, and the two
add up to `0` in characteristic `2`. -/
theorem tHat_mem_hyperplane [CharP F 2] {c : Circuit F n} {L : Slots F n} {h : F}
    (hA : Acoef c L ≠ 0) (hB : Bcoef c L = 0) (b : F) {z : Slots F n}
    (hz : z ∈ Hyperplane L h) : tHat c L b z ∈ Hyperplane L h := by
  simp only [mem_hyperplane] at hz ⊢
  rw [tHat, form_gauge, form_transl, hB, mul_zero, add_zero, hz]
  have key : (Acoef c L + Ecoef c L) / Acoef c L * b * Acoef c L
      = b * (Acoef c L + Ecoef c L) := by
    field_simp
  rw [key, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **Step 5, second half.**  `𝒯̂_b` still shifts the variable by `b`: the gauge factor
contributes nothing to the output polynomial. -/
theorem eval_tHat [CharP F 2] (c : Circuit F n) (L : Slots F n) (b : F) (z : Slots F n)
    (x : F) : eval c (tHat c L b z) x = eval c z (x + b) := by
  rw [tHat, eval_gauge, eval_transl]

/-- `𝒯̂_b` in the shape used by §6: as a self-map of `H` it intertwines evaluation at `x`
with evaluation at `x + b`. -/
theorem outMap_tHat [CharP F 2] (c : Circuit F n) (L : Slots F n) (b : F) (z : Slots F n)
    (x : F) : outMap c (tHat c L b z) x = outMap c z (x + b) :=
  eval_tHat c L b z x

end Derived

end FastPoly.LowerBoundChar2
