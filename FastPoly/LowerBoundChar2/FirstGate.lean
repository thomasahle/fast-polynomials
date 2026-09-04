/-
The characteristic-two lower bound (`sections/lower_char2.md` §2): the first gate cannot
be scalar.
-/
import FastPoly.LowerBoundChar2.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.LinearCombination

/-!
# Step 2: the first gate cannot be scalar

If `α₁ = β₁ = 0` then `G₁ = u₁ v₁` carries no `x`, so the *only* way it can influence the
output is through its value, and that value can be absorbed into every later additive
slot:

```
s̃ⱼ = sⱼ + λⱼ · u₁v₁ ,
```

where `λⱼ` is the coefficient with which `G₁` enters the factor (or the output) attached
to the slot `sⱼ`.  `gate_eq_of_absorb`/`eval_eq_of_absorb` make this precise: the whole
output function `x ↦ f_z(x)` depends on `z` only through the `2n-1` absorbed slots
`absorb c z`.

The `2n` parameters range over `Q^{2n}` tuples while the absorbed slots range over only
`Q^{2n-1}` values, so `Fintype.exists_ne_map_eq_of_card_lt` produces two distinct
parameter tuples with *identical* output functions — contradicting injectivity of
evaluation.  This is `first_gate_not_scalar`.

The counting is done directly on parameter space, so this step does not need the rank
normalisation of §1.
-/

namespace FastPoly.LowerBoundChar2

variable {F : Type*} [Field F] {n : ℕ}

section Absorb

variable [NeZero n]

/-- The absorbed slot vector `s̃ = s + λ · (u₁ v₁)` of §2.  Its two first-gate entries
vanish, so it really carries only the `2n-1` quantities `s̃`. -/
def absorb (c : Circuit F n) (z : Slots F n) : Slots F n :=
  tailPart z + (z (U 0) * z (V 0)) • lamVec c

@[simp] theorem absorb_U_zero (c : Circuit F n) (z : Slots F n) : absorb c z (U 0) = 0 := by
  simp [absorb, tailPart, lamVec]

@[simp] theorem absorb_V_zero (c : Circuit F n) (z : Slots F n) : absorb c z (V 0) = 0 := by
  simp [absorb, tailPart, lamVec]

theorem absorb_U_of_ne (c : Circuit F n) (z : Slots F n) {i : Fin n} (hi : i ≠ 0) :
    absorb c z (U i) = z (U i) + (z (U 0) * z (V 0)) * c.p i 0 := by
  simp [absorb, tailPart, lamVec, hi]

theorem absorb_V_of_ne (c : Circuit F n) (z : Slots F n) {i : Fin n} (hi : i ≠ 0) :
    absorb c z (V i) = z (V i) + (z (U 0) * z (V 0)) * c.q i 0 := by
  simp [absorb, tailPart, lamVec, hi]

theorem absorb_W (c : Circuit F n) (z : Slots F n) :
    absorb c z (W : SlotIdx n) = z W + (z (U 0) * z (V 0)) * c.r 0 := by
  simp [absorb, tailPart, lamVec]

/-- A scalar first gate has value `u₁ v₁`. -/
theorem gate_zero_of_scalar {c : Circuit F n} (hα : c.α 0 = 0) (hβ : c.β 0 = 0)
    (z : Slots F n) (x : F) : gate c z x 0 = z (U 0) * z (V 0) := by
  rw [gate_zero, hα, hβ]; ring

/-- Split off the first-gate term of a guarded gate sum: since `i ≠ 0` the guard `j < i`
holds at `j = 0`. -/
theorem sum_split_zero {i : Fin n} (hi : i ≠ 0) (co g : Fin n → F) :
    (∑ j : Fin n, if j < i then co j * g j else 0)
      = co 0 * g 0 + ∑ j ∈ Finset.univ.erase (0 : Fin n), (if j < i then co j * g j else 0) := by
  have h0 : (0 : Fin n) < i := (Fin.pos_iff_ne_zero' i).mpr hi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n)), if_pos h0]

/-- **The output depends only on the absorbed slots.**  With a scalar first gate, two slot
vectors with the same `s̃` produce the same value at every gate other than the first. -/
theorem gate_eq_of_absorb {c : Circuit F n} (hα : c.α 0 = 0) (hβ : c.β 0 = 0)
    {z z' : Slots F n} (habs : absorb c z = absorb c z') (x : F) :
    ∀ i : Fin n, i ≠ 0 → gate c z x i = gate c z' x i := by
  have main : ∀ m : ℕ, ∀ i : Fin n, i.val = m → i ≠ 0 → gate c z x i = gate c z' x i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hm hi
      -- the earlier gates other than `G₁` already agree
      have hprev : ∀ j : Fin n, j < i → j ≠ 0 → gate c z x j = gate c z' x j := by
        intro j hj hj0
        exact ih j.val (by omega) j rfl hj0
      have hsum : ∀ (co : Fin n → F),
          (∑ jj ∈ Finset.univ.erase (0 : Fin n), (if jj < i then co jj * gate c z x jj else 0))
            = ∑ jj ∈ Finset.univ.erase (0 : Fin n),
                (if jj < i then co jj * gate c z' x jj else 0) := by
        intro co
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
        by_cases hlt : j < i
        · rw [if_pos hlt, if_pos hlt, hprev j hlt hj0]
        · rw [if_neg hlt, if_neg hlt]
      -- the two first-gate values enter only through the absorbed slots
      have hU : z (U i) + (z (U 0) * z (V 0)) * c.p i 0
          = z' (U i) + (z' (U 0) * z' (V 0)) * c.p i 0 := by
        have h := congrFun habs (U i)
        rwa [absorb_U_of_ne c z hi, absorb_U_of_ne c z' hi] at h
      have hV : z (V i) + (z (U 0) * z (V 0)) * c.q i 0
          = z' (V i) + (z' (U 0) * z' (V 0)) * c.q i 0 := by
        have h := congrFun habs (V i)
        rwa [absorb_V_of_ne c z hi, absorb_V_of_ne c z' hi] at h
      rw [gate_eq, gate_eq]
      have hleft : leftFactor c z x i = leftFactor c z' x i := by
        rw [leftFactor, leftFactor, sum_split_zero hi (c.p i), sum_split_zero hi (c.p i),
          hsum (c.p i), gate_zero_of_scalar hα hβ, gate_zero_of_scalar hα hβ]
        linear_combination hU
      have hright : rightFactor c z x i = rightFactor c z' x i := by
        rw [rightFactor, rightFactor, sum_split_zero hi (c.q i), sum_split_zero hi (c.q i),
          hsum (c.q i), gate_zero_of_scalar hα hβ, gate_zero_of_scalar hα hβ]
        linear_combination hV
      rw [hleft, hright]
  intro i hi
  exact main i.val i rfl hi

/-- **Step 2, semantic half.**  With a scalar first gate the output function factors
through the `2n-1` absorbed slots. -/
theorem eval_eq_of_absorb {c : Circuit F n} (hα : c.α 0 = 0) (hβ : c.β 0 = 0)
    {z z' : Slots F n} (habs : absorb c z = absorb c z') (x : F) :
    eval c z x = eval c z' x := by
  have hsplit : ∀ y : Slots F n, (∑ j : Fin n, c.r j * gate c y x j)
      = c.r 0 * gate c y x 0
        + ∑ j ∈ Finset.univ.erase (0 : Fin n), c.r j * gate c y x j := fun y =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin n))).symm
  have hsum : (∑ j ∈ Finset.univ.erase (0 : Fin n), c.r j * gate c z x j)
      = ∑ j ∈ Finset.univ.erase (0 : Fin n), c.r j * gate c z' x j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [gate_eq_of_absorb hα hβ habs x j (Finset.mem_erase.mp hj).1]
  have hW : z W + (z (U 0) * z (V 0)) * c.r 0 = z' W + (z' (U 0) * z' (V 0)) * c.r 0 := by
    have h := congrFun habs (W : SlotIdx n)
    rwa [absorb_W, absorb_W] at h
  rw [eval, eval, hsplit z, hsplit z', hsum, gate_zero_of_scalar hα hβ,
    gate_zero_of_scalar hα hβ]
  linear_combination hW

end Absorb

/-! ## The pigeonhole -/

section Counting

variable [NeZero n]

/-- The `2n-1` slot indices other than the two first-gate slots. -/
def sIdx (n : ℕ) [NeZero n] : Finset (SlotIdx n) := ({U 0, V 0} : Finset (SlotIdx n))ᶜ

theorem mem_sIdx {k : SlotIdx n} (h1 : k ≠ U 0) (h2 : k ≠ V 0) : k ∈ sIdx n := by
  simp [sIdx, h1, h2]

theorem card_sIdx (n : ℕ) [NeZero n] : (sIdx n).card = 2 * n - 1 := by
  rw [sIdx, Finset.card_compl, Finset.card_pair (by simp [U, V]), card_slotIdx]
  omega

variable [Fintype F]

omit [Field F] in
theorem card_sIdx_fun (n : ℕ) [NeZero n] :
    Fintype.card (↥(sIdx n) → F) = Fintype.card F ^ (2 * n - 1) := by
  rw [Fintype.card_fun, Fintype.card_coe, card_sIdx]

/-- **Step 2, counting half.**  With a scalar first gate, two distinct parameter tuples
give the same output function: the `Q^{2n}` parameter tuples are compressed into the
`Q^{2n-1}` absorbed slot vectors. -/
theorem exists_collision_of_scalar_first_gate (hn : 0 < n) {c : Circuit F n}
    (hα : c.α 0 = 0) (hβ : c.β 0 = 0) (P : ParamMap F n) :
    ∃ a a' : Fin (2 * n) → F, a ≠ a' ∧ ∀ x : F, family c P a x = family c P a' x := by
  classical
  set Θ : (Fin (2 * n) → F) → (↥(sIdx n) → F) :=
    fun a k => absorb c (P.slots a) (k : SlotIdx n) with hΘdef
  have hlt : Fintype.card (↥(sIdx n) → F) < Fintype.card (Fin (2 * n) → F) := by
    rw [card_sIdx_fun, Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_lt_pow_right Fintype.one_lt_card (by omega)
  obtain ⟨a, a', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt Θ hlt
  refine ⟨a, a', hne, fun x => ?_⟩
  have habs : absorb c (P.slots a) = absorb c (P.slots a') := by
    funext k
    by_cases h1 : k = U 0
    · rw [h1, absorb_U_zero, absorb_U_zero]
    by_cases h2 : k = V 0
    · rw [h2, absorb_V_zero, absorb_V_zero]
    · exact congrFun heq ⟨k, mem_sIdx h1 h2⟩
  exact eval_eq_of_absorb hα hβ habs x

/-- **Step 2.**  If evaluation at every `2n` distinct points is a bijection, then the first
gate is not scalar: at least one of `α₁, β₁` is nonzero. -/
theorem first_gate_not_scalar (hn : 0 < n) (hQ : 2 * n ≤ Fintype.card F)
    {c : Circuit F n} {P : ParamMap F n} (hcon : IsConstruction c P) :
    ¬ (c.α 0 = 0 ∧ c.β 0 = 0) := by
  rintro ⟨hα, hβ⟩
  obtain ⟨a, a', hne, hcoll⟩ := exists_collision_of_scalar_first_gate hn hα hβ P
  obtain ⟨X⟩ : Nonempty (Fin (2 * n) ↪ F) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hQ)
  exact hne ((hcon X X.injective).1 (funext fun k => hcoll (X k)))

end Counting

end FastPoly.LowerBoundChar2
