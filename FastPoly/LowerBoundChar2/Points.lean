/-
The characteristic-two lower bound (`sections/lower_char2.md` §6): choosing `2n` evaluation
points paired by the translation `x ↦ x + b`.
-/
import FastPoly.LowerBoundChar2.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.LinearCombination

/-!
# Step 6, first half: `n` disjoint translation orbits

Because `Q ≥ 2n` and translation by `b ≠ 0` is a fixed-point-free involution of `F` (in
characteristic `2`, `x + b + b = x` and `x + b ≠ x`), the field splits into `Q/2 ≥ n`
orbits of size `2`, and we may choose `n` of them.

The write-up says "choose `r₁, …, rₙ` such that the `2n` elements `r₁, r₁+b, …, rₙ, rₙ+b`
are distinct".  The formal content is a **transversal**: a set `R ⊆ F` meeting every orbit
exactly once, i.e. with `x ∈ R → x + b ∉ R`.  It is produced with no quotient machinery at
all: transport an arbitrary linear order to `F` along `Fintype.equivFin` and keep, in each
orbit, the element of smaller index,

```
R = {x | idx x < idx (x + b)} .
```

Translation by `b` then maps `R` into `Rᶜ` and `Rᶜ` into `R`, so `|R| = |Rᶜ|` and
`2 |R| = Q ≥ 2n`; picking `n` elements of `R` gives `exists_paired_points`.

The output is packaged as a map `X : Fin n × Fin 2 → F` satisfying
`X (i, j+1) = X (i, j) + b`, which is exactly the form the pair-swap `π` of
`FixedPoints.card_fixed_of_pairing` consumes (`j + 1` is computed in `Fin 2`, so the
identity for `j = 1` is `X (i, 0) = X (i, 1) + b`, another use of characteristic `2`).
-/

namespace FastPoly.LowerBoundChar2

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] {n : ℕ}

/-- **Step 6, choice of points.**  For `b ≠ 0` and `Q ≥ 2n` there are `n` pairwise disjoint
`b`-orbits `{rᵢ, rᵢ + b}`, presented as an injective `X : Fin n × Fin 2 → F` with
`X (i, j+1) = X (i, j) + b`. -/
theorem exists_paired_points (hQ : 2 * n ≤ Fintype.card F) {b : F} (hb : b ≠ 0) :
    ∃ X : Fin n × Fin 2 → F, Function.Injective X ∧
      ∀ (i : Fin n) (j : Fin 2), X (i, j + 1) = X (i, j) + b := by
  classical
  -- an arbitrary injective index, used only to pick one element out of each orbit
  obtain ⟨idx, hidxinj⟩ : ∃ idx : F → ℕ, Function.Injective idx :=
    ⟨fun x => ((Fintype.equivFin F) x : ℕ),
      fun x y hxy => (Fintype.equivFin F).injective (Fin.val_injective hxy)⟩
  -- translation by `b` is a fixed-point-free involution (characteristic `2`)
  have hstep : ∀ x : F, x + b + b = x := by
    intro x
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hmove : ∀ x : F, x + b ≠ x := fun x hx => hb (by linear_combination hx)
  -- the transversal
  set R : Finset F := Finset.univ.filter (fun x => idx x < idx (x + b)) with hR
  have hmemR : ∀ x : F, x ∈ R ↔ idx x < idx (x + b) := by
    intro x; simp [hR]
  have hfree : ∀ x ∈ R, x + b ∉ R := by
    intro x hx hxb
    rw [hmemR] at hx
    rw [hmemR, hstep] at hxb
    omega
  have hcompl : ∀ x : F, x ∉ R → x + b ∈ R := by
    intro x hx
    rw [hmemR] at hx
    rw [hmemR, hstep]
    have hne : idx (x + b) ≠ idx x := fun hh => hmove x (hidxinj hh)
    omega
  -- translation swaps `R` and its complement, so `2 |R| = Q`
  have hle1 : R.card ≤ Rᶜ.card := by
    refine Finset.card_le_card_of_injOn (fun x => x + b) (fun x hx => ?_) (fun x _ y _ hxy => ?_)
    · exact Finset.mem_compl.mpr (hfree x hx)
    · exact add_right_cancel hxy
  have hle2 : Rᶜ.card ≤ R.card := by
    refine Finset.card_le_card_of_injOn (fun x => x + b) (fun x hx => ?_) (fun x _ y _ hxy => ?_)
    · exact hcompl x (Finset.mem_compl.mp hx)
    · exact add_right_cancel hxy
  have hsum : R.card + Rᶜ.card = Fintype.card F := Finset.card_add_card_compl R
  have hn : n ≤ R.card := by omega
  -- choose `n` of the orbits
  obtain ⟨emb⟩ : Nonempty (Fin n ↪ ↥R) := by
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa using hn
  refine ⟨fun p => ((emb p.1 : ↥R) : F) + (p.2.val : ℕ) • b, ?_, ?_⟩
  · -- injectivity: the `Fin n` part is pinned by the transversal, the `Fin 2` part by `b`
    have hmem : ∀ i : Fin n, ((emb i : ↥R) : F) ∈ R := fun i => (emb i).2
    have hcross : ∀ i i' : Fin n, ((emb i : ↥R) : F) ≠ ((emb i' : ↥R) : F) + b := by
      intro i i' hh
      exact hfree _ (hmem i') (by rw [← hh]; exact hmem i)
    rintro ⟨i, j⟩ ⟨i', j'⟩ hEq
    have hEq' : ((emb i : ↥R) : F) + (j.val : ℕ) • b
        = ((emb i' : ↥R) : F) + (j'.val : ℕ) • b := hEq
    have hj : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
    have hj' : j'.val = 0 ∨ j'.val = 1 := by have := j'.isLt; omega
    have hii : ∀ i i' : Fin n, ((emb i : ↥R) : F) = ((emb i' : ↥R) : F) → i = i' := by
      intro i i' hh
      exact emb.injective (Subtype.ext hh)
    have hjj : j.val = j'.val → j = j' := fun hh => Fin.val_injective hh
    rcases hj with h0 | h1 <;> rcases hj' with h0' | h1'
    · rw [h0, h0'] at hEq'
      simp only [zero_smul, add_zero] at hEq'
      have hi : i = i' := hii i i' hEq'
      have hjv : j = j' := hjj (by rw [h0, h0'])
      rw [hi, hjv]
    · rw [h0, h1'] at hEq'
      simp only [zero_smul, one_smul, add_zero] at hEq'
      exact absurd hEq' (hcross i i')
    · rw [h1, h0'] at hEq'
      simp only [zero_smul, one_smul, add_zero] at hEq'
      exact absurd hEq'.symm (hcross i' i)
    · rw [h1, h1'] at hEq'
      simp only [one_smul] at hEq'
      have hi : i = i' := hii i i' (add_right_cancel hEq')
      have hjv : j = j' := hjj (by rw [h1, h1'])
      rw [hi, hjv]
  · -- the pairing identity, in `Fin 2`
    intro i j
    have hj : j.val = 0 ∨ j.val = 1 := by have := j.isLt; omega
    rcases hj with h0 | h1
    · have hj0 : j = 0 := Fin.val_injective h0
      subst hj0
      simp
    · have hj1 : j = 1 := Fin.val_injective h1
      subst hj1
      show ((emb i : ↥R) : F) + ((0 : Fin 2).val : ℕ) • b
        = ((emb i : ↥R) : F) + ((1 : Fin 2).val : ℕ) • b + b
      simp only [Fin.val_zero, Fin.val_one, zero_smul, one_smul, add_zero]
      rw [hstep]

end FastPoly.LowerBoundChar2
