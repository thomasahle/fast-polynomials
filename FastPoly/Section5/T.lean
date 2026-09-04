import FastPoly.Section4.KnownPowers
import FastPoly.Section4.Peeled

/-!
# The `T_{k,2^l}` recursion

Definitional layer for `alg:constr-Tk2l` and `alg:constr-Tk2l-base`: the recursive pair
`(T¹_{k,2^l}, T²_{k,2^l})` over a tower of known powers `Hp` (with `Hp i` playing
`H_{2^i}`) and the shifted top power `Ht` (playing `H̃_{2^l}`).  The recursion is
fuel-indexed with a fuel-irrelevance lemma, as in `Section4/KnownPowers.lean`.

Each branch component is a named definition (`tS1`, `evenH`, `oddH`, `obH8`, …) so that
the structural lemmas below can speak about them directly and elaboration stays cheap.

Parameter layout (the paper's): a call of size `d = (k-1)·2^l` uses slots `0,…,d-1`.
For `k ≥ 2` the tail block sits at `b = (k-2)·2^l`:
* even `k`, `l ≥ 2`: `(σ, Q⁻-block, δ, Q⁺-block) = (α_b, …, α_{b+2^l-1})`, inner block
  `α_0,…,α_{b-1}` passed unshifted;
* odd `k`, `l ≥ 3`: `(ζ, Q⁻-block, ε, Q₀-block, δ, Q⁺-block) = (α_b, …, α_{b+2^l-1})`,
  low block `Q_{2^l-1}[α_1,…,α_{2^l-1}] ⊕ α_0`, inner block shifted by `2^l`;
* the shared bases (`l = 1` even, `l = 2` odd) specialize these with scalar/linear blocks.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {A : Type*} [CommRing A]

/-- `S⁽¹⁾₁` of a main branch (`l ≥ 2`, either parity): the monic degree-`2^{l-1}`
auxiliary `H_{2^{l-1}} + Q_{2^{l-1}-1}` with the `Q⁺` parameter block. -/
noncomputable def tS1 (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  Hp (l - 1) + peel Hp (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))

/-- `S⁽²⁾₁` of a main branch: the scalar-shifted companion `H_{2^{l-1}} + δ`. -/
noncomputable def tS1t (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  Hp (l - 1) + C (α ((k - 2) * 2 ^ l + 2 ^ (l - 1)))

/-- Even branch `S⁽¹⁾₂ = Q_{2^{l-1}-1}` with the `Q⁻` parameter block. -/
noncomputable def eS2 (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  peel Hp (l - 1) (fun j => α ((k - 2) * 2 ^ l + 1 + j))

/-- Even main step: the new power `H_{2^{l+1}}`. -/
noncomputable def evenH (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  (Hp l + tS1 Hp k l α) * (Hp l - tS1 Hp k l α) + eS2 Hp k l α

/-- Even main step: the new shifted power `H̃_{2^{l+1}}` (with the scalar `σ = α_b`). -/
noncomputable def evenHt (Hp : ℕ → A[X]) (Ht : A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  (Ht + tS1t Hp k l α) * (Ht - tS1t Hp k l α) + C (α ((k - 2) * 2 ^ l))

/-- Odd branch `S⁽¹⁾₂ = H_{2^{l-2}} + Q_{2^{l-2}-1}` with the `Q₀` parameter block. -/
noncomputable def oS2 (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  Hp (l - 2) + peel Hp (l - 2) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 2) + 1 + j))

/-- Odd branch `S⁽¹⁾₃ = Q_{2^{l-2}-1}` with the `Q⁻` parameter block. -/
noncomputable def oS3 (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  peel Hp (l - 2) (fun j => α ((k - 2) * 2 ^ l + 1 + j))

/-- Odd branch `S⁽²⁾₂ = H_{2^{l-2}} + ε`. -/
noncomputable def oS2t (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  Hp (l - 2) + C (α ((k - 2) * 2 ^ l + 2 ^ (l - 2)))

/-- Odd main step: the new power `H_{2^{l+1}}`. -/
noncomputable def oddH (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  ((Hp l + tS1 Hp k l α) + oS2 Hp k l α) * ((Hp l + tS1 Hp k l α) - oS2 Hp k l α)
    + oS3 Hp k l α

/-- Odd main step: the new shifted power `H̃_{2^{l+1}}` (with the scalar `ζ = α_b`). -/
noncomputable def oddHt (Hp : ℕ → A[X]) (Ht : A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  ((Ht + tS1t Hp k l α) + oS2t Hp k l α) * ((Ht + tS1t Hp k l α) - oS2t Hp k l α)
    + C (α ((k - 2) * 2 ^ l))

/-- Odd main step: output assembly around the recursive pair (`l ≥ 3`). -/
noncomputable def oddOut (Hp : ℕ → A[X]) (Ht : A[X]) (k l : ℕ) (α : ℕ → A)
    (inner : A[X] × A[X]) : A[X] × A[X] :=
  ((Hp l - (k - 1) • tS1 Hp k l α) * inner.1 + peel Hp l (fun j => α (1 + j)),
   (Ht - (k - 1) • tS1t Hp k l α) * inner.2 + C (α 0))

/-- Shared even base (`l = 1`): the new power `H₄`. -/
noncomputable def ebH (Hp : ℕ → A[X]) (k : ℕ) (α : ℕ → A) : A[X] :=
  (Hp 1 + (X + C (α (2 * k - 3)))) * (Hp 1 - (X + C (α (2 * k - 3)))) + C (α (2 * k - 4))

/-- Shared odd base (`l = 2`): `S⁽¹⁾₁ = H₂ + (x + u)`. -/
noncomputable def obS1 (Hp : ℕ → A[X]) (k : ℕ) (α : ℕ → A) : A[X] :=
  Hp 1 + (X + C (α (4 * (k - 2) + 3)))

/-- Shared odd base: the common octic core `H₈`. -/
noncomputable def obH8 (Hp : ℕ → A[X]) (k : ℕ) (α : ℕ → A) : A[X] :=
  ((Hp 2 + obS1 Hp k α) + (X + C (α (4 * (k - 2) + 2))))
    * ((Hp 2 + obS1 Hp k α) - (X + C (α (4 * (k - 2) + 2)))) + C (α (4 * (k - 2) + 1))

/-- Shared odd base: output assembly (`S⁽²⁾₁ = S⁽¹⁾₁ - ρ` with `ρ = H̃₄ - H₄`). -/
noncomputable def obOut (Hp : ℕ → A[X]) (Ht : A[X]) (k : ℕ) (α : ℕ → A)
    (inner : A[X] × A[X]) : A[X] × A[X] :=
  ((Hp 2 - (k - 1) • obS1 Hp k α) * inner.1 + Q₃ (Hp 1) (α 1) (α 2) (α 3),
   (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * inner.2 + C (α 0))

/-- Fuel-indexed `T_{k,2^l}` pair.  `TF fuel k l Hp Ht α`; fuel `≥ k` suffices. -/
noncomputable def TF : ℕ → ℕ → ℕ → (ℕ → A[X]) → A[X] → (ℕ → A) → A[X] × A[X]
  | 0, _, l, Hp, Ht, _ => (Hp l, Ht)
  | f + 1, k, l, Hp, Ht, α =>
    if k ≤ 1 then (Hp l, Ht)
    else if k % 2 = 0 then
      if l ≤ 1 then
        TF f (k / 2) 2 (Function.update Hp 2 (ebH Hp k α)) (ebH Hp k α + (Ht - Hp 1)) α
      else
        TF f (k / 2) (l + 1) (Function.update Hp (l + 1) (evenH Hp k l α))
          (evenHt Hp Ht k l α) α
    else
      if l ≤ 2 then
        obOut Hp Ht k α (TF f ((k - 1) / 2) 3 (Function.update Hp 3 (obH8 Hp k α))
          (obH8 Hp k α + C (α (4 * (k - 2)))) (fun j => α (4 + j)))
      else
        oddOut Hp Ht k l α (TF f ((k - 1) / 2) (l + 1)
          (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
          (fun j => α (2 ^ l + j)))

/-- The `T_{k,2^l}` pair (`alg:constr-Tk2l`, `alg:constr-Tk2l-base`). -/
noncomputable def Tpair (Hp : ℕ → A[X]) (Ht : A[X]) (k l : ℕ) (α : ℕ → A) :
    A[X] × A[X] :=
  TF k k l Hp Ht α

/-- One-step unfolding of `TF` (definitional). -/
theorem TF_succ (g k l : ℕ) (Hp : ℕ → A[X]) (Ht : A[X]) (α : ℕ → A) :
    TF (g + 1) k l Hp Ht α =
      if k ≤ 1 then (Hp l, Ht)
      else if k % 2 = 0 then
        if l ≤ 1 then
          TF g (k / 2) 2 (Function.update Hp 2 (ebH Hp k α)) (ebH Hp k α + (Ht - Hp 1)) α
        else
          TF g (k / 2) (l + 1) (Function.update Hp (l + 1) (evenH Hp k l α))
            (evenHt Hp Ht k l α) α
      else
        if l ≤ 2 then
          obOut Hp Ht k α (TF g ((k - 1) / 2) 3 (Function.update Hp 3 (obH8 Hp k α))
            (obH8 Hp k α + C (α (4 * (k - 2)))) (fun j => α (4 + j)))
        else
          oddOut Hp Ht k l α (TF g ((k - 1) / 2) (l + 1)
            (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
            (fun j => α (2 ^ l + j))) := rfl

/-- Branch equation: trivial sizes. -/
theorem TF_succ_le_one {g k l : ℕ} {Hp : ℕ → A[X]} {Ht : A[X]} {α : ℕ → A}
    (h : k ≤ 1) : TF (g + 1) k l Hp Ht α = (Hp l, Ht) := by
  rw [TF_succ, if_pos h]

/-- Branch equation: shared even base (`l = 1`). -/
theorem TF_succ_even_base {g k l : ℕ} {Hp : ℕ → A[X]} {Ht : A[X]} {α : ℕ → A}
    (h1 : ¬ k ≤ 1) (h2 : k % 2 = 0) (h3 : l ≤ 1) :
    TF (g + 1) k l Hp Ht α
      = TF g (k / 2) 2 (Function.update Hp 2 (ebH Hp k α)) (ebH Hp k α + (Ht - Hp 1)) α := by
  rw [TF_succ, if_neg h1, if_pos h2, if_pos h3]

/-- Branch equation: even main step (`l ≥ 2`). -/
theorem TF_succ_even_main {g k l : ℕ} {Hp : ℕ → A[X]} {Ht : A[X]} {α : ℕ → A}
    (h1 : ¬ k ≤ 1) (h2 : k % 2 = 0) (h3 : ¬ l ≤ 1) :
    TF (g + 1) k l Hp Ht α
      = TF g (k / 2) (l + 1) (Function.update Hp (l + 1) (evenH Hp k l α))
          (evenHt Hp Ht k l α) α := by
  rw [TF_succ, if_neg h1, if_pos h2, if_neg h3]

/-- Branch equation: shared odd base (`l = 2`). -/
theorem TF_succ_odd_base {g k l : ℕ} {Hp : ℕ → A[X]} {Ht : A[X]} {α : ℕ → A}
    (h1 : ¬ k ≤ 1) (h2 : ¬ k % 2 = 0) (h3 : l ≤ 2) :
    TF (g + 1) k l Hp Ht α
      = obOut Hp Ht k α (TF g ((k - 1) / 2) 3 (Function.update Hp 3 (obH8 Hp k α))
          (obH8 Hp k α + C (α (4 * (k - 2)))) (fun j => α (4 + j))) := by
  rw [TF_succ, if_neg h1, if_neg h2, if_pos h3]

/-- Branch equation: odd main step (`l ≥ 3`). -/
theorem TF_succ_odd_main {g k l : ℕ} {Hp : ℕ → A[X]} {Ht : A[X]} {α : ℕ → A}
    (h1 : ¬ k ≤ 1) (h2 : ¬ k % 2 = 0) (h3 : ¬ l ≤ 2) :
    TF (g + 1) k l Hp Ht α
      = oddOut Hp Ht k l α (TF g ((k - 1) / 2) (l + 1)
          (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
          (fun j => α (2 ^ l + j))) := by
  rw [TF_succ, if_neg h1, if_neg h2, if_neg h3]

/-- Fuel irrelevance for `TF`: any fuel at least `k` computes the same pair. -/
theorem TF_fuel : ∀ k f f', k ≤ f → k ≤ f' → ∀ l (Hp : ℕ → A[X]) (Ht : A[X]) (α : ℕ → A),
    TF f k l Hp Ht α = TF f' k l Hp Ht α := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f f' hf hf' l Hp Ht α
    match k, f, f', hf, hf' with
    | 0, 0, 0, _, _ => rfl
    | 0, 0, _ + 1, _, _ => rw [TF_succ_le_one (by omega)]; rfl
    | 0, _ + 1, 0, _, _ => rw [TF_succ_le_one (by omega)]; rfl
    | 0, _ + 1, _ + 1, _, _ => rw [TF_succ_le_one (by omega), TF_succ_le_one (by omega)]
    | k + 1, 0, _, hf, _ => exact absurd hf (by omega)
    | k + 1, _ + 1, 0, _, hf' => exact absurd hf' (by omega)
    | k + 1, f + 1, f' + 1, hf, hf' =>
      rcases Nat.lt_or_ge k 1 with h1 | h1
      · rw [TF_succ_le_one (by omega), TF_succ_le_one (by omega)]
      · rcases eq_or_ne ((k + 1) % 2) 0 with hpar | hpar
        · rcases Nat.lt_or_ge l 2 with hl | hl
          · rw [TF_succ_even_base (by omega) hpar (by omega),
              TF_succ_even_base (by omega) hpar (by omega)]
            exact ih ((k + 1) / 2) (by omega) f f' (by omega) (by omega) 2 _ _ _
          · rw [TF_succ_even_main (by omega) hpar (by omega),
              TF_succ_even_main (by omega) hpar (by omega)]
            exact ih ((k + 1) / 2) (by omega) f f' (by omega) (by omega) (l + 1) _ _ _
        · rcases Nat.lt_or_ge l 3 with hl | hl
          · rw [TF_succ_odd_base (by omega) hpar (by omega),
              TF_succ_odd_base (by omega) hpar (by omega)]
            exact congrArg (obOut Hp Ht (k + 1) α)
              (ih ((k + 1 - 1) / 2) (by omega) f f' (by omega) (by omega) 3 _ _ _)
          · rw [TF_succ_odd_main (by omega) hpar (by omega),
              TF_succ_odd_main (by omega) hpar (by omega)]
            exact congrArg (oddOut Hp Ht (k + 1) l α)
              (ih ((k + 1 - 1) / 2) (by omega) f f' (by omega) (by omega) (l + 1) _ _ _)

section structural

variable [Nontrivial A] {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}

/-- Degree collapse of a difference of monics of equal degree. -/
theorem sub_monic_low {P Q : A[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hd : P.natDegree = Q.natDegree) :
    P - Q = 0 ∨ (P - Q).natDegree < P.natDegree := by
  rcases eq_or_ne (P - Q) 0 with h0 | hne
  · exact Or.inl h0
  · refine Or.inr (natDegree_lt_natDegree hne ?_)
    refine degree_sub_lt ?_ hP.ne_zero ?_
    · rw [degree_eq_natDegree hP.ne_zero, degree_eq_natDegree hQ.ne_zero, hd]
    · rw [hP.leadingCoeff, hQ.leadingCoeff]

/-- Monic minus a lower-degree polynomial. -/
theorem monic_sub_low {P e : A[X]} (hP : P.Monic)
    (he : e = 0 ∨ e.natDegree < P.natDegree) :
    (P - e).Monic ∧ (P - e).natDegree = P.natDegree := by
  have hsub : P - e = P + -e := by ring
  rw [hsub]
  refine monic_add_low hP ?_
  rcases he with rfl | hlt
  · exact Or.inl neg_zero
  · exact Or.inr (by rwa [natDegree_neg])

/-- Engine for the `*_good` lemmas: `(F + e)·(F - e) + low` is monic of doubled degree,
for a perturbation `e` below `deg F = n` and a remainder `low` below `n + n`. -/
theorem monic_sq_diff_add_low {F e low : A[X]} {n : ℕ} (hF : F.Monic)
    (hFd : F.natDegree = n) (he : e = 0 ∨ e.natDegree < n)
    (hlow : low = 0 ∨ low.natDegree < n + n) :
    ((F + e) * (F - e) + low).Monic ∧ ((F + e) * (F - e) + low).natDegree = n + n := by
  subst hFd
  obtain ⟨hf1m, hf1d⟩ := monic_add_low hF he
  obtain ⟨hf2m, hf2d⟩ := monic_sub_low hF he
  have hprodm : ((F + e) * (F - e)).Monic := hf1m.mul hf2m
  have hprodd : ((F + e) * (F - e)).natDegree = F.natDegree + F.natDegree := by
    rw [hf1m.natDegree_mul hf2m, hf1d, hf2d]
  obtain ⟨hm', hd'⟩ := monic_add_low (e := low) hprodm (by
    rcases hlow with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr (by rw [hprodd]; exact hlt))
  exact ⟨hm', hd'.trans hprodd⟩

/-- Good towers survive an update one level up. -/
theorem good_update {m : ℕ} {H' : A[X]}
    (hHp : ∀ i, 1 ≤ i → i ≤ m → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hH' : H'.Monic) (hd' : H'.natDegree = 2 ^ (m + 1)) :
    ∀ i, 1 ≤ i → i ≤ m + 1 →
      ((Function.update Hp (m + 1) H') i).Monic ∧
      ((Function.update Hp (m + 1) H') i).natDegree = 2 ^ i := by
  intro i h1 hi
  rcases eq_or_ne i (m + 1) with rfl | hne
  · have hupd : Function.update Hp (m + 1) H' (m + 1) = H' := by
      rw [update_last]
    rw [hupd]
    exact ⟨hH', hd'⟩
  · have hupd : Function.update Hp (m + 1) H' i = Hp i := by
      rw [update_ne _ hne]
    rw [hupd]
    exact hHp i h1 (by omega)

/-- `S⁽¹⁾₁` is monic of degree `2^{l-1}`. -/
theorem tS1_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l) :
    (tS1 Hp k l α).Monic ∧ (tS1 Hp k l α).natDegree = 2 ^ (l - 1) := by
  obtain ⟨hm, hd⟩ := hHp (l - 1) (by omega) (by omega)
  obtain ⟨hqm, hqd⟩ := peel_monic Hp (l - 1)
    (fun i' h1' hik => hHp i' h1' (by omega)) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  unfold tS1
  obtain ⟨hm', hd'⟩ := monic_add_low
    (e := peel Hp (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))) hm
    (Or.inr (by rw [hqd, hd]; omega))
  exact ⟨hm', hd'.trans hd⟩

/-- `S⁽²⁾₁` is monic of degree `2^{l-1}`. -/
theorem tS1t_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l) :
    (tS1t Hp k l α).Monic ∧ (tS1t Hp k l α).natDegree = 2 ^ (l - 1) := by
  obtain ⟨hm, hd⟩ := hHp (l - 1) (by omega) (by omega)
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  unfold tS1t
  obtain ⟨hm', hd'⟩ := monic_add_low (e := C (α ((k - 2) * 2 ^ l + 2 ^ (l - 1)))) hm
    (Or.inr (by rw [natDegree_C, hd]; omega))
  exact ⟨hm', hd'.trans hd⟩

/-- The even-step power `H_{2^{l+1}}` is monic of degree `2^{l+1}`. -/
theorem evenH_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l) :
    (evenH Hp k l α).Monic ∧ (evenH Hp k l α).natDegree = 2 ^ (l + 1) := by
  obtain ⟨hLm, hLd⟩ := hHp l (by omega) le_rfl
  obtain ⟨-, hs1d⟩ := tS1_good (k := k) (α := α) hHp hl
  obtain ⟨-, hqd⟩ := peel_monic Hp (l - 1)
    (fun i' h1' hik => hHp i' h1' (by omega)) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 1 + j))
  have heS2d : (eS2 Hp k l α).natDegree = 2 ^ (l - 1) - 1 := hqd
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hle : (2:ℕ) ^ (l - 1 + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hdouble : (2:ℕ) ^ (l - 1 + 1) = 2 ^ (l - 1) + 2 ^ (l - 1) := by ring
  have hsum : (2:ℕ) ^ (l + 1) = 2 ^ l + 2 ^ l := by ring
  unfold evenH
  obtain ⟨hm', hd'⟩ := monic_sq_diff_add_low (e := tS1 Hp k l α) (low := eS2 Hp k l α)
    hLm hLd (Or.inr (by rw [hs1d]; omega)) (Or.inr (by rw [heS2d]; omega))
  exact ⟨hm', hd'.trans (by omega)⟩

/-- The even-step shifted power `H̃_{2^{l+1}}` is monic of degree `2^{l+1}`. -/
theorem evenHt_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l) (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) :
    (evenHt Hp Ht k l α).Monic ∧ (evenHt Hp Ht k l α).natDegree = 2 ^ (l + 1) := by
  obtain ⟨-, hs1d⟩ := tS1t_good (k := k) (α := α) hHp hl
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have h1l : (1:ℕ) ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hle : (2:ℕ) ^ (l - 1 + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hdouble : (2:ℕ) ^ (l - 1 + 1) = 2 ^ (l - 1) + 2 ^ (l - 1) := by ring
  have hsum : (2:ℕ) ^ (l + 1) = 2 ^ l + 2 ^ l := by ring
  unfold evenHt
  obtain ⟨hm', hd'⟩ := monic_sq_diff_add_low (e := tS1t Hp k l α)
    (low := C (α ((k - 2) * 2 ^ l))) hHt hdHt
    (Or.inr (by rw [hs1d]; omega)) (Or.inr (by rw [natDegree_C]; omega))
  exact ⟨hm', hd'.trans (by omega)⟩

/-- Odd branch `S⁽¹⁾₂` is monic of degree `2^{l-2}`. -/
theorem oS2_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) :
    (oS2 Hp k l α).Monic ∧ (oS2 Hp k l α).natDegree = 2 ^ (l - 2) := by
  obtain ⟨hm, hd⟩ := hHp (l - 2) (by omega) (by omega)
  obtain ⟨hqm, hqd⟩ := peel_monic Hp (l - 2)
    (fun i' h1' hik => hHp i' h1' (by omega)) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 2) + 1 + j))
  have h1p : (1:ℕ) ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  unfold oS2
  obtain ⟨hm', hd'⟩ := monic_add_low
    (e := peel Hp (l - 2) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 2) + 1 + j))) hm
    (Or.inr (by rw [hqd, hd]; omega))
  exact ⟨hm', hd'.trans hd⟩

/-- Odd branch `S⁽²⁾₂` is monic of degree `2^{l-2}`. -/
theorem oS2t_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) :
    (oS2t Hp k l α).Monic ∧ (oS2t Hp k l α).natDegree = 2 ^ (l - 2) := by
  obtain ⟨hm, hd⟩ := hHp (l - 2) (by omega) (by omega)
  have h1p : (1:ℕ) ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  unfold oS2t
  obtain ⟨hm', hd'⟩ := monic_add_low (e := C (α ((k - 2) * 2 ^ l + 2 ^ (l - 2)))) hm
    (Or.inr (by rw [natDegree_C, hd]; omega))
  exact ⟨hm', hd'.trans hd⟩

/-- The odd-step power is monic of degree `2^{l+1}`. -/
theorem oddH_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) :
    (oddH Hp k l α).Monic ∧ (oddH Hp k l α).natDegree = 2 ^ (l + 1) := by
  obtain ⟨hLm, hLd⟩ := hHp l (by omega) le_rfl
  obtain ⟨-, hs1d⟩ := tS1_good (k := k) (α := α) hHp (by omega)
  obtain ⟨-, ho2d⟩ := oS2_good (k := k) (α := α) hHp hl
  obtain ⟨-, hq3d⟩ := peel_monic Hp (l - 2)
    (fun i' h1' hik => hHp i' h1' (by omega)) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 1 + j))
  have hoS3d : (oS3 Hp k l α).natDegree = 2 ^ (l - 2) - 1 := hq3d
  have h1a : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have h1b : (1:ℕ) ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have hlea : (2:ℕ) ^ (l - 1 + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hda : (2:ℕ) ^ (l - 1 + 1) = 2 ^ (l - 1) + 2 ^ (l - 1) := by ring
  have hleb : (2:ℕ) ^ (l - 2 + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hdb : (2:ℕ) ^ (l - 2 + 1) = 2 ^ (l - 2) + 2 ^ (l - 2) := by ring
  have hsum : (2:ℕ) ^ (l + 1) = 2 ^ l + 2 ^ l := by ring
  obtain ⟨hGm, hGd⟩ := monic_add_low (e := tS1 Hp k l α) hLm
    (Or.inr (by rw [hs1d, hLd]; omega))
  unfold oddH
  obtain ⟨hm', hd'⟩ := monic_sq_diff_add_low (e := oS2 Hp k l α) (low := oS3 Hp k l α)
    hGm (hGd.trans hLd) (Or.inr (by rw [ho2d]; omega))
    (Or.inr (by rw [hoS3d]; omega))
  exact ⟨hm', hd'.trans (by omega)⟩

/-- The odd-step shifted power is monic of degree `2^{l+1}`. -/
theorem oddHt_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) :
    (oddHt Hp Ht k l α).Monic ∧ (oddHt Hp Ht k l α).natDegree = 2 ^ (l + 1) := by
  obtain ⟨-, hs1d⟩ := tS1t_good (k := k) (α := α) hHp (by omega)
  obtain ⟨-, ho2d⟩ := oS2t_good (k := k) (α := α) hHp hl
  have h1a : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have h1b : (1:ℕ) ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have h1l : (1:ℕ) ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hlea : (2:ℕ) ^ (l - 1 + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hda : (2:ℕ) ^ (l - 1 + 1) = 2 ^ (l - 1) + 2 ^ (l - 1) := by ring
  have hleb : (2:ℕ) ^ (l - 2 + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hdb : (2:ℕ) ^ (l - 2 + 1) = 2 ^ (l - 2) + 2 ^ (l - 2) := by ring
  have hsum : (2:ℕ) ^ (l + 1) = 2 ^ l + 2 ^ l := by ring
  obtain ⟨hGm, hGd⟩ := monic_add_low (e := tS1t Hp k l α) hHt
    (Or.inr (by rw [hs1d, hdHt]; omega))
  unfold oddHt
  obtain ⟨hm', hd'⟩ := monic_sq_diff_add_low (e := oS2t Hp k l α)
    (low := C (α ((k - 2) * 2 ^ l))) hGm (hGd.trans hdHt)
    (Or.inr (by rw [ho2d]; omega)) (Or.inr (by rw [natDegree_C]; omega))
  exact ⟨hm', hd'.trans (by omega)⟩

/-- The shared even-base power `H₄` is monic of degree `4`. -/
theorem ebH_good (h1 : (Hp 1).Monic ∧ (Hp 1).natDegree = 2 ^ 1) :
    (ebH Hp k α).Monic ∧ (ebH Hp k α).natDegree = 2 ^ 2 := by
  obtain ⟨h1m, h1d⟩ := h1
  have hXd : (X + C (α (2 * k - 3)) : A[X]).natDegree = 1 := natDegree_X_add_C _
  unfold ebH
  obtain ⟨hm', hd'⟩ := monic_sq_diff_add_low (e := X + C (α (2 * k - 3)))
    (low := C (α (2 * k - 4))) h1m h1d
    (Or.inr (by rw [hXd]; norm_num)) (Or.inr (by rw [natDegree_C]; norm_num))
  exact ⟨hm', hd'.trans (by norm_num)⟩

/-- The shared odd-base `S⁽¹⁾₁` is monic of degree `2`. -/
theorem obS1_good (h1 : (Hp 1).Monic ∧ (Hp 1).natDegree = 2 ^ 1) :
    (obS1 Hp k α).Monic ∧ (obS1 Hp k α).natDegree = 2 := by
  obtain ⟨h1m, h1d⟩ := h1
  have hXd : (X + C (α (4 * (k - 2) + 3)) : A[X]).natDegree = 1 := natDegree_X_add_C _
  unfold obS1
  obtain ⟨hm', hd'⟩ := monic_add_low (e := X + C (α (4 * (k - 2) + 3))) h1m
    (Or.inr (by rw [hXd, h1d]; norm_num))
  refine ⟨hm', hd'.trans (h1d.trans (by norm_num))⟩

/-- The shared odd-base octic core `H₈` is monic of degree `8`. -/
theorem obH8_good (h1 : (Hp 1).Monic ∧ (Hp 1).natDegree = 2 ^ 1)
    (h2 : (Hp 2).Monic ∧ (Hp 2).natDegree = 2 ^ 2) :
    (obH8 Hp k α).Monic ∧ (obH8 Hp k α).natDegree = 2 ^ 3 := by
  obtain ⟨h2m, h2d⟩ := h2
  obtain ⟨-, hbd⟩ := obS1_good (k := k) (α := α) h1
  have hXd : (X + C (α (4 * (k - 2) + 2)) : A[X]).natDegree = 1 := natDegree_X_add_C _
  obtain ⟨hGm, hGd⟩ := monic_add_low (e := obS1 Hp k α) h2m
    (Or.inr (by rw [hbd, h2d]; norm_num))
  unfold obH8
  obtain ⟨hm', hd'⟩ := monic_sq_diff_add_low (e := X + C (α (4 * (k - 2) + 2)))
    (low := C (α (4 * (k - 2) + 1))) hGm (hGd.trans h2d)
    (Or.inr (by rw [hXd]; norm_num)) (Or.inr (by rw [natDegree_C]; norm_num))
  exact ⟨hm', hd'.trans (by norm_num)⟩

end structural

section structural2

variable [Nontrivial A] {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}

/-- Shared odd base output: monicity and degree `k·2²`. -/
theorem obOut_good (h1 : (Hp 1).Monic ∧ (Hp 1).natDegree = 2 ^ 1)
    (h2 : (Hp 2).Monic ∧ (Hp 2).natDegree = 2 ^ 2)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ 2)
    (hk : 3 ≤ k) (hkodd : k % 2 = 1)
    {inner : A[X] × A[X]}
    (hi1 : inner.1.Monic) (hd1 : inner.1.natDegree = (k - 1) / 2 * 2 ^ 3)
    (hi2 : inner.2.Monic) (hd2 : inner.2.natDegree = (k - 1) / 2 * 2 ^ 3) :
    ((obOut Hp Ht k α inner).1.Monic ∧
      (obOut Hp Ht k α inner).1.natDegree = k * 2 ^ 2) ∧
    ((obOut Hp Ht k α inner).2.Monic ∧
      (obOut Hp Ht k α inner).2.natDegree = k * 2 ^ 2) := by
  obtain ⟨h2m, h2d⟩ := h2
  obtain ⟨hbm, hbd⟩ := obS1_good (k := k) (α := α) h1
  have hsm : ((k - 1) • obS1 Hp k α).natDegree ≤ 2 :=
    le_trans (natDegree_smul_le _ _) (le_of_eq hbd)
  obtain ⟨hL1m, hL1d⟩ := monic_sub_low (e := (k - 1) • obS1 Hp k α) h2m
    (Or.inr (by rw [h2d]; omega))
  have hQd : (Q₃ (Hp 1) (α 1) (α 2) (α 3)).natDegree = 2 ^ 2 - 1 :=
    (peel_monic Hp 2 (fun i' h1' hik => by
      have hi1' : i' = 1 := by omega
      subst hi1'
      exact h1) (by omega) (fun j => α (1 + j))).2
  have hP1m : ((Hp 2 - (k - 1) • obS1 Hp k α) * inner.1).Monic := hL1m.mul hi1
  have hP1d : ((Hp 2 - (k - 1) • obS1 Hp k α) * inner.1).natDegree = k * 2 ^ 2 := by
    rw [hL1m.natDegree_mul hi1, hL1d, hd1, h2d]
    omega
  obtain ⟨hout1m, hout1d⟩ := monic_add_low (e := Q₃ (Hp 1) (α 1) (α 2) (α 3)) hP1m
    (Or.inr (by rw [hQd, hP1d]; omega))
  have hNd : (obS1 Hp k α - (Ht - Hp 2)).natDegree ≤ 3 := by
    rcases sub_monic_low hHt h2m (by rw [hdHt, h2d]) with h0 | hlt
    · rw [h0, sub_zero, hbd]
      omega
    · refine le_trans (natDegree_sub_le _ _) (max_le (by omega) ?_)
      rw [hdHt] at hlt
      omega
  have hsm2 : ((k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree ≤ 3 :=
    le_trans (natDegree_smul_le _ _) hNd
  obtain ⟨hL2m, hL2d⟩ := monic_sub_low
    (e := (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) hHt
    (Or.inr (by rw [hdHt]; omega))
  have hP2m : ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * inner.2).Monic :=
    hL2m.mul hi2
  have hP2d : ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * inner.2).natDegree
      = k * 2 ^ 2 := by
    rw [hL2m.natDegree_mul hi2, hL2d, hd2, hdHt]
    omega
  obtain ⟨hout2m, hout2d⟩ := monic_add_low (e := C (α 0)) hP2m
    (Or.inr (by rw [natDegree_C, hP2d]; omega))
  unfold obOut
  exact ⟨⟨hout1m, hout1d.trans hP1d⟩, ⟨hout2m, hout2d.trans hP2d⟩⟩

/-- Odd main output: monicity and degree `k·2^l`. -/
theorem oddOut_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l)
    (hk : 3 ≤ k) (hkodd : k % 2 = 1)
    {inner : A[X] × A[X]}
    (hi1 : inner.1.Monic) (hd1 : inner.1.natDegree = (k - 1) / 2 * 2 ^ (l + 1))
    (hi2 : inner.2.Monic) (hd2 : inner.2.natDegree = (k - 1) / 2 * 2 ^ (l + 1)) :
    ((oddOut Hp Ht k l α inner).1.Monic ∧
      (oddOut Hp Ht k l α inner).1.natDegree = k * 2 ^ l) ∧
    ((oddOut Hp Ht k l α inner).2.Monic ∧
      (oddOut Hp Ht k l α inner).2.natDegree = k * 2 ^ l) := by
  obtain ⟨hLm, hLd⟩ := hHp l (by omega) le_rfl
  obtain ⟨-, hs1d⟩ := tS1_good (k := k) (α := α) hHp (by omega)
  obtain ⟨-, hs1td⟩ := tS1t_good (k := k) (α := α) hHp (by omega)
  have hQd : (peel Hp l (fun j => α (1 + j))).natDegree = 2 ^ l - 1 :=
    (peel_monic Hp l (fun i' h1' hik => hHp i' h1' (by omega)) (by omega)
      (fun j => α (1 + j))).2
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have h1l : (1:ℕ) ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hle : (2:ℕ) ^ (l - 1 + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hda : (2:ℕ) ^ (l - 1 + 1) = 2 ^ (l - 1) + 2 ^ (l - 1) := by ring
  have hdiv : (k - 1) / 2 * 2 = k - 1 := Nat.div_mul_cancel (by omega : 2 ∣ k - 1)
  have hinnerd : (k - 1) / 2 * 2 ^ (l + 1) = (k - 1) * 2 ^ l := by
    calc (k - 1) / 2 * 2 ^ (l + 1) = (k - 1) / 2 * 2 * 2 ^ l := by ring
    _ = (k - 1) * 2 ^ l := by rw [hdiv]
  have htot : 2 ^ l + (k - 1) * 2 ^ l = k * 2 ^ l := by
    have hk1 : k - 1 + 1 = k := by omega
    calc 2 ^ l + (k - 1) * 2 ^ l = (k - 1 + 1) * 2 ^ l := by ring
    _ = k * 2 ^ l := by rw [hk1]
  have hsm : ((k - 1) • tS1 Hp k l α).natDegree ≤ 2 ^ (l - 1) :=
    le_trans (natDegree_smul_le _ _) (le_of_eq hs1d)
  obtain ⟨hL1m, hL1d⟩ := monic_sub_low (e := (k - 1) • tS1 Hp k l α) hLm
    (Or.inr (by rw [hLd]; omega))
  have hP1m : ((Hp l - (k - 1) • tS1 Hp k l α) * inner.1).Monic := hL1m.mul hi1
  have hP1d : ((Hp l - (k - 1) • tS1 Hp k l α) * inner.1).natDegree = k * 2 ^ l := by
    rw [hL1m.natDegree_mul hi1, hL1d, hd1, hLd, hinnerd]
    exact htot
  obtain ⟨hout1m, hout1d⟩ := monic_add_low (e := peel Hp l (fun j => α (1 + j))) hP1m
    (Or.inr (by
      rw [hQd, hP1d]
      have hsplit : k * 2 ^ l = 2 ^ l + (k - 1) * 2 ^ l := htot.symm
      have hge : 1 * 2 ^ l ≤ (k - 1) * 2 ^ l := Nat.mul_le_mul_right _ (by omega)
      omega))
  have hsm2 : ((k - 1) • tS1t Hp k l α).natDegree ≤ 2 ^ (l - 1) :=
    le_trans (natDegree_smul_le _ _) (le_of_eq hs1td)
  obtain ⟨hL2m, hL2d⟩ := monic_sub_low (e := (k - 1) • tS1t Hp k l α) hHt
    (Or.inr (by rw [hdHt]; omega))
  have hP2m : ((Ht - (k - 1) • tS1t Hp k l α) * inner.2).Monic := hL2m.mul hi2
  have hP2d : ((Ht - (k - 1) • tS1t Hp k l α) * inner.2).natDegree = k * 2 ^ l := by
    rw [hL2m.natDegree_mul hi2, hL2d, hd2, hdHt, hinnerd]
    exact htot
  obtain ⟨hout2m, hout2d⟩ := monic_add_low (e := C (α 0)) hP2m
    (Or.inr (by
      rw [natDegree_C, hP2d]
      have hge : 1 * 2 ^ l ≤ k * 2 ^ l := Nat.mul_le_mul_right _ (by omega)
      omega))
  unfold oddOut
  exact ⟨⟨hout1m, hout1d.trans hP1d⟩, ⟨hout2m, hout2d.trans hP2d⟩⟩

/-- **Monicity and degree of the `T` recursion**: both components of `TF f k l Hp Ht α`
are monic of degree `k·2^l`, over a good tower and shifted top power (with the parity
admissibility of the level: `l ≥ 2` whenever `k ≥ 3` is odd). -/
theorem TF_good :
    ∀ k f l (Hp : ℕ → A[X]) (Ht : A[X]) (α : ℕ → A),
      1 ≤ k → k ≤ f → 1 ≤ l → (k % 2 = 1 → 3 ≤ k → 2 ≤ l) →
      (∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i) →
      Ht.Monic → Ht.natDegree = 2 ^ l →
      ((TF f k l Hp Ht α).1.Monic ∧ (TF f k l Hp Ht α).1.natDegree = k * 2 ^ l) ∧
      ((TF f k l Hp Ht α).2.Monic ∧ (TF f k l Hp Ht α).2.natDegree = k * 2 ^ l) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f l Hp Ht α hk hf hl hodd hHp hHt hdHt
    match k, f, hk, hf with
    | 0, _, hk, _ => exact absurd hk (by omega)
    | k + 1, 0, _, hf => exact absurd hf (by omega)
    | k + 1, f + 1, hk, hf =>
      rcases Nat.lt_or_ge k 1 with h1 | h1
      · have hk1 : k = 0 := by omega
        subst hk1
        rw [TF_succ_le_one (by omega)]
        obtain ⟨hm, hd⟩ := hHp l (by omega) le_rfl
        exact ⟨⟨hm, by rw [hd]; ring⟩, ⟨hHt, by rw [hdHt]; ring⟩⟩
      · rcases eq_or_ne ((k + 1) % 2) 0 with hpar | hpar
        · have hdvd : 2 ∣ k + 1 := Nat.dvd_of_mod_eq_zero hpar
          have hhalf : (k + 1) / 2 * 2 = k + 1 := Nat.div_mul_cancel hdvd
          rcases Nat.lt_or_ge l 2 with hlb | hl2
          · -- shared even base, l = 1
            have hleq : l = 1 := by omega
            subst hleq
            rw [TF_succ_even_base (by omega) hpar (by omega)]
            have h1g := hHp 1 (by omega) le_rfl
            obtain ⟨hebm, hebd⟩ := ebH_good (k := k + 1) (α := α) h1g
            have hgood2 := good_update (m := 1) (H' := ebH Hp (k + 1) α) hHp hebm hebd
            obtain ⟨h1m, h1d⟩ := h1g
            obtain ⟨htm, htd⟩ := monic_add_low (e := Ht - Hp 1) hebm (by
              rcases sub_monic_low hHt h1m (by rw [hdHt, h1d]) with h0 | hlt
              · exact Or.inl h0
              · refine Or.inr ?_
                rw [hebd]
                rw [hdHt] at hlt
                omega)
            have hres := ih ((k + 1) / 2) (by omega) f 2
              (Function.update Hp 2 (ebH Hp (k + 1) α))
              (ebH Hp (k + 1) α + (Ht - Hp 1)) α
              (by omega) (by omega) (by omega) (fun _ _ => le_rfl) hgood2 htm
              (htd.trans hebd)
            have hdeg : (k + 1) / 2 * 2 ^ 2 = (k + 1) * 2 ^ 1 := by omega
            obtain ⟨⟨ha, hb⟩, ⟨hc, hd2⟩⟩ := hres
            exact ⟨⟨ha, by rw [hb, hdeg]⟩, ⟨hc, by rw [hd2, hdeg]⟩⟩
          · -- even main, l ≥ 2
            rw [TF_succ_even_main (by omega) hpar (by omega)]
            obtain ⟨hHm, hHd⟩ := evenH_good (k := k + 1) (α := α) hHp hl2
            obtain ⟨hTm, hTd⟩ := evenHt_good (k := k + 1) (α := α) hHp hl2 hHt hdHt
            have hgood' := good_update (m := l) (H' := evenH Hp (k + 1) l α) hHp hHm hHd
            have hres := ih ((k + 1) / 2) (by omega) f (l + 1)
              (Function.update Hp (l + 1) (evenH Hp (k + 1) l α))
              (evenHt Hp Ht (k + 1) l α) α
              (by omega) (by omega) (by omega) (fun _ _ => by omega) hgood' hTm hTd
            have hdeg : (k + 1) / 2 * 2 ^ (l + 1) = (k + 1) * 2 ^ l := by
              calc (k + 1) / 2 * 2 ^ (l + 1) = (k + 1) / 2 * 2 * 2 ^ l := by ring
              _ = (k + 1) * 2 ^ l := by rw [hhalf]
            obtain ⟨⟨ha, hb⟩, ⟨hc, hd2⟩⟩ := hres
            exact ⟨⟨ha, by rw [hb, hdeg]⟩, ⟨hc, by rw [hd2, hdeg]⟩⟩
        · -- odd
          have hkodd : (k + 1) % 2 = 1 := by omega
          have hk3 : 3 ≤ k + 1 := by omega
          have hl2 : 2 ≤ l := hodd hkodd hk3
          rcases Nat.lt_or_ge l 3 with hlb | hl3
          · -- shared odd base, l = 2
            have hleq : l = 2 := by omega
            subst hleq
            rw [TF_succ_odd_base (by omega) (by omega) (by omega)]
            have h1g := hHp 1 (by omega) (by omega)
            have h2g := hHp 2 (by omega) le_rfl
            obtain ⟨h8m, h8d⟩ := obH8_good (k := k + 1) (α := α) h1g h2g
            have hgood3 := good_update (m := 2) (H' := obH8 Hp (k + 1) α) hHp h8m h8d
            obtain ⟨ht8m, ht8d⟩ := monic_add_low (e := C (α (4 * (k + 1 - 2)))) h8m
              (Or.inr (by rw [natDegree_C, h8d]; norm_num))
            have hres := ih ((k + 1 - 1) / 2) (by omega) f 3
              (Function.update Hp 3 (obH8 Hp (k + 1) α))
              (obH8 Hp (k + 1) α + C (α (4 * (k + 1 - 2)))) (fun j => α (4 + j))
              (by omega) (by omega) (by omega) (fun _ _ => by omega) hgood3 ht8m
              (ht8d.trans h8d)
            obtain ⟨⟨ha, hb⟩, ⟨hc, hd2⟩⟩ := hres
            exact obOut_good (k := k + 1) (α := α) h1g h2g hHt hdHt hk3 hkodd
              ha hb hc hd2
          · -- odd main, l ≥ 3
            rw [TF_succ_odd_main (by omega) (by omega) (by omega)]
            obtain ⟨hHm, hHd⟩ := oddH_good (k := k + 1) (α := α) hHp hl3
            obtain ⟨hTm, hTd⟩ := oddHt_good (k := k + 1) (α := α) hHp hl3 hHt hdHt
            have hgood' := good_update (m := l) (H' := oddH Hp (k + 1) l α) hHp hHm hHd
            have hres := ih ((k + 1 - 1) / 2) (by omega) f (l + 1)
              (Function.update Hp (l + 1) (oddH Hp (k + 1) l α))
              (oddHt Hp Ht (k + 1) l α) (fun j => α (2 ^ l + j))
              (by omega) (by omega) (by omega) (fun _ _ => by omega) hgood' hTm hTd
            obtain ⟨⟨ha, hb⟩, ⟨hc, hd2⟩⟩ := hres
            exact oddOut_good (k := k + 1) (α := α) hHp hl3 hHt hdHt hk3 hkodd
              ha hb hc hd2

/-- Monicity and degree of the `T`-pair (`lem:Rk2l`, structural part). -/
theorem Tpair_good (hk : 1 ≤ k) (hl : 1 ≤ l) (hodd : k % 2 = 1 → 3 ≤ k → 2 ≤ l)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) :
    ((Tpair Hp Ht k l α).1.Monic ∧ (Tpair Hp Ht k l α).1.natDegree = k * 2 ^ l) ∧
    ((Tpair Hp Ht k l α).2.Monic ∧ (Tpair Hp Ht k l α).2.natDegree = k * 2 ^ l) :=
  TF_good k k l Hp Ht α hk le_rfl hl hodd hHp hHt hdHt

end structural2

section remainder

variable [Nontrivial A] {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}

/-- The remainder pair `R⁽ⁱ⁾_{k,2^l}` (paper `lem:Rk2l`(1)):
`R⁽¹⁾ = T⁽¹⁾ - H_{2^l}^k` and `R⁽²⁾ = T⁽²⁾ - H̃_{2^l}^k`. -/
noncomputable def Rpair (Hp : ℕ → A[X]) (Ht : A[X]) (k l : ℕ) (α : ℕ → A) :
    A[X] × A[X] :=
  ((Tpair Hp Ht k l α).1 - Hp l ^ k, (Tpair Hp Ht k l α).2 - Ht ^ k)

/-- `lem:Rk2l`(1): the defining split `T⁽¹⁾ = H^k + R⁽¹⁾`, `T⁽²⁾ = H̃^k + R⁽²⁾`. -/
theorem Tpair_eq_pow_add_R :
    (Tpair Hp Ht k l α).1 = Hp l ^ k + (Rpair Hp Ht k l α).1 ∧
    (Tpair Hp Ht k l α).2 = Ht ^ k + (Rpair Hp Ht k l α).2 := by
  unfold Rpair
  constructor <;> ring

/-- The `k = 1` remainders vanish (`lem:Rk2l`(2), trivial case). -/
theorem Rpair_one : Rpair Hp Ht 1 l α = (0, 0) := by
  unfold Rpair
  have h1 : Tpair Hp Ht 1 l α = (Hp l, Ht) := TF_succ_le_one le_rfl
  rw [h1, pow_one, pow_one]
  simp

end remainder

end FastPoly
