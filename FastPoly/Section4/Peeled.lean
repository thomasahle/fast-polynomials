import FastPoly.Section4.KnownPowers
import FastPoly.Polynomial.MonicDivision

/-!
# The peeled (depth-balanced) known-powers gadget

Formalizes `eq:peeled-Q` / `lem:peeled-Q-decodable` of the paper: the recursion

  `Q^peel_{2^k-1} = (H_{2^{k-1}} + γ) · Q^peel_{2^{k-1}-1} + Q'^peel_{2^{k-1}-1}`

with the bases `Q_1 = X + α₀` and `Q_3 = (X + α₂)(H_2 + α₁) + α₀` of
`alg:constr-known-2n-1`.  It spans the same family as the sequential fill at the same
multiplication and addition ledger, with multiplicative height exactly `k`.

Parameter layout: slot `0` is the glue key `γ`; slots `1 .. 2^{k-1}-1` are the first
child (`W`, the quotient); slots `2^{k-1} .. 2^k-2` are the second child (`B`).

The decoder (`peel_correct`) is three steps riding on `lem:monic-division`: dividing by
the known monic `H_{2^{k-1}}` returns `W` as the quotient and `R = γ·W + B` as the
remainder exactly (the one-degree offset keeps `deg R < deg H`); both children are monic
of degree `2^{k-1}-1`, so `R`'s top coefficient is `γ + 1`; then `B = R - γ·W`, and the
children recurse.  Every pivot is a monic leading `1` — no division by `2` anywhere.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Fuel-indexed peeled construction; the fuel always equals the level, so unfolding is
definitional and no fuel-irrelevance lemma is needed. -/
noncomputable def peelF (Hp : ℕ → A[X]) : ℕ → ℕ → (ℕ → A) → A[X]
  | 0, _, α => X + C (α 0)
  | f + 1, k, α =>
    match k with
    | 0 => X + C (α 0)
    | 1 => X + C (α 0)
    | 2 => (X + C (α 2)) * (Hp 1 + C (α 1)) + C (α 0)
    | 3 =>
      (Hp 2 + C (α 0)) * ((X + C (α 3)) * (Hp 1 + C (α 2)) + C (α 1))
        + ((X + C (α 6)) * (Hp 1 + C (α 5)) + C (α 4))
    | (kk + 4) =>
      (Hp (kk + 3) + C (α 0)) * peelF Hp f (kk + 3) (fun j => α (1 + j))
        + peelF Hp f (kk + 3) (fun j => α (2 ^ (kk + 3) + j))

/-- The peeled known-powers polynomial `Q^peel_{2^k-1}` over the powers `Hp`
(`Hp i` playing `H_{2^i}`) and parameters `α`. -/
noncomputable def peel (Hp : ℕ → A[X]) (k : ℕ) (α : ℕ → A) : A[X] := peelF Hp k k α

theorem peel_unfold (Hp : ℕ → A[X]) (kk : ℕ) (α : ℕ → A) :
    peel Hp (kk + 3) α
      = (Hp (kk + 2) + C (α 0)) * peel Hp (kk + 2) (fun j => α (1 + j))
        + peel Hp (kk + 2) (fun j => α (2 ^ (kk + 2) + j)) := by
  match kk with
  | 0 => rfl
  | kk + 1 => rfl

/-- Monicity and exact degree `2^k - 1` of the peeled gadget. -/
theorem peel_monic [Nontrivial A] (Hp : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i) →
      1 ≤ k → ∀ α : ℕ → A,
      (peel Hp k α).Monic ∧ (peel Hp k α).natDegree = 2 ^ k - 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α
    match k with
    | 0 => omega
    | 1 =>
      exact ⟨monic_X_add_C (α 0), (natDegree_X_add_C (α 0)).trans (by norm_num)⟩
    | 2 =>
      obtain ⟨h1m, h1d⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨hbm, hbd⟩ := monic_add_low (e := C (α 1)) h1m (Or.inr (by
        rw [natDegree_C, h1d]; norm_num))
      have hXm : (X + C (α 2) : A[X]).Monic := monic_X_add_C (α 2)
      have hmul : ((X + C (α 2)) * (Hp 1 + C (α 1))).Monic := hXm.mul hbm
      have hmuld : ((X + C (α 2)) * (Hp 1 + C (α 1))).natDegree = 3 := by
        rw [hXm.natDegree_mul hbm, natDegree_X_add_C, hbd, h1d]
        norm_num
      obtain ⟨hm, hd⟩ := monic_add_low (e := C (α 0)) hmul (Or.inr (by
        rw [natDegree_C, hmuld]; norm_num))
      exact ⟨hm, (hd.trans hmuld).trans (by norm_num)⟩
    | kk + 3 =>
      rw [peel_unfold]
      obtain ⟨hHm, hHd⟩ := hHp (kk + 2) (by omega) (by omega)
      obtain ⟨hWm, hWd⟩ := ih (kk + 2) (by omega)
        (fun i' h1 hik => hHp i' h1 (by omega)) (by omega) (fun j => α (1 + j))
      obtain ⟨hBm, hBd⟩ := ih (kk + 2) (by omega)
        (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
        (fun j => α (2 ^ (kk + 2) + j))
      have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
      obtain ⟨hFm, hFd⟩ := monic_add_low (e := C (α 0)) hHm (Or.inr (by
        rw [natDegree_C, hHd]; omega))
      have hmul : ((Hp (kk + 2) + C (α 0)) *
          peel Hp (kk + 2) (fun j => α (1 + j))).Monic := hFm.mul hWm
      have hmuld : ((Hp (kk + 2) + C (α 0)) *
          peel Hp (kk + 2) (fun j => α (1 + j))).natDegree
          = 2 ^ (kk + 3) - 1 := by
        rw [hFm.natDegree_mul hWm, hFd, hHd, hWd]
        have : (2:ℕ) ^ (kk + 3) = 2 ^ (kk + 2) + 2 ^ (kk + 2) := by ring
        omega
      obtain ⟨hm, hd⟩ := monic_add_low
        (e := peel Hp (kk + 2) (fun j => α (2 ^ (kk + 2) + j))) hmul (Or.inr (by
          rw [hBd, hmuld]
          have : (2:ℕ) ^ (kk + 3) = 2 ^ (kk + 2) + 2 ^ (kk + 2) := by ring
          omega))
      exact ⟨hm, hd.trans hmuld⟩

/-- **Decodability of the peeled gadget** (`lem:peeled-Q-decodable`): over known powers
`Hp i = H_{2^i}` (monic, right degree, coefficients in `K`), every parameter `α t`,
`t < 2^k - 1`, lies in any subalgebra `V ⊇ K` containing the coefficients of the value.
Same interface as `mers_correct`, so the two gadget families are interchangeable at
every consumption site of the master construction. -/
theorem peel_correct [Nontrivial A] {K : Subalgebra R A} (Hp : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k →
        (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧ ∀ j, (Hp i).coeff j ∈ K) →
      1 ≤ k → ∀ α : ℕ → A, ∀ V : Subalgebra R A, K ≤ V →
      (∀ j, (peel Hp k α).coeff j ∈ V) → ∀ t, t < 2 ^ k - 1 → α t ∈ V := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α V hKV hV
    match k with
    | 0 => exact absurd hk (by omega)
    | 1 =>
      intro t ht
      have ht0 : t = 0 := by omega
      subst ht0
      have hkey : α 0 = (peel Hp 1 α).coeff 0 := by
        show α 0 = (X + C (α 0) : A[X]).coeff 0
        rw [coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
      rw [hkey]
      exact hV 0
    | 2 =>
      obtain ⟨h1m, h1d2, h1K⟩ := hHp 1 (by omega) (by omega)
      have h1d : (Hp 1).natDegree = 2 := h1d2.trans (by norm_num)
      have hQ : ∀ j, (Q₃ (Hp 1) (α 0) (α 1) (α 2)).coeff j ∈ V := fun j => hV j
      have hα2 : α 2 ∈ V := by
        have hkey : α 2 = (Q₃ (Hp 1) (α 0) (α 1) (α 2)).coeff 2 - (Hp 1).coeff 1 := by
          rw [Q₃_coeff_two (α 0) (α 1) (α 2) h1m h1d]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ (hQ 2) (hKV (h1K 1))
      have hα1 : α 1 ∈ V := by
        have hkey : α 1 = (Q₃ (Hp 1) (α 0) (α 1) (α 2)).coeff 1
            - ((Hp 1).coeff 0 + α 2 * (Hp 1).coeff 1) := by
          rw [Q₃_coeff_one (α 0) (α 1) (α 2)]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ (hQ 1) (Subalgebra.add_mem _ (hKV (h1K 0))
          (Subalgebra.mul_mem _ hα2 (hKV (h1K 1))))
      have hα0 : α 0 ∈ V := by
        have hkey : α 0 = (Q₃ (Hp 1) (α 0) (α 1) (α 2)).coeff 0
            - α 2 * ((Hp 1).coeff 0 + α 1) := by
          rw [Q₃_coeff_zero (α 0) (α 1) (α 2)]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ (hQ 0) (Subalgebra.mul_mem _ hα2
          (Subalgebra.add_mem _ (hKV (h1K 0)) hα1))
      intro t ht
      match t with
      | 0 => exact hα0
      | 1 => exact hα1
      | 2 => exact hα2
      | (s + 3) => omega
    | kk + 3 =>
      obtain ⟨hHm, hHd, hHK⟩ := hHp (kk + 2) (by omega) (by omega)
      have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
      set W : A[X] := peel Hp (kk + 2) (fun j => α (1 + j)) with hWdef
      set B : A[X] := peel Hp (kk + 2) (fun j => α (2 ^ (kk + 2) + j)) with hBdef
      obtain ⟨hWm, hWd⟩ := peel_monic Hp (kk + 2)
        (fun i' h1 hik => ⟨(hHp i' h1 (by omega)).1, (hHp i' h1 (by omega)).2.1⟩)
        (by omega) (fun j => α (1 + j))
      obtain ⟨hBm, hBd⟩ := peel_monic Hp (kk + 2)
        (fun i' h1 hik => ⟨(hHp i' h1 (by omega)).1, (hHp i' h1 (by omega)).2.1⟩)
        (by omega) (fun j => α (2 ^ (kk + 2) + j))
      rw [← hWdef] at hWm hWd
      rw [← hBdef] at hBm hBd
      -- rearrange for division by the known monic `Hp (kk+2)`
      have hsplit : peel Hp (kk + 3) α
          = W * Hp (kk + 2) + (C (α 0) * W + B) := by
        rw [peel_unfold, ← hWdef, ← hBdef]; ring
      have hRd : (C (α 0) * W + B).natDegree < 2 ^ (kk + 2) := by
        have hCW : (C (α 0) * W).natDegree ≤ 2 ^ (kk + 2) - 1 :=
          le_trans natDegree_mul_le (by rw [natDegree_C, hWd]; omega)
        have hle : (C (α 0) * W + B).natDegree ≤ 2 ^ (kk + 2) - 1 :=
          le_trans (natDegree_add_le _ _) (max_le hCW hBd.le)
        omega
      -- Step 1: the quotient `W` and remainder `R` have coefficients in `V`
      have hWV : ∀ j, W.coeff j ∈ V := by
        intro j
        rcases Nat.lt_or_ge (2 ^ (kk + 2) - 1) j with hj | hj
        · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
          exact Subalgebra.zero_mem _
        · have h := coeff_quot_mem K hHm (a := 2 ^ (kk + 2)) (b := 2 ^ (kk + 2) - 1)
            hHd h1p hHK (hWd.le) hRd hsplit j hj
          refine SetLike.le_def.1 (sup_le hKV (Algebra.adjoin_le ?_)) h
          rintro _ ⟨i, -, rfl⟩
          exact hV i
      have hRV : ∀ j, (C (α 0) * W + B).coeff j ∈ V := by
        intro j
        have h := coeff_rem_mem K hHm (a := 2 ^ (kk + 2)) (b := 2 ^ (kk + 2) - 1)
          hHd h1p hHK (hWd.le) hRd hsplit j
        refine SetLike.le_def.1 (sup_le hKV (Algebra.adjoin_le ?_)) h
        rintro _ ⟨i, -, rfl⟩
        exact hV i
      -- Step 2: `γ = α 0` from the remainder's top coefficient
      have hγ : α 0 ∈ V := by
        have hWtop : W.coeff (2 ^ (kk + 2) - 1) = 1 := by
          have := hWm.coeff_natDegree
          rwa [hWd] at this
        have hBtop : B.coeff (2 ^ (kk + 2) - 1) = 1 := by
          have := hBm.coeff_natDegree
          rwa [hBd] at this
        have hkey : α 0 = (C (α 0) * W + B).coeff (2 ^ (kk + 2) - 1) - 1 := by
          rw [coeff_add, coeff_C_mul, hWtop, hBtop]
          ring
        rw [hkey]
        exact Subalgebra.sub_mem _ (hRV (2 ^ (kk + 2) - 1)) (Subalgebra.one_mem _)
      -- Step 3: `B = R - γ·W`
      have hBV : ∀ j, B.coeff j ∈ V := by
        intro j
        have hkey : B.coeff j = (C (α 0) * W + B).coeff j - α 0 * W.coeff j := by
          rw [coeff_add, coeff_C_mul]
          ring
        rw [hkey]
        exact Subalgebra.sub_mem _ (hRV j) (Subalgebra.mul_mem _ hγ (hWV j))
      -- recurse into the two children and dispatch the parameter index
      have hWrec := ih (kk + 2) (by omega)
        (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
        (fun j => α (1 + j)) V hKV hWV
      have hBrec := ih (kk + 2) (by omega)
        (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
        (fun j => α (2 ^ (kk + 2) + j)) V hKV hBV
      intro t ht
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · subst ht0; exact hγ
      rcases Nat.lt_or_ge t (2 ^ (kk + 2)) with htW | htB
      · have h : α (1 + (t - 1)) ∈ V := hWrec (t - 1) (by omega)
        rwa [show 1 + (t - 1) = t from by omega] at h
      · have hup : (2:ℕ) ^ (kk + 3) = 2 ^ (kk + 2) + 2 ^ (kk + 2) := by ring
        have h : α (2 ^ (kk + 2) + (t - 2 ^ (kk + 2))) ∈ V :=
          hBrec (t - 2 ^ (kk + 2)) (by omega)
        rwa [show 2 ^ (kk + 2) + (t - 2 ^ (kk + 2)) = t from by omega] at h

/-- Encode-side coefficient membership (mirror of `mers_coeff_mem`): all
coefficients of the peeled gadget lie in any subalgebra containing the power
coefficients and the parameters. -/
theorem peel_coeff_mem {K : Subalgebra R A} (Hp : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k → ∀ j, (Hp i).coeff j ∈ K) → 1 ≤ k →
      ∀ α : ℕ → A, ∀ V : Subalgebra R A, K ≤ V →
      (∀ t, t < 2 ^ k - 1 → α t ∈ V) →
      ∀ j, (peel Hp k α).coeff j ∈ V := by
  have hXC : ∀ (V : Subalgebra R A) (a : A), a ∈ V →
      ∀ j, ((X : A[X]) + C a).coeff j ∈ V := by
    intro V a ha j
    rw [coeff_add, coeff_X, coeff_C]
    refine Subalgebra.add_mem _ ?_ ?_
    · split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · split
      · exact ha
      · exact Subalgebra.zero_mem _
  have hCmem : ∀ (V : Subalgebra R A) (a : A), a ∈ V → ∀ j, (C a : A[X]).coeff j ∈ V := by
    intro V a ha j
    rw [coeff_C]
    split
    · exact ha
    · exact Subalgebra.zero_mem _
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α V hKV hα j
    match k with
    | 0 => exact absurd hk (by omega)
    | 1 => exact hXC V (α 0) (hα 0 (by norm_num)) j
    | 2 =>
      show ((X + C (α 2)) * (Hp 1 + C (α 1)) + C (α 0)).coeff j ∈ V
      rw [coeff_add]
      refine Subalgebra.add_mem _ ?_ (hCmem V (α 0) (hα 0 (by norm_num)) j)
      refine coeff_mul_mem V (hXC V (α 2) (hα 2 (by norm_num))) ?_ j
      intro j'
      rw [coeff_add]
      exact Subalgebra.add_mem _ (hKV (hHp 1 (by omega) (by omega) j'))
        (hCmem V (α 1) (hα 1 (by norm_num)) j')
    | kk + 3 =>
      have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
      have hup : (2:ℕ) ^ (kk + 3) = 2 ^ (kk + 2) + 2 ^ (kk + 2) := by ring
      have hW := ih (kk + 2) (by omega)
        (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
        (fun t => α (1 + t)) V hKV
        (fun t ht => hα (1 + t) (by omega))
      have hB := ih (kk + 2) (by omega)
        (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
        (fun t => α (2 ^ (kk + 2) + t)) V hKV
        (fun t ht => hα (2 ^ (kk + 2) + t) (by omega))
      rw [peel_unfold, coeff_add]
      refine Subalgebra.add_mem _ ?_ (hB j)
      refine coeff_mul_mem V ?_ hW j
      intro j'
      rw [coeff_add]
      exact Subalgebra.add_mem _ (hKV (hHp (kk + 2) (by omega) (by omega) j'))
        (hCmem V (α 0) (hα 0 (by omega)) j')

end FastPoly
