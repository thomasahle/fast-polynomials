import FastPoly.Cost.MersennePeephole

/-!
# Decoder for the scalar-head Mersenne family

`Cost.MersennePeephole.value` is the manuscript's optimized `Q_{2^k-1}`: identical to
the uniform `mers` except that the level-two fill uses the scalar head `H₄ + β₃` in
place of `H₄ + (x + β₃)`.  This file supplies its Section-4 side: fuel irrelevance,
monicity/degree, and the decoder (`value_correct`), adapting `mers_correct` only at
level two, where the head pair `(H₄ + C β₃, H₄ + C β₄)` is compatible by the scalar
shifts `compatiblePair_shifts` and the scalar `β₃` is read off directly.
-/

namespace FastPoly.Cost.MersennePeephole

open Polynomial Algebra FastPoly

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Fuel irrelevance for the optimized family. -/
theorem valueF_fuel (powers : ℕ → A[X]) :
    ∀ k, ∀ f f', k ≤ f → k ≤ f' → ∀ α : ℕ → A,
      valueF powers f k α = valueF powers f' k α := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f f' hf hf' α
    match k, f, f' with
    | 0, 0, 0 => rfl
    | 0, 0, _ + 1 => rfl
    | 0, _ + 1, 0 => rfl
    | 0, _ + 1, _ + 1 => rfl
    | k + 1, f + 1, f' + 1 =>
      match k with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | (kk + 3) =>
        show valueF powers (f + 1) (kk + 4) α = valueF powers (f' + 1) (kk + 4) α
        rw [valueF_succ_four, valueF_succ_four]
        have hSP : valueF powers f (kk + 2) (fun j => α (6 + j))
            = valueF powers f' (kk + 2) (fun j => α (6 + j)) :=
          ih (kk + 2) (by omega) f f' (by omega) (by omega) _
        have hchain : fillChain powers
              (fillDataValue powers (valueF powers f) (kk + 4) α) (kk + 2)
              (powers (kk + 3) + valueF powers f (kk + 2) (fun j => α (6 + j)),
               powers (kk + 3) + C (α 5))
            = fillChain powers
              (fillDataValue powers (valueF powers f') (kk + 4) α) (kk + 2)
              (powers (kk + 3) + valueF powers f' (kk + 2) (fun j => α (6 + j)),
               powers (kk + 3) + C (α 5)) := by
          rw [hSP]
          exact fillChain_congr powers (kk + 2) _ (fun i h2 hi => by
            show fillDataValue powers (valueF powers f) (kk + 4) α i
              = fillDataValue powers (valueF powers f') (kk + 4) α i
            unfold fillDataValue
            rcases eq_or_ne i 2 with rfl | hne
            · rw [if_pos rfl, if_pos rfl]
              unfold scalarHeadDataValue
              rw [show valueF powers f 2 = valueF powers f' 2 from
                funext fun β => ih 2 (by omega) f f' (by omega) (by omega) β]
            · rw [if_neg hne, if_neg hne]
              unfold FastPoly.mersD
              rw [show valueF powers f (i - 1) = valueF powers f' (i - 1) from
                  funext fun β => ih (i - 1) (by omega) f f' (by omega) (by omega) β,
                show valueF powers f i = valueF powers f' i from
                  funext fun β => ih i (by omega) f f' (by omega) (by omega) β])
        simp only [fillPairValue]
        rw [hchain]

/-- Unfolding at `k = kk + 4`, recursive occurrences through `value` itself. -/
theorem value_unfold (powers : ℕ → A[X]) (kk : ℕ) (α : ℕ → A) :
    value powers (kk + 4) α
      = (X + C (α 0)) * ((powers 1 + C (α 1)) *
          (fillChain powers (fillDataValue powers (value powers) (kk + 4) α)
            (kk + 2)
            (powers (kk + 3) + value powers (kk + 2) (fun j => α (6 + j)),
             powers (kk + 3) + C (α 5))).1 + C (α 4))
        + ((powers 1 + C (α 2)) *
          (fillChain powers (fillDataValue powers (value powers) (kk + 4) α)
            (kk + 2)
            (powers (kk + 3) + value powers (kk + 2) (fun j => α (6 + j)),
             powers (kk + 3) + C (α 5))).2 + C (α 3)) := by
  show valueF powers (kk + 3 + 1) (kk + 4) α = _
  rw [valueF_succ_four]
  have hSP : valueF powers (kk + 3) (kk + 2) (fun j => α (6 + j))
      = value powers (kk + 2) (fun j => α (6 + j)) :=
    valueF_fuel powers (kk + 2) (kk + 3) (kk + 2) (by omega) (by omega) _
  have hdata : ∀ i, 2 ≤ i → i ≤ kk + 2 →
      fillDataValue powers (valueF powers (kk + 3)) (kk + 4) α i
        = fillDataValue powers (value powers) (kk + 4) α i := by
    intro i h2 hi
    unfold fillDataValue
    rcases eq_or_ne i 2 with rfl | hne
    · rw [if_pos rfl, if_pos rfl]
      unfold scalarHeadDataValue
      rw [show valueF powers (kk + 3) 2 = valueF powers 2 2 from
        funext fun β => valueF_fuel powers 2 (kk + 3) 2 (by omega) (by omega) β]
      rfl
    · rw [if_neg hne, if_neg hne]
      unfold FastPoly.mersD
      rw [show valueF powers (kk + 3) (i - 1) = valueF powers (i - 1) (i - 1) from
          funext fun β =>
            valueF_fuel powers (i - 1) (kk + 3) (i - 1) (by omega) (by omega) β,
        show valueF powers (kk + 3) i = valueF powers i i from
          funext fun β => valueF_fuel powers i (kk + 3) i (by omega) (by omega) β]
      rfl
  simp only [fillPairValue]
  rw [hSP, fillChain_congr powers (kk + 2) _ hdata]

/-- The optimized family agrees with the uniform one below degree sixteen. -/
theorem value_eq_mers_of_le_three (powers : ℕ → A[X]) (k : ℕ) (hk : k ≤ 3)
    (α : ℕ → A) : value powers k α = mers powers k α := by
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- Monicity and degree of the optimized family. -/
theorem value_monic [Nontrivial A] (powers : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k → (powers i).Monic ∧ (powers i).natDegree = 2 ^ i) →
      1 ≤ k → ∀ α : ℕ → A,
      (value powers k α).Monic ∧ (value powers k α).natDegree = 2 ^ k - 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · rw [value_eq_mers_of_le_three powers k (by omega) α]
      exact mers_monic powers k hHp hk α
    · obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 4 := ⟨k - 4, by omega⟩
      rw [value_unfold]
      obtain ⟨h1m, h1d⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨h3m, h3d⟩ := hHp (kk + 3) (by omega) (by omega)
      obtain ⟨-, hqd⟩ := ih (kk + 2) (by omega)
        (fun i' h1 hik => hHp i' h1 (by omega)) (by omega) (fun j => α (6 + j))
      obtain ⟨hSP₁m, hSP₁d⟩ := monic_add_low
        (e := value powers (kk + 2) (fun j => α (6 + j))) h3m (Or.inr (by
          rw [hqd, h3d]
          have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
          have hle : (2:ℕ) ^ (kk + 2) ≤ 2 ^ (kk + 3) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          omega))
      obtain ⟨hSP₂m, hSP₂d⟩ := monic_add_low (e := C (α 5)) h3m (Or.inr (by
        rw [natDegree_C, h3d]
        exact Nat.one_le_pow _ _ (by omega)))
      rw [h3d] at hSP₁d hSP₂d
      have hlev : ∀ i, 2 ≤ i → i ≤ kk + 2 → (powers i).Monic ∧
          (powers i).natDegree = 2 ^ i ∧
          (fillDataValue powers (value powers) (kk + 4) α i).q.natDegree < 2 ^ i ∧
          (fillDataValue powers (value powers) (kk + 4) α i).qh.natDegree
            < 2 ^ i := by
        intro i h2 hi
        obtain ⟨him, hid⟩ := hHp i (by omega) (by omega)
        refine ⟨him, hid, ?_, ?_⟩
        · rcases eq_or_ne i 2 with rfl | hne
          · show (fillDataValue powers (value powers) (kk + 4) α 2).q.natDegree
              < 2 ^ 2
            rw [show (fillDataValue powers (value powers) (kk + 4) α 2).q
                = C (α (doff (kk + 4) 2 + 2)) from rfl]
            rw [natDegree_C]
            norm_num
          · obtain ⟨-, hqd'⟩ := ih (i - 1) (by omega)
              (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
              (fun j => α (doff (kk + 4) i + 2 + j))
            show (fillDataValue powers (value powers) (kk + 4) α i).q.natDegree
              < 2 ^ i
            rw [show (fillDataValue powers (value powers) (kk + 4) α i).q
                = value powers (i - 1)
                  (fun j => α (doff (kk + 4) i + 2 + j)) from by
              unfold fillDataValue
              rw [if_neg hne]
              rfl]
            rw [hqd']
            have h1p : (1:ℕ) ≤ 2 ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
            have hle : (2:ℕ) ^ (i - 1) ≤ 2 ^ i :=
              Nat.pow_le_pow_right (by omega) (by omega)
            omega
        · rcases eq_or_ne i 2 with rfl | hne
          · obtain ⟨-, hqhd'⟩ := ih 2 (by omega)
              (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
              (fun j => α (doff (kk + 4) 2 + 3 + j))
            show (fillDataValue powers (value powers) (kk + 4) α 2).qh.natDegree
              < 2 ^ 2
            rw [show (fillDataValue powers (value powers) (kk + 4) α 2).qh
                = value powers 2
                  (fun j => α (doff (kk + 4) 2 + 3 + j)) from rfl]
            rw [hqhd']
            norm_num
          · obtain ⟨-, hqhd'⟩ := ih i (by omega)
              (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
              (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j))
            show (fillDataValue powers (value powers) (kk + 4) α i).qh.natDegree
              < 2 ^ i
            rw [show (fillDataValue powers (value powers) (kk + 4) α i).qh
                = value powers i
                  (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)) from by
              unfold fillDataValue
              rw [if_neg hne]
              rfl]
            rw [hqhd']
            have h1p : (1:ℕ) ≤ 2 ^ i := Nat.one_le_pow _ _ (by omega)
            omega
      obtain ⟨⟨hc₁m, hc₁d⟩, ⟨hc₂m, hc₂d⟩⟩ := fillChain_monic (kk + 2)
        (powers (kk + 3) + value powers (kk + 2) (fun j => α (6 + j)),
          powers (kk + 3) + C (α 5))
        (2 ^ (kk + 3)) hSP₁m hSP₁d hSP₂m hSP₂d hlev
      obtain ⟨hPm, hPd⟩ := fill_output_monic (β₀ := α 0) (β₁ := α 1) (β₂ := α 2)
        (α₀ := α 3) (α₁ := α 4) h1m (h1d.trans (by norm_num)) hc₁m hc₁d hc₂m hc₂d
      have harith : 2 ^ (kk + 3) + (2 ^ (kk + 2 + 1) - 4) + 3 = 2 ^ (kk + 4) - 1 := by
        have h4 : (4:ℕ) ≤ 2 ^ (kk + 3) := by
          calc (4:ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (kk + 3) := Nat.pow_le_pow_right (by omega) (by omega)
        have h5 : (2:ℕ) ^ (kk + 2 + 1) = 2 ^ (kk + 3) := by ring
        have h6 : (2:ℕ) ^ (kk + 4) = 2 ^ (kk + 3) + 2 ^ (kk + 3) := by ring
        omega
      exact ⟨hPm, hPd.trans harith⟩

/-- **Decodability of the scalar-head Mersenne family**: `mers_correct`, adapted only
at level two, where the head pair `(H₄ + C β₃, H₄ + C β₄)` is compatible by scalar
shifts and the scalar `β₃` is read off directly from the level datum. -/
theorem value_correct [Nontrivial A] {K : Subalgebra R A} (powers : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k →
        (powers i).Monic ∧ (powers i).natDegree = 2 ^ i ∧
          ∀ j, (powers i).coeff j ∈ K) →
      1 ≤ k → ∀ α : ℕ → A, ∀ V : Subalgebra R A, K ≤ V →
      (∀ j, (value powers k α).coeff j ∈ V) → ∀ t, t < 2 ^ k - 1 → α t ∈ V := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α V hKV hV
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · rw [value_eq_mers_of_le_three powers k (by omega) α] at hV
      exact mers_correct powers k hHp hk α V hKV hV
    · obtain ⟨kk, rfl⟩ : ∃ kk, k = kk + 4 := ⟨k - 4, by omega⟩
      obtain ⟨h1m, h1d2, h1K⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨h3m, h3d, h3K⟩ := hHp (kk + 3) (by omega) (by omega)
      obtain ⟨hQm, hQd⟩ := value_monic powers (kk + 2)
        (fun i' h1 hik => ⟨(hHp i' h1 (by omega)).1, (hHp i' h1 (by omega)).2.1⟩)
        (by omega) (fun j => α (6 + j))
      have hSpair := compatiblePair_aux_add_left h3m h3d h3K hQm hQd (by
        have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
        have hle2 : (2:ℕ) ^ (kk + 2) ≤ 2 ^ (kk + 3) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega) (α 5)
      have hgood : ∀ i, 2 ≤ i → i ≤ kk + 2 →
          GoodLevel K (powers i)
            (fillDataValue powers (value powers) (kk + 4) α i) i
            (Finset.range (2 ^ (i - 1) - 1 + 1)) := by
        intro i h2i hi
        obtain ⟨him, hid, hiK⟩ := hHp i (by omega) (by omega)
        rcases eq_or_ne i 2 with rfl | hne
        · obtain ⟨hqhm, hqhd⟩ := value_monic powers 2
            (fun i' h1 hik =>
              ⟨(hHp i' h1 (by omega)).1, (hHp i' h1 (by omega)).2.1⟩)
            (by omega) (fun j => α (doff (kk + 4) 2 + 3 + j))
          have hpair := compatiblePair_shifts (K := K) him hid (by norm_num)
            hiK (α (doff (kk + 4) 2 + 2)) (α (doff (kk + 4) 2))
          have hset : ({0, 1} : Finset ℕ) = Finset.range (2 ^ (2 - 1) - 1 + 1) := by
            decide
          refine { pair := ?_, wlt := ?_, qh_monic := hqhm, qh_deg := hqhd, HK := hiK }
          · show CompatiblePair K
              (powers 2 + (fillDataValue powers (value powers) (kk + 4) α 2).q)
              (powers 2
                + C (fillDataValue powers (value powers) (kk + 4) α 2).b)
              (2 ^ 2) (Finset.range (2 ^ (2 - 1) - 1 + 1))
            rw [show (fillDataValue powers (value powers) (kk + 4) α 2).q
                = C (α (doff (kk + 4) 2 + 2)) from rfl,
              show (fillDataValue powers (value powers) (kk + 4) α 2).b
                = α (doff (kk + 4) 2) from rfl, ← hset]
            exact hpair
          · intro j hj
            have hjr := Finset.mem_range.1 hj
            omega
        · obtain ⟨hqm, hqd'⟩ := value_monic powers (i - 1)
            (fun i' h1 hik =>
              ⟨(hHp i' h1 (by omega)).1, (hHp i' h1 (by omega)).2.1⟩)
            (by omega) (fun j => α (doff (kk + 4) i + 2 + j))
          obtain ⟨hqhm, hqhd⟩ := value_monic powers i
            (fun i' h1 hik =>
              ⟨(hHp i' h1 (by omega)).1, (hHp i' h1 (by omega)).2.1⟩)
            (by omega) (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j))
          have hdq : (fillDataValue powers (value powers) (kk + 4) α i)
              = FastPoly.mersD powers (value powers) (kk + 4) α i := by
            unfold fillDataValue
            rw [if_neg hne]
          rw [hdq]
          refine { pair := ?_, wlt := ?_, qh_monic := hqhm, qh_deg := hqhd, HK := hiK }
          · exact compatiblePair_aux_add_left him hid hiK hqm hqd' (by
              have h1p : (1:ℕ) ≤ 2 ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
              have hle2 : (2:ℕ) ^ (i - 1) ≤ 2 ^ i :=
                Nat.pow_le_pow_right (by omega) (by omega)
              omega) (α (doff (kk + 4) i))
          · intro j hj
            have hjr := Finset.mem_range.1 hj
            have h1p : (1:ℕ) ≤ 2 ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
            omega
      obtain ⟨hβ₀, hβ₁, hβ₂, hα₀', hα₁', hS₁, hS₂, hlev⟩ :=
        fill_correct (K := K)
          (S := (powers (kk + 3) + value powers (kk + 2) (fun j => α (6 + j)),
                 powers (kk + 3) + C (α 5)))
          (H := powers)
          (D := fillDataValue powers (value powers) (kk + 4) α)
          (Wh := fun i => Finset.range (2 ^ (i - 1) - 1 + 1))
          (n := 2 ^ (kk + 3)) (l := kk + 2)
          (G := Finset.range (2 ^ (kk + 2) - 1 + 1))
          (β₀ := α 0) (β₁ := α 1) (β₂ := α 2) (α₀ := α 3) (α₁ := α 4)
          (P := value powers (kk + 4) α)
          (by omega) hSpair
          (by intro i hi
              have hir := Finset.mem_range.1 hi
              have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
              have hsum : (2:ℕ) ^ (kk + 3) = 2 ^ (kk + 2) + 2 ^ (kk + 2) := by ring
              omega)
          (Nat.pow_le_pow_right (by omega) (by omega))
          hgood h1m (h1d2.trans (by norm_num)) h1K (value_unfold powers kk α)
      have hle : K ⊔ adjoin R (Set.range fun i =>
          (value powers (kk + 4) α).coeff i) ≤ V :=
        sup_adjoin_range_le hKV hV
      have hQV : ∀ j, (value powers (kk + 2) (fun j => α (6 + j))).coeff j ∈ V :=
        add_known_coeff_mem (fun j => hle (hS₁ j)) (fun j => hKV (h3K j))
      have hα5 : α 5 ∈ V := by
        have hc0 : (powers (kk + 3) + C (α 5)).coeff 0 ∈ V := hle (hS₂ 0)
        have hkey : α 5 = (powers (kk + 3) + C (α 5)).coeff 0
            - (powers (kk + 3)).coeff 0 := by
          rw [coeff_add, coeff_C_zero]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ hc0 (hKV (h3K 0))
      have hblock : ∀ t', t' < 2 ^ (kk + 2) - 1 → α (6 + t') ∈ V := by
        intro t' ht'
        exact ih (kk + 2) (by omega)
          (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
          (fun j => α (6 + j)) V hKV hQV t' ht'
      have hlevel : ∀ i, 2 ≤ i → i ≤ kk + 2 → ∀ r, r < 3 * 2 ^ (i - 1) →
          α (doff (kk + 4) i + r) ∈ V := by
        intro i h2i hi r hr
        obtain ⟨hqV, hbV, hqhV, hahV⟩ := hlev i h2i hi
        have hb : (fillDataValue powers (value powers) (kk + 4) α i).b
            = α (doff (kk + 4) i) := by
          unfold fillDataValue
          rcases eq_or_ne i 2 with rfl | hne
          · rw [if_pos rfl]
            rfl
          · rw [if_neg hne]
            rfl
        have hah : (fillDataValue powers (value powers) (kk + 4) α i).ah
            = α (doff (kk + 4) i + 1) := by
          unfold fillDataValue
          rcases eq_or_ne i 2 with rfl | hne
          · rw [if_pos rfl]
            rfl
          · rw [if_neg hne]
            rfl
        match r with
        | 0 => exact hb ▸ hle hbV
        | 1 => exact hah ▸ hle hahV
        | (r' + 2) =>
          rcases eq_or_ne i 2 with rfl | hne
          · rcases Nat.lt_or_ge r' (2 ^ (2 - 1) - 1) with hq | hq
            · have hr0 : r' = 0 := by
                have : (2:ℕ) ^ (2 - 1) - 1 = 1 := by norm_num
                omega
              subst hr0
              have hc := hle (hqV 0)
              rw [show (fillDataValue powers (value powers) (kk + 4) α 2).q
                  = C (α (doff (kk + 4) 2 + 2)) from rfl, coeff_C_zero] at hc
              have heq : doff (kk + 4) 2 + 2 = doff (kk + 4) 2 + (0 + 2) := by omega
              rw [heq] at hc
              exact hc
            · have hqhV' : ∀ j, (value powers 2
                  (fun j => α (doff (kk + 4) 2 + 3 + j))).coeff j ∈ V := by
                intro j
                have h := hle (hqhV j)
                rwa [show (fillDataValue powers (value powers) (kk + 4) α 2).qh
                    = value powers 2
                      (fun j => α (doff (kk + 4) 2 + 3 + j)) from rfl] at h
              have hmem := ih 2 (by omega)
                (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
                (fun j => α (doff (kk + 4) 2 + 3 + j)) V hKV hqhV'
                (r' - 1) (by norm_num; omega)
              have heq : doff (kk + 4) 2 + 3 + (r' - 1)
                  = doff (kk + 4) 2 + (r' + 2) := by
                have : (2:ℕ) ^ (2 - 1) - 1 = 1 := by norm_num
                omega
              rw [← heq]
              exact hmem
          · have hdq : (fillDataValue powers (value powers) (kk + 4) α i)
                = FastPoly.mersD powers (value powers) (kk + 4) α i := by
              unfold fillDataValue
              rw [if_neg hne]
            rw [hdq] at hqV hqhV
            rcases Nat.lt_or_ge r' (2 ^ (i - 1) - 1) with hq | hq
            · have hqV' : ∀ j, (value powers (i - 1)
                  (fun j => α (doff (kk + 4) i + 2 + j))).coeff j ∈ V :=
                fun j => hle (hqV j)
              have hmem := ih (i - 1) (by omega)
                (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
                (fun j => α (doff (kk + 4) i + 2 + j)) V hKV hqV' r' hq
              have heq : doff (kk + 4) i + 2 + r'
                  = doff (kk + 4) i + (r' + 2) := by omega
              rw [← heq]
              exact hmem
            · have hqhV' : ∀ j, (value powers i
                  (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j))).coeff j
                    ∈ V :=
                fun j => hle (hqhV j)
              have hsum : (2:ℕ) ^ i = 2 ^ (i - 1) + 2 ^ (i - 1) := by
                have hi1 : i - 1 + 1 = i := by omega
                calc (2:ℕ) ^ i = 2 ^ (i - 1 + 1) := by rw [hi1]
                _ = 2 ^ (i - 1) + 2 ^ (i - 1) := by ring
              have h1p : (1:ℕ) ≤ 2 ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
              have hmem := ih i (by omega)
                (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
                (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)) V hKV
                hqhV' (r' - (2 ^ (i - 1) - 1)) (by omega)
              have heq : doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1)
                  + (r' - (2 ^ (i - 1) - 1)) = doff (kk + 4) i + (r' + 2) := by
                omega
              rw [← heq]
              exact hmem
      intro t ht
      rcases Nat.lt_or_ge t 6 with h6 | h6
      · match t with
        | 0 => exact hle hβ₀
        | 1 => exact hle hβ₁
        | 2 => exact hle hβ₂
        | 3 => exact hle hα₀'
        | 4 => exact hle hα₁'
        | 5 => exact hα5
        | (s + 6) => omega
      · rcases Nat.lt_or_ge t (6 + (2 ^ (kk + 2) - 1)) with hm | hm
        · have heq : 6 + (t - 6) = t := by omega
          rw [← heq]
          exact hblock (t - 6) (by omega)
        · have h1W : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
          have hend : (2:ℕ) ^ (kk + 4) = 4 * 2 ^ (kk + 2) := by ring
          obtain ⟨i₀, hi1, him, hvle, hvlt⟩ := exists_pow_interval (kk + 2)
            ((t - (5 + 2 ^ (kk + 2))) / 3 + 2) (by omega) (by omega)
          have hdoff : doff (kk + 4) (i₀ + 1)
              = 5 + 2 ^ (kk + 2) + 3 * (2 ^ i₀ - 2) := by
            unfold doff
            rw [show kk + 4 - 2 = kk + 2 from rfl, show i₀ + 1 - 1 = i₀ from rfl]
          have hp1 : (2:ℕ) ^ (i₀ + 1) = 2 ^ i₀ + 2 ^ i₀ := by ring
          have h2i0 : (2:ℕ) ≤ 2 ^ i₀ := by
            calc (2:ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ i₀ := Nat.pow_le_pow_right (by omega) (by omega)
          have hr : t - doff (kk + 4) (i₀ + 1) < 3 * 2 ^ (i₀ + 1 - 1) := by
            rw [hdoff, show i₀ + 1 - 1 = i₀ from rfl]
            omega
          have hge : doff (kk + 4) (i₀ + 1) ≤ t := by
            rw [hdoff]
            omega
          have hmem := hlevel (i₀ + 1) (by omega) (by omega)
            (t - doff (kk + 4) (i₀ + 1)) hr
          have heq : doff (kk + 4) (i₀ + 1) + (t - doff (kk + 4) (i₀ + 1)) = t := by
            omega
          rw [← heq]
          exact hmem

end FastPoly.Cost.MersennePeephole
