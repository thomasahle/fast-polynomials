import FastPoly.Section4.FillCert
import FastPoly.Section4.KnownPowers
import FastPoly.Section4.Unitriangular

/-!
# `lem:Q-unitriangular`, general case

`mersSlot k α` is the row-to-parameter map of `Q_{2^k-1}`'s unit-pivot certificate
(fuel-indexed, mirroring `mersF`); `mers_unitriangular` assembles `sp_cert`,
`fillChain_cert`, and `head_step` by strong induction on `k`.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Fuel-indexed slot function of the Mersenne certificate, mirroring `mersF`:
the row `r` pivot of `Q_{2^k-1}` is `mersSlotF f k α r`. -/
noncomputable def mersSlotF : ℕ → ℕ → (ℕ → A) → ℕ → A
  | 0, _, α, r => α r
  | f + 1, k, α, r =>
    match k with
    | 0 => α r
    | 1 => α r
    | 2 => α r
    | 3 => headSlot 2 4 (fun g => if g = 0 then α 6 else α 5)
        (α 0) (α 1) (α 2) (α 3) (α 4) r
    | (kk + 4) =>
      headSlot (2 ^ (kk + 4) - 6) (2 ^ (kk + 4) - 4)
        (chainSlot
          (fun i => mersSlotF f (i - 1) (fun j => α (doff (kk + 4) i + 2 + j)))
          (fun i => mersSlotF f i
            (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)))
          (fun i => α (doff (kk + 4) i))
          (fun i => α (doff (kk + 4) i + 1))
          (kk + 2) (2 ^ (kk + 3))
          (spSlot (2 ^ (kk + 2)) (α 5) (mersSlotF f (kk + 2) (fun j => α (6 + j)))))
        (α 0) (α 1) (α 2) (α 3) (α 4) r

/-- The slot function of `Q_{2^k-1}`'s certificate. -/
noncomputable def mersSlot (k : ℕ) (α : ℕ → A) : ℕ → A := mersSlotF k k α

/-- `chainSlot` only reads the per-level data at levels `2 ≤ i ≤ l`. -/
theorem chainSlot_congr {Bq Bqh Bq' Bqh' : ℕ → ℕ → A} {bs ahs : ℕ → A} :
    ∀ l n (β : ℕ → A), (∀ i, 2 ≤ i → i ≤ l → Bq i = Bq' i ∧ Bqh i = Bqh' i) →
      chainSlot Bq Bqh bs ahs l n β = chainSlot Bq' Bqh' bs ahs l n β := by
  intro l
  induction l with
  | zero => intro n β h; rfl
  | succ i ih =>
    match i with
    | 0 => intro n β h; rfl
    | i + 1 =>
      intro n β h
      show chainSlot Bq Bqh bs ahs (i + 1) (n + 2 ^ (i + 2)) _
        = chainSlot Bq' Bqh' bs ahs (i + 1) (n + 2 ^ (i + 2)) _
      obtain ⟨hq, hqh⟩ := h (i + 2) (by omega) le_rfl
      rw [hq, hqh]
      exact ih (n + 2 ^ (i + 2)) _ (fun i' h2 hle => h i' h2 (by omega))

/-- Fuel irrelevance for the slot function: any fuel at least `k` computes the same. -/
theorem mersSlotF_fuel :
    ∀ k f f', k ≤ f → k ≤ f' → ∀ (α : ℕ → A) (r : ℕ),
      mersSlotF f k α r = mersSlotF f' k α r := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f f' hf hf' α r
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
        have hsp : mersSlotF f (kk + 2) (fun j => α (6 + j))
            = mersSlotF f' (kk + 2) (fun j => α (6 + j)) := by
          funext j
          exact ih (kk + 2) (by omega) f f' (by omega) (by omega) _ j
        have hchain : chainSlot (A := A)
            (fun i => mersSlotF f (i - 1) (fun j => α (doff (kk + 4) i + 2 + j)))
            (fun i => mersSlotF f i
              (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)))
            (fun i => α (doff (kk + 4) i)) (fun i => α (doff (kk + 4) i + 1))
            (kk + 2) (2 ^ (kk + 3))
            (spSlot (2 ^ (kk + 2)) (α 5) (mersSlotF f (kk + 2) (fun j => α (6 + j))))
            = chainSlot
            (fun i => mersSlotF f' (i - 1) (fun j => α (doff (kk + 4) i + 2 + j)))
            (fun i => mersSlotF f' i
              (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)))
            (fun i => α (doff (kk + 4) i)) (fun i => α (doff (kk + 4) i + 1))
            (kk + 2) (2 ^ (kk + 3))
            (spSlot (2 ^ (kk + 2)) (α 5)
              (mersSlotF f' (kk + 2) (fun j => α (6 + j)))) := by
          rw [hsp]
          refine chainSlot_congr (kk + 2) (2 ^ (kk + 3)) _ (fun i h2 hle => ⟨?_, ?_⟩)
          · funext j
            exact ih (i - 1) (by omega) f f' (by omega) (by omega) _ j
          · funext j
            exact ih i (by omega) f f' (by omega) (by omega) _ j
        exact congrArg (fun s => headSlot (2 ^ (kk + 4) - 6) (2 ^ (kk + 4) - 4) s
          (α 0) (α 1) (α 2) (α 3) (α 4) r) hchain

section main

variable [Nontrivial A]

/-- **`lem:Q-unitriangular`**: the Mersenne gadget `Q_{2^k-1}` is coefficient-triangular
with unit slopes; row `r`'s pivot parameter is `mersSlot k α r` (the band permutation of
the `α`-slots). -/
theorem mers_unitriangular {K : Subalgebra R A} (Hp : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
        (∀ j, (Hp i).coeff j ∈ K)) →
      1 ≤ k → ∀ α : ℕ → A,
      CoeffTriangular K (mersSlot k α) (fun _ => (1 : R)) (2 ^ k - 1)
        0 (mers Hp k α - X ^ (2 ^ k - 1)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α
    match k with
    | 1 =>
      have h1 : mers Hp 1 α - X ^ (2 ^ 1 - 1) = C (α 0) := by
        show (X + C (α 0)) - X ^ (2 ^ 1 - 1) = C (α 0)
        norm_num
      rw [h1, show mersSlot (A := A) 1 α = α from funext fun r => rfl]
      refine
        { unit := fun j hj => isUnit_one
          supp₁ := fun j => by rw [coeff_zero]; exact Subalgebra.zero_mem _
          supp₂ := ?_
          pivot := ?_ }
      · intro j
        rw [coeff_C]
        split
        · rename_i hj0
          subst hj0
          exact (le_sup_right : adjoin R _ ≤ _)
            (subset_adjoin ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩)
        · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
      · intro j hj
        match j, hj with
        | 0, _ =>
          refine ⟨0, (le_sup_left : K ≤ _) (Subalgebra.zero_mem _), ?_⟩
          rw [coeff_combined_zero, coeff_C_zero, map_one, one_mul, add_zero]
    | 2 =>
      obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
      have hs2 : mersSlot (A := A) 2 α = α := funext fun r => rfl
      rw [show (2 : ℕ) ^ 2 - 1 = 3 from by norm_num, hs2]
      exact mers_two_unitriangular Hp h1m h1d h1K α
    | 3 =>
      obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
      obtain ⟨hs₁m, hs₁d⟩ := monic_add_C h2m (by omega) (α 5)
      obtain ⟨hs₂m, hs₂d⟩ := monic_add_C h2m (by omega) (α 6)
      exact head_step (b₀ := α 0) (b₁ := α 1) (b₂ := α 2) (c₀ := α 3) (c₁ := α 4)
        h1m h1d h1K hs₁m (hs₁d.trans h2d) hs₂m (hs₂d.trans h2d)
        (mers_three_inner Hp h2K α) (by omega) (by omega)
    | (kk + 4) =>
      -- power facts
      have hp3 : (2 : ℕ) ^ (kk + 3) = 2 ^ (kk + 2) * 2 := pow_succ 2 (kk + 2)
      have hp4 : (2 : ℕ) ^ (kk + 4) = 2 ^ (kk + 3) * 2 := pow_succ 2 (kk + 3)
      have h33 : (2 : ℕ) ^ (kk + 2 + 1) = 2 ^ (kk + 3) := rfl
      have h2lb : (2 : ℕ) ^ 2 ≤ 2 ^ (kk + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2e : (2 : ℕ) ^ 2 = 4 := by norm_num
      -- tower facts
      have hHp' : ∀ i, 1 ≤ i → i < kk + 4 →
          (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i :=
        fun i h1 h2 => ⟨(hHp i h1 h2).1, (hHp i h1 h2).2.1⟩
      obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨hkm, hkd, hkK⟩ := hHp (kk + 3) (by omega) (by omega)
      -- the inner mers of the SP pair, with fuel-normalized slots
      have hinner := ih (kk + 2) (by omega)
        (fun i h1 h2 => hHp i h1 (by omega)) (by omega) (fun j => α (6 + j))
      have hfin : mersSlotF (A := A) (kk + 3) (kk + 2) (fun j => α (6 + j))
          = mersSlot (kk + 2) (fun j => α (6 + j)) :=
        funext fun r => mersSlotF_fuel (kk + 2) (kk + 3) (kk + 2) (by omega) le_rfl _ r
      rw [← hfin] at hinner
      obtain ⟨hinm, hind⟩ := mers_monic Hp (kk + 2)
        (fun i h1 h2 => hHp' i h1 (by omega)) (by omega) (fun j => α (6 + j))
      -- SP certificate
      have hsp := sp_cert (δ := α 5) (m := 2 ^ (kk + 3)) (e := 2 ^ (kk + 2))
        hkK hind hinner hinm (by omega) (by omega)
      -- SP monicity
      have haddlow : ∀ (P Q : A[X]), P.Monic → Q.natDegree < P.natDegree →
          ((P + Q).Monic ∧ (P + Q).natDegree = P.natDegree) := by
        intro P Q hP hlt
        have hdeg : Q.degree < P.degree := by
          rcases eq_or_ne Q 0 with rfl | hne
          · rw [degree_zero, degree_eq_natDegree hP.ne_zero]
            exact WithBot.bot_lt_coe _
          · rw [degree_eq_natDegree hne, degree_eq_natDegree hP.ne_zero]
            exact_mod_cast hlt
        exact ⟨hP.add_of_left hdeg,
          natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hdeg)⟩
      obtain ⟨hsp1m, hsp1d⟩ := haddlow (Hp (kk + 3))
        (mers Hp (kk + 2) (fun j => α (6 + j))) hkm (by omega)
      obtain ⟨hsp2m, hsp2d⟩ := monic_add_C hkm (by omega) (α 5)
      -- chain data
      have hdata : ∀ i, 2 ≤ i → i ≤ kk + 2 →
          (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ K) ∧
          (mersD Hp (mers Hp) (kk + 4) α i).q.Monic ∧
          (mersD Hp (mers Hp) (kk + 4) α i).q.natDegree = 2 ^ (i - 1) - 1 ∧
          (mersD Hp (mers Hp) (kk + 4) α i).qh.Monic ∧
          (mersD Hp (mers Hp) (kk + 4) α i).qh.natDegree = 2 ^ i - 1 ∧
          CoeffTriangular K
            (mersSlotF (kk + 3) (i - 1) (fun j => α (doff (kk + 4) i + 2 + j)))
            (fun _ => (1 : R)) (2 ^ (i - 1) - 1) 0
            ((mersD Hp (mers Hp) (kk + 4) α i).q - X ^ (2 ^ (i - 1) - 1)) ∧
          CoeffTriangular K
            (mersSlotF (kk + 3) i
              (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)))
            (fun _ => (1 : R)) (2 ^ i - 1) 0
            ((mersD Hp (mers Hp) (kk + 4) α i).qh - X ^ (2 ^ i - 1)) := by
        intro i h2 hle
        obtain ⟨him, hid, hiK⟩ := hHp i (by omega) (by omega)
        obtain ⟨hqm, hqd⟩ := mers_monic Hp (i - 1)
          (fun i' h1 h2 => hHp' i' h1 (by omega)) (by omega)
          (fun j => α (doff (kk + 4) i + 2 + j))
        obtain ⟨hqhm, hqhd⟩ := mers_monic Hp i
          (fun i' h1 h2 => hHp' i' h1 (by omega)) (by omega)
          (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j))
        have hbq : mersSlotF (A := A) (kk + 3) (i - 1)
            (fun j => α (doff (kk + 4) i + 2 + j))
            = mersSlot (i - 1) (fun j => α (doff (kk + 4) i + 2 + j)) :=
          funext fun r => mersSlotF_fuel (i - 1) (kk + 3) (i - 1) (by omega) le_rfl _ r
        have hbqh : mersSlotF (A := A) (kk + 3) i
            (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j))
            = mersSlot i (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)) :=
          funext fun r => mersSlotF_fuel i (kk + 3) i (by omega) le_rfl _ r
        refine ⟨him, hid, hiK, hqm, hqd, hqhm, hqhd, ?_, ?_⟩
        · rw [hbq]
          exact ih (i - 1) (by omega) (fun i' h1 h2 => hHp i' h1 (by omega))
            (by omega) _
        · rw [hbqh]
          exact ih i (by omega) (fun i' h1 h2 => hHp i' h1 (by omega)) (by omega) _
      -- dead tail of the SP certificate
      have hdead : ∀ r, 2 ^ (kk + 3) - 2 ^ (kk + 2) ≤ r → r < 2 ^ (kk + 3) - 2 →
          spSlot (2 ^ (kk + 2)) (α 5)
            (mersSlotF (kk + 3) (kk + 2) (fun j => α (6 + j))) r = 0 := by
        intro r h1 h2
        exact spSlot_tail _ _ _ r (by omega) (by omega)
      -- the chain certificate
      have hchain := fillChain_cert Hp (mersD Hp (mers Hp) (kk + 4) α)
        (fun i => mersSlotF (kk + 3) (i - 1) (fun j => α (doff (kk + 4) i + 2 + j)))
        (fun i => mersSlotF (kk + 3) i
          (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)))
        (kk + 2)
        (Hp (kk + 3) + mers Hp (kk + 2) (fun j => α (6 + j)),
          Hp (kk + 3) + C (α 5))
        (2 ^ (kk + 3))
        (spSlot (2 ^ (kk + 2)) (α 5)
          (mersSlotF (kk + 3) (kk + 2) (fun j => α (6 + j))))
        hsp1m (hsp1d.trans hkd) hsp2m (hsp2d.trans hkd)
        hsp hdead (by omega) hdata
      -- degree bookkeeping into head form
      have heq2 : 2 ^ (kk + 3) + (2 ^ (kk + 2 + 1) - 4) = 2 ^ (kk + 4) - 4 := by
        omega
      rw [heq2] at hchain
      have heq3 : 2 ^ (kk + 4) - 4 - 2 = 2 ^ (kk + 4) - 6 := by omega
      rw [heq3] at hchain
      -- chain output monic/degrees
      obtain ⟨⟨hc1m, hc1d⟩, ⟨hc2m, hc2d⟩⟩ := fillChain_monic (H := Hp)
        (D := mersD Hp (mers Hp) (kk + 4) α) (kk + 2)
        (Hp (kk + 3) + mers Hp (kk + 2) (fun j => α (6 + j)), Hp (kk + 3) + C (α 5))
        (2 ^ (kk + 3)) hsp1m (hsp1d.trans hkd) hsp2m (hsp2d.trans hkd)
        (fun i h2 hle => by
          obtain ⟨him, hid, hiK, hqm, hqd, hqhm, hqhd, _, _⟩ := hdata i h2 hle
          have h2i : (2 : ℕ) ^ (i - 1) ≤ 2 ^ i :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have h1i : 1 ≤ (2 : ℕ) ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
          have h1i' : 1 ≤ (2 : ℕ) ^ i := Nat.one_le_pow _ _ (by omega)
          exact ⟨him, hid, by omega, by omega⟩)
      rw [heq2] at hc1d hc2d
      -- head assembly
      have h16 : (2 : ℕ) ^ 4 ≤ 2 ^ (kk + 4) := Nat.pow_le_pow_right (by omega) (by omega)
      have h16e : (2 : ℕ) ^ 4 = 16 := by norm_num
      have hhead := head_step (b₀ := α 0) (b₁ := α 1) (b₂ := α 2) (c₀ := α 3)
        (c₁ := α 4) h1m h1d h1K hc1m hc1d hc2m hc2d hchain (by omega) (by omega)
      have heq4 : 2 ^ (kk + 4) - 4 + 3 = 2 ^ (kk + 4) - 1 := by omega
      rw [heq4] at hhead
      rw [mers_unfold Hp kk α]
      exact hhead

end main

end FastPoly
