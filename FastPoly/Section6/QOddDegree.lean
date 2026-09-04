import FastPoly.Section5.SlotSurj

/-!
# `lem:Q-odd-degree-with-powers`

The `Q_{2^{l+1}k + (2^l - 1)}` construction: an `A_{2^{l-1}}` fill over the even
`T_{2k,2^l}` call with a Mersenne-perturbed top power.  `q_odd_degree_decodable`
composes the fill decoder (`fill_correct`), the causal perturbed-`T` recovery
(`perturbed_Q_vis`/`perturbed_delta_vis`), the Mersenne decoder (`peel_correct`),
and the full `Rk2l` extraction (`Rk2l_extract`) to recover every parameter block
from the output coefficients and the given powers.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {Hp : ℕ → A[X]} {k l : ℕ} {α β : ℕ → A} {δ : A}

set_option maxHeartbeats 1000000 in
/-- **`lem:Q-odd-degree-with-powers`, decodability content**: every parameter block of
the `Q_{2^{l+1}k + (2^l - 1)}` construction is recovered from the output coefficients
and the given powers: the five outer fill-two parameters, the per-level fill data, the
perturbation block `β` (through the recovered `Ĥ`), the scalar shift `δ`, and the full
inner `T`-block `α`. -/
theorem q_odd_degree_decodable
    (hk : 1 ≤ k) (hl : 2 ≤ l)
    (htower : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k → IsUnit (((n : ℕ) : ℤ) : R))
    {D : ℕ → FillData A} {Wh : ℕ → Finset ℕ}
    (hgood : ∀ i, 2 ≤ i → i ≤ l - 1 → GoodLevel K (Hp i) (D i) i (Wh i))
    {β₀ β₁ β₂ α₀ α₁ : A} {P : A[X]}
    (hP : P = (X + C β₀) * ((Hp 1 + C β₁)
        * (fillChain Hp D (l - 1)
            (Tpair (Function.update Hp l (Hp l + peel Hp (l - 1) β))
              (Hp l + peel Hp (l - 1) β + C δ) (2 * k) l α)).1 + C α₁)
      + ((Hp 1 + C β₂)
          * (fillChain Hp D (l - 1)
              (Tpair (Function.update Hp l (Hp l + peel Hp (l - 1) β))
                (Hp l + peel Hp (l - 1) β + C δ) (2 * k) l α)).2 + C α₀)) :
    β₀ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    β₁ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    β₂ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    α₀ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    α₁ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    (∀ i, 2 ≤ i → i ≤ l - 1 →
      LevelMem (K ⊔ adjoin R (Set.range fun i => P.coeff i)) (D i)) ∧
    (∀ t, t < 2 ^ (l - 1) - 1 →
      β t ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i)) ∧
    δ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    (∀ t, t < (2 * k - 1) * 2 ^ l →
      α t ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i)) := by
  obtain ⟨hMm, hMd, hMK⟩ := htower l (by omega) le_rfl
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have h2 : IsUnit (2 : R) := isUnit_two_of_cast hadm (by omega)
  obtain ⟨hQm, hQd⟩ := peel_monic Hp (l - 1)
    (fun i h1 h2' => ⟨(htower i h1 (by omega)).1, (htower i h1 (by omega)).2.1⟩)
    (by omega) β
  -- the compatible pair from the perturbed call
  have hS := causal_perturbed_T (K := K) (Hp := Hp) (l := l) (M := 2 * k)
    (α := α) (Q := peel Hp (l - 1) β) (δ := δ) hl (by omega) (by omega)
    htower hQm hQd hadm
  -- the outer fill decode
  obtain ⟨hβ₀, hβ₁, hβ₂, hα₀, hα₁, hS₁, hS₂, hlev⟩ := fill_correct
    (S := (Tpair (Function.update Hp l (Hp l + peel Hp (l - 1) β))
      (Hp l + peel Hp (l - 1) β + C δ) (2 * k) l α))
    (H := Hp) (D := D) (Wh := Wh) (n := 2 * k * 2 ^ l)
    (l := l - 1) (G := Finset.range (2 * k * 2 ^ l - 2 ^ (l - 1)))
    (β₀ := β₀) (β₁ := β₁) (β₂ := β₂) (α₀ := α₀) (α₁ := α₁) (P := P)
    (by omega) hS
    (by
      intro i hi
      have h := Finset.mem_range.1 hi
      omega)
    (by
      have h := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ 2 * k from by omega)
      omega)
    hgood
    (htower 1 (by omega) (by omega)).1
    (by
      have h := (htower 1 (by omega) (by omega)).2.1
      rw [h]
      norm_num)
    (htower 1 (by omega) (by omega)).2.2
    hP
  -- the combined inner polynomial is visible
  have hΨV : ∀ i, (combined
      (Tpair (Function.update Hp l (Hp l + peel Hp (l - 1) β))
        (Hp l + peel Hp (l - 1) β + C δ) (2 * k) l α).1
      (Tpair (Function.update Hp l (Hp l + peel Hp (l - 1) β))
        (Hp l + peel Hp (l - 1) β + C δ) (2 * k) l α).2).coeff i
      ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) :=
    coeff_combined_mem hS₁ hS₂
  have hVisle : ∀ t, Vis R K (combined
      (Tpair (Function.update Hp l (Hp l + peel Hp (l - 1) β))
        (Hp l + peel Hp (l - 1) β + C δ) (2 * k) l α).1
      (Tpair (Function.update Hp l (Hp l + peel Hp (l - 1) β))
        (Hp l + peel Hp (l - 1) β + C δ) (2 * k) l α).2)
      (Finset.range (2 * k * 2 ^ l - 2 ^ (l - 1))) t
      ≤ K ⊔ adjoin R (Set.range fun i => P.coeff i) := by
    intro t
    exact Vis_le le_sup_left (fun i _ _ => hΨV i)
  -- the perturbation coefficients and the scalar shift
  have hQco : ∀ q, (peel Hp (l - 1) β).coeff q
      ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) := by
    intro q
    have h := perturbed_Q_vis (K := K) (Hp := Hp) (l := l) (M := 2 * k)
      (α := α) (Q := peel Hp (l - 1) β) (δ := δ) hl (by omega) (by omega)
      htower hQm hQd hadm q
    exact hVisle _ h
  have hβblock : ∀ t, t < 2 ^ (l - 1) - 1 →
      β t ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) := by
    intro t ht
    refine peel_correct (K := K) Hp (l - 1)
      (fun i h1 h2' => htower i h1 (by omega)) (by omega) β
      (K ⊔ adjoin R (Set.range fun i => P.coeff i)) le_sup_left hQco t ht
  have hδv : δ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) := by
    have h := perturbed_delta_vis (K := K) (Hp := Hp) (l := l) (M := 2 * k)
      (α := α) (Q := peel Hp (l - 1) β) (δ := δ) hl (by omega) (by omega)
      htower hQm hQd hadm
    exact hVisle _ h
  -- the inner `T` block through the full extraction
  have hαblock : ∀ t, t < (2 * k - 1) * 2 ^ l →
      α t ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) := by
    obtain ⟨hHhm, hHhd0⟩ := monic_add_low (e := peel Hp (l - 1) β) hMm
      (Or.inr (by rw [hQd, hMd]; omega))
    have hHhd : (Hp l + peel Hp (l - 1) β).natDegree = 2 ^ l := hHhd0.trans hMd
    have hHhV : ∀ j, (Hp l + peel Hp (l - 1) β).coeff j
        ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) := by
      intro j
      rw [coeff_add]
      exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hMK j)) (hQco j)
    obtain ⟨hHtim, hHtid0⟩ := monic_add_C hHhm (by rw [hHhd]; positivity) δ
    have hHtid : (Hp l + peel Hp (l - 1) β + C δ).natDegree = 2 ^ l :=
      hHtid0.trans hHhd
    have hHtiV : ∀ j, (Hp l + peel Hp (l - 1) β + C δ).coeff j
        ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) :=
      coeff_add_C_mem hHhV hδv
    have htowerV : ∀ i, 1 ≤ i → i ≤ l →
        ((Function.update Hp l (Hp l + peel Hp (l - 1) β)) i).Monic ∧
        ((Function.update Hp l (Hp l + peel Hp (l - 1) β)) i).natDegree = 2 ^ i ∧
        (∀ j, ((Function.update Hp l (Hp l + peel Hp (l - 1) β)) i).coeff j
          ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i)) := by
      intro i h1 hi
      rcases Nat.lt_or_ge i l with hlt | hge
      · have hne : i ≠ l := by omega
        have hupd : Function.update Hp l (Hp l + peel Hp (l - 1) β) i = Hp i := by
          rw [update_ne _ hne]
        rw [hupd]
        exact ⟨(htower i h1 (by omega)).1, (htower i h1 (by omega)).2.1,
          fun j => (le_sup_left : K ≤ _) ((htower i h1 (by omega)).2.2 j)⟩
      · have hie : i = l := by omega
        subst hie
        have hupd : Function.update Hp i (Hp i + peel Hp (i - 1) β) i
            = Hp i + peel Hp (i - 1) β := by
          rw [update_last]
        rw [hupd]
        exact ⟨hHhm, hHhd, hHhV⟩
    have hcombR := Rpair_combined_coeff_mem
      (V := K ⊔ adjoin R (Set.range fun i => P.coeff i))
      (Hp := Function.update Hp l (Hp l + peel Hp (l - 1) β))
      (Ht := Hp l + peel Hp (l - 1) β + C δ) (k := 2 * k) (l := l) (α := α)
      hS₁ hS₂ (fun j => by rw [update_last]; exact hHhV j) hHtiV
    exact Rk2l_extract (K := K ⊔ adjoin R (Set.range fun i => P.coeff i))
      (V := K ⊔ adjoin R (Set.range fun i => P.coeff i))
      (2 * k) (by omega) l α hl htowerV hHtim hHtid hHtiV
      (fun _ hodd _ => absurd (by omega : (2 * k) % 2 = 0) hodd)
      (fun n h1 h2' => hadm n h1 (by omega)) h2 le_rfl hcombR
  exact ⟨hβ₀, hβ₁, hβ₂, hα₀, hα₁, hlev, hβblock, hδv, hαblock⟩

end FastPoly
