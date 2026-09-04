import FastPoly.Recover.Combination
import FastPoly.Recover.Multiplication
import FastPoly.Recover.Power
import FastPoly.Recover.XAlpha
import FastPoly.Recover.BasePairs
import FastPoly.Polynomial.MonicDivision

/-!
# The level-1 fill construction

The `l = 1` base case of the paper's `lem:fill-correctness`:

  `A¹ = (H₂ + β₁)·S₁ + α₁`, `A² = (H₂ + β₂)·S₂ + α₀`, `P = (x + β₀)·A¹ + A²`.

Given a compatible input pair `(S₁, S₂)` of degree `n` on a window below `n - 2` and a known
monic quadratic `H₂`, all five parameters and all coefficients of `S₁, S₂` are recoverable
from the coefficients of `P` given `K`.

The proof composes, in order: `compatiblePair_shifts` × Multiplicativity,
`compatiblePair_pow_add_consts` × equal-degree Additivity, `(x+α)`-extraction, the collapsed
top window of the input pair, and monic division — exactly the paper's proof.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]

/-- **Fill correctness at level 1** (paper `lem:fill-correctness`, base case). -/
theorem fill_two_mem (K : Subalgebra R A) {S₁ S₂ H₂ : A[X]} {n : ℕ} {G : Finset ℕ}
    (hS : CompatiblePair K S₁ S₂ n G) (hGlt : ∀ i ∈ G, i < n - 2) (hn : 2 ≤ n)
    (hH : H₂.Monic) (hdH : H₂.natDegree = 2) (hHK : ∀ j, H₂.coeff j ∈ K)
    {β₀ β₁ β₂ α₀ α₁ : A} {A₁ A₂ P : A[X]}
    (hA1 : A₁ = (H₂ + C β₁) * S₁ + C α₁) (hA2 : A₂ = (H₂ + C β₂) * S₂ + C α₀)
    (hP : P = (X + C β₀) * A₁ + A₂) :
    β₀ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    β₁ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    β₂ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    α₀ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    α₁ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    (∀ j, S₁.coeff j ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i)) ∧
    (∀ j, S₂.coeff j ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i)) := by
  classical
  set VP := K ⊔ adjoin R (Set.range fun i => P.coeff i) with hVP
  have hKVP : K ≤ VP := le_sup_left
  -- Step 1: the head pair and the product pair
  have hpair2 : CompatiblePair K (H₂ + C β₁) (H₂ + C β₂) 2 ({0, 1} : Finset ℕ) :=
    compatiblePair_shifts hH hdH le_rfl hHK β₁ β₂
  have hdis₁ : Disjoint (shiftW n ({0, 1} : Finset ℕ)) (shiftW 2 G) := by
    rw [Finset.disjoint_left]
    intro a h₁ h₂
    rcases mem_shiftW.1 h₁ with ⟨i, hi, rfl⟩
    rcases mem_shiftW.1 h₂ with ⟨i', hi', hii'⟩
    have hia : i ≤ 1 := by
      rcases Finset.mem_insert.1 hi with rfl | hi
      · omega
      · rw [Finset.mem_singleton.1 hi]
    have := hGlt i' hi'
    omega
  have hmul := hpair2.mul hS hdis₁
  have hmul' : CompatiblePair K ((H₂ + C β₁) * S₁) ((H₂ + C β₂) * S₂) (n + 2)
      (shiftW n ({0, 1} : Finset ℕ) ∪ shiftW 2 G) := by
    rwa [Nat.add_comm 2 n] at hmul
  -- Step 2: add the constants pair (equal degrees, X^{n+2} correction)
  have hconsts : CompatiblePair K ((X : A[X]) ^ (n + 2) + C α₁) ((X : A[X]) ^ (n + 2) + C α₀)
      (n + 2) ({0, 1} : Finset ℕ) :=
    compatiblePair_pow_add_consts (by omega) α₁ α₀
  have hdis₂ : Disjoint (shiftW n ({0, 1} : Finset ℕ) ∪ shiftW 2 G)
      ({0, 1} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro a h₁ h₂
    have ha2 : a ≤ 1 := by
      rcases Finset.mem_insert.1 h₂ with rfl | h₂
      · omega
      · rw [Finset.mem_singleton.1 h₂]
    rcases Finset.mem_union.1 h₁ with h₁ | h₁
    · have := le_of_mem_shiftW h₁; omega
    · have := le_of_mem_shiftW h₁; omega
  have hadd := hmul'.add_of_eq hconsts hdis₂
  have hA1eq : (H₂ + C β₁) * S₁ + ((X : A[X]) ^ (n + 2) + C α₁) - X ^ (n + 2) = A₁ := by
    rw [hA1]; ring
  have hA2eq : (H₂ + C β₂) * S₂ + ((X : A[X]) ^ (n + 2) + C α₀) - X ^ (n + 2) = A₂ := by
    rw [hA2]; ring
  rw [hA1eq, hA2eq] at hadd
  -- Step 3: (x + β₀)-extraction
  set G' := shiftW n ({0, 1} : Finset ℕ) ∪ shiftW 2 G ∪ ({0, 1} : Finset ℕ) with hG'
  have hG'lt : ∀ i ∈ G', i < n + 2 := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · rcases Finset.mem_union.1 hi with hi | hi
      · rcases mem_shiftW.1 hi with ⟨i', hi', rfl⟩
        have : i' ≤ 1 := by
          rcases Finset.mem_insert.1 hi' with rfl | hi'
          · omega
          · rw [Finset.mem_singleton.1 hi']
        omega
      · rcases mem_shiftW.1 hi with ⟨i', hi', rfl⟩
        have := hGlt i' hi'
        omega
    · have : i ≤ 1 := by
        rcases Finset.mem_insert.1 hi with rfl | hi
        · omega
        · rw [Finset.mem_singleton.1 hi]
      omega
  obtain ⟨hβ₀, hA₁mem, hA₂mem⟩ := x_alpha_mem hadd (by omega) hG'lt hP
  have hβ₀VP : β₀ ∈ VP := by
    refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono ?_) K) hβ₀
    exact Set.singleton_subset_iff.2 ⟨n + 2, rfl⟩
  -- Step 4: the top coefficients of the input pair are known
  have hStop : ∀ j, n - 2 ≤ j → S₁.coeff j ∈ K ∧ S₂.coeff j ∈ K := by
    intro j hj
    constructor
    · have h1 := hS.mem₁ j
      rwa [Vis_eq_known_of_lt (fun i hi => by have := hGlt i hi; omega)] at h1
    · have h2 := hS.mem₂ j
      rwa [Vis_eq_known_of_lt (fun i hi => by have := hGlt i hi; omega)] at h2
  -- Step 5: extract β₁ and β₂ from the degree-n coefficients of A₁, A₂
  have hcoeffA : ∀ (T : A[X]) (b c : A), T.Monic → T.natDegree = n →
      ((H₂ + C b) * T + C c).coeff n
        = T.coeff (n - 2) + ((H₂.coeff 0 + b) + H₂.coeff 1 * T.coeff (n - 1)) := by
    intro T b c hT hdT
    have hmb : (H₂ + C b).Monic := (monic_add_C hH (by omega) b).1
    have hdb : (H₂ + C b).natDegree = 2 := by rw [(monic_add_C hH (by omega) b).2, hdH]
    have hsplit : ((H₂ + C b) * T + C c).coeff n = (T * (H₂ + C b)).coeff (2 + (n - 2)) := by
      rw [coeff_add, coeff_C, if_neg (by omega), add_zero, mul_comm,
        show 2 + (n - 2) = n from by omega]
    have hcm := coeff_mul_monic T (H₂ + C b) hmb (n - 2)
    rw [hdb] at hcm
    rw [hsplit, hcm, Finset.sum_range_succ, Finset.sum_range_one]
    have hc0 : (H₂ + C b).coeff 0 = H₂.coeff 0 + b := by
      rw [coeff_add, coeff_C, if_pos rfl]
    have hc1 : (H₂ + C b).coeff 1 = H₂.coeff 1 := by
      rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
    have hTn : T.coeff (2 + (n - 2) - 0) = 1 := by
      rw [show 2 + (n - 2) - 0 = n from by omega, ← hdT]
      exact hT.coeff_natDegree
    have hTn1 : 2 + (n - 2) - 1 = n - 1 := by omega
    rw [hc0, hc1, hTn, hTn1, mul_one]
  have hβ₁VP : β₁ ∈ VP := by
    have hkey : β₁ = A₁.coeff n - S₁.coeff (n - 2) - H₂.coeff 0
        - H₂.coeff 1 * S₁.coeff (n - 1) := by
      rw [hA1, hcoeffA S₁ β₁ α₁ hS.monic₁ hS.natDegree₁]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (hA₁mem n)
      (hKVP (hStop (n - 2) le_rfl).1)) (hKVP (hHK 0)))
      (Subalgebra.mul_mem _ (hKVP (hHK 1)) (hKVP (hStop (n - 1) (by omega)).1))
  have hβ₂VP : β₂ ∈ VP := by
    have hkey : β₂ = A₂.coeff n - S₂.coeff (n - 2) - H₂.coeff 0
        - H₂.coeff 1 * S₂.coeff (n - 1) := by
      rw [hA2, hcoeffA S₂ β₂ α₀ hS.monic₂ hS.natDegree₂]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (hA₂mem n)
      (hKVP (hStop (n - 2) le_rfl).2)) (hKVP (hHK 0)))
      (Subalgebra.mul_mem _ (hKVP (hHK 1)) (hKVP (hStop (n - 1) (by omega)).2))
  -- Step 6: monic division recovers the input pair and the remaining constants
  have hdiv : ∀ (T F : A[X]) (b c : A), T.Monic → T.natDegree = n → b ∈ VP →
      (∀ i, F.coeff i ∈ VP) → F = (H₂ + C b) * T + C c →
      (∀ j, T.coeff j ∈ VP) ∧ c ∈ VP := by
    intro T F b c hT hdT hbVP hFVP hF
    have hmb : (H₂ + C b).Monic := (monic_add_C hH (by omega) b).1
    have hdb : (H₂ + C b).natDegree = 2 := by rw [(monic_add_C hH (by omega) b).2, hdH]
    have hDK : ∀ j, (H₂ + C b).coeff j ∈ VP := by
      intro j
      rw [coeff_add, coeff_C]
      refine Subalgebra.add_mem _ (hKVP (hHK j)) ?_
      split
      · exact hbVP
      · exact Subalgebra.zero_mem _
    have hF' : F = T * (H₂ + C b) + C c := by rw [hF]; ring
    have hcollapse : ∀ (Sset : Set A), Sset ⊆ SetLike.coe VP →
        VP ⊔ adjoin R Sset ≤ VP := fun Sset hsub =>
      sup_le le_rfl (adjoin_le hsub)
    have hquot : ∀ j, T.coeff j ∈ VP := by
      intro j
      rcases Nat.lt_or_ge n j with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        exact Subalgebra.zero_mem _
      · have h := coeff_quot_mem VP hmb hdb (by omega) hDK
          (le_of_eq hdT) (by rw [natDegree_C]; omega) hF' j hle
        refine hcollapse _ ?_ h
        rintro _ ⟨i, _, rfl⟩
        exact hFVP i
    refine ⟨hquot, ?_⟩
    have h := coeff_rem_mem VP hmb hdb (by omega) hDK
      (le_of_eq hdT) (by rw [natDegree_C]; omega) hF' 0
    rw [coeff_C, if_pos rfl] at h
    refine hcollapse _ ?_ h
    rintro _ ⟨i, _, rfl⟩
    exact hFVP i
  obtain ⟨hS₁VP, hα₁VP⟩ := hdiv S₁ A₁ β₁ α₁ hS.monic₁ hS.natDegree₁ hβ₁VP hA₁mem hA1
  obtain ⟨hS₂VP, hα₀VP⟩ := hdiv S₂ A₂ β₂ α₀ hS.monic₂ hS.natDegree₂ hβ₂VP hA₂mem hA2
  exact ⟨hβ₀VP, hβ₁VP, hβ₂VP, hα₀VP, hα₁VP, hS₁VP, hS₂VP⟩

end FastPoly
