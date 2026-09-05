import FastPoly.Section4.Peeled
import FastPoly.Section4.FillRec
import FastPoly.Recover.Triangular
import FastPoly.Section5.Binomial

/-!
# `lem:Q-unitriangular`: unit pivots of the known-powers gadgets

The cubic base has unit pivots in coefficient order. The remaining lemmas certify
the generic fill head used by the auxiliary odd-degree gadgets. The full binary
known-powers certificate is proved in `PeeledCert.lean`.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]

/-- The `k = 2` instance of `lem:Q-unitriangular`: `Q₃ - x³` is coefficient-triangular
with unit pivots at rows `0, 1, 2` in slot order `α₀, α₁, α₂` (identity permutation). -/
theorem peel_two_unitriangular {K : Subalgebra R A} (Hp : ℕ → A[X])
    (h1m : (Hp 1).Monic) (h1d : (Hp 1).natDegree = 2)
    (h1K : ∀ j, (Hp 1).coeff j ∈ K) (α : ℕ → A) :
    CoeffTriangular K α (fun _ => (1 : R)) 3
      0 (peel Hp 2 α - X ^ 3) := by
  have hco2 : (peel Hp 2 α - X ^ 3).coeff 2 = α 2 + (Hp 1).coeff 1 := by
    show (Q₃ (Hp 1) (α 0) (α 1) (α 2) - X ^ 3).coeff 2 = _
    rw [coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero,
      Q₃_coeff_two (α 0) (α 1) (α 2) h1m h1d]
  have hco1 : (peel Hp 2 α - X ^ 3).coeff 1
      = α 1 + ((Hp 1).coeff 0 + α 2 * (Hp 1).coeff 1) := by
    show (Q₃ (Hp 1) (α 0) (α 1) (α 2) - X ^ 3).coeff 1 = _
    rw [coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero,
      Q₃_coeff_one (α 0) (α 1) (α 2)]
  have hco0 : (peel Hp 2 α - X ^ 3).coeff 0
      = α 0 + α 2 * ((Hp 1).coeff 0 + α 1) := by
    show (Q₃ (Hp 1) (α 0) (α 1) (α 2) - X ^ 3).coeff 0 = _
    rw [coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero,
      Q₃_coeff_zero (α 0) (α 1) (α 2)]
  have hmem : ∀ lo t d' : ℕ, lo ≤ t → t < d' →
      α t ∈ K ⊔ adjoin R (α '' Set.Ico lo d') := fun lo t d' hlo ht =>
    (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨hlo, ht⟩, rfl⟩)
  have hK' : ∀ a ∈ K, ∀ (s : Set A), a ∈ K ⊔ adjoin R s := fun a ha s =>
    (le_sup_left : K ≤ _) ha
  have hcomb : ∀ j, (combined (0 : A[X]) (peel Hp 2 α - X ^ 3)).coeff j
      = (peel Hp 2 α - X ^ 3).coeff j := by
    intro j
    cases j with
    | zero => rw [coeff_combined_zero]
    | succ m =>
      rw [coeff_combined, coeff_zero, zero_add]
  refine
    { unit := fun j hj => isUnit_one
      supp₁ := fun j => by
        rw [coeff_zero]
        exact Subalgebra.zero_mem _
      supp₂ := ?_
      pivot := ?_ }
  · intro j
    match j with
    | 0 =>
      rw [hco0]
      refine Subalgebra.add_mem _ (hmem _ 0 3 (by omega) (by omega)) (Subalgebra.mul_mem _
        (hmem _ 2 3 (by omega) (by omega)) (Subalgebra.add_mem _ (hK' _ (h1K 0) _)
          (hmem _ 1 3 (by omega) (by omega))))
    | 1 =>
      rw [hco1]
      refine Subalgebra.add_mem _ (hmem _ 1 3 (by omega) (by omega)) (Subalgebra.add_mem _
        (hK' _ (h1K 0) _) (Subalgebra.mul_mem _ (hmem _ 2 3 (by omega) (by omega))
          (hK' _ (h1K 1) _)))
    | 2 =>
      rw [hco2]
      exact Subalgebra.add_mem _ (hmem _ 2 3 (by omega) (by omega)) (hK' _ (h1K 1) _)
    | (m + 3) =>
      have hz : (peel Hp 2 α - X ^ 3).coeff (m + 3) = 0 := by
        have hm := peel_monic Hp 2 (fun i' hi1 hik => by
          have : i' = 1 := by omega
          subst this
          exact ⟨h1m, h1d.trans (by norm_num)⟩) (by omega) α
        rcases Nat.eq_zero_or_pos m with rfl | hmpos
        · rw [coeff_sub, coeff_X_pow, if_pos rfl]
          have hlead : (peel Hp 2 α).coeff 3 = 1 := by
            have h3 : (2:ℕ) ^ 2 - 1 = 3 := by norm_num
            rw [← h3, ← hm.2]
            exact hm.1.coeff_natDegree
          rw [show (0:ℕ) + 3 = 3 from rfl, hlead]
          ring
        · rw [coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero]
          refine coeff_eq_zero_of_natDegree_lt ?_
          rw [hm.2]
          have h3 : (2:ℕ) ^ 2 - 1 = 3 := by norm_num
          omega
      rw [hz]
      exact Subalgebra.zero_mem _
  · intro j hj
    match j, hj with
    | 0, _ =>
      refine ⟨α 2 * ((Hp 1).coeff 0 + α 1), ?_, ?_⟩
      · exact Subalgebra.mul_mem _ (hmem _ 2 3 (by omega) (by omega)) (Subalgebra.add_mem _
          (hK' _ (h1K 0) _) (hmem _ 1 3 (by omega) (by omega)))
      · rw [hcomb, hco0, map_one, one_mul]
    | 1, _ =>
      refine ⟨(Hp 1).coeff 0 + α 2 * (Hp 1).coeff 1, ?_, ?_⟩
      · exact Subalgebra.add_mem _ (hK' _ (h1K 0) _) (Subalgebra.mul_mem _
          (hmem _ 2 3 (by omega) (by omega)) (hK' _ (h1K 1) _))
      · rw [hcomb, hco1, map_one, one_mul]
    | 2, _ =>
      refine ⟨(Hp 1).coeff 1, hK' _ (h1K 1) _, ?_⟩
      rw [hcomb, hco2, map_one, one_mul]


section headBand

variable (H : A[X]) (S₁ S₂ : A[X]) (b₀ b₁ b₂ c₀ c₁ : A)

/-- Row 0 of the head shape `(x+b₀)((H+b₁)S₁+c₁) + ((H+b₂)S₂+c₀)`:
the constant coefficient exposes `c₀` with slope 1. -/
theorem head_coeff_zero :
    ((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀)).coeff 0
      = c₀ + (b₀ * ((H.coeff 0 + b₁) * S₁.coeff 0 + c₁)
          + (H.coeff 0 + b₂) * S₂.coeff 0) := by
  simp only [coeff_add, mul_coeff_zero, coeff_X_zero, coeff_C_zero, zero_add]
  ring

/-- Row 1 of the head shape: exposes `c₁` with slope 1 (plus terms in rows ≥ 1 data). -/
theorem head_coeff_one :
    ((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀)).coeff 1
      = c₁ + (((H.coeff 0 + b₁) * S₁.coeff 0)
          + b₀ * ((H.coeff 0 + b₁) * S₁.coeff 1 + H.coeff 1 * S₁.coeff 0)
          + ((H.coeff 0 + b₂) * S₂.coeff 1 + H.coeff 1 * S₂.coeff 0)) := by
  have hmul1 : ∀ (P Q : A[X]), (P * Q).coeff 1
      = P.coeff 0 * Q.coeff 1 + P.coeff 1 * Q.coeff 0 := by
    intro P Q
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hC1 : ∀ a : A, (C a : A[X]).coeff 1 = 0 := by
    intro a
    rw [coeff_C, if_neg (by omega)]
  simp only [coeff_add, hmul1, mul_coeff_zero, hC1, coeff_C_zero, coeff_X_zero,
    coeff_X_one, add_zero, zero_add]
  try ring

end headBand


section headTop

variable {H S₁ S₂ : A[X]} {n : ℕ} (b₀ b₁ b₂ c₀ c₁ : A)

/-- Top row `n+3` of the head shape is monic-fixed (leading term). -/
theorem head_coeff_lead (hH : H.Monic) (hdH : H.natDegree = 2)
    (hS₁ : S₁.Monic) (hd₁ : S₁.natDegree = n) (hS₂ : S₂.Monic) (hd₂ : S₂.natDegree = n) :
    ((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀)).coeff (n + 3)
      = 1 := by
  obtain ⟨hm, hd⟩ := fill_output_monic (β₀ := b₀) (β₁ := b₁) (β₂ := b₂) (α₀ := c₀)
    (α₁ := c₁) hH hdH hS₁ hd₁ hS₂ hd₂
  rw [← hd]
  exact hm.coeff_natDegree
/-- Row `n+2` of the head shape: exposes `b₀` with slope 1, corrected by the monic-fixed
`1 + [x^1]H` and the input coefficient `[x^{n-1}]S₁`. -/
theorem head_coeff_b0 (hH : H.Monic) (hdH : H.natDegree = 2)
    (hS₁ : S₁.Monic) (hd₁ : S₁.natDegree = n) (hS₂ : S₂.Monic) (hd₂ : S₂.natDegree = n)
    (hn : 1 ≤ n) :
    ((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀)).coeff (n + 2)
      = b₀ + (H.coeff 1 + S₁.coeff (n - 1) + 1) := by
  obtain ⟨hmb₁, hdb₁⟩ := monic_add_C hH (by omega) b₁
  obtain ⟨hmb₂, hdb₂⟩ := monic_add_C hH (by omega) b₂
  have hA₁m : ((H + C b₁) * S₁).Monic := hmb₁.mul hS₁
  have hA₁d : ((H + C b₁) * S₁).natDegree = n + 2 := by
    rw [hmb₁.natDegree_mul hS₁, hdb₁, hdH, hd₁]
    omega
  obtain ⟨hAm, hAd⟩ := monic_add_low (e := C c₁) hA₁m
    (Or.inr (by rw [natDegree_C, hA₁d]; omega))
  have hAd' : ((H + C b₁) * S₁ + C c₁).natDegree = n + 2 := hAd.trans hA₁d
  -- first branch at n+2 via coeff_mul_monic with p := X + C b₀
  have hcm := coeff_mul_monic (X + C b₀) ((H + C b₁) * S₁ + C c₁) hAm 0
  rw [hAd', add_zero] at hcm
  have hsum : ∑ j ∈ Finset.range (n + 2),
      ((H + C b₁) * S₁ + C c₁).coeff j * (X + C b₀).coeff (n + 2 - j)
      = ((H + C b₁) * S₁ + C c₁).coeff (n + 1) := by
    rw [Finset.sum_eq_single_of_mem (n + 1) (Finset.mem_range.2 (by omega))]
    · have hX1 : (X + C b₀ : A[X]).coeff (n + 2 - (n + 1)) = 1 := by
        rw [show n + 2 - (n + 1) = 1 from by omega, coeff_add, coeff_X_one, coeff_C,
          if_neg (by omega), add_zero]
      rw [hX1, mul_one]
    · intro j hj hne
      have hjr := Finset.mem_range.1 hj
      have hz : (X + C b₀ : A[X]).coeff (n + 2 - j) = 0 := by
        rw [coeff_add, coeff_X, if_neg (by omega), coeff_C, if_neg (by omega), add_zero]
      rw [hz, mul_zero]
  -- the subleading of the inner product
  have hsub : ((H + C b₁) * S₁).coeff (n + 1) = (H + C b₁).coeff 1 + S₁.coeff (n - 1) := by
    have hkey := monic_mul_coeff_sub_one hmb₁ hS₁ (hdb₁.trans hdH) hd₁ (by omega) hn
    have hidx : 2 + n - 1 = n + 1 := by omega
    rw [hidx] at hkey
    rw [hkey, show (2:ℕ) - 1 = 1 from rfl]
  have hb₁1 : (H + C b₁).coeff 1 = H.coeff 1 := by
    rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
  -- second branch at n+2: leading 1
  have hB : ((H + C b₂) * S₂ + C c₀).coeff (n + 2) = 1 := by
    have hBm : ((H + C b₂) * S₂).Monic := hmb₂.mul hS₂
    have hBd : ((H + C b₂) * S₂).natDegree = n + 2 := by
      rw [hmb₂.natDegree_mul hS₂, hdb₂, hdH, hd₂]
      omega
    rw [coeff_add, coeff_C, if_neg (by omega), add_zero, ← hBd]
    exact hBm.coeff_natDegree
  have hCc₁ : (C c₁ : A[X]).coeff (n + 1) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  rw [coeff_add, hcm, hsum, hB, coeff_add ((H + C b₁) * S₁) (C c₁) (n + 1),
    hCc₁, add_zero, hsub, hb₁1, coeff_add X (C b₀) 0, coeff_X_zero, coeff_C_zero]
  ring

/-- Exact `X`-shift coefficient identity (no degree hypotheses). -/
theorem x_shift_coeff (b : A) (q : A[X]) (m : ℕ) :
    ((X + C b) * q).coeff (m + 1) = q.coeff m + b * q.coeff (m + 1) := by
  rw [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]

/-- Coefficient formula for a monic degree-2 multiplier:
`[x^m]((H+b)·S₁) = (h₀+b)s_m + h₁s_{m-1} + s_{m-2}` for `m ≥ 2`. -/
theorem deg_two_mul_coeff {b : A} (hH : H.Monic) (hdH : H.natDegree = 2)
    {m : ℕ} (hm : 2 ≤ m) :
    ((H + C b) * S₁).coeff m
      = (H.coeff 0 + b) * S₁.coeff m + H.coeff 1 * S₁.coeff (m - 1)
        + S₁.coeff (m - 2) := by
  obtain ⟨hmb, hdb⟩ := monic_add_C hH (by omega) b
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsplit : Finset.range (m + 1)
      = insert 0 (insert 1 (insert 2 (Finset.Icc 3 m))) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_Icc]),
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_Icc]),
    Finset.sum_insert (by simp [Finset.mem_Icc])]
  have hrest : ∑ j ∈ Finset.Icc 3 m, (H + C b).coeff j * S₁.coeff (m - j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨h3j, hjm⟩ := Finset.mem_Icc.1 hj
    have hz : (H + C b).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hdb, hdH]; omega)
    rw [hz, zero_mul]
  have hc0 : (H + C b).coeff 0 = H.coeff 0 + b := by
    rw [coeff_add, coeff_C_zero]
  have hc1 : (H + C b).coeff 1 = H.coeff 1 := by
    rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
  have hc2 : (H + C b).coeff 2 = 1 := by
    have hl : H.coeff 2 = 1 := by
      rw [← hdH]
      exact hH.coeff_natDegree
    rw [coeff_add, hl, coeff_C, if_neg (by omega), add_zero]
  rw [hrest, add_zero, hc0, hc1, hc2, one_mul, show m - 0 = m from by omega]
  ring

/-- Row `n+1` of the head shape (`n ≥ 2`): exposes `b₁` with slope 1. -/
theorem head_coeff_b1 (hH : H.Monic) (hdH : H.natDegree = 2)
    (hS₁ : S₁.Monic) (hd₁ : S₁.natDegree = n) (hS₂ : S₂.Monic) (hd₂ : S₂.natDegree = n)
    (hn : 2 ≤ n) :
    ((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀)).coeff (n + 1)
      = b₁ + (H.coeff 0 + H.coeff 1 * S₁.coeff (n - 1) + S₁.coeff (n - 2)
          + b₀ * (H.coeff 1 + S₁.coeff (n - 1))
          + (H.coeff 1 * S₂.coeff n + S₂.coeff (n - 1))) := by
  obtain ⟨hmb₁, hdb₁⟩ := monic_add_C hH (by omega) b₁
  have hlead₁ : S₁.coeff n = 1 := by
    rw [← hd₁]
    exact hS₁.coeff_natDegree
  have hS₂hi : S₂.coeff (n + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hCc₁n : (C c₁ : A[X]).coeff n = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hCc₁n1 : (C c₁ : A[X]).coeff (n + 1) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hCc₀n1 : (C c₀ : A[X]).coeff (n + 1) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hAn : ((H + C b₁) * S₁ + C c₁).coeff n
      = (H.coeff 0 + b₁) * S₁.coeff n + H.coeff 1 * S₁.coeff (n - 1)
        + S₁.coeff (n - 2) := by
    rw [coeff_add, hCc₁n, add_zero, deg_two_mul_coeff hH hdH hn]
  have hAn1 : ((H + C b₁) * S₁ + C c₁).coeff (n + 1)
      = H.coeff 1 + S₁.coeff (n - 1) := by
    have hkey := monic_mul_coeff_sub_one hmb₁ hS₁ (hdb₁.trans hdH) hd₁ (by omega)
      (by omega)
    have hidx : 2 + n - 1 = n + 1 := by omega
    rw [hidx] at hkey
    have hb₁1 : (H + C b₁).coeff 1 = H.coeff 1 := by
      rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
    rw [coeff_add, hCc₁n1, add_zero, hkey, show (2:ℕ) - 1 = 1 from rfl, hb₁1]
  have hB : ((H + C b₂) * S₂ + C c₀).coeff (n + 1)
      = H.coeff 1 * S₂.coeff n + S₂.coeff (n - 1) := by
    rw [coeff_add, hCc₀n1, add_zero, deg_two_mul_coeff hH hdH (by omega : 2 ≤ n + 1),
      show n + 1 - 1 = n from by omega, show n + 1 - 2 = n - 1 from by omega,
      hS₂hi, mul_zero, zero_add]
  rw [coeff_add, x_shift_coeff, hAn, hAn1, hB, hlead₁]
  ring

/-- Row `n` of the head shape (`n ≥ 3`): exposes `b₂` with slope 1. -/
theorem head_coeff_b2 (hH : H.Monic) (hdH : H.natDegree = 2)
    (hS₁ : S₁.Monic) (hd₁ : S₁.natDegree = n) (hS₂ : S₂.Monic) (hd₂ : S₂.natDegree = n)
    (hn : 3 ≤ n) :
    ((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀)).coeff n
      = b₂ + ((H.coeff 0 + b₁) * S₁.coeff (n - 1) + H.coeff 1 * S₁.coeff (n - 2)
          + S₁.coeff (n - 3)
          + b₀ * (H.coeff 0 + b₁ + H.coeff 1 * S₁.coeff (n - 1) + S₁.coeff (n - 2))
          + (H.coeff 0 + H.coeff 1 * S₂.coeff (n - 1) + S₂.coeff (n - 2))) := by
  have hlead₁ : S₁.coeff n = 1 := by
    rw [← hd₁]
    exact hS₁.coeff_natDegree
  have hlead₂ : S₂.coeff n = 1 := by
    rw [← hd₂]
    exact hS₂.coeff_natDegree
  have hCc₁a : (C c₁ : A[X]).coeff (n - 1) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hCc₁b : (C c₁ : A[X]).coeff n = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hCc₀ : (C c₀ : A[X]).coeff n = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hAa : ((H + C b₁) * S₁ + C c₁).coeff (n - 1)
      = (H.coeff 0 + b₁) * S₁.coeff (n - 1) + H.coeff 1 * S₁.coeff (n - 1 - 1)
        + S₁.coeff (n - 1 - 2) := by
    rw [coeff_add, hCc₁a, add_zero, deg_two_mul_coeff hH hdH (by omega : 2 ≤ n - 1)]
  have hAb : ((H + C b₁) * S₁ + C c₁).coeff n
      = (H.coeff 0 + b₁) + H.coeff 1 * S₁.coeff (n - 1) + S₁.coeff (n - 2) := by
    rw [coeff_add, hCc₁b, add_zero, deg_two_mul_coeff hH hdH (by omega : 2 ≤ n),
      hlead₁, mul_one]
  have hB : ((H + C b₂) * S₂ + C c₀).coeff n
      = (H.coeff 0 + b₂) + H.coeff 1 * S₂.coeff (n - 1) + S₂.coeff (n - 2) := by
    rw [coeff_add, hCc₀, add_zero, deg_two_mul_coeff hH hdH (by omega : 2 ≤ n),
      hlead₂, mul_one]
  have hxs : ((X + C b₀) * ((H + C b₁) * S₁ + C c₁)).coeff n
      = ((H + C b₁) * S₁ + C c₁).coeff (n - 1)
        + b₀ * ((H + C b₁) * S₁ + C c₁).coeff n := by
    have hkey := x_shift_coeff b₀ ((H + C b₁) * S₁ + C c₁) (n - 1)
    rw [show n - 1 + 1 = n from by omega] at hkey
    exact hkey
  rw [coeff_add, hxs, hAa, hAb, hB,
    show n - 1 - 1 = n - 2 from by omega, show n - 1 - 2 = n - 3 from by omega]
  ring

/-- Middle band of the head shape (`1 ≤ g`): row `g+2` reads the inner pair's combined
coefficient at `g` with slope 1; every other term uses strictly higher inner
coefficients or the top scalars. -/
theorem head_coeff_mid (hH : H.Monic) (hdH : H.natDegree = 2) {g : ℕ} (hg : 1 ≤ g) :
    ((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀)).coeff (g + 2)
      = (S₁.coeff (g - 1) + S₂.coeff g)
        + ((H.coeff 0 + b₁) * S₁.coeff (g + 1) + H.coeff 1 * S₁.coeff g
          + b₀ * ((H.coeff 0 + b₁) * S₁.coeff (g + 2) + H.coeff 1 * S₁.coeff (g + 1)
              + S₁.coeff g)
          + ((H.coeff 0 + b₂) * S₂.coeff (g + 2) + H.coeff 1 * S₂.coeff (g + 1))) := by
  have hCc₁a : (C c₁ : A[X]).coeff (g + 1) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hCc₁b : (C c₁ : A[X]).coeff (g + 2) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hCc₀ : (C c₀ : A[X]).coeff (g + 2) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hAa : ((H + C b₁) * S₁ + C c₁).coeff (g + 1)
      = (H.coeff 0 + b₁) * S₁.coeff (g + 1) + H.coeff 1 * S₁.coeff (g + 1 - 1)
        + S₁.coeff (g + 1 - 2) := by
    rw [coeff_add, hCc₁a, add_zero, deg_two_mul_coeff hH hdH (by omega : 2 ≤ g + 1)]
  have hAb : ((H + C b₁) * S₁ + C c₁).coeff (g + 2)
      = (H.coeff 0 + b₁) * S₁.coeff (g + 2) + H.coeff 1 * S₁.coeff (g + 2 - 1)
        + S₁.coeff (g + 2 - 2) := by
    rw [coeff_add, hCc₁b, add_zero, deg_two_mul_coeff hH hdH (by omega : 2 ≤ g + 2)]
  have hB : ((H + C b₂) * S₂ + C c₀).coeff (g + 2)
      = (H.coeff 0 + b₂) * S₂.coeff (g + 2) + H.coeff 1 * S₂.coeff (g + 2 - 1)
        + S₂.coeff (g + 2 - 2) := by
    rw [coeff_add, hCc₀, add_zero, deg_two_mul_coeff hH hdH (by omega : 2 ≤ g + 2)]
  have hxs : ((X + C b₀) * ((H + C b₁) * S₁ + C c₁)).coeff (g + 2)
      = ((H + C b₁) * S₁ + C c₁).coeff (g + 1)
        + b₀ * ((H + C b₁) * S₁ + C c₁).coeff (g + 2) := by
    have hkey := x_shift_coeff b₀ ((H + C b₁) * S₁ + C c₁) (g + 1)
    rw [show g + 1 + 1 = g + 2 from by omega] at hkey
    exact hkey
  rw [coeff_add, hxs, hAa, hAb, hB,
    show g + 1 - 1 = g from by omega, show g + 1 - 2 = g - 1 from by omega,
    show g + 2 - 1 = g + 1 from by omega, show g + 2 - 2 = g from by omega]
  ring

end headTop


section headSlot

/-- The head-step local slot function: rows `0,1` are the two additive constants, rows
`g+2` (`g < e`) read the inner slots, rows `n, n+1, n+2` are the multiplier scalars.
Rows in `[e+2, n)` are `K`-known and the value is irrelevant. -/
def headSlot (e n : ℕ) (β : ℕ → A) (b₀ b₁ b₂ c₀ c₁ : A) : ℕ → A := fun j =>
  if j = 0 then c₀
  else if j = 1 then c₁
  else if j < e + 2 then β (j - 2)
  else if j = n then b₂
  else if j = n + 1 then b₁
  else if j = n + 2 then b₀
  else 0

variable {e n : ℕ} {β : ℕ → A} {b₀ b₁ b₂ c₀ c₁ : A}

/-- Row 0 reads the first additive constant. -/
theorem headSlot_zero : headSlot e n β b₀ b₁ b₂ c₀ c₁ 0 = c₀ := rfl

/-- Row 1 reads the second additive constant. -/
theorem headSlot_one : headSlot e n β b₀ b₁ b₂ c₀ c₁ 1 = c₁ := rfl

/-- Middle rows `g + 2` (`g < e`) read the inner slots. -/
theorem headSlot_mid {g : ℕ} (hg : g < e) :
    headSlot e n β b₀ b₁ b₂ c₀ c₁ (g + 2) = β g := by
  unfold headSlot
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show g + 2 - 2 = g from by omega]

/-- Row `n` reads the multiplier scalar `b₂`. -/
theorem headSlot_b2 (he : e + 2 ≤ n) : headSlot e n β b₀ b₁ b₂ c₀ c₁ n = b₂ := by
  unfold headSlot
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- Row `n + 1` reads the multiplier scalar `b₁`. -/
theorem headSlot_b1 (he : e + 2 ≤ n) : headSlot e n β b₀ b₁ b₂ c₀ c₁ (n + 1) = b₁ := by
  unfold headSlot
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl]

/-- Row `n + 2` reads the multiplier scalar `b₀`. -/
theorem headSlot_b0 (he : e + 2 ≤ n) : headSlot e n β b₀ b₁ b₂ c₀ c₁ (n + 2) = b₀ := by
  unfold headSlot
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

/-- Dead rows `g + 2` with `e ≤ g` and `g + 2 < n` hold `0`. -/
theorem headSlot_dead {g : ℕ} (hge : e ≤ g) (hlt : g + 2 < n) :
    headSlot e n β b₀ b₁ b₂ c₀ c₁ (g + 2) = 0 := by
  unfold headSlot
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end headSlot


section headStep

variable {K : Subalgebra R A} {β : ℕ → A} {e n : ℕ} {b₀ b₁ b₂ c₀ c₁ : A}

/-- Row 2 of the head shape: reads the inner second component's constant term. -/
theorem head_coeff_two (hH : H.Monic) (hdH : H.natDegree = 2) :
    ((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀)).coeff 2
      = S₂.coeff 0
        + ((H.coeff 0 + b₁) * S₁.coeff 1 + H.coeff 1 * S₁.coeff 0
          + b₀ * ((H.coeff 0 + b₁) * S₁.coeff 2 + H.coeff 1 * S₁.coeff 1 + S₁.coeff 0)
          + ((H.coeff 0 + b₂) * S₂.coeff 2 + H.coeff 1 * S₂.coeff 1)) := by
  have hmul1 : ∀ (P Q : A[X]), (P * Q).coeff 1
      = P.coeff 0 * Q.coeff 1 + P.coeff 1 * Q.coeff 0 := by
    intro P Q
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hC1 : ∀ a : A, (C a : A[X]).coeff 1 = 0 := fun a => by
    rw [coeff_C, if_neg (by omega)]
  have hC2 : ∀ a : A, (C a : A[X]).coeff 2 = 0 := fun a => by
    rw [coeff_C, if_neg (by omega)]
  have hb₁0 : (H + C b₁).coeff 0 = H.coeff 0 + b₁ := by rw [coeff_add, coeff_C_zero]
  have hb₁1 : (H + C b₁).coeff 1 = H.coeff 1 := by
    rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
  have hA1 : ((H + C b₁) * S₁ + C c₁).coeff 1
      = (H.coeff 0 + b₁) * S₁.coeff 1 + H.coeff 1 * S₁.coeff 0 := by
    rw [coeff_add, hC1, add_zero, hmul1, hb₁0, hb₁1]
  have hA2 : ((H + C b₁) * S₁ + C c₁).coeff 2
      = (H.coeff 0 + b₁) * S₁.coeff 2 + H.coeff 1 * S₁.coeff 1 + S₁.coeff 0 := by
    rw [coeff_add, hC2, add_zero, deg_two_mul_coeff hH hdH (by omega : 2 ≤ 2)]
  have hB2 : ((H + C b₂) * S₂ + C c₀).coeff 2
      = (H.coeff 0 + b₂) * S₂.coeff 2 + H.coeff 1 * S₂.coeff 1 + S₂.coeff 0 := by
    rw [coeff_add, hC2, add_zero, deg_two_mul_coeff hH hdH (by omega : 2 ≤ 2)]
  have hxs := x_shift_coeff b₀ ((H + C b₁) * S₁ + C c₁) 1
  rw [coeff_add, show (2:ℕ) = 1 + 1 from rfl, hxs, hA1, hA2, hB2]
  ring

/-- **Supports half of the head certificate** (`S_l` slot assertion, support part). -/
theorem head_step_supp (hH : H.Monic) (hdH : H.natDegree = 2)
    (hHK : ∀ j, H.coeff j ∈ K)
    (hS₁ : S₁.Monic) (hd₁ : S₁.natDegree = n)
    (hS₂ : S₂.Monic) (hd₂ : S₂.natDegree = n)
    (hin : CoeffTriangular K β (fun _ => (1 : R)) e (S₁ - X ^ n) (S₂ - X ^ n))
    (he : e + 2 ≤ n) (hn : 3 ≤ n) :
    ∀ j, (((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀))
        - X ^ (n + 3)).coeff j
      ∈ K ⊔ adjoin R ((headSlot e n β b₀ b₁ b₂ c₀ c₁ (A := A)) '' Set.Ico j (n + 3)) := by
  intro j
  set γ := headSlot e n β b₀ b₁ b₂ c₀ c₁ (A := A) with hγdef
  set V := K ⊔ adjoin R (γ '' Set.Ico j (n + 3)) with hV
  have hKV : ∀ x ∈ K, x ∈ V := fun x hx => (le_sup_left : K ≤ V) hx
  have hslot : ∀ t, j ≤ t → t < n + 3 → γ t ∈ V := fun t h1 h2 =>
    (le_sup_right : adjoin R _ ≤ V) (subset_adjoin ⟨t, ⟨h1, h2⟩, rfl⟩)
  have hγ0 : γ 0 = c₀ := rfl
  have hγ1 : γ 1 = c₁ := rfl
  have hγn : γ n = b₂ := headSlot_b2 he
  have hγn1 : γ (n + 1) = b₁ := headSlot_b1 he
  have hγn2 : γ (n + 2) = b₀ := headSlot_b0 he
  have hγmid : ∀ g, g < e → γ (g + 2) = β g := fun g hg => headSlot_mid hg
  have hb₂V : j ≤ n → b₂ ∈ V := fun h => hγn ▸ hslot n h (by omega)
  have hb₁V : j ≤ n + 1 → b₁ ∈ V := fun h => hγn1 ▸ hslot (n + 1) h (by omega)
  have hb₀V : j ≤ n + 2 → b₀ ∈ V := fun h => hγn2 ▸ hslot (n + 2) h (by omega)
  have hβV : ∀ g, g < e → j ≤ g + 2 → β g ∈ V := fun g hg hj =>
    hγmid g hg ▸ hslot (g + 2) hj (by omega)
  have hS₁V : ∀ m, j ≤ m + 3 → S₁.coeff m ∈ V := by
    intro m hm
    refine coeff_mem_of_sub_X_pow (n := n) ?_
    have hs := hin.supp₁ m
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ V) (adjoin_le ?_)) hs
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hβV g hg2 (by omega)
  have hS₂V : ∀ m, j ≤ m + 2 → S₂.coeff m ∈ V := by
    intro m hm
    refine coeff_mem_of_sub_X_pow (n := n) ?_
    have hs := hin.supp₂ m
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ V) (adjoin_le ?_)) hs
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hβV g hg2 (by omega)
  have hHV : ∀ m, H.coeff m ∈ V := fun m => hKV _ (hHK m)
  rcases Nat.lt_or_ge j (n + 3) with hjlt | hjge
  · have hXz : ((X : A[X]) ^ (n + 3)).coeff j = 0 := by
      rw [coeff_X_pow, if_neg (by omega)]
    rw [coeff_sub, hXz, sub_zero]
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · match j, hj3 with
      | 0, _ =>
        rw [head_coeff_zero]
        refine Subalgebra.add_mem _ (hγ0 ▸ hslot 0 le_rfl (by omega))
          (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hb₀V (by omega))
            (Subalgebra.add_mem _ (Subalgebra.mul_mem _
              (Subalgebra.add_mem _ (hHV 0) (hb₁V (by omega))) (hS₁V 0 (by omega)))
              (hγ1 ▸ hslot 1 (by omega) (by omega))))
            (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hHV 0) (hb₂V (by omega)))
              (hS₂V 0 (by omega))))
      | 1, _ =>
        rw [head_coeff_one]
        refine Subalgebra.add_mem _ (hγ1 ▸ hslot 1 le_rfl (by omega))
          (Subalgebra.add_mem _ (Subalgebra.add_mem _
            (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hHV 0) (hb₁V (by omega)))
              (hS₁V 0 (by omega)))
            (Subalgebra.mul_mem _ (hb₀V (by omega)) (Subalgebra.add_mem _
              (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hHV 0) (hb₁V (by omega)))
                (hS₁V 1 (by omega)))
              (Subalgebra.mul_mem _ (hHV 1) (hS₁V 0 (by omega))))))
            (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hHV 0)
              (hb₂V (by omega))) (hS₂V 1 (by omega)))
              (Subalgebra.mul_mem _ (hHV 1) (hS₂V 0 (by omega)))))
      | 2, _ =>
        rw [head_coeff_two hH hdH]
        refine Subalgebra.add_mem _ (hS₂V 0 (by omega))
          (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
            (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hHV 0) (hb₁V (by omega)))
              (hS₁V 1 (by omega)))
            (Subalgebra.mul_mem _ (hHV 1) (hS₁V 0 (by omega))))
            (Subalgebra.mul_mem _ (hb₀V (by omega)) (Subalgebra.add_mem _
              (Subalgebra.add_mem _ (Subalgebra.mul_mem _
                (Subalgebra.add_mem _ (hHV 0) (hb₁V (by omega))) (hS₁V 2 (by omega)))
                (Subalgebra.mul_mem _ (hHV 1) (hS₁V 1 (by omega))))
              (hS₁V 0 (by omega)))))
            (Subalgebra.add_mem _ (Subalgebra.mul_mem _
              (Subalgebra.add_mem _ (hHV 0) (hb₂V (by omega))) (hS₂V 2 (by omega)))
              (Subalgebra.mul_mem _ (hHV 1) (hS₂V 1 (by omega)))))
    · rcases Nat.lt_or_ge j n with hjn | hjn
      · -- middle band
        have hj' : j = (j - 2) + 2 := by omega
        rw [hj', head_coeff_mid (hH := hH) (hdH := hdH) (g := j - 2) (hg := by omega)]
        refine Subalgebra.add_mem _ (Subalgebra.add_mem _
          (hS₁V (j - 2 - 1) (by omega)) (hS₂V (j - 2) (by omega)))
          (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
            (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hHV 0) (hb₁V (by omega)))
              (hS₁V (j - 2 + 1) (by omega)))
            (Subalgebra.mul_mem _ (hHV 1) (hS₁V (j - 2) (by omega))))
            (Subalgebra.mul_mem _ (hb₀V (by omega)) (Subalgebra.add_mem _
              (Subalgebra.add_mem _ (Subalgebra.mul_mem _
                (Subalgebra.add_mem _ (hHV 0) (hb₁V (by omega)))
                (hS₁V (j - 2 + 2) (by omega)))
                (Subalgebra.mul_mem _ (hHV 1) (hS₁V (j - 2 + 1) (by omega))))
              (hS₁V (j - 2) (by omega)))))
            (Subalgebra.add_mem _ (Subalgebra.mul_mem _
              (Subalgebra.add_mem _ (hHV 0) (hb₂V (by omega)))
              (hS₂V (j - 2 + 2) (by omega)))
              (Subalgebra.mul_mem _ (hHV 1) (hS₂V (j - 2 + 1) (by omega)))))
      · -- top scalar rows
        rcases (by omega : j = n ∨ j = n + 1 ∨ j = n + 2) with hc | rfl | rfl
        · rw [hc, head_coeff_b2 (hH := hH) (hdH := hdH) (hS₁ := hS₁) (hd₁ := hd₁)
            (hS₂ := hS₂) (hd₂ := hd₂) (hn := hn)]
          refine Subalgebra.add_mem _ (hb₂V (by omega))
            (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
              (Subalgebra.add_mem _ (Subalgebra.mul_mem _
                (Subalgebra.add_mem _ (hHV 0) (hb₁V (by omega)))
                (hS₁V (n - 1) (by omega)))
                (Subalgebra.mul_mem _ (hHV 1) (hS₁V (n - 2) (by omega))))
              (hS₁V (n - 3) (by omega)))
              (Subalgebra.mul_mem _ (hb₀V (by omega)) (Subalgebra.add_mem _
                (Subalgebra.add_mem _ (Subalgebra.add_mem _ (hHV 0) (hb₁V (by omega)))
                  (Subalgebra.mul_mem _ (hHV 1) (hS₁V (n - 1) (by omega))))
                (hS₁V (n - 2) (by omega)))))
              (Subalgebra.add_mem _ (Subalgebra.add_mem _ (hHV 0)
                (Subalgebra.mul_mem _ (hHV 1) (hS₂V (n - 1) (by omega))))
                (hS₂V (n - 2) (by omega))))
        · rw [head_coeff_b1 (hH := hH) (hdH := hdH) (hS₁ := hS₁) (hd₁ := hd₁)
            (hS₂ := hS₂) (hd₂ := hd₂) (hn := by omega)]
          refine Subalgebra.add_mem _ (hb₁V le_rfl)
            (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
              (Subalgebra.add_mem _ (hHV 0)
                (Subalgebra.mul_mem _ (hHV 1) (hS₁V (n - 1) (by omega))))
              (hS₁V (n - 2) (by omega)))
              (Subalgebra.mul_mem _ (hb₀V (by omega)) (Subalgebra.add_mem _ (hHV 1)
                (hS₁V (n - 1) (by omega)))))
              (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hHV 1) (hS₂V n (by omega)))
                (hS₂V (n - 1) (by omega))))
        · rw [head_coeff_b0 (hH := hH) (hdH := hdH) (hS₁ := hS₁) (hd₁ := hd₁)
            (hS₂ := hS₂) (hd₂ := hd₂) (hn := by omega)]
          refine Subalgebra.add_mem _ (hb₀V le_rfl)
            (Subalgebra.add_mem _ (Subalgebra.add_mem _ (hHV 1)
              (hS₁V (n - 1) (by omega))) (hKV _ (Subalgebra.one_mem _)))
  · -- rows at or above the leading term
    obtain ⟨hPm, hPd⟩ := fill_output_monic (β₀ := b₀) (β₁ := b₁) (β₂ := b₂) (α₀ := c₀)
      (α₁ := c₁) hH hdH hS₁ hd₁ hS₂ hd₂
    rcases eq_or_ne j (n + 3) with rfl | hne
    · have hlead : ((X + C b₀) * ((H + C b₁) * S₁ + C c₁)
          + ((H + C b₂) * S₂ + C c₀)).coeff (n + 3) = 1 := by
        rw [← hPd]
        exact hPm.coeff_natDegree
      have hXl : ((X : A[X]) ^ (n + 3)).coeff (n + 3) = 1 := by
        rw [coeff_X_pow, if_pos rfl]
      rw [coeff_sub, hlead, hXl, sub_self]
      exact hKV _ (Subalgebra.zero_mem _)
    · have hz : ((X + C b₀) * ((H + C b₁) * S₁ + C c₁)
          + ((H + C b₂) * S₂ + C c₀)).coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hPd]; omega)
      have hXz : ((X : A[X]) ^ (n + 3)).coeff j = 0 := by
        rw [coeff_X_pow, if_neg (by omega)]
      rw [coeff_sub, hz, hXz, sub_self]
      exact hKV _ (Subalgebra.zero_mem _)

/-- **`S_l` head step** (induction step of `lem:Q-unitriangular`): the head shape applied
to a certified inner pair is a full unit-slope certificate on `n + 3` rows with slots
`headSlot` (constants at rows `0,1`, inner slots shifted by 2, multiplier scalars at
rows `n, n+1, n+2`). -/
theorem head_step (hH : H.Monic) (hdH : H.natDegree = 2)
    (hHK : ∀ j, H.coeff j ∈ K)
    (hS₁ : S₁.Monic) (hd₁ : S₁.natDegree = n)
    (hS₂ : S₂.Monic) (hd₂ : S₂.natDegree = n)
    (hin : CoeffTriangular K β (fun _ => (1 : R)) e (S₁ - X ^ n) (S₂ - X ^ n))
    (he : e + 2 ≤ n) (hn : 3 ≤ n) :
    CoeffTriangular K (headSlot e n β b₀ b₁ b₂ c₀ c₁) (fun _ => (1 : R)) (n + 3)
      0 (((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀))
        - X ^ (n + 3)) := by
  refine
    { unit := fun j hj => isUnit_one
      supp₁ := fun j => by rw [coeff_zero]; exact Subalgebra.zero_mem _
      supp₂ := head_step_supp hH hdH hHK hS₁ hd₁ hS₂ hd₂ hin he hn
      pivot := ?_ }
  intro j hj
  set γ := headSlot e n β b₀ b₁ b₂ c₀ c₁ (A := A) with hγdef
  have hcomb : ∀ i, (combined (0 : A[X])
      (((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀))
        - X ^ (n + 3))).coeff i
      = (((X + C b₀) * ((H + C b₁) * S₁ + C c₁) + ((H + C b₂) * S₂ + C c₀))
        - X ^ (n + 3)).coeff i := by
    intro i
    cases i with
    | zero => rw [coeff_combined_zero]
    | succ m => rw [coeff_combined, coeff_zero, zero_add]
  have hγ0 : γ 0 = c₀ := rfl
  have hγ1 : γ 1 = c₁ := rfl
  have hγn : γ n = b₂ := headSlot_b2 he
  have hγn1 : γ (n + 1) = b₁ := headSlot_b1 he
  have hγn2 : γ (n + 2) = b₀ := headSlot_b0 he
  have hγmid : ∀ g, g < e → γ (g + 2) = β g := fun g hg => headSlot_mid hg
  have hslotW : ∀ lo t, lo ≤ t → t < n + 3 →
      γ t ∈ K ⊔ adjoin R (γ '' Set.Ico lo (n + 3)) := fun lo t h1 h2 =>
    (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨h1, h2⟩, rfl⟩)
  have hKW : ∀ (lo : ℕ) (x : A), x ∈ K →
      x ∈ K ⊔ adjoin R (γ '' Set.Ico lo (n + 3)) := fun lo x hx =>
    (le_sup_left : K ≤ _) hx
  have hb₀W : ∀ lo, lo ≤ n + 2 → b₀ ∈ K ⊔ adjoin R (γ '' Set.Ico lo (n + 3)) :=
    fun lo h => hγn2 ▸ hslotW lo (n + 2) h (by omega)
  have hb₁W : ∀ lo, lo ≤ n + 1 → b₁ ∈ K ⊔ adjoin R (γ '' Set.Ico lo (n + 3)) :=
    fun lo h => hγn1 ▸ hslotW lo (n + 1) h (by omega)
  have hb₂W : ∀ lo, lo ≤ n → b₂ ∈ K ⊔ adjoin R (γ '' Set.Ico lo (n + 3)) :=
    fun lo h => hγn ▸ hslotW lo n h (by omega)
  have hβW : ∀ lo g, g < e → lo ≤ g + 2 →
      β g ∈ K ⊔ adjoin R (γ '' Set.Ico lo (n + 3)) := fun lo g hg hlo =>
    hγmid g hg ▸ hslotW lo (g + 2) hlo (by omega)
  have hS₁W : ∀ lo m, lo ≤ m + 3 →
      S₁.coeff m ∈ K ⊔ adjoin R (γ '' Set.Ico lo (n + 3)) := by
    intro lo m hm
    refine coeff_mem_of_sub_X_pow (n := n) ?_
    have hs := hin.supp₁ m
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hs
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hβW lo g hg2 (by omega)
  have hS₂W : ∀ lo m, lo ≤ m + 2 →
      S₂.coeff m ∈ K ⊔ adjoin R (γ '' Set.Ico lo (n + 3)) := by
    intro lo m hm
    refine coeff_mem_of_sub_X_pow (n := n) ?_
    have hs := hin.supp₂ m
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hs
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hβW lo g hg2 (by omega)
  have hS₁K : ∀ m, e ≤ m + 1 → S₁.coeff m ∈ K := fun m hm =>
    coeff_mem_of_sub_X_pow (cert_high_mem₁ hin hm)
  have hS₂K : ∀ m, e ≤ m → S₂.coeff m ∈ K := fun m hm =>
    coeff_mem_of_sub_X_pow (cert_high_mem₂ hin hm)
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · match j, hj2 with
    | 0, _ =>
      refine ⟨b₀ * ((H.coeff 0 + b₁) * S₁.coeff 0 + c₁)
        + (H.coeff 0 + b₂) * S₂.coeff 0, ?_, ?_⟩
      · exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hb₀W 1 (by omega))
          (Subalgebra.add_mem _ (Subalgebra.mul_mem _
            (Subalgebra.add_mem _ (hKW 1 _ (hHK 0)) (hb₁W 1 (by omega)))
            (hS₁W 1 0 (by omega))) (hγ1 ▸ hslotW 1 1 (by omega) (by omega))))
          (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hKW 1 _ (hHK 0))
            (hb₂W 1 (by omega))) (hS₂W 1 0 (by omega)))
      · rw [hcomb, coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero,
          head_coeff_zero, hγ0]
        simp only [map_one, one_mul]
    | 1, _ =>
      refine ⟨(H.coeff 0 + b₁) * S₁.coeff 0
        + b₀ * ((H.coeff 0 + b₁) * S₁.coeff 1 + H.coeff 1 * S₁.coeff 0)
        + ((H.coeff 0 + b₂) * S₂.coeff 1 + H.coeff 1 * S₂.coeff 0), ?_, ?_⟩
      · exact Subalgebra.add_mem _ (Subalgebra.add_mem _
          (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hKW 2 _ (hHK 0))
            (hb₁W 2 (by omega))) (hS₁W 2 0 (by omega)))
          (Subalgebra.mul_mem _ (hb₀W 2 (by omega)) (Subalgebra.add_mem _
            (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hKW 2 _ (hHK 0))
              (hb₁W 2 (by omega))) (hS₁W 2 1 (by omega)))
            (Subalgebra.mul_mem _ (hKW 2 _ (hHK 1)) (hS₁W 2 0 (by omega))))))
          (Subalgebra.add_mem _ (Subalgebra.mul_mem _
            (Subalgebra.add_mem _ (hKW 2 _ (hHK 0)) (hb₂W 2 (by omega)))
            (hS₂W 2 1 (by omega)))
            (Subalgebra.mul_mem _ (hKW 2 _ (hHK 1)) (hS₂W 2 0 (by omega))))
      · rw [hcomb, coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero,
          head_coeff_one, hγ1]
        simp only [map_one, one_mul]
  · rcases Nat.lt_or_ge j n with hjn | hjn
    · -- middle band, rows j = g + 2 with 0 ≤ g < n - 2
      obtain ⟨g, rfl⟩ : ∃ g, j = g + 2 := ⟨j - 2, by omega⟩
      have hXk : (((X + C b₀) * ((H + C b₁) * S₁ + C c₁)
          + ((H + C b₂) * S₂ + C c₀)) - X ^ (n + 3)).coeff (g + 2)
          = ((X + C b₀) * ((H + C b₁) * S₁ + C c₁)
            + ((H + C b₂) * S₂ + C c₀)).coeff (g + 2) := by
        rw [coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero]
      have hbridge : ((X + C b₀) * ((H + C b₁) * S₁ + C c₁)
          + ((H + C b₂) * S₂ + C c₀)).coeff (g + 2)
          = (combined (S₁ - X ^ n) (S₂ - X ^ n)).coeff g
            + ((H.coeff 0 + b₁) * S₁.coeff (g + 1) + H.coeff 1 * S₁.coeff g
              + b₀ * ((H.coeff 0 + b₁) * S₁.coeff (g + 2)
                + H.coeff 1 * S₁.coeff (g + 1) + S₁.coeff g)
              + ((H.coeff 0 + b₂) * S₂.coeff (g + 2)
                + H.coeff 1 * S₂.coeff (g + 1))) := by
        rcases Nat.eq_zero_or_pos g with rfl | hg1
        · rw [head_coeff_two hH hdH, coeff_combined_zero, coeff_sub, coeff_X_pow,
            if_neg (by omega), sub_zero]
        · rw [head_coeff_mid (hH := hH) (hdH := hdH) (hg := hg1)]
          cases g with
          | zero => omega
          | succ m =>
            rw [coeff_combined, coeff_sub, coeff_sub, coeff_X_pow, coeff_X_pow,
              if_neg (by omega), if_neg (by omega), sub_zero, sub_zero,
              Nat.add_sub_cancel]
      have hCm : (H.coeff 0 + b₁) * S₁.coeff (g + 1) + H.coeff 1 * S₁.coeff g
          + b₀ * ((H.coeff 0 + b₁) * S₁.coeff (g + 2)
            + H.coeff 1 * S₁.coeff (g + 1) + S₁.coeff g)
          + ((H.coeff 0 + b₂) * S₂.coeff (g + 2) + H.coeff 1 * S₂.coeff (g + 1))
          ∈ K ⊔ adjoin R (γ '' Set.Ico (g + 2 + 1) (n + 3)) := by
        refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
          (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hKW _ _ (hHK 0))
            (hb₁W _ (by omega))) (hS₁W _ (g + 1) (by omega)))
          (Subalgebra.mul_mem _ (hKW _ _ (hHK 1)) (hS₁W _ g (by omega))))
          (Subalgebra.mul_mem _ (hb₀W _ (by omega)) (Subalgebra.add_mem _
            (Subalgebra.add_mem _ (Subalgebra.mul_mem _
              (Subalgebra.add_mem _ (hKW _ _ (hHK 0)) (hb₁W _ (by omega)))
              (hS₁W _ (g + 2) (by omega)))
              (Subalgebra.mul_mem _ (hKW _ _ (hHK 1)) (hS₁W _ (g + 1) (by omega))))
            (hS₁W _ g (by omega)))))
          (Subalgebra.add_mem _ (Subalgebra.mul_mem _
            (Subalgebra.add_mem _ (hKW _ _ (hHK 0)) (hb₂W _ (by omega)))
            (hS₂W _ (g + 2) (by omega)))
            (Subalgebra.mul_mem _ (hKW _ _ (hHK 1)) (hS₂W _ (g + 1) (by omega))))
      rcases Nat.lt_or_ge g e with hge | hge
      · -- live inner pivot
        obtain ⟨F', hF', hFe⟩ := hin.pivot g hge
        have hFe' : (combined (S₁ - X ^ n) (S₂ - X ^ n)).coeff g = β g + F' := by
          rw [hFe]; simp only [map_one, one_mul]
        refine ⟨F' + ((H.coeff 0 + b₁) * S₁.coeff (g + 1) + H.coeff 1 * S₁.coeff g
          + b₀ * ((H.coeff 0 + b₁) * S₁.coeff (g + 2)
            + H.coeff 1 * S₁.coeff (g + 1) + S₁.coeff g)
          + ((H.coeff 0 + b₂) * S₂.coeff (g + 2)
            + H.coeff 1 * S₂.coeff (g + 1))), ?_, ?_⟩
        · refine Subalgebra.add_mem _ ?_ hCm
          refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF'
          rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
          exact hβW _ t ht2 (by omega)
        · rw [hcomb, hXk, hbridge, hFe', hγmid g hge]
          simp only [map_one, one_mul]
          ring
      · -- dead row: inner value is K-known, slot is zero
        have hγz : γ (g + 2) = 0 := headSlot_dead hge hjn
        have hDgK : (combined (S₁ - X ^ n) (S₂ - X ^ n)).coeff g ∈ K := by
          cases g with
          | zero =>
            rw [coeff_combined_zero]
            exact cert_high_mem₂ hin hge
          | succ m =>
            rw [coeff_combined]
            exact Subalgebra.add_mem _ (cert_high_mem₁ hin (by omega))
              (cert_high_mem₂ hin (by omega))
        refine ⟨(combined (S₁ - X ^ n) (S₂ - X ^ n)).coeff g
          + ((H.coeff 0 + b₁) * S₁.coeff (g + 1) + H.coeff 1 * S₁.coeff g
            + b₀ * ((H.coeff 0 + b₁) * S₁.coeff (g + 2)
              + H.coeff 1 * S₁.coeff (g + 1) + S₁.coeff g)
            + ((H.coeff 0 + b₂) * S₂.coeff (g + 2)
              + H.coeff 1 * S₂.coeff (g + 1))), ?_, ?_⟩
        · exact Subalgebra.add_mem _ (hKW _ _ hDgK) hCm
        · rw [hcomb, hXk, hbridge, hγz]
          simp only [map_one, mul_zero, zero_add]
    · -- multiplier scalar rows n, n + 1, n + 2
      rcases (by omega : j = n ∨ j = n + 1 ∨ j = n + 2) with hc | rfl | rfl
      · refine ⟨(H.coeff 0 + b₁) * S₁.coeff (n - 1) + H.coeff 1 * S₁.coeff (n - 2)
          + S₁.coeff (n - 3)
          + b₀ * (H.coeff 0 + b₁ + H.coeff 1 * S₁.coeff (n - 1) + S₁.coeff (n - 2))
          + (H.coeff 0 + H.coeff 1 * S₂.coeff (n - 1) + S₂.coeff (n - 2)), ?_, ?_⟩
        · refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
            (Subalgebra.add_mem _ (Subalgebra.mul_mem _
              (Subalgebra.add_mem _ (hKW _ _ (hHK 0)) (hb₁W _ (by omega)))
              (hKW _ _ (hS₁K (n - 1) (by omega))))
              (Subalgebra.mul_mem _ (hKW _ _ (hHK 1))
                (hKW _ _ (hS₁K (n - 2) (by omega)))))
            (hKW _ _ (hS₁K (n - 3) (by omega))))
            (Subalgebra.mul_mem _ (hb₀W _ (by omega)) (Subalgebra.add_mem _
              (Subalgebra.add_mem _ (Subalgebra.add_mem _ (hKW _ _ (hHK 0))
                (hb₁W _ (by omega))) (Subalgebra.mul_mem _ (hKW _ _ (hHK 1))
                  (hKW _ _ (hS₁K (n - 1) (by omega)))))
              (hKW _ _ (hS₁K (n - 2) (by omega))))))
            (Subalgebra.add_mem _ (Subalgebra.add_mem _ (hKW _ _ (hHK 0))
              (Subalgebra.mul_mem _ (hKW _ _ (hHK 1))
                (hKW _ _ (hS₂K (n - 1) (by omega)))))
              (hKW _ _ (hS₂K (n - 2) (by omega))))
        · rw [hcomb, coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero, hc,
            head_coeff_b2 (hH := hH) (hdH := hdH) (hS₁ := hS₁) (hd₁ := hd₁)
              (hS₂ := hS₂) (hd₂ := hd₂) (hn := hn), hγn]
          simp only [map_one, one_mul]
      · refine ⟨H.coeff 0 + H.coeff 1 * S₁.coeff (n - 1) + S₁.coeff (n - 2)
          + b₀ * (H.coeff 1 + S₁.coeff (n - 1))
          + (H.coeff 1 * S₂.coeff n + S₂.coeff (n - 1)), ?_, ?_⟩
        · refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
            (Subalgebra.add_mem _ (hKW _ _ (hHK 0))
              (Subalgebra.mul_mem _ (hKW _ _ (hHK 1))
                (hKW _ _ (hS₁K (n - 1) (by omega)))))
            (hKW _ _ (hS₁K (n - 2) (by omega))))
            (Subalgebra.mul_mem _ (hb₀W _ (by omega)) (Subalgebra.add_mem _
              (hKW _ _ (hHK 1)) (hKW _ _ (hS₁K (n - 1) (by omega))))))
            (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hKW _ _ (hHK 1))
              (hKW _ _ (hS₂K n (by omega)))) (hKW _ _ (hS₂K (n - 1) (by omega))))
        · rw [hcomb, coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero,
            head_coeff_b1 (hH := hH) (hdH := hdH) (hS₁ := hS₁) (hd₁ := hd₁)
              (hS₂ := hS₂) (hd₂ := hd₂) (hn := by omega), hγn1]
          simp only [map_one, one_mul]
      · refine ⟨H.coeff 1 + S₁.coeff (n - 1) + 1, ?_, ?_⟩
        · exact hKW _ _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ (hHK 1)
            (hS₁K (n - 1) (by omega))) (Subalgebra.one_mem _))
        · rw [hcomb, coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero,
            head_coeff_b0 (hH := hH) (hdH := hdH) (hS₁ := hS₁) (hd₁ := hd₁)
              (hS₂ := hS₂) (hd₂ := hd₂) (hn := by omega), hγn2]
          simp only [map_one, one_mul]

end headStep


end FastPoly
