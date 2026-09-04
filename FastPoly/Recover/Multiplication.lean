import FastPoly.Recover.Context

/-!
# Combination lemmas: Multiplicativity — support lemmas

Window shifts and boundary/rest splits of the Cauchy product, in preparation for the
Multiplicativity engine (paper `lem:compatible-multiplicativity`).
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Shift a window upward by `n`. -/
def shiftW (n : ℕ) (G : Finset ℕ) : Finset ℕ := G.image fun i => n + i

theorem mem_shiftW {n : ℕ} {G : Finset ℕ} {k : ℕ} :
    k ∈ shiftW n G ↔ ∃ i ∈ G, n + i = k := by
  simp [shiftW]

theorem le_of_mem_shiftW {n : ℕ} {G : Finset ℕ} {k : ℕ} (hk : k ∈ shiftW n G) : n ≤ k := by
  rcases mem_shiftW.1 hk with ⟨i, -, rfl⟩; omega

theorem add_mem_shiftW {n : ℕ} {G : Finset ℕ} {i : ℕ} (hi : i ∈ G) : n + i ∈ shiftW n G :=
  mem_shiftW.2 ⟨i, hi, rfl⟩

/-- Boundary/rest split of a Cauchy coefficient along the second factor's index. -/
theorem coeff_mul_split_snd (P Q : A[X]) (m nQ : ℕ) :
    (P * Q).coeff m =
      (if nQ ≤ m then P.coeff (m - nQ) * Q.coeff nQ else 0) +
        ∑ x ∈ (Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.2 ≠ nQ),
          P.coeff x.1 * Q.coeff x.2 := by
  classical
  rw [coeff_mul, ← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal m)
    (fun x : ℕ × ℕ => x.2 = nQ)]
  congr 1
  · rw [show (Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.2 = nQ) =
        if nQ ≤ m then {(m - nQ, nQ)} else ∅ from by
      simpa using Finset.filter_snd_eq_antidiagonal m nQ]
    split
    · rw [Finset.sum_singleton]
    · rw [Finset.sum_empty]

/-- Boundary/rest split of a Cauchy coefficient along the first factor's index. -/
theorem coeff_mul_split_fst (P Q : A[X]) (m nP : ℕ) :
    (P * Q).coeff m =
      (if nP ≤ m then P.coeff nP * Q.coeff (m - nP) else 0) +
        ∑ x ∈ (Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.1 ≠ nP),
          P.coeff x.1 * Q.coeff x.2 := by
  classical
  rw [coeff_mul, ← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal m)
    (fun x : ℕ × ℕ => x.1 = nP)]
  congr 1
  · rw [show (Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.1 = nP) =
        if nP ≤ m then {(nP, m - nP)} else ∅ from by
      simpa using Finset.filter_fst_eq_antidiagonal m nP]
    split
    · rw [Finset.sum_singleton]
    · rw [Finset.sum_empty]

/-- Double boundary/rest split of a Cauchy coefficient: extract both the `x.1 = nP` and the
`x.2 = nQ` boundary terms (with the overlap at `m = nP + nQ` corrected), leaving the double
rest sum over `x.1 ≠ nP ∧ x.2 ≠ nQ`. -/
theorem coeff_mul_double_split (P Q : A[X]) (m nP nQ : ℕ) :
    (P * Q).coeff m
      = (if nQ ≤ m then P.coeff (m - nQ) * Q.coeff nQ else 0)
        + ((if nP ≤ m then P.coeff nP * Q.coeff (m - nP) else 0)
            - (if m = nP + nQ then P.coeff nP * Q.coeff nQ else 0))
        + ∑ x ∈ (Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.1 ≠ nP ∧ x.2 ≠ nQ),
            P.coeff x.1 * Q.coeff x.2 := by
  classical
  rw [coeff_mul_split_snd P Q m nQ]
  have hsplit : ∑ x ∈ (Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.2 ≠ nQ),
        P.coeff x.1 * Q.coeff x.2
      = (∑ x ∈ ((Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.2 ≠ nQ)).filter
            (fun x : ℕ × ℕ => x.1 = nP), P.coeff x.1 * Q.coeff x.2)
        + ∑ x ∈ ((Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.2 ≠ nQ)).filter
            (fun x : ℕ × ℕ => ¬ x.1 = nP), P.coeff x.1 * Q.coeff x.2 :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hset1 : ((Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.2 ≠ nQ)).filter
      (fun x : ℕ × ℕ => x.1 = nP)
      = if nP ≤ m ∧ m ≠ nP + nQ then {(nP, m - nP)} else ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, ne_eq]
    constructor
    · rintro ⟨⟨hadd, hne⟩, hx1⟩
      rw [if_pos ⟨by omega, by omega⟩, Finset.mem_singleton, Prod.ext_iff]
      exact ⟨hx1, by omega⟩
    · intro hx
      split at hx
      · rw [Finset.mem_singleton] at hx
        rename_i hcond
        subst hx
        exact ⟨⟨show nP + (m - nP) = m by omega, show ¬(m - nP = nQ) by omega⟩, rfl⟩
      · exact absurd hx (Finset.notMem_empty _)
  have hset2 : ((Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.2 ≠ nQ)).filter
      (fun x : ℕ × ℕ => ¬ x.1 = nP)
      = (Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.1 ≠ nP ∧ x.2 ≠ nQ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, ne_eq]
    tauto
  have hval1 : (∑ x ∈ ((Finset.antidiagonal m).filter (fun x : ℕ × ℕ => x.2 ≠ nQ)).filter
        (fun x : ℕ × ℕ => x.1 = nP), P.coeff x.1 * Q.coeff x.2)
      = (if nP ≤ m then P.coeff nP * Q.coeff (m - nP) else 0)
        - (if m = nP + nQ then P.coeff nP * Q.coeff nQ else 0) := by
    rw [hset1]
    rcases Nat.lt_or_ge m nP with h1 | h1
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
    · rcases eq_or_ne m (nP + nQ) with h2 | h2
      · rw [if_neg (by omega), if_pos h1, if_pos h2, show m - nP = nQ by omega]
        simp
      · rw [if_pos ⟨h1, h2⟩, Finset.sum_singleton, if_pos h1, if_neg h2]
        simp
  rw [hsplit, hval1, hset2]
  ring

section engine

variable {K : Subalgebra R A} {gL gR : Finset ℕ} {nL nR : ℕ} {PL₁ PL₂ PR₁ PR₂ : A[X]}

/-- **Two-source separation for products** (the engine of Multiplicativity, paper
`lem:compatible-multiplicativity`): with disjoint shifted windows, the visible algebra of the
left factor pair at cutoff `t` embeds into that of the product pair at cutoff `nR + t`. -/
theorem vis_le_vis_mul (hL : CompatiblePair K PL₁ PL₂ nL gL)
    (hR : CompatiblePair K PR₁ PR₂ nR gR)
    (hdis : Disjoint (shiftW nR gL) (shiftW nL gR)) (t : ℕ) :
    Vis R K (combined PL₁ PL₂) gL t ≤
      Vis R K (combined (PL₁ * PR₁) (PL₂ * PR₂)) (shiftW nR gL ∪ shiftW nL gR) (nR + t) := by
  classical
  set φL := combined PL₁ PL₂ with hφL
  set φR := combined PR₁ PR₂ with hφR
  set Ψ := combined (PL₁ * PR₁) (PL₂ * PR₂) with hΨ
  set G := shiftW nR gL ∪ shiftW nL gR with hG
  set V := Vis R K Ψ G (nR + t) with hV
  set U := G.filter (fun i => nR + t ≤ i) with hU
  -- the four monic leading coefficients
  have hl1 : PL₁.coeff nL = 1 := by rw [← hL.natDegree₁]; exact hL.monic₁.coeff_natDegree
  have hl2 : PL₂.coeff nL = 1 := by rw [← hL.natDegree₂]; exact hL.monic₂.coeff_natDegree
  have hr1 : PR₁.coeff nR = 1 := by rw [← hR.natDegree₁]; exact hR.monic₁.coeff_natDegree
  have hr2 : PR₂.coeff nR = 1 := by rw [← hR.natDegree₂]; exact hR.monic₂.coeff_natDegree
  -- one descending step
  have step : ∀ k, k ∈ U →
      (∀ i ∈ U, k < i →
        (i ∈ shiftW nR gL → φL.coeff (i - nR) ∈ V) ∧
        (i ∈ shiftW nL gR → φR.coeff (i - nL) ∈ V)) →
      (k ∈ shiftW nR gL → φL.coeff (k - nR) ∈ V) ∧
      (k ∈ shiftW nL gR → φR.coeff (k - nL) ∈ V) := by
    intro k hkU ih
    have hktU : nR + t ≤ k := (Finset.mem_filter.1 hkU).2
    have hkG : k ∈ G := (Finset.mem_filter.1 hkU).1
    have hks : Ψ.coeff k ∈ V := coeff_mem_Vis hkG hktU
    -- cutoff-transport helpers
    have mapL : ∀ u, k + 1 ≤ nR + u → Vis R K φL gL u ≤ V := by
      intro u hu
      refine Vis_le le_sup_left ?_
      intro i' hi' hui'
      have hiU : nR + i' ∈ U := Finset.mem_filter.2
        ⟨Finset.mem_union_left _ (add_mem_shiftW hi'), by omega⟩
      have h := (ih (nR + i') hiU (by omega)).1 (add_mem_shiftW hi')
      simpa using h
    have mapR : ∀ u, k + 1 ≤ nL + u → Vis R K φR gR u ≤ V := by
      intro u hu
      refine Vis_le le_sup_left ?_
      intro i' hi' hui'
      have hiU : nL + i' ∈ U := Finset.mem_filter.2
        ⟨Finset.mem_union_right _ (add_mem_shiftW hi'), by omega⟩
      have h := (ih (nL + i') hiU (by omega)).2 (add_mem_shiftW hi')
      simpa using h
    have memL₁ : ∀ j, k ≤ nR + j → PL₁.coeff j ∈ V :=
      fun j hj => mapL (j + 1) (by omega) (hL.mem₁ j)
    have memL₂ : ∀ j, k + 1 ≤ nR + j → PL₂.coeff j ∈ V :=
      fun j hj => mapL j hj (hL.mem₂ j)
    have memR₁ : ∀ j, k ≤ nL + j → PR₁.coeff j ∈ V :=
      fun j hj => mapR (j + 1) (by omega) (hR.mem₁ j)
    have memR₂ : ∀ j, k + 1 ≤ nL + j → PR₂.coeff j ∈ V :=
      fun j hj => mapR j hj (hR.mem₂ j)
    -- causal recovery of the off-window side's combined coefficient
    have hφRoff : k ∉ shiftW nL gR → φR.coeff (k - nL) ∈ V := by
      intro hkR
      rcases Nat.lt_or_ge k nL with hklt | hkge
      · have h0 : Vis R K φR gR 0 ≤ V := mapR 0 (by omega)
        exact h0 (Vis_antitone_cutoff (Nat.zero_le _) (hR.toCausalPair.combined_coeff_mem (k - nL)))
      · have hnot : k - nL ∉ gR := fun h => hkR (by
          have : nL + (k - nL) = k := by omega
          exact this ▸ add_mem_shiftW h)
        have hbump : Vis R K φR gR (k - nL) = Vis R K φR gR (k - nL + 1) :=
          Vis_succ_of_not_mem hnot
        refine mapR (k - nL + 1) (by omega) ?_
        rw [← hbump]
        exact hR.toCausalPair.combined_coeff_mem (k - nL)
    have hφLoff : k ∉ shiftW nR gL → φL.coeff (k - nR) ∈ V := by
      intro hkL
      rcases Nat.lt_or_ge k nR with hklt | hkge
      · have h0 : Vis R K φL gL 0 ≤ V := mapL 0 (by omega)
        exact h0 (Vis_antitone_cutoff (Nat.zero_le _) (hL.toCausalPair.combined_coeff_mem (k - nR)))
      · have hnot : k - nR ∉ gL := fun h => hkL (by
          have : nR + (k - nR) = k := by omega
          exact this ▸ add_mem_shiftW h)
        have hbump : Vis R K φL gL (k - nR) = Vis R K φL gL (k - nR + 1) :=
          Vis_succ_of_not_mem hnot
        refine mapL (k - nR + 1) (by omega) ?_
        rw [← hbump]
        exact hL.toCausalPair.combined_coeff_mem (k - nR)
    -- the k = 0 degenerate case: one factor pair has degree 0
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · constructor
      · intro hkL
        have hnR0 : nR = 0 := by have := le_of_mem_shiftW hkL; omega
        have hψ0 : Ψ.coeff 0 = φL.coeff 0 := by
          rw [hΨ, hφL, coeff_combined_zero, coeff_combined_zero, mul_coeff_zero,
            show PR₂.coeff 0 = 1 from by rw [← show nR = 0 from hnR0, hr2], mul_one]
        rw [Nat.zero_sub, ← hψ0]
        exact hks
      · intro hkR
        have hnL0 : nL = 0 := by have := le_of_mem_shiftW hkR; omega
        have hψ0 : Ψ.coeff 0 = φR.coeff 0 := by
          rw [hΨ, hφR, coeff_combined_zero, coeff_combined_zero, mul_coeff_zero,
            show PL₂.coeff 0 = 1 from by rw [← show nL = 0 from hnL0, hl2], one_mul]
        rw [Nat.zero_sub, ← hψ0]
        exact hks
    -- k ≥ 1: write k = k' + 1 and expand
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    set E₁ := ∑ x ∈ (Finset.antidiagonal k').filter (fun x : ℕ × ℕ => x.1 ≠ nL ∧ x.2 ≠ nR),
        PL₁.coeff x.1 * PR₁.coeff x.2 with hE₁
    set E₂ := ∑ x ∈ (Finset.antidiagonal (k' + 1)).filter
        (fun x : ℕ × ℕ => x.1 ≠ nL ∧ x.2 ≠ nR),
        PL₂.coeff x.1 * PR₂.coeff x.2 with hE₂
    have hE₁mem : E₁ ∈ V := by
      rw [hE₁]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hm := Finset.mem_filter.1 hx
      have hxa : x.1 + x.2 = k' := Finset.mem_antidiagonal.1 hm.1
      obtain ⟨hx1, hx2⟩ := hm.2
      rcases Nat.lt_or_ge nL x.1 with hgt | hle1
      · have hz : PL₁.coeff x.1 = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hL.natDegree₁]; omega)
        rw [hz, zero_mul]
        exact Subalgebra.zero_mem _
      rcases Nat.lt_or_ge nR x.2 with hgt2 | hle2
      · have hz : PR₁.coeff x.2 = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hR.natDegree₁]; omega)
        rw [hz, mul_zero]
        exact Subalgebra.zero_mem _
      exact Subalgebra.mul_mem _ (memL₁ x.1 (by omega)) (memR₁ x.2 (by omega))
    have hE₂mem : E₂ ∈ V := by
      rw [hE₂]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hm := Finset.mem_filter.1 hx
      have hxa : x.1 + x.2 = k' + 1 := Finset.mem_antidiagonal.1 hm.1
      obtain ⟨hx1, hx2⟩ := hm.2
      rcases Nat.lt_or_ge nL x.1 with hgt | hle1
      · have hz : PL₂.coeff x.1 = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hL.natDegree₂]; omega)
        rw [hz, zero_mul]
        exact Subalgebra.zero_mem _
      rcases Nat.lt_or_ge nR x.2 with hgt2 | hle2
      · have hz : PR₂.coeff x.2 = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hR.natDegree₂]; omega)
        rw [hz, mul_zero]
        exact Subalgebra.zero_mem _
      exact Subalgebra.mul_mem _ (memL₂ x.1 (by omega)) (memR₂ x.2 (by omega))
    have hcorr₁ : (if k' = nL + nR then (1:A) else 0) ∈ V := by
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    have hcorr₂ : (if k' + 1 = nL + nR then (1:A) else 0) ∈ V := by
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    -- the master identity
    have hmaster : Ψ.coeff (k' + 1)
        = ((if nR ≤ k' then PL₁.coeff (k' - nR) else 0)
            + (if nR ≤ k' + 1 then PL₂.coeff (k' + 1 - nR) else 0))
          + ((if nL ≤ k' then PR₁.coeff (k' - nL) else 0)
            + (if nL ≤ k' + 1 then PR₂.coeff (k' + 1 - nL) else 0))
          - (if k' = nL + nR then (1:A) else 0)
          - (if k' + 1 = nL + nR then (1:A) else 0)
          + E₁ + E₂ := by
      rw [hΨ, coeff_combined, coeff_mul_double_split PL₁ PR₁ k' nL nR,
        coeff_mul_double_split PL₂ PR₂ (k' + 1) nL nR, hl1, hl2, hr1, hr2, ← hE₁, ← hE₂]
      simp only [mul_one, one_mul]
      ring
    -- boundary sums vs combined coefficients
    have hBL : nR ≤ k' + 1 →
        (if nR ≤ k' then PL₁.coeff (k' - nR) else 0)
          + (if nR ≤ k' + 1 then PL₂.coeff (k' + 1 - nR) else 0)
        = φL.coeff (k' + 1 - nR) := by
      intro hknR
      rcases Nat.lt_or_ge k' nR with h1 | h1
      · rw [if_neg (by omega), if_pos hknR, show k' + 1 - nR = 0 by omega, hφL,
          coeff_combined_zero, zero_add]
      · rw [if_pos h1, if_pos hknR, show k' + 1 - nR = (k' - nR) + 1 by omega, hφL,
          coeff_combined]
    have hBR : nL ≤ k' + 1 →
        (if nL ≤ k' then PR₁.coeff (k' - nL) else 0)
          + (if nL ≤ k' + 1 then PR₂.coeff (k' + 1 - nL) else 0)
        = φR.coeff (k' + 1 - nL) := by
      intro hknL
      rcases Nat.lt_or_ge k' nL with h1 | h1
      · rw [if_neg (by omega), if_pos hknL, show k' + 1 - nL = 0 by omega, hφR,
          coeff_combined_zero, zero_add]
      · rw [if_pos h1, if_pos hknL, show k' + 1 - nL = (k' - nL) + 1 by omega, hφR,
          coeff_combined]
    have hBRmem : k' + 1 ∉ shiftW nL gR →
        ((if nL ≤ k' then PR₁.coeff (k' - nL) else 0)
          + (if nL ≤ k' + 1 then PR₂.coeff (k' + 1 - nL) else 0)) ∈ V := by
      intro hkR
      rcases Nat.lt_or_ge (k' + 1) nL with h1 | h1
      · rw [if_neg (by omega), if_neg (by omega)]
        simp
      · rw [hBR h1]
        exact hφRoff hkR
    have hBLmem : k' + 1 ∉ shiftW nR gL →
        ((if nR ≤ k' then PL₁.coeff (k' - nR) else 0)
          + (if nR ≤ k' + 1 then PL₂.coeff (k' + 1 - nR) else 0)) ∈ V := by
      intro hkL
      rcases Nat.lt_or_ge (k' + 1) nR with h1 | h1
      · rw [if_neg (by omega), if_neg (by omega)]
        simp
      · rw [hBL h1]
        exact hφLoff hkL
    constructor
    · -- left component: k ∈ shiftW nR gL
      intro hkL
      have hkR : k' + 1 ∉ shiftW nL gR := Finset.disjoint_left.1 hdis hkL
      have hknR : nR ≤ k' + 1 := le_of_mem_shiftW hkL
      have hkey : φL.coeff (k' + 1 - nR)
          = Ψ.coeff (k' + 1)
            - ((if nL ≤ k' then PR₁.coeff (k' - nL) else 0)
              + (if nL ≤ k' + 1 then PR₂.coeff (k' + 1 - nL) else 0))
            + (if k' = nL + nR then (1:A) else 0)
            + (if k' + 1 = nL + nR then (1:A) else 0)
            - E₁ - E₂ := by
        rw [hmaster, ← hBL hknR]
        ring
      rw [hkey]
      exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (Subalgebra.sub_mem _ hks (hBRmem hkR)) hcorr₁) hcorr₂)
        hE₁mem) hE₂mem
    · -- right component: k ∈ shiftW nL gR
      intro hkR
      have hkL : k' + 1 ∉ shiftW nR gL := Finset.disjoint_right.1 hdis hkR
      have hknL : nL ≤ k' + 1 := le_of_mem_shiftW hkR
      have hkey : φR.coeff (k' + 1 - nL)
          = Ψ.coeff (k' + 1)
            - ((if nR ≤ k' then PL₁.coeff (k' - nR) else 0)
              + (if nR ≤ k' + 1 then PL₂.coeff (k' + 1 - nR) else 0))
            + (if k' = nL + nR then (1:A) else 0)
            + (if k' + 1 = nL + nR then (1:A) else 0)
            - E₁ - E₂ := by
        rw [hmaster, ← hBR hknL]
        ring
      rw [hkey]
      exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (Subalgebra.sub_mem _ hks (hBLmem hkL)) hcorr₁) hcorr₂)
        hE₁mem) hE₂mem
  -- close the descending induction
  have main : ∀ k ∈ U,
      (k ∈ shiftW nR gL → (combined PL₁ PL₂).coeff (k - nR) ∈ V) ∧
      (k ∈ shiftW nL gR → (combined PR₁ PR₂).coeff (k - nL) ∈ V) :=
    descend_on_finset step
  refine Vis_le le_sup_left ?_
  intro i higL hti
  have hiU : nR + i ∈ U := Finset.mem_filter.2
    ⟨Finset.mem_union_left _ (add_mem_shiftW higL), by omega⟩
  have h := (main (nR + i) hiU).1 (add_mem_shiftW higL)
  simpa using h


/-- Right-factor version of the engine, by commuting the products and windows. -/
theorem vis_le_vis_mul' (hL : CompatiblePair K PL₁ PL₂ nL gL)
    (hR : CompatiblePair K PR₁ PR₂ nR gR)
    (hdis : Disjoint (shiftW nR gL) (shiftW nL gR)) (t : ℕ) :
    Vis R K (combined PR₁ PR₂) gR t ≤
      Vis R K (combined (PL₁ * PR₁) (PL₂ * PR₂)) (shiftW nR gL ∪ shiftW nL gR) (nL + t) := by
  have h := vis_le_vis_mul hR hL hdis.symm t
  rwa [mul_comm PR₁ PL₁, mul_comm PR₂ PL₂, Finset.union_comm] at h

/-- **Multiplicativity of compatible pairs** (paper `lem:compatible-multiplicativity`):
products of compatible pairs with disjoint shifted windows are compatible on the union of
the shifted windows. -/
theorem CompatiblePair.mul (hL : CompatiblePair K PL₁ PL₂ nL gL)
    (hR : CompatiblePair K PR₁ PR₂ nR gR)
    (hdis : Disjoint (shiftW nR gL) (shiftW nL gR)) :
    CompatiblePair K (PL₁ * PR₁) (PL₂ * PR₂) (nL + nR)
      (shiftW nR gL ∪ shiftW nL gR) := by
  set Ψ := combined (PL₁ * PR₁) (PL₂ * PR₂) with hΨ
  set G := shiftW nR gL ∪ shiftW nL gR with hG
  have hmem₁ : ∀ j, (PL₁ * PR₁).coeff j ∈ Vis R K Ψ G (j + 1) := by
    intro j
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge nL x.1 with hgt | hle1
    · have hz : PL₁.coeff x.1 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hL.natDegree₁]; omega)
      rw [hz, zero_mul]; exact Subalgebra.zero_mem _
    rcases Nat.lt_or_ge nR x.2 with hgt2 | hle2
    · have hz : PR₁.coeff x.2 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hR.natDegree₁]; omega)
      rw [hz, mul_zero]; exact Subalgebra.zero_mem _
    refine Subalgebra.mul_mem _ ?_ ?_
    · exact Vis_antitone_cutoff (by omega) (vis_le_vis_mul hL hR hdis (x.1 + 1) (hL.mem₁ x.1))
    · exact Vis_antitone_cutoff (by omega) (vis_le_vis_mul' hL hR hdis (x.2 + 1) (hR.mem₁ x.2))
  have hmem₂ : ∀ j, (PL₂ * PR₂).coeff j ∈ Vis R K Ψ G j := by
    intro j
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge nL x.1 with hgt | hle1
    · have hz : PL₂.coeff x.1 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hL.natDegree₂]; omega)
      rw [hz, zero_mul]; exact Subalgebra.zero_mem _
    rcases Nat.lt_or_ge nR x.2 with hgt2 | hle2
    · have hz : PR₂.coeff x.2 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hR.natDegree₂]; omega)
      rw [hz, mul_zero]; exact Subalgebra.zero_mem _
    refine Subalgebra.mul_mem _ ?_ ?_
    · exact Vis_antitone_cutoff (by omega) (vis_le_vis_mul hL hR hdis x.1 (hL.mem₂ x.1))
    · exact Vis_antitone_cutoff (by omega) (vis_le_vis_mul' hL hR hdis x.2 (hR.mem₂ x.2))
  exact
    { mem₁ := hmem₁
      mem₂ := hmem₂
      monic₁ := hL.monic₁.mul hR.monic₁
      monic₂ := hL.monic₂.mul hR.monic₂
      natDegree₁ := by rw [hL.monic₁.natDegree_mul hR.monic₁, hL.natDegree₁, hR.natDegree₁]
      natDegree₂ := by rw [hL.monic₂.natDegree_mul hR.monic₂, hL.natDegree₂, hR.natDegree₂]
      window := by
        refine Finset.union_subset ?_ ?_
        · intro i hi
          rcases mem_shiftW.1 hi with ⟨i', hi', rfl⟩
          have := Finset.mem_range.1 (hL.window hi')
          exact Finset.mem_range.2 (by omega)
        · intro i hi
          rcases mem_shiftW.1 hi with ⟨i', hi', rfl⟩
          have := Finset.mem_range.1 (hR.window hi')
          exact Finset.mem_range.2 (by omega) }

end engine

end FastPoly
