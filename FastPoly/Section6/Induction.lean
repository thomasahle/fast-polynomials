import FastPoly.Section6.QOddDegree
import FastPoly.Polynomial.SquareGadget
import FastPoly.Polynomial.CausalShell

/-!
# `lem:8k+3-splittable`, compatibility half

The `8k+3` output pair `T₁ = S₂² - S₁² + S₃`, `T₂ = (S₂+a)² - S̃₁² + α₀` over a
compatible smaller pair `(S₁, S̃₁)` of degree `2k` and monic auxiliaries `S₂`
(degree `4k+1`), `S₃` (degree `≤ 2k-1`, known lead) is compatible on
`{4k+1,…,8k+2} ∪ (2k+G) ∪ rng(2k+1)`: the top block through the causal
square-gadget shell, the middle block through square closure of the smaller pair,
and the low block through direct row reads.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {k : ℕ}

/-- The four-term shell error vanishes strictly above the seam row. -/
private theorem shell_coeff_zero₄ {P Q W Z : A[X]} {d : ℕ}
    (hP : P.natDegree + 1 ≤ d) (hQ : Q.natDegree ≤ d)
    (hW : W.natDegree + 1 ≤ d) (hZ : Z.natDegree ≤ d) :
    ∀ i, d < i → (-(X * P) - Q + X * W + Z).coeff i = 0 := by
  intro i hi
  rw [coeff_add, coeff_add, coeff_sub, coeff_neg,
    coeff_X_mul_of_pos (show 1 ≤ i by omega),
    show P.coeff (i - 1) = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
    show Q.coeff i = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
    coeff_X_mul_of_pos (show 1 ≤ i by omega),
    show W.coeff (i - 1) = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
    show Z.coeff i = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]
  ring

/-- The two-term shell error vanishes strictly above the seam row. -/
private theorem shell_coeff_zero₂ {P Q : A[X]} {d : ℕ}
    (hP : P.natDegree + 1 ≤ d) (hQ : Q.natDegree ≤ d) :
    ∀ i, d < i → (-(X * P) - Q).coeff i = 0 := by
  intro i hi
  rw [coeff_sub, coeff_neg, coeff_X_mul_of_pos (show 1 ≤ i by omega),
    show P.coeff (i - 1) = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
    show Q.coeff i = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]
  ring

/-- The seam coefficient of the four-term shell error is the fixed `-1`. -/
private theorem shell_coeff_seam₄ {P Q W Z : A[X]} {e s : ℕ}
    (hlead : P.coeff e = 1) (hQ : Q.natDegree ≤ e)
    (hW : W.natDegree < e) (hZ : Z.natDegree ≤ e) (hs : s = e + 1) :
    (-(X * P) - Q + X * W + Z).coeff s = -1 := by
  subst hs
  rw [coeff_add, coeff_add, coeff_sub, coeff_neg,
    coeff_X_mul_of_pos (show 1 ≤ e + 1 by omega),
    coeff_X_mul_of_pos (show 1 ≤ e + 1 by omega),
    show e + 1 - 1 = e from by omega, hlead,
    show Q.coeff (e + 1) = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
    show W.coeff e = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
    show Z.coeff (e + 1) = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]
  ring

/-- The seam coefficient of the two-term shell error is the fixed `-1`. -/
private theorem shell_coeff_seam₂ {P Q : A[X]} {e s : ℕ}
    (hlead : P.coeff e = 1) (hQ : Q.natDegree ≤ e) (hs : s = e + 1) :
    (-(X * P) - Q).coeff s = -1 := by
  subst hs
  rw [coeff_sub, coeff_neg, coeff_X_mul_of_pos (show 1 ≤ e + 1 by omega),
    show e + 1 - 1 = e from by omega, hlead,
    show Q.coeff (e + 1) = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]
  ring

/-- The combined output pair of a difference-of-squares step, rewritten as the
causal square-gadget shell over its error term. -/
private theorem combined_shell_eq (S Plow Qlow W Z : A[X]) (c : A) :
    combined (S * S - Plow + W) ((S + C c) * (S + C c) - Qlow + Z)
      = X * S ^ 2 + (S + C c) ^ 2 + (-(X * Plow) - Qlow + X * W + Z) := by
  show X * (S * S - Plow + W) + ((S + C c) * (S + C c) - Qlow + Z) = _
  ring

set_option maxHeartbeats 1000000 in
/-- **`lem:8k+3-splittable`, compatibility half**: the `8k+3` output pair is
compatible on `{4k+1,…,8k+2} ∪ (2k+G) ∪ rng(2k+1)` with no additional data. -/
theorem eightk3_compatible (hk : 1 ≤ k) (h2 : IsUnit (2 : R))
    {S₁ St₁ S₂ S₃ : A[X]} {a α₀ : A} {G : Finset ℕ}
    (hsmall : CompatiblePair K S₁ St₁ (2 * k) G)
    (hS₂m : S₂.Monic) (hS₂d : S₂.natDegree = 4 * k + 1)
    (hS₃d : S₃.natDegree ≤ 2 * k - 1) (hS₃lead : S₃.coeff (2 * k - 1) ∈ K) :
    CompatiblePair K (S₂ * S₂ - S₁ * S₁ + S₃)
      ((S₂ + C a) * (S₂ + C a) - St₁ * St₁ + C α₀) (8 * k + 2)
      (Finset.Icc (4 * k + 1) (8 * k + 2) ∪ shiftW (2 * k) G
        ∪ Finset.range (2 * k + 1)) := by
  set G8 : Finset ℕ := Finset.Icc (4 * k + 1) (8 * k + 2) ∪ shiftW (2 * k) G
    ∪ Finset.range (2 * k + 1) with hG8
  set T₁ : A[X] := S₂ * S₂ - S₁ * S₁ + S₃ with hT₁
  set T₂ : A[X] := (S₂ + C a) * (S₂ + C a) - St₁ * St₁ + C α₀ with hT₂
  set Y : A[X] := combined T₁ T₂ with hY
  have hXmul : ∀ (P : A[X]) (i : ℕ), 1 ≤ i → (X * P).coeff i = P.coeff (i - 1) :=
    fun P _ hi => coeff_X_mul_of_pos hi
  -- degree bookkeeping
  have hS₁m := hsmall.monic₁
  have hSt₁m := hsmall.monic₂
  have hS₁d := hsmall.natDegree₁
  have hSt₁d := hsmall.natDegree₂
  have hS₁sqd : (S₁ * S₁).natDegree = 4 * k := by
    rw [hS₁m.natDegree_mul hS₁m, hS₁d]
    ring
  have hSt₁sqd : (St₁ * St₁).natDegree = 4 * k := by
    rw [hSt₁m.natDegree_mul hSt₁m, hSt₁d]
    ring
  obtain ⟨hS₂am, hS₂ad0⟩ := monic_add_C hS₂m (by rw [hS₂d]; omega) a
  have hS₂ad : (S₂ + C a).natDegree = 4 * k + 1 := hS₂ad0.trans hS₂d
  have hS₂sqm : (S₂ * S₂).Monic := hS₂m.mul hS₂m
  have hS₂sqd : (S₂ * S₂).natDegree = 8 * k + 2 := by
    rw [hS₂m.natDegree_mul hS₂m, hS₂d]
    ring
  obtain ⟨hT₁m, hT₁d⟩ : T₁.Monic ∧ T₁.natDegree = 8 * k + 2 := by
    have heq : T₁ = S₂ * S₂ + (S₃ - S₁ * S₁) := by
      rw [hT₁]
      ring
    rw [heq]
    have h := monic_add_low (P := S₂ * S₂) (e := S₃ - S₁ * S₁) hS₂sqm
      (Or.inr (by
        have hs := natDegree_sub_le S₃ (S₁ * S₁)
        omega))
    exact ⟨h.1, h.2.trans hS₂sqd⟩
  obtain ⟨hT₂m, hT₂d⟩ : T₂.Monic ∧ T₂.natDegree = 8 * k + 2 := by
    have hS₂asqm : ((S₂ + C a) * (S₂ + C a)).Monic := hS₂am.mul hS₂am
    have hS₂asqd : ((S₂ + C a) * (S₂ + C a)).natDegree = 8 * k + 2 := by
      rw [hS₂am.natDegree_mul hS₂am, hS₂ad]
      ring
    have heq : T₂ = (S₂ + C a) * (S₂ + C a) + (C α₀ - St₁ * St₁) := by
      rw [hT₂]
      ring
    rw [heq]
    have h := monic_add_low (P := (S₂ + C a) * (S₂ + C a))
      (e := C α₀ - St₁ * St₁) hS₂asqm
      (Or.inr (by
        have hs := natDegree_sub_le (C α₀) (St₁ * St₁)
        have hc : (C α₀ : A[X]).natDegree = 0 := natDegree_C _
        omega))
    exact ⟨h.1, h.2.trans hS₂asqd⟩
  -- the top shell: recover S₂ and a at their causal cutoffs
  have hVanti : Antitone (fun t => Vis R K Y G8 t) := by
    intro s t hst
    exact Vis_antitone_cutoff hst
  have hEz : ∀ i, 4 * k + 1 < i →
      (-(X * (S₁ * S₁)) - St₁ * St₁ + X * S₃ + C α₀).coeff i = 0 :=
    shell_coeff_zero₄ (by omega) (by omega) (by omega)
      ((natDegree_C α₀).le.trans (Nat.zero_le _))
  have hEb : (-(X * (S₁ * S₁)) - St₁ * St₁ + X * S₃ + C α₀).coeff (4 * k + 1)
      ∈ Vis R K Y G8 (4 * k + 1) := by
    have hlead : (S₁ * S₁).coeff (4 * k) = 1 := by
      have h := (hS₁m.mul hS₁m).coeff_natDegree
      rwa [hS₁sqd] at h
    rw [shell_coeff_seam₄ hlead (by omega) (by omega)
      ((natDegree_C α₀).le.trans (Nat.zero_le _)) (by omega)]
    exact known_mem_Vis (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
  have hYeq : Y = X * S₂ ^ 2 + (S₂ + C a) ^ 2
      + (-(X * (S₁ * S₁)) - St₁ * St₁ + X * S₃ + C α₀) := by
    rw [hY, hT₁, hT₂]
    exact combined_shell_eq S₂ (S₁ * S₁) (St₁ * St₁) S₃ (C α₀) a
  obtain ⟨hS₂cut, hacut⟩ := coeff_mem_of_square_gadget_relative
    (fun t => Vis R K Y G8 t) hVanti hS₂m hS₂d (by omega) h2
    (by
      intro i h1 hi
      refine coeff_mem_Vis ?_ le_rfl
      rw [hG8]
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      exact Finset.mem_Icc.2 ⟨h1, by omega⟩)
    hEz hEb hYeq
  -- squares of the smaller pair, transported to the output windows
  have hsq := hsmall.sq h2
  have hS₂sqcut : ∀ j t, t ≤ j + 1 → (S₂ * S₂).coeff j ∈ Vis R K Y G8 t := by
    intro j t htj
    refine Vis_antitone_cutoff htj ?_
    rw [← sq]
    exact coeff_sq_mem_of_schedule (V := fun t => Vis R K Y G8 t)
      (d := 4 * k + 1) (e := 1) hVanti (le_of_eq hS₂d)
      (fun i => Vis_antitone_cutoff (by omega) (hS₂cut i)) j
  have hS₂asqcut : ∀ j t, t ≤ j → ((S₂ + C a) * (S₂ + C a)).coeff j
      ∈ Vis R K Y G8 t := by
    intro j t htj
    refine Vis_antitone_cutoff htj ?_
    have hadd : ∀ i, (S₂ + C a).coeff i ∈ Vis R K Y G8 (i + (4 * k + 1) + 0) := by
      intro i
      rw [coeff_add, coeff_C]
      refine Subalgebra.add_mem _ (Vis_antitone_cutoff (by omega) (hS₂cut i)) ?_
      split
      · exact Vis_antitone_cutoff (by omega) hacut
      · exact Subalgebra.zero_mem _
    rw [← sq]
    exact coeff_sq_mem_of_schedule (V := fun t => Vis R K Y G8 t)
      (d := 4 * k + 1) (e := 0) hVanti (le_of_eq hS₂ad) hadd j
  -- the Ψ-window transport
  have hΨle : ∀ t, Vis R K (combined (S₁ * S₁) (St₁ * St₁)) (shiftW (2 * k) G) t
      ≤ Vis R K Y G8 t := by
    intro t
    refine Vis_le le_sup_left ?_
    intro r hr htr
    obtain ⟨i, hiG, hir⟩ := mem_shiftW.1 hr
    have hiW := hsmall.window hiG
    have hile : i ≤ 2 * k := by
      have := Finset.mem_range.1 hiW
      omega
    have hrle : r ≤ 4 * k := by omega
    have hr1 : 1 ≤ r := by omega
    have hkey : (combined (S₁ * S₁) (St₁ * St₁)).coeff r
        = (X * S₂ ^ 2 + (S₂ + C a) ^ 2).coeff r
          + (X * S₃ + C α₀).coeff r - Y.coeff r := by
      have hYc : Y.coeff r = (X * S₂ ^ 2 + (S₂ + C a) ^ 2).coeff r
          + (-(X * (S₁ * S₁)) - St₁ * St₁ + X * S₃ + C α₀).coeff r := by
        conv_lhs => rw [hYeq]
        rw [coeff_add]
      have hcombc : (combined (S₁ * S₁) (St₁ * St₁)).coeff r
          = (X * (S₁ * S₁)).coeff r + (St₁ * St₁).coeff r := by
        show (X * (S₁ * S₁) + St₁ * St₁).coeff r = _
        rw [coeff_add]
      rw [hcombc, hYc]
      simp only [coeff_add, coeff_sub, coeff_neg]
      ring
    rw [hkey]
    refine Subalgebra.sub_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_
    · rw [coeff_add, hXmul _ r (by omega)]
      refine Subalgebra.add_mem _ ?_ ?_
      · rw [sq]
        exact hS₂sqcut (r - 1) t (by omega)
      · rw [sq]
        exact hS₂asqcut r t (by omega)
    · rw [coeff_add, hXmul _ r (by omega), coeff_C, if_neg (by omega)]
      refine Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _)
      rcases Nat.lt_or_ge (r - 1) (2 * k - 1) with hlo | hhi
      · -- below the S₃ lead the window rows do not reach: r - 1 < 2k - 1
        -- but then r ≤ 2k - 1 < 2k, contradicting r = 2k + i
        omega
      · rcases eq_or_lt_of_le hhi with heq | hgt
        · rw [← heq]
          exact known_mem_Vis hS₃lead
        · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
          exact Subalgebra.zero_mem _
    · refine Vis_antitone_cutoff htr (coeff_mem_Vis ?_ le_rfl)
      rw [hG8]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hr)
  -- assemble the compatible pair
  refine
    { mem₁ := ?_
      mem₂ := ?_
      monic₁ := hT₁m
      monic₂ := hT₂m
      natDegree₁ := hT₁d
      natDegree₂ := hT₂d
      window := ?_ }
  · intro j
    rcases Nat.lt_or_ge j (2 * k) with hjlo | hjhi
    · -- low rows: read through the next output row
      have hrow : j + 1 ∈ G8 := by
        rw [hG8]
        exact Finset.mem_union_right _ (Finset.mem_range.2 (by omega))
      have hYr : Y.coeff (j + 1) ∈ Vis R K Y G8 (j + 1) :=
        coeff_mem_Vis hrow le_rfl
      have hT₂r : T₂.coeff (j + 1) ∈ Vis R K Y G8 (j + 1) := by
        rw [hT₂, coeff_add, coeff_sub, coeff_C, if_neg (by omega)]
        refine Subalgebra.add_mem _ (Subalgebra.sub_mem _
          (hS₂asqcut (j + 1) (j + 1) le_rfl) ?_) (Subalgebra.zero_mem _)
        exact hΨle (j + 1) (hsq.mem₂ (j + 1))
      have hkey : T₁.coeff j = Y.coeff (j + 1) - T₂.coeff (j + 1) := by
        rw [hY, coeff_combined]
        ring
      rw [hkey]
      exact Subalgebra.sub_mem _ hYr hT₂r
    · -- content route: `S₃` vanishes here
      rw [hT₁, coeff_add, coeff_sub,
        show S₃.coeff j = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
        add_zero]
      refine Subalgebra.sub_mem _ (hS₂sqcut j (j + 1) le_rfl) ?_
      exact hΨle (j + 1) (hsq.mem₁ j)
  · intro j
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      have hrow : 0 ∈ G8 := by
        rw [hG8]
        exact Finset.mem_union_right _ (Finset.mem_range.2 (by omega))
      have hkey : T₂.coeff 0 = Y.coeff 0 := by
        rw [hY, coeff_combined_zero]
      rw [hkey]
      exact coeff_mem_Vis hrow le_rfl
    · rw [hT₂, coeff_add, coeff_sub, coeff_C, if_neg (by omega)]
      refine Subalgebra.add_mem _ (Subalgebra.sub_mem _
        (hS₂asqcut j j le_rfl) ?_) (Subalgebra.zero_mem _)
      exact hΨle j (hsq.mem₂ j)
  · intro x hx
    rw [hG8] at hx
    refine Finset.mem_range.2 ?_
    rcases Finset.mem_union.1 hx with hx' | hx'
    · rcases Finset.mem_union.1 hx' with hx'' | hx''
      · have := Finset.mem_Icc.1 hx''
        omega
      · obtain ⟨i, hiG, hir⟩ := mem_shiftW.1 hx''
        have := Finset.mem_range.1 (hsmall.window hiG)
        omega
    · have := Finset.mem_range.1 hx'
      omega

set_option maxHeartbeats 1000000 in
/-- **`lem:8k+7-splittable`, compatibility half**: the `8k+7` output pair over a
compatible smaller pair and the two monic auxiliaries is compatible on
`{2k+1,…,8k+6} ∪ G`. -/
theorem eightk7_compatible (hk : 1 ≤ k) (h2 : IsUnit (2 : R))
    {T₁' T₂' S₂ S₃ : A[X]} {a b : A} {G : Finset ℕ}
    (hsmall : CompatiblePair K T₁' T₂' (2 * k) G)
    (hS₂m : S₂.Monic) (hS₂d : S₂.natDegree = 2 * k + 1)
    (hS₃m : S₃.Monic) (hS₃d : S₃.natDegree = 4 * k + 3) :
    CompatiblePair K (S₃ * S₃ - S₂ * S₂ + T₁')
      ((S₃ + C b) * (S₃ + C b) - (S₂ + C a) * (S₂ + C a) + T₂')
      (8 * k + 6) (Finset.Icc (2 * k + 1) (8 * k + 6) ∪ G) := by
  set G8 : Finset ℕ := Finset.Icc (2 * k + 1) (8 * k + 6) ∪ G with hG8
  set T₁ : A[X] := S₃ * S₃ - S₂ * S₂ + T₁' with hT₁
  set T₂ : A[X] := (S₃ + C b) * (S₃ + C b) - (S₂ + C a) * (S₂ + C a) + T₂'
    with hT₂
  set Y : A[X] := combined T₁ T₂ with hY
  have hXmul : ∀ (P : A[X]) (i : ℕ), 1 ≤ i → (X * P).coeff i = P.coeff (i - 1) :=
    fun P _ hi => coeff_X_mul_of_pos hi
  have hT₁'m := hsmall.monic₁
  have hT₂'m := hsmall.monic₂
  have hT₁'d := hsmall.natDegree₁
  have hT₂'d := hsmall.natDegree₂
  -- monic shift facts
  obtain ⟨hS₃bm, hS₃bd0⟩ := monic_add_C hS₃m (by rw [hS₃d]; omega) b
  have hS₃bd : (S₃ + C b).natDegree = 4 * k + 3 := hS₃bd0.trans hS₃d
  obtain ⟨hS₂am, hS₂ad0⟩ := monic_add_C hS₂m (by rw [hS₂d]; omega) a
  have hS₂ad : (S₂ + C a).natDegree = 2 * k + 1 := hS₂ad0.trans hS₂d
  have hS₃sqm : (S₃ * S₃).Monic := hS₃m.mul hS₃m
  have hS₃sqd : (S₃ * S₃).natDegree = 8 * k + 6 := by
    rw [hS₃m.natDegree_mul hS₃m, hS₃d]
    ring
  have hS₃bsqm : ((S₃ + C b) * (S₃ + C b)).Monic := hS₃bm.mul hS₃bm
  have hS₃bsqd : ((S₃ + C b) * (S₃ + C b)).natDegree = 8 * k + 6 := by
    rw [hS₃bm.natDegree_mul hS₃bm, hS₃bd]
    ring
  have hS₂sqd : (S₂ * S₂).natDegree = 4 * k + 2 := by
    rw [hS₂m.natDegree_mul hS₂m, hS₂d]
    ring
  have hS₂asqd : ((S₂ + C a) * (S₂ + C a)).natDegree = 4 * k + 2 := by
    rw [hS₂am.natDegree_mul hS₂am, hS₂ad]
    ring
  obtain ⟨hT₁m, hT₁d⟩ : T₁.Monic ∧ T₁.natDegree = 8 * k + 6 := by
    have heq : T₁ = S₃ * S₃ + (T₁' - S₂ * S₂) := by
      rw [hT₁]
      ring
    rw [heq]
    have h := monic_add_low (P := S₃ * S₃) (e := T₁' - S₂ * S₂) hS₃sqm
      (Or.inr (by
        have hs := natDegree_sub_le T₁' (S₂ * S₂)
        omega))
    exact ⟨h.1, h.2.trans hS₃sqd⟩
  obtain ⟨hT₂m, hT₂d⟩ : T₂.Monic ∧ T₂.natDegree = 8 * k + 6 := by
    have heq : T₂ = (S₃ + C b) * (S₃ + C b)
        + (T₂' - (S₂ + C a) * (S₂ + C a)) := by
      rw [hT₂]
      ring
    rw [heq]
    have h := monic_add_low (P := (S₃ + C b) * (S₃ + C b))
      (e := T₂' - (S₂ + C a) * (S₂ + C a)) hS₃bsqm
      (Or.inr (by
        have hs := natDegree_sub_le T₂' ((S₂ + C a) * (S₂ + C a))
        omega))
    exact ⟨h.1, h.2.trans hS₃bsqd⟩
  have hVanti : Antitone (fun t => Vis R K Y G8 t) := by
    intro s t hst
    exact Vis_antitone_cutoff hst
  -- shell 1: recover S₃ and b
  have hE₃z : ∀ i, 4 * k + 3 < i →
      (-(X * (S₂ * S₂)) - (S₂ + C a) * (S₂ + C a) + X * T₁' + T₂').coeff i
        = 0 :=
    shell_coeff_zero₄ (by omega) (by omega) (by omega) (by omega)
  have hE₃b : (-(X * (S₂ * S₂)) - (S₂ + C a) * (S₂ + C a) + X * T₁'
      + T₂').coeff (4 * k + 3) ∈ Vis R K Y G8 (4 * k + 3) := by
    have hlead : (S₂ * S₂).coeff (4 * k + 2) = 1 := by
      have h := (hS₂m.mul hS₂m).coeff_natDegree
      rwa [hS₂sqd] at h
    rw [shell_coeff_seam₄ hlead (by omega) (by omega) (by omega) (by omega)]
    exact known_mem_Vis (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
  have hYeq : Y = X * S₃ ^ 2 + (S₃ + C b) ^ 2
      + (-(X * (S₂ * S₂)) - (S₂ + C a) * (S₂ + C a) + X * T₁' + T₂') := by
    rw [hY, hT₁, hT₂]
    exact combined_shell_eq S₃ (S₂ * S₂) ((S₂ + C a) * (S₂ + C a)) T₁' T₂' b
  obtain ⟨hS₃cut, hbcut⟩ := coeff_mem_of_square_gadget_relative
    (fun t => Vis R K Y G8 t) hVanti hS₃m hS₃d (by omega) h2
    (by
      intro i h1 hi
      refine coeff_mem_Vis ?_ le_rfl
      rw [hG8]
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    hE₃z hE₃b hYeq
  -- pair products of `S₃` at their cutoffs
  have hS₃sqcut : ∀ j t, t ≤ j + 1 → (S₃ * S₃).coeff j ∈ Vis R K Y G8 t := by
    intro j t htj
    refine Vis_antitone_cutoff htj ?_
    rw [← sq]
    exact coeff_sq_mem_of_schedule (V := fun t => Vis R K Y G8 t)
      (d := 4 * k + 3) (e := 1) hVanti (le_of_eq hS₃d)
      (fun i => Vis_antitone_cutoff (by omega) (hS₃cut i)) j
  have hS₃bsqcut : ∀ j t, t ≤ j → ((S₃ + C b) * (S₃ + C b)).coeff j
      ∈ Vis R K Y G8 t := by
    intro j t htj
    refine Vis_antitone_cutoff htj ?_
    have hadd : ∀ i, (S₃ + C b).coeff i ∈ Vis R K Y G8 (i + (4 * k + 3) + 0) := by
      intro i
      rw [coeff_add, coeff_C]
      refine Subalgebra.add_mem _ (Vis_antitone_cutoff (by omega) (hS₃cut i)) ?_
      split
      · exact Vis_antitone_cutoff (by omega) hbcut
      · exact Subalgebra.zero_mem _
    rw [← sq]
    exact coeff_sq_mem_of_schedule (V := fun t => Vis R K Y G8 t)
      (d := 4 * k + 3) (e := 0) hVanti (le_of_eq hS₃bd) hadd j
  -- shell 2: recover S₂ and a from the peeled rows
  set Y₂ : A[X] := X * S₂ ^ 2 + (S₂ + C a) ^ 2 + (-(X * T₁') - T₂') with hY₂
  have hY₂c : ∀ i, Y₂.coeff i
      = (X * S₃ ^ 2).coeff i + ((S₃ + C b) ^ 2).coeff i - Y.coeff i := by
    intro i
    have hkey : Y₂ = X * S₃ ^ 2 + (S₃ + C b) ^ 2 - Y := by
      rw [hY₂, hYeq]
      ring
    rw [hkey, coeff_sub, coeff_add]
  have hE₂z : ∀ i, 2 * k + 1 < i → (-(X * T₁') - T₂').coeff i = 0 :=
    shell_coeff_zero₂ (by omega) (by omega)
  have hE₂b : (-(X * T₁') - T₂').coeff (2 * k + 1) ∈ Vis R K Y G8 (2 * k + 1) := by
    have hlead : T₁'.coeff (2 * k) = 1 := by
      rw [← hT₁'d]
      exact hT₁'m.coeff_natDegree
    rw [shell_coeff_seam₂ hlead (by omega) (by omega)]
    exact known_mem_Vis (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
  obtain ⟨hS₂cut, hacut⟩ := coeff_mem_of_square_gadget_relative
    (fun t => Vis R K Y G8 t) hVanti hS₂m hS₂d (by omega) h2
    (by
      intro i h1 hi
      rw [hY₂c]
      refine Subalgebra.sub_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_
      · rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · omega
        · rw [hXmul _ i (by omega), sq]
          exact hS₃sqcut (i - 1) i (by omega)
      · rw [sq]
        exact hS₃bsqcut i i le_rfl
      · refine coeff_mem_Vis ?_ le_rfl
        rw [hG8]
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    hE₂z hE₂b rfl
  have hS₂sqcut : ∀ j t, t ≤ j + 1 → (S₂ * S₂).coeff j ∈ Vis R K Y G8 t := by
    intro j t htj
    refine Vis_antitone_cutoff htj ?_
    rw [← sq]
    exact coeff_sq_mem_of_schedule (V := fun t => Vis R K Y G8 t)
      (d := 2 * k + 1) (e := 1) hVanti (le_of_eq hS₂d)
      (fun i => Vis_antitone_cutoff (by omega) (hS₂cut i)) j
  have hS₂asqcut : ∀ j t, t ≤ j → ((S₂ + C a) * (S₂ + C a)).coeff j
      ∈ Vis R K Y G8 t := by
    intro j t htj
    refine Vis_antitone_cutoff htj ?_
    have hadd : ∀ i, (S₂ + C a).coeff i ∈ Vis R K Y G8 (i + (2 * k + 1) + 0) := by
      intro i
      rw [coeff_add, coeff_C]
      refine Subalgebra.add_mem _ (Vis_antitone_cutoff (by omega) (hS₂cut i)) ?_
      split
      · exact Vis_antitone_cutoff (by omega) hacut
      · exact Subalgebra.zero_mem _
    rw [← sq]
    exact coeff_sq_mem_of_schedule (V := fun t => Vis R K Y G8 t)
      (d := 2 * k + 1) (e := 0) hVanti (le_of_eq hS₂ad) hadd j
  -- the smaller pair transported to the output windows
  have hsmle : ∀ t, Vis R K (combined T₁' T₂') G t ≤ Vis R K Y G8 t := by
    intro t
    refine Vis_le le_sup_left ?_
    intro r hr htr
    have hrW := hsmall.window hr
    have hrle : r ≤ 2 * k := by
      have := Finset.mem_range.1 hrW
      omega
    have hkey : (combined T₁' T₂').coeff r
        = Y.coeff r - (X * (S₃ * S₃)).coeff r - ((S₃ + C b) * (S₃ + C b)).coeff r
          + (X * (S₂ * S₂)).coeff r + ((S₂ + C a) * (S₂ + C a)).coeff r := by
      have hYc : Y.coeff r = (X * (S₃ * S₃)).coeff r
          + ((S₃ + C b) * (S₃ + C b)).coeff r
          - (X * (S₂ * S₂)).coeff r - ((S₂ + C a) * (S₂ + C a)).coeff r
          + (X * T₁').coeff r + T₂'.coeff r := by
        conv_lhs => rw [hYeq]
        simp only [coeff_add, coeff_sub, coeff_neg, sq]
        ring
      have hcombc : (combined T₁' T₂').coeff r
          = (X * T₁').coeff r + T₂'.coeff r := by
        show (X * T₁' + T₂').coeff r = _
        rw [coeff_add]
      rw [hcombc]
      rw [hYc]
      ring
    rw [hkey]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (Subalgebra.sub_mem _ ?_ ?_) ?_) ?_) ?_
    · exact Vis_antitone_cutoff htr (coeff_mem_Vis (by
        rw [hG8]
        exact Finset.mem_union_right _ hr) le_rfl)
    · rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · subst hr0
        have hz : (X * (S₃ * S₃)).coeff 0 = 0 := by
          rw [mul_coeff_zero, coeff_X_zero, zero_mul]
        rw [hz]
        exact Subalgebra.zero_mem _
      · rw [hXmul _ r (by omega)]
        exact Vis_antitone_cutoff htr (hS₃sqcut (r - 1) r (by omega))
    · exact Vis_antitone_cutoff htr (hS₃bsqcut r r le_rfl)
    · rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · subst hr0
        have hz : (X * (S₂ * S₂)).coeff 0 = 0 := by
          rw [mul_coeff_zero, coeff_X_zero, zero_mul]
        rw [hz]
        exact Subalgebra.zero_mem _
      · rw [hXmul _ r (by omega)]
        exact Vis_antitone_cutoff htr (hS₂sqcut (r - 1) r (by omega))
    · exact Vis_antitone_cutoff htr (hS₂asqcut r r le_rfl)
  -- assemble
  refine
    { mem₁ := ?_
      mem₂ := ?_
      monic₁ := hT₁m
      monic₂ := hT₂m
      natDegree₁ := hT₁d
      natDegree₂ := hT₂d
      window := ?_ }
  · intro j
    rw [hT₁, coeff_add, coeff_sub]
    refine Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (hS₃sqcut j (j + 1) le_rfl) (hS₂sqcut j (j + 1) le_rfl)) ?_
    exact hsmle (j + 1) (hsmall.mem₁ j)
  · intro j
    rw [hT₂, coeff_add, coeff_sub]
    refine Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (hS₃bsqcut j j le_rfl) (hS₂asqcut j j le_rfl)) ?_
    exact hsmle j (hsmall.mem₂ j)
  · intro x hx
    rw [hG8] at hx
    refine Finset.mem_range.2 ?_
    rcases Finset.mem_union.1 hx with hx' | hx'
    · have := Finset.mem_Icc.1 hx'
      omega
    · have := Finset.mem_range.1 (hsmall.window hx')
      omega

set_option maxHeartbeats 1000000 in
/-- **`lem:8k+3-splittable`, decodability half**: with V-relative decoders for the
smaller pair and the two auxiliary gadgets, every parameter of the `8k+3` output is
recovered from the output coefficients.  The auxiliary decoders are only invoked after
the powers they need have been reconstructed. -/
theorem eightk3_decodable (hk : 1 ≤ k) (h2 : IsUnit (2 : R))
    {S₁ St₁ S₂ S₃ H₂ H₄ : A[X]} {a α₀ : A} {G : Finset ℕ}
    {Θs Θ₂ Θ₃ : Set A}
    (hsmall : CompatiblePair K S₁ St₁ (2 * k) G)
    (hS₂m : S₂.Monic) (hS₂d : S₂.natDegree = 4 * k + 1)
    (hS₃d : S₃.natDegree ≤ 2 * k - 1) (hS₃lead : S₃.coeff (2 * k - 1) ∈ K)
    (hsmalldec : ∀ V : Subalgebra R A, K ≤ V →
      (∀ j, (combined S₁ St₁).coeff j ∈ V) →
      Θs ⊆ (V : Set A) ∧ (∀ j, H₂.coeff j ∈ V))
    (hS₂dec : ∀ V : Subalgebra R A, K ≤ V →
      (∀ j, S₂.coeff j ∈ V) → (∀ j, H₂.coeff j ∈ V) →
      Θ₂ ⊆ (V : Set A) ∧ (∀ j, H₄.coeff j ∈ V))
    (hS₃dec : ∀ V : Subalgebra R A, K ≤ V →
      (∀ j, S₃.coeff j ∈ V) → (∀ j, H₂.coeff j ∈ V) → (∀ j, H₄.coeff j ∈ V) →
      Θ₃ ⊆ (V : Set A))
    {P : A[X]}
    (hP : P = combined (S₂ * S₂ - S₁ * S₁ + S₃)
      ((S₂ + C a) * (S₂ + C a) - St₁ * St₁ + C α₀)) :
    a ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    α₀ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    Θs ⊆ ((K ⊔ adjoin R (Set.range fun i => P.coeff i) : Subalgebra R A) : Set A) ∧
    Θ₂ ⊆ ((K ⊔ adjoin R (Set.range fun i => P.coeff i) : Subalgebra R A) : Set A) ∧
    Θ₃ ⊆ ((K ⊔ adjoin R (Set.range fun i => P.coeff i) : Subalgebra R A) : Set A) := by
  set VP : Subalgebra R A := K ⊔ adjoin R (Set.range fun i => P.coeff i) with hVP
  have hKVP : K ≤ VP := le_sup_left
  have hPmem : ∀ i, P.coeff i ∈ VP :=
    fun i => (le_sup_right : adjoin R _ ≤ VP) (subset_adjoin ⟨i, rfl⟩)
  have hXmul : ∀ (Q : A[X]) (i : ℕ), 1 ≤ i → (X * Q).coeff i = Q.coeff (i - 1) :=
    fun Q _ hi => coeff_X_mul_of_pos hi
  have hS₁m := hsmall.monic₁
  have hSt₁m := hsmall.monic₂
  have hS₁d := hsmall.natDegree₁
  have hSt₁d := hsmall.natDegree₂
  have hS₁sqd : (S₁ * S₁).natDegree = 4 * k := by
    rw [hS₁m.natDegree_mul hS₁m, hS₁d]
    ring
  have hSt₁sqd : (St₁ * St₁).natDegree = 4 * k := by
    rw [hSt₁m.natDegree_mul hSt₁m, hSt₁d]
    ring
  -- the outer shell at the constant context
  have hEz : ∀ i, 4 * k + 1 < i →
      (-(X * (S₁ * S₁)) - St₁ * St₁ + X * S₃ + C α₀).coeff i = 0 :=
    shell_coeff_zero₄ (by omega) (by omega) (by omega)
      ((natDegree_C α₀).le.trans (Nat.zero_le _))
  have hEb : (-(X * (S₁ * S₁)) - St₁ * St₁ + X * S₃ + C α₀).coeff (4 * k + 1)
      ∈ VP := by
    have hlead : (S₁ * S₁).coeff (4 * k) = 1 := by
      have h := (hS₁m.mul hS₁m).coeff_natDegree
      rwa [hS₁sqd] at h
    rw [shell_coeff_seam₄ hlead (by omega) (by omega)
      ((natDegree_C α₀).le.trans (Nat.zero_le _)) (by omega)]
    exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
  have hPeq : P = X * S₂ ^ 2 + (S₂ + C a) ^ 2
      + (-(X * (S₁ * S₁)) - St₁ * St₁ + X * S₃ + C α₀) := by
    rw [hP]
    exact combined_shell_eq S₂ (S₁ * S₁) (St₁ * St₁) S₃ (C α₀) a
  obtain ⟨hS₂cV, hacV⟩ := coeff_mem_of_square_gadget_relative
    (fun _ => VP) (fun _ _ _ => le_rfl) hS₂m hS₂d (by omega) h2
    (fun i _ _ => hPmem i) hEz hEb hPeq
  have hS₂cV' : ∀ j, S₂.coeff j ∈ VP := fun j => hS₂cV j
  have haV : a ∈ VP := hacV
  have hS₂sqV : ∀ j, (S₂ * S₂).coeff j ∈ VP := coeff_mem_mul hS₂cV' hS₂cV'
  have hco : ∀ i, (S₂ + C a).coeff i ∈ VP := coeff_add_C_mem hS₂cV' haV
  have hS₂asqV : ∀ j, ((S₂ + C a) * (S₂ + C a)).coeff j ∈ VP :=
    coeff_mem_mul hco hco
  -- squares of the smaller pair from the middle window
  have hsq := hsmall.sq h2
  have hΨwin : ∀ r ∈ shiftW (2 * k) G,
      (combined (S₁ * S₁) (St₁ * St₁)).coeff r ∈ VP := by
    intro r hr
    obtain ⟨i, hiG, hir⟩ := mem_shiftW.1 hr
    have hile : i ≤ 2 * k := by
      have := Finset.mem_range.1 (hsmall.window hiG)
      omega
    have hr1 : 1 ≤ r := by omega
    have hkey : (combined (S₁ * S₁) (St₁ * St₁)).coeff r
        = (X * S₂ ^ 2 + (S₂ + C a) ^ 2).coeff r
          + (X * S₃ + C α₀).coeff r - P.coeff r := by
      have hPc : P.coeff r = (X * S₂ ^ 2 + (S₂ + C a) ^ 2).coeff r
          + (-(X * (S₁ * S₁)) - St₁ * St₁ + X * S₃ + C α₀).coeff r := by
        conv_lhs => rw [hPeq]
        rw [coeff_add]
      have hcombc : (combined (S₁ * S₁) (St₁ * St₁)).coeff r
          = (X * (S₁ * S₁)).coeff r + (St₁ * St₁).coeff r := by
        show (X * (S₁ * S₁) + St₁ * St₁).coeff r = _
        rw [coeff_add]
      rw [hcombc, hPc]
      simp only [coeff_add, coeff_sub, coeff_neg]
      ring
    rw [hkey]
    refine Subalgebra.sub_mem _ (Subalgebra.add_mem _ ?_ ?_) (hPmem r)
    · rw [coeff_add, hXmul _ r (by omega), sq, sq]
      exact Subalgebra.add_mem _ (hS₂sqV (r - 1)) (hS₂asqV r)
    · rw [coeff_add, hXmul _ r (by omega), coeff_C, if_neg (by omega)]
      refine Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _)
      rcases Nat.lt_or_ge (r - 1) (2 * k - 1) with hlo | hhi
      · omega
      · rcases eq_or_lt_of_le hhi with heq | hgt
        · rw [← heq]
          exact hKVP hS₃lead
        · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
          exact Subalgebra.zero_mem _
  have hS₁sqV : ∀ j, (S₁ * S₁).coeff j ∈ VP := by
    intro j
    have h := hsq.coeff₁_mem j
    refine SetLike.le_def.1 (Vis_le hKVP ?_) h
    intro i hi _
    exact hΨwin i hi
  have hSt₁sqV : ∀ j, (St₁ * St₁).coeff j ∈ VP := by
    intro j
    have h := hsq.coeff₂_mem j
    refine SetLike.le_def.1 (Vis_le hKVP ?_) h
    intro i hi _
    exact hΨwin i hi
  -- monic square roots
  have h2u : IsUnit ((2 : ℕ) : R) := by
    have hcast : ((2 : ℕ) : R) = (2 : R) := by norm_num
    rwa [hcast]
  have hS₁V : ∀ j, S₁.coeff j ∈ VP :=
    coeff_mem_of_sq_mem VP hS₁m hS₁d h2u hS₁sqV
  have hSt₁V : ∀ j, St₁.coeff j ∈ VP :=
    coeff_mem_of_sq_mem VP hSt₁m hSt₁d h2u hSt₁sqV
  -- the smaller block
  have hcombV : ∀ j, (combined S₁ St₁).coeff j ∈ VP :=
    coeff_combined_mem hS₁V hSt₁V
  obtain ⟨hΘs, hH₂V⟩ := hsmalldec VP hKVP hcombV
  -- `S₃` and `α₀`
  have hS₃V : ∀ j, S₃.coeff j ∈ VP := by
    intro j
    have hkey : S₃.coeff j
        = P.coeff (j + 1) - (X * S₂ ^ 2 + (S₂ + C a) ^ 2).coeff (j + 1)
          + (X * (S₁ * S₁)).coeff (j + 1) + (St₁ * St₁).coeff (j + 1) := by
      have hPc : P.coeff (j + 1) = (X * S₂ ^ 2 + (S₂ + C a) ^ 2).coeff (j + 1)
          + (-(X * (S₁ * S₁)) - St₁ * St₁ + X * S₃ + C α₀).coeff (j + 1) := by
        conv_lhs => rw [hPeq]
        rw [coeff_add]
      rw [hPc]
      simp only [coeff_add, coeff_sub, coeff_neg]
      rw [hXmul S₃ (j + 1) (by omega), show j + 1 - 1 = j from by omega,
        coeff_C, if_neg (by omega)]
      ring
    rw [hkey, coeff_add, hXmul _ (j + 1) (by omega), hXmul _ (j + 1) (by omega),
      show j + 1 - 1 = j from by omega, sq, sq]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (hPmem _) (Subalgebra.add_mem _ (hS₂sqV j) (hS₂asqV (j + 1)))) ?_) ?_
    · exact hS₁sqV j
    · exact hSt₁sqV (j + 1)
  have hα₀V : α₀ ∈ VP := by
    have hkey : α₀ = P.coeff 0 - ((S₂ + C a) * (S₂ + C a)).coeff 0
        + (St₁ * St₁).coeff 0 := by
      have hPc : P.coeff 0
          = ((S₂ + C a) * (S₂ + C a) - St₁ * St₁ + C α₀).coeff 0 := by
        rw [hP, coeff_combined_zero]
      rw [hPc, coeff_add, coeff_sub, coeff_C_zero]
      ring
    rw [hkey]
    exact Subalgebra.add_mem _ (Subalgebra.sub_mem _ (hPmem 0) (hS₂asqV 0))
      (hSt₁sqV 0)
  -- the auxiliary blocks, powers reconstructed first
  obtain ⟨hΘ₂, hH₄V⟩ := hS₂dec VP hKVP hS₂cV' hH₂V
  have hΘ₃ := hS₃dec VP hKVP hS₃V hH₂V hH₄V
  exact ⟨haV, hα₀V, hΘs, hΘ₂, hΘ₃⟩


set_option maxHeartbeats 1000000 in
/-- **`lem:8k+7-splittable`, decodability half**: the two nested shells recover the
auxiliaries, the smaller polynomial is isolated linearly, and the V-relative decoders
extract every block — powers reconstructed before the gadget decoders run. -/
theorem eightk7_decodable (hk : 1 ≤ k) (h2 : IsUnit (2 : R))
    {T₁' T₂' S₂ S₃ H₂ H₄ : A[X]} {a b : A} {G : Finset ℕ}
    {Θs Θ₂ Θ₃ : Set A}
    (hsmall : CompatiblePair K T₁' T₂' (2 * k) G)
    (hS₂m : S₂.Monic) (hS₂d : S₂.natDegree = 2 * k + 1)
    (hS₃m : S₃.Monic) (hS₃d : S₃.natDegree = 4 * k + 3)
    (hsmalldec : ∀ V : Subalgebra R A, K ≤ V →
      (∀ j, (combined T₁' T₂').coeff j ∈ V) →
      Θs ⊆ (V : Set A) ∧ (∀ j, H₂.coeff j ∈ V) ∧ (∀ j, H₄.coeff j ∈ V))
    (hS₂dec : ∀ V : Subalgebra R A, K ≤ V →
      (∀ j, S₂.coeff j ∈ V) → (∀ j, H₂.coeff j ∈ V) → (∀ j, H₄.coeff j ∈ V) →
      Θ₂ ⊆ (V : Set A))
    (hS₃dec : ∀ V : Subalgebra R A, K ≤ V →
      (∀ j, S₃.coeff j ∈ V) → (∀ j, H₂.coeff j ∈ V) → (∀ j, H₄.coeff j ∈ V) →
      Θ₃ ⊆ (V : Set A))
    {P : A[X]}
    (hP : P = combined (S₃ * S₃ - S₂ * S₂ + T₁')
      ((S₃ + C b) * (S₃ + C b) - (S₂ + C a) * (S₂ + C a) + T₂')) :
    a ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    b ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    Θs ⊆ ((K ⊔ adjoin R (Set.range fun i => P.coeff i) : Subalgebra R A) : Set A) ∧
    Θ₂ ⊆ ((K ⊔ adjoin R (Set.range fun i => P.coeff i) : Subalgebra R A) : Set A) ∧
    Θ₃ ⊆ ((K ⊔ adjoin R (Set.range fun i => P.coeff i) : Subalgebra R A) : Set A) := by
  set VP : Subalgebra R A := K ⊔ adjoin R (Set.range fun i => P.coeff i) with hVP
  have hKVP : K ≤ VP := le_sup_left
  have hPmem : ∀ i, P.coeff i ∈ VP :=
    fun i => (le_sup_right : adjoin R _ ≤ VP) (subset_adjoin ⟨i, rfl⟩)
  have hXmul : ∀ (Q : A[X]) (i : ℕ), 1 ≤ i → (X * Q).coeff i = Q.coeff (i - 1) :=
    fun Q _ hi => coeff_X_mul_of_pos hi
  have hT₁'m := hsmall.monic₁
  have hT₂'m := hsmall.monic₂
  have hT₁'d := hsmall.natDegree₁
  have hT₂'d := hsmall.natDegree₂
  have hS₂sqd : (S₂ * S₂).natDegree = 4 * k + 2 := by
    rw [hS₂m.natDegree_mul hS₂m, hS₂d]
    ring
  obtain ⟨hS₂am, hS₂ad0⟩ := monic_add_C hS₂m (by rw [hS₂d]; omega) a
  have hS₂ad : (S₂ + C a).natDegree = 2 * k + 1 := hS₂ad0.trans hS₂d
  have hS₂asqd : ((S₂ + C a) * (S₂ + C a)).natDegree = 4 * k + 2 := by
    rw [hS₂am.natDegree_mul hS₂am, hS₂ad]
    ring
  -- shell 1
  have hE₃z : ∀ i, 4 * k + 3 < i →
      (-(X * (S₂ * S₂)) - (S₂ + C a) * (S₂ + C a) + X * T₁' + T₂').coeff i
        = 0 :=
    shell_coeff_zero₄ (by omega) (by omega) (by omega) (by omega)
  have hE₃b : (-(X * (S₂ * S₂)) - (S₂ + C a) * (S₂ + C a) + X * T₁'
      + T₂').coeff (4 * k + 3) ∈ VP := by
    have hlead : (S₂ * S₂).coeff (4 * k + 2) = 1 := by
      have h := (hS₂m.mul hS₂m).coeff_natDegree
      rwa [hS₂sqd] at h
    rw [shell_coeff_seam₄ hlead (by omega) (by omega) (by omega) (by omega)]
    exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
  have hPeq : P = X * S₃ ^ 2 + (S₃ + C b) ^ 2
      + (-(X * (S₂ * S₂)) - (S₂ + C a) * (S₂ + C a) + X * T₁' + T₂') := by
    rw [hP]
    exact combined_shell_eq S₃ (S₂ * S₂) ((S₂ + C a) * (S₂ + C a)) T₁' T₂' b
  obtain ⟨hS₃cV, hbV⟩ := coeff_mem_of_square_gadget_relative
    (fun _ => VP) (fun _ _ _ => le_rfl) hS₃m hS₃d (by omega) h2
    (fun i _ _ => hPmem i) hE₃z hE₃b hPeq
  have hS₃sqV : ∀ j, (S₃ * S₃).coeff j ∈ VP := coeff_mem_mul hS₃cV hS₃cV
  have hS₃bV : ∀ i, (S₃ + C b).coeff i ∈ VP := coeff_add_C_mem hS₃cV hbV
  have hS₃bsqV : ∀ j, ((S₃ + C b) * (S₃ + C b)).coeff j ∈ VP :=
    coeff_mem_mul hS₃bV hS₃bV
  -- shell 2 on the peeled polynomial
  set Y₂ : A[X] := X * S₂ ^ 2 + (S₂ + C a) ^ 2 + (-(X * T₁') - T₂') with hY₂
  have hY₂rows : ∀ i, Y₂.coeff i ∈ VP := by
    intro i
    have hkey : Y₂ = X * S₃ ^ 2 + (S₃ + C b) ^ 2 - P := by
      rw [hY₂, hPeq]
      ring
    rw [hkey, coeff_sub, coeff_add, sq, sq]
    refine Subalgebra.sub_mem _ (Subalgebra.add_mem _ ?_ (hS₃bsqV i))
      (hPmem i)
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hz : (X * (S₃ * S₃)).coeff 0 = 0 := by
        rw [mul_coeff_zero, coeff_X_zero, zero_mul]
      rw [hz]
      exact Subalgebra.zero_mem _
    · rw [hXmul _ i (by omega)]
      exact hS₃sqV (i - 1)
  have hE₂z : ∀ i, 2 * k + 1 < i → (-(X * T₁') - T₂').coeff i = 0 :=
    shell_coeff_zero₂ (by omega) (by omega)
  have hE₂b : (-(X * T₁') - T₂').coeff (2 * k + 1) ∈ VP := by
    have hlead : T₁'.coeff (2 * k) = 1 := by
      rw [← hT₁'d]
      exact hT₁'m.coeff_natDegree
    rw [shell_coeff_seam₂ hlead (by omega) (by omega)]
    exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
  obtain ⟨hS₂cV, haV⟩ := coeff_mem_of_square_gadget_relative
    (fun _ => VP) (fun _ _ _ => le_rfl) hS₂m hS₂d (by omega) h2
    (fun i _ _ => hY₂rows i) hE₂z hE₂b rfl
  have hS₂sqV : ∀ j, (S₂ * S₂).coeff j ∈ VP := coeff_mem_mul hS₂cV hS₂cV
  have hS₂aV : ∀ i, (S₂ + C a).coeff i ∈ VP := coeff_add_C_mem hS₂cV haV
  have hS₂asqV : ∀ j, ((S₂ + C a) * (S₂ + C a)).coeff j ∈ VP :=
    coeff_mem_mul hS₂aV hS₂aV
  -- the smaller polynomial
  have hcombV : ∀ r, (combined T₁' T₂').coeff r ∈ VP := by
    intro r
    have hkey : (combined T₁' T₂').coeff r
        = P.coeff r - (X * (S₃ * S₃)).coeff r
          - ((S₃ + C b) * (S₃ + C b)).coeff r
          + (X * (S₂ * S₂)).coeff r + ((S₂ + C a) * (S₂ + C a)).coeff r := by
      have hPc : P.coeff r = (X * (S₃ * S₃)).coeff r
          + ((S₃ + C b) * (S₃ + C b)).coeff r
          - (X * (S₂ * S₂)).coeff r - ((S₂ + C a) * (S₂ + C a)).coeff r
          + (X * T₁').coeff r + T₂'.coeff r := by
        conv_lhs => rw [hPeq]
        simp only [coeff_add, coeff_sub, coeff_neg, sq]
        ring
      have hcombc : (combined T₁' T₂').coeff r
          = (X * T₁').coeff r + T₂'.coeff r := by
        show (X * T₁' + T₂').coeff r = _
        rw [coeff_add]
      rw [hcombc, hPc]
      ring
    rw [hkey]
    have hXS₃ : (X * (S₃ * S₃)).coeff r ∈ VP := by
      rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · subst hr0
        have hz : (X * (S₃ * S₃)).coeff 0 = 0 := by
          rw [mul_coeff_zero, coeff_X_zero, zero_mul]
        rw [hz]
        exact Subalgebra.zero_mem _
      · rw [hXmul _ r (by omega)]
        exact hS₃sqV (r - 1)
    have hXS₂ : (X * (S₂ * S₂)).coeff r ∈ VP := by
      rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · subst hr0
        have hz : (X * (S₂ * S₂)).coeff 0 = 0 := by
          rw [mul_coeff_zero, coeff_X_zero, zero_mul]
        rw [hz]
        exact Subalgebra.zero_mem _
      · rw [hXmul _ r (by omega)]
        exact hS₂sqV (r - 1)
    exact Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (Subalgebra.sub_mem _ (hPmem r) hXS₃) (hS₃bsqV r)) hXS₂) (hS₂asqV r)
  obtain ⟨hΘs, hH₂V, hH₄V⟩ := hsmalldec VP hKVP hcombV
  have hΘ₂ := hS₂dec VP hKVP hS₂cV hH₂V hH₄V
  have hΘ₃ := hS₃dec VP hKVP hS₃cV hH₂V hH₄V
  exact ⟨haV, hbV, hΘs, hΘ₂, hΘ₃⟩

end FastPoly
