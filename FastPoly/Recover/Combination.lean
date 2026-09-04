import FastPoly.Recover.Context

/-!
# Combination lemmas: Additivity

The two-source separation engine behind the paper's Additivity lemma: if two causal pairs
have disjoint windows, then everything visible for one summand is visible for the sum, with
the same cutoff.  The proof is a descending induction over the union window: at each index,
disjointness puts the index off-window for one side, whose combined coefficient is then
supplied by causality from strictly higher indices, and subtraction isolates the other side.

(The monic bookkeeping — degree corrections for the equal-degree case — is layered on top
in `CompatiblePair.add`, to come.)
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section additivity

variable {K : Subalgebra R A} {gL gR : Finset ℕ} {PL₁ PL₂ PR₁ PR₂ : A[X]}

/-- **Two-source separation** (the engine of Additivity): with disjoint windows, the visible
algebra of one summand's combined polynomial embeds into that of the sum, at every cutoff. -/
theorem vis_le_vis_add (hL : CausalPair K PL₁ PL₂ gL) (hR : CausalPair K PR₁ PR₂ gR)
    (hdis : Disjoint gL gR) (t : ℕ) :
    Vis R K (combined PL₁ PL₂) gL t ≤
      Vis R K (combined (PL₁ + PR₁) (PL₂ + PR₂)) (gL ∪ gR) t := by
  classical
  set ψL := combined PL₁ PL₂ with hψL
  set ψR := combined PR₁ PR₂ with hψR
  set ψs := combined (PL₁ + PR₁) (PL₂ + PR₂) with hψs
  have hsplit : ψs = ψL + ψR := by
    simp only [hψs, hψL, hψR, combined]; ring
  have hsum : ∀ i, ψs.coeff i = ψL.coeff i + ψR.coeff i := by
    intro i; rw [hsplit, coeff_add]
  set V := Vis R K ψs (gL ∪ gR) t with hV
  set U := (gL ∪ gR).filter (fun i => t ≤ i) with hU
  -- one descending step
  have step : ∀ k, k ∈ U → (∀ i ∈ U, k < i → ψL.coeff i ∈ V ∧ ψR.coeff i ∈ V) →
      ψL.coeff k ∈ V ∧ ψR.coeff k ∈ V := by
    intro k hkU ih
    obtain ⟨hkG, htk⟩ := Finset.mem_filter.1 hkU
    have hks : ψs.coeff k ∈ V := coeff_mem_Vis hkG htk
    rcases Finset.mem_union.1 hkG with hkL | hkR
    · -- k ∈ gL, hence k ∉ gR: the right side at k is causally determined from above
      have hkR' : k ∉ gR := Finset.disjoint_left.1 hdis hkL
      have hVR : Vis R K ψR gR k ≤ V := by
        refine Vis_le le_sup_left ?_
        intro i higR hki
        have hik : k < i :=
          lt_of_le_of_ne hki (fun h => hkR' (h ▸ higR))
        exact (ih i (Finset.mem_filter.2
          ⟨Finset.mem_union_right _ higR, le_trans htk (le_of_lt hik)⟩) hik).2
      have hRk : ψR.coeff k ∈ V := hVR (hR.combined_coeff_mem k)
      have hLk : ψL.coeff k ∈ V := by
        have hkey : ψL.coeff k = ψs.coeff k - ψR.coeff k := by rw [hsum k]; ring
        rw [hkey]; exact Subalgebra.sub_mem _ hks hRk
      exact ⟨hLk, hRk⟩
    · -- symmetric case: k ∈ gR, k ∉ gL
      have hkL' : k ∉ gL := Finset.disjoint_right.1 hdis hkR
      have hVL : Vis R K ψL gL k ≤ V := by
        refine Vis_le le_sup_left ?_
        intro i higL hki
        have hik : k < i :=
          lt_of_le_of_ne hki (fun h => hkL' (h ▸ higL))
        exact (ih i (Finset.mem_filter.2
          ⟨Finset.mem_union_left _ higL, le_trans htk (le_of_lt hik)⟩) hik).1
      have hLk : ψL.coeff k ∈ V := hVL (hL.combined_coeff_mem k)
      have hRk : ψR.coeff k ∈ V := by
        have hkey : ψR.coeff k = ψs.coeff k - ψL.coeff k := by rw [hsum k]; ring
        rw [hkey]; exact Subalgebra.sub_mem _ hks hLk
      exact ⟨hLk, hRk⟩
  -- close the descending induction
  have all : ∀ k ∈ U, ψL.coeff k ∈ V ∧ ψR.coeff k ∈ V :=
    descend_on_finset step
  -- transport the generators
  refine Vis_le le_sup_left ?_
  intro i higL hti
  exact (all i (Finset.mem_filter.2 ⟨Finset.mem_union_left _ higL, hti⟩)).1

/-- **Additivity for causal pairs** (paper Additivity, causal part; degree corrections for
the monic bookkeeping are layered on separately). -/
theorem CausalPair.add (hL : CausalPair K PL₁ PL₂ gL) (hR : CausalPair K PR₁ PR₂ gR)
    (hdis : Disjoint gL gR) :
    CausalPair K (PL₁ + PR₁) (PL₂ + PR₂) (gL ∪ gR) := by
  have hLle : ∀ t, Vis R K (combined PL₁ PL₂) gL t ≤
      Vis R K (combined (PL₁ + PR₁) (PL₂ + PR₂)) (gL ∪ gR) t :=
    vis_le_vis_add hL hR hdis
  have hRle : ∀ t, Vis R K (combined PR₁ PR₂) gR t ≤
      Vis R K (combined (PL₁ + PR₁) (PL₂ + PR₂)) (gL ∪ gR) t := by
    intro t
    have h := vis_le_vis_add hR hL hdis.symm t
    rwa [add_comm PR₁ PL₁, add_comm PR₂ PL₂, Finset.union_comm gR gL] at h
  exact
    { mem₁ := fun j => by
        rw [coeff_add]
        exact Subalgebra.add_mem _ (hLle (j + 1) (hL.mem₁ j)) (hRle (j + 1) (hR.mem₁ j))
      mem₂ := fun j => by
        rw [coeff_add]
        exact Subalgebra.add_mem _ (hLle j (hL.mem₂ j)) (hRle j (hR.mem₂ j)) }

end additivity

section additivity_monic

variable {K : Subalgebra R A} {gL gR : Finset ℕ} {PL₁ PL₂ PR₁ PR₂ : A[X]}

/-- Visible algebras agree for combined polynomials whose coefficients differ by known
elements. -/
theorem Vis_congr_of_diff_known {Φ Φ' : A[X]} {G : Finset ℕ}
    (h : ∀ i, Φ.coeff i - Φ'.coeff i ∈ K) (t : ℕ) :
    Vis R K Φ G t = Vis R K Φ' G t := by
  have half : ∀ (Ψ Ψ' : A[X]), (∀ i, Ψ.coeff i - Ψ'.coeff i ∈ K) →
      Vis R K Ψ G t ≤ Vis R K Ψ' G t := by
    intro Ψ Ψ' hd
    refine Vis_le le_sup_left ?_
    intro i hi hti
    have hkey : Ψ.coeff i = (Ψ.coeff i - Ψ'.coeff i) + Ψ'.coeff i := by ring
    rw [hkey]
    exact Subalgebra.add_mem _ (known_mem_Vis (hd i)) (coeff_mem_Vis hi hti)
  refine le_antisymm (half Φ Φ' h) (half Φ' Φ fun i => ?_)
  have hkey : Φ'.coeff i - Φ.coeff i = -(Φ.coeff i - Φ'.coeff i) := by ring
  rw [hkey]
  exact Subalgebra.neg_mem _ (h i)

/-- Subtracting polynomials with known coefficients preserves causal pairs. -/
theorem CausalPair.sub_known {P₁ P₂ : A[X]} {G : Finset ℕ}
    (h : CausalPair K P₁ P₂ G) {D₁ D₂ : A[X]}
    (hD₁ : ∀ j, D₁.coeff j ∈ K) (hD₂ : ∀ j, D₂.coeff j ∈ K) :
    CausalPair K (P₁ - D₁) (P₂ - D₂) G := by
  have hcomb : combined (P₁ - D₁) (P₂ - D₂) = combined P₁ P₂ - combined D₁ D₂ := by
    simp only [combined]; ring
  have hDcomb : ∀ i, (combined D₁ D₂).coeff i ∈ K := by
    intro i
    cases i with
    | zero => simpa using hD₂ 0
    | succ j => rw [coeff_combined]; exact Subalgebra.add_mem _ (hD₁ j) (hD₂ (j + 1))
  have hVis : ∀ t, Vis R K (combined (P₁ - D₁) (P₂ - D₂)) G t =
      Vis R K (combined P₁ P₂) G t := by
    intro t
    refine Vis_congr_of_diff_known (fun i => ?_) t
    rw [hcomb, coeff_sub]
    have hkey : (combined P₁ P₂).coeff i - (combined D₁ D₂).coeff i -
        (combined P₁ P₂).coeff i = -((combined D₁ D₂).coeff i) := by ring
    rw [hkey]
    exact Subalgebra.neg_mem _ (hDcomb i)
  refine { mem₁ := fun j => ?_, mem₂ := fun j => ?_ }
  · rw [hVis (j + 1), coeff_sub]
    exact Subalgebra.sub_mem _ (h.mem₁ j) (known_mem_Vis (hD₁ j))
  · rw [hVis j, coeff_sub]
    exact Subalgebra.sub_mem _ (h.mem₂ j) (known_mem_Vis (hD₂ j))

/-- Coefficients of `X^n` lie in every subalgebra. -/
theorem coeff_X_pow_mem (K : Subalgebra R A) (n j : ℕ) : (X ^ n : A[X]).coeff j ∈ K := by
  rw [coeff_X_pow]
  split
  · exact K.one_mem
  · exact K.zero_mem

/-- Transport a coefficient membership through subtracting the monomial `X ^ n`: the two
coefficients differ by a coefficient of `X ^ n`, which every subalgebra contains. -/
theorem coeff_mem_of_sub_X_pow {V : Subalgebra R A} {S : A[X]} {n m : ℕ}
    (h : (S - X ^ n).coeff m ∈ V) : S.coeff m ∈ V := by
  have hsplit : S.coeff m = (S - X ^ n).coeff m + (X ^ n : A[X]).coeff m := by
    rw [coeff_sub]; ring
  rw [hsplit]
  exact Subalgebra.add_mem _ h (coeff_X_pow_mem V n m)

variable [Nontrivial A]

/-- **Additivity of compatible pairs**, unequal degrees. -/
theorem CompatiblePair.add_of_lt {nL nR : ℕ}
    (hL : CompatiblePair K PL₁ PL₂ nL gL) (hR : CompatiblePair K PR₁ PR₂ nR gR)
    (hdis : Disjoint gL gR) (hlt : nL < nR) :
    CompatiblePair K (PL₁ + PR₁) (PL₂ + PR₂) nR (gL ∪ gR) := by
  have hdeg : ∀ (p q : A[X]), p.Monic → q.Monic → p.natDegree = nL → q.natDegree = nR →
      (p + q).Monic ∧ (p + q).natDegree = nR := by
    intro p q hp hq hdp hdq
    have hpd : p.degree = (nL : WithBot ℕ) := by
      rw [degree_eq_natDegree hp.ne_zero, hdp]
    have hqd : q.degree = (nR : WithBot ℕ) := by
      rw [degree_eq_natDegree hq.ne_zero, hdq]
    have hlt' : p.degree < q.degree := by
      rw [hpd, hqd]; exact_mod_cast hlt
    refine ⟨hq.add_of_right hlt', ?_⟩
    have := degree_add_eq_right_of_degree_lt hlt'
    exact natDegree_eq_of_degree_eq_some (by rw [this, hqd])
  obtain ⟨hm1, hd1⟩ := hdeg PL₁ PR₁ hL.monic₁ hR.monic₁ hL.natDegree₁ hR.natDegree₁
  obtain ⟨hm2, hd2⟩ := hdeg PL₂ PR₂ hL.monic₂ hR.monic₂ hL.natDegree₂ hR.natDegree₂
  exact
    { toCausalPair := hL.toCausalPair.add hR.toCausalPair hdis
      monic₁ := hm1
      monic₂ := hm2
      natDegree₁ := hd1
      natDegree₂ := hd2
      window := Finset.union_subset
        (hL.window.trans (Finset.range_mono (by omega))) hR.window }

/-- **Additivity of compatible pairs**, equal degrees, with the `X^n` correction
(paper Additivity, second case). -/
theorem CompatiblePair.add_of_eq {n : ℕ}
    (hL : CompatiblePair K PL₁ PL₂ n gL) (hR : CompatiblePair K PR₁ PR₂ n gR)
    (hdis : Disjoint gL gR) :
    CompatiblePair K (PL₁ + PR₁ - X ^ n) (PL₂ + PR₂ - X ^ n) n (gL ∪ gR) := by
  have hdeg : ∀ (p q : A[X]), p.Monic → q.Monic → p.natDegree = n → q.natDegree = n →
      (p + q - X ^ n).Monic ∧ (p + q - X ^ n).natDegree = n := by
    intro p q hp hq hdp hdq
    have hpd : p.degree = (n : WithBot ℕ) := by
      rw [degree_eq_natDegree hp.ne_zero, hdp]
    have hqd : q.degree = (n : WithBot ℕ) := by
      rw [degree_eq_natDegree hq.ne_zero, hdq]
    have hsub : (q - X ^ n).degree < p.degree := by
      rw [hpd]
      refine lt_of_lt_of_le (degree_sub_lt ?_ hq.ne_zero ?_) (le_of_eq hqd)
      · rw [hqd, degree_X_pow]
      · rw [hq.leadingCoeff, leadingCoeff_X_pow]
    have hrw : p + q - X ^ n = p + (q - X ^ n) := by ring
    rw [hrw]
    refine ⟨hp.add_of_left hsub, ?_⟩
    have := degree_add_eq_left_of_degree_lt hsub
    exact natDegree_eq_of_degree_eq_some (by rw [this, hpd])
  obtain ⟨hm1, hd1⟩ := hdeg PL₁ PR₁ hL.monic₁ hR.monic₁ hL.natDegree₁ hR.natDegree₁
  obtain ⟨hm2, hd2⟩ := hdeg PL₂ PR₂ hL.monic₂ hR.monic₂ hL.natDegree₂ hR.natDegree₂
  exact
    { toCausalPair := (hL.toCausalPair.add hR.toCausalPair hdis).sub_known
        (fun j => coeff_X_pow_mem K n j) (fun j => coeff_X_pow_mem K n j)
      monic₁ := hm1
      monic₂ := hm2
      natDegree₁ := hd1
      natDegree₂ := hd2
      window := Finset.union_subset hL.window hR.window }

end additivity_monic

end FastPoly
