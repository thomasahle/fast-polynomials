import FastPoly.Recover.Context

/-!
# `(x+α)`-extraction

Paper `lem:x-alpha-extraction`: from `P = (X + C α)·T₁ + T₂` with `(T₁, T₂)` a compatible
pair of degree `n ≥ 1` on a window `G ⊆ {0,…,n-1}`, the scalar `α` is recoverable from the
single coefficient `[x^n]P` (given `K`), and then every coefficient of `T₁` and `T₂` is
recoverable from the coefficients of `P` — by the descending induction that alternates
between the compatibility cutoffs and the identity `[x^i]Φ = [x^i]P - α·[x^i]T₁`.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section xalpha

variable {K : Subalgebra R A} {G : Finset ℕ} {n : ℕ} {T₁ T₂ : A[X]} {a : A}

/-- If every window index is below the cutoff, the visible algebra collapses to `K`. -/
theorem Vis_eq_known_of_lt {Φ : A[X]} {t : ℕ} (h : ∀ i ∈ G, i < t) :
    Vis R K Φ G t = K :=
  le_antisymm
    (Vis_le le_rfl fun i hi hti => absurd (h i hi) (not_lt.2 hti))
    known_le_Vis

/-- **`(x+α)`-extraction** (paper `lem:x-alpha-extraction`). -/
theorem x_alpha_mem (h : CompatiblePair K T₁ T₂ n G) (hn : 1 ≤ n)
    (hG : ∀ i ∈ G, i < n) {P : A[X]} (hP : P = (X + C a) * T₁ + T₂) :
    (a ∈ K ⊔ adjoin R {P.coeff n}) ∧
      (∀ j, T₁.coeff j ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i)) ∧
      (∀ j, T₂.coeff j ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hPc : P = combined T₁ T₂ + C a * T₁ := by
    rw [hP]; simp only [combined]; ring
  -- the top coefficient of T₁ below the leading one is known
  have hT1top : T₁.coeff m ∈ K := by
    have hh := h.mem₁ m
    rwa [Vis_eq_known_of_lt hG] at hh
  have hT1lead : T₁.coeff (m + 1) = 1 := by
    rw [← h.natDegree₁]; exact h.monic₁.coeff_natDegree
  have hT2lead : T₂.coeff (m + 1) = 1 := by
    rw [← h.natDegree₂]; exact h.monic₂.coeff_natDegree
  -- the pivot for α at degree n = m+1
  have hpivot : P.coeff (m + 1) = T₁.coeff m + 1 + a := by
    rw [hPc, coeff_add, coeff_C_mul, hT1lead, mul_one, coeff_combined, hT2lead]
  have ha : a ∈ K ⊔ adjoin R {P.coeff (m + 1)} := by
    have hkey : a = P.coeff (m + 1) - T₁.coeff m - 1 := by rw [hpivot]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _
      ((le_sup_right : adjoin R {P.coeff (m + 1)} ≤ _) (subset_adjoin rfl))
      ((le_sup_left : K ≤ _) hT1top)) (Subalgebra.one_mem _)
  set VP := K ⊔ adjoin R (Set.range fun i => P.coeff i) with hVP
  have hPmem : ∀ i, P.coeff i ∈ VP :=
    fun i => (le_sup_right : adjoin R _ ≤ VP) (subset_adjoin ⟨i, rfl⟩)
  have haVP : a ∈ VP := by
    refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono ?_) K) ha
    exact Set.singleton_subset_iff.2 ⟨m + 1, rfl⟩
  -- coefficients at or above the degree are constants
  have hhigh : ∀ j, m + 1 ≤ j → T₁.coeff j ∈ VP ∧ T₂.coeff j ∈ VP := by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hlt
    · rw [hT1lead, hT2lead]
      exact ⟨Subalgebra.one_mem _, Subalgebra.one_mem _⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₁]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₂]; omega)]
      exact ⟨Subalgebra.zero_mem _, Subalgebra.zero_mem _⟩
  -- the coefficient identity for the combined polynomial
  have hkeyφ : ∀ i, (combined T₁ T₂).coeff i = P.coeff i - a * T₁.coeff i := by
    intro i
    rw [hPc, coeff_add, coeff_C_mul]; ring
  -- descending recovery
  have step : ∀ j, j < m + 1 →
      (∀ i, j < i → T₁.coeff i ∈ VP ∧ T₂.coeff i ∈ VP) →
      T₁.coeff j ∈ VP ∧ T₂.coeff j ∈ VP := by
    intro j _hjn ih
    have hVis₁ : Vis R K (combined T₁ T₂) G (j + 1) ≤ VP := by
      refine Vis_le le_sup_left ?_
      intro i hi hii
      have hiT₁ : T₁.coeff i ∈ VP := (ih i (by omega)).1
      rw [hkeyφ i]
      exact Subalgebra.sub_mem _ (hPmem i) (Subalgebra.mul_mem _ haVP hiT₁)
    have hT1j : T₁.coeff j ∈ VP := hVis₁ (h.mem₁ j)
    have hVis₂ : Vis R K (combined T₁ T₂) G j ≤ VP := by
      refine Vis_le le_sup_left ?_
      intro i hi hii
      have hiT₁ : T₁.coeff i ∈ VP := by
        rcases eq_or_lt_of_le hii with rfl | hlt
        · exact hT1j
        · exact (ih i (by omega)).1
      rw [hkeyφ i]
      exact Subalgebra.sub_mem _ (hPmem i) (Subalgebra.mul_mem _ haVP hiT₁)
    exact ⟨hT1j, hVis₂ (h.mem₂ j)⟩
  have main : ∀ j, T₁.coeff j ∈ VP ∧ T₂.coeff j ∈ VP := descend_below hhigh step
  exact ⟨ha, fun j => (main j).1, fun j => (main j).2⟩

end xalpha

end FastPoly
