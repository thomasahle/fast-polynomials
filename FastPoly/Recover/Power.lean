import FastPoly.Recover.Multiplication

/-!
# Combination lemmas: square closure

Paper `lem:compatible-power`: if `(P₁, P₂)` is a compatible pair of degree `n` on `G` and `2`
is a unit, then `(P₁², P₂²)` is compatible on `n + G`.  The engine is the same double
boundary/rest split as for Multiplicativity, except that the two boundary terms coincide —
which is exactly why the pivot is `2` and invertibility of `2` is needed.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section power

variable {K : Subalgebra R A} {G : Finset ℕ} {n : ℕ} {P₁ P₂ : A[X]}

/-- **Separation for squares** (the engine of square closure): the visible algebra of the
pair at cutoff `t` embeds into that of the squared pair at cutoff `n + t`. -/
theorem vis_le_vis_sq (h : CompatiblePair K P₁ P₂ n G) (h2 : IsUnit (2 : R)) (t : ℕ) :
    Vis R K (combined P₁ P₂) G t ≤
      Vis R K (combined (P₁ * P₁) (P₂ * P₂)) (shiftW n G) (n + t) := by
  classical
  set φ := combined P₁ P₂ with hφ
  set Ψ := combined (P₁ * P₁) (P₂ * P₂) with hΨ
  set G' := shiftW n G with hG'
  set V := Vis R K Ψ G' (n + t) with hV
  set U := G'.filter (fun i => n + t ≤ i) with hU
  have hp1 : P₁.coeff n = 1 := by rw [← h.natDegree₁]; exact h.monic₁.coeff_natDegree
  have hp2 : P₂.coeff n = 1 := by rw [← h.natDegree₂]; exact h.monic₂.coeff_natDegree
  have step : ∀ k, k ∈ U →
      (∀ i ∈ U, k < i → φ.coeff (i - n) ∈ V) →
      φ.coeff (k - n) ∈ V := by
    intro k hkU ih
    have hktU : n + t ≤ k := (Finset.mem_filter.1 hkU).2
    have hkG : k ∈ G' := (Finset.mem_filter.1 hkU).1
    have hkn : n ≤ k := le_of_mem_shiftW hkG
    have hks : Ψ.coeff k ∈ V := coeff_mem_Vis hkG hktU
    have map : ∀ u', k + 1 ≤ n + u' → Vis R K φ G u' ≤ V := by
      intro u' hu'
      refine Vis_le le_sup_left ?_
      intro i' hi' hui'
      have hiU : n + i' ∈ U := Finset.mem_filter.2
        ⟨add_mem_shiftW hi', by omega⟩
      have hh := ih (n + i') hiU (by omega)
      simpa using hh
    have mem₁ : ∀ j, k ≤ n + j → P₁.coeff j ∈ V :=
      fun j hj => map (j + 1) (by omega) (h.mem₁ j)
    have mem₂ : ∀ j, k + 1 ≤ n + j → P₂.coeff j ∈ V :=
      fun j hj => map j hj (h.mem₂ j)
    -- degenerate k = 0 (forces n = 0)
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hn0 : n = 0 := by omega
      have hφ0 : φ.coeff 0 = 1 := by
        have h0 : P₂.coeff 0 = 1 := by
          rw [show (0 : ℕ) = n from hn0.symm]
          exact hp2
        rw [hφ, coeff_combined_zero, h0]
      rw [Nat.zero_sub, hφ0]
      exact Subalgebra.one_mem _
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    set E₁ := ∑ x ∈ (Finset.antidiagonal k').filter (fun x : ℕ × ℕ => x.1 ≠ n ∧ x.2 ≠ n),
        P₁.coeff x.1 * P₁.coeff x.2 with hE₁
    set E₂ := ∑ x ∈ (Finset.antidiagonal (k' + 1)).filter
        (fun x : ℕ × ℕ => x.1 ≠ n ∧ x.2 ≠ n),
        P₂.coeff x.1 * P₂.coeff x.2 with hE₂
    have hE₁mem : E₁ ∈ V := by
      rw [hE₁]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hm := Finset.mem_filter.1 hx
      have hxa : x.1 + x.2 = k' := Finset.mem_antidiagonal.1 hm.1
      obtain ⟨hx1, hx2⟩ := hm.2
      rcases Nat.lt_or_ge n x.1 with hgt | hle1
      · have hz : P₁.coeff x.1 = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₁]; omega)
        rw [hz, zero_mul]; exact Subalgebra.zero_mem _
      rcases Nat.lt_or_ge n x.2 with hgt2 | hle2
      · have hz : P₁.coeff x.2 = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₁]; omega)
        rw [hz, mul_zero]; exact Subalgebra.zero_mem _
      exact Subalgebra.mul_mem _ (mem₁ x.1 (by omega)) (mem₁ x.2 (by omega))
    have hE₂mem : E₂ ∈ V := by
      rw [hE₂]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hm := Finset.mem_filter.1 hx
      have hxa : x.1 + x.2 = k' + 1 := Finset.mem_antidiagonal.1 hm.1
      obtain ⟨hx1, hx2⟩ := hm.2
      rcases Nat.lt_or_ge n x.1 with hgt | hle1
      · have hz : P₂.coeff x.1 = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₂]; omega)
        rw [hz, zero_mul]; exact Subalgebra.zero_mem _
      rcases Nat.lt_or_ge n x.2 with hgt2 | hle2
      · have hz : P₂.coeff x.2 = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₂]; omega)
        rw [hz, mul_zero]; exact Subalgebra.zero_mem _
      exact Subalgebra.mul_mem _ (mem₂ x.1 (by omega)) (mem₂ x.2 (by omega))
    have hcorr₁ : (if k' = n + n then (1:A) else 0) ∈ V := by
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    have hcorr₂ : (if k' + 1 = n + n then (1:A) else 0) ∈ V := by
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    have hmaster : Ψ.coeff (k' + 1)
        = ((if n ≤ k' then P₁.coeff (k' - n) else 0)
            + (if n ≤ k' + 1 then P₂.coeff (k' + 1 - n) else 0))
          + ((if n ≤ k' then P₁.coeff (k' - n) else 0)
            + (if n ≤ k' + 1 then P₂.coeff (k' + 1 - n) else 0))
          - (if k' = n + n then (1:A) else 0)
          - (if k' + 1 = n + n then (1:A) else 0)
          + E₁ + E₂ := by
      rw [hΨ, coeff_combined, coeff_mul_double_split P₁ P₁ k' n n,
        coeff_mul_double_split P₂ P₂ (k' + 1) n n, hp1, hp2, ← hE₁, ← hE₂]
      simp only [mul_one, one_mul]
      ring
    have hB : (if n ≤ k' then P₁.coeff (k' - n) else 0)
        + (if n ≤ k' + 1 then P₂.coeff (k' + 1 - n) else 0)
        = φ.coeff (k' + 1 - n) := by
      rcases Nat.lt_or_ge k' n with h1 | h1
      · rw [if_neg (by omega), if_pos (by omega), show k' + 1 - n = 0 by omega, hφ,
          coeff_combined_zero, zero_add]
      · rw [if_pos h1, if_pos (by omega), show k' + 1 - n = (k' - n) + 1 by omega, hφ,
          coeff_combined]
    have hsimp : Ψ.coeff (k' + 1)
        + (if k' = n + n then (1:A) else 0)
        + (if k' + 1 = n + n then (1:A) else 0)
        - E₁ - E₂ = 2 * φ.coeff (k' + 1 - n) := by
      rw [hmaster, ← hB]; ring
    exact mem_of_two_mul_eq h2
      (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ hks hcorr₁) hcorr₂) hE₁mem) hE₂mem)
      hsimp.symm
  have main : ∀ k ∈ U, (combined P₁ P₂).coeff (k - n) ∈ V :=
    descend_on_finset step
  refine Vis_le le_sup_left ?_
  intro i hiG hti
  have hiU : n + i ∈ U := Finset.mem_filter.2 ⟨add_mem_shiftW hiG, by omega⟩
  have hh := main (n + i) hiU
  simpa using hh

/-- **Square closure for compatible pairs** (paper `lem:compatible-power`). -/
theorem CompatiblePair.sq (h : CompatiblePair K P₁ P₂ n G) (h2 : IsUnit (2 : R)) :
    CompatiblePair K (P₁ * P₁) (P₂ * P₂) (n + n) (shiftW n G) := by
  set Ψ := combined (P₁ * P₁) (P₂ * P₂) with hΨ
  have hmem₁ : ∀ j, (P₁ * P₁).coeff j ∈ Vis R K Ψ (shiftW n G) (j + 1) := by
    intro j
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge n x.1 with hgt | hle1
    · have hz : P₁.coeff x.1 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₁]; omega)
      rw [hz, zero_mul]; exact Subalgebra.zero_mem _
    rcases Nat.lt_or_ge n x.2 with hgt2 | hle2
    · have hz : P₁.coeff x.2 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₁]; omega)
      rw [hz, mul_zero]; exact Subalgebra.zero_mem _
    refine Subalgebra.mul_mem _ ?_ ?_
    · exact Vis_antitone_cutoff (by omega) (vis_le_vis_sq h h2 (x.1 + 1) (h.mem₁ x.1))
    · exact Vis_antitone_cutoff (by omega) (vis_le_vis_sq h h2 (x.2 + 1) (h.mem₁ x.2))
  have hmem₂ : ∀ j, (P₂ * P₂).coeff j ∈ Vis R K Ψ (shiftW n G) j := by
    intro j
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge n x.1 with hgt | hle1
    · have hz : P₂.coeff x.1 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₂]; omega)
      rw [hz, zero_mul]; exact Subalgebra.zero_mem _
    rcases Nat.lt_or_ge n x.2 with hgt2 | hle2
    · have hz : P₂.coeff x.2 = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [h.natDegree₂]; omega)
      rw [hz, mul_zero]; exact Subalgebra.zero_mem _
    refine Subalgebra.mul_mem _ ?_ ?_
    · exact Vis_antitone_cutoff (by omega) (vis_le_vis_sq h h2 x.1 (h.mem₂ x.1))
    · exact Vis_antitone_cutoff (by omega) (vis_le_vis_sq h h2 x.2 (h.mem₂ x.2))
  exact
    { mem₁ := hmem₁
      mem₂ := hmem₂
      monic₁ := h.monic₁.mul h.monic₁
      monic₂ := h.monic₂.mul h.monic₂
      natDegree₁ := by rw [h.monic₁.natDegree_mul h.monic₁, h.natDegree₁]
      natDegree₂ := by rw [h.monic₂.natDegree_mul h.monic₂, h.natDegree₂]
      window := by
        intro i hi
        rcases mem_shiftW.1 hi with ⟨i', hi', rfl⟩
        have := Finset.mem_range.1 (h.window hi')
        exact Finset.mem_range.2 (by omega) }

end power

end FastPoly
