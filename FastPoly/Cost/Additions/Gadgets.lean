import FastPoly.Cost.Additions.T

/-!
# Addition ledgers for auxiliary odd gadgets

This module selects the exact share-aware ledger for every auxiliary odd gadget and
proves the sharp and uniform bounds used by the outer compatible-pair recursion.
-/

namespace FastPoly.Cost

/-! ## Auxiliary gadgets -/

/-- Exact addition ledgers for the selected odd auxiliary gadgets. -/
inductive GadgetAddCost : ℕ → ℕ → Prop where
  | one : GadgetAddCost 1 1
  | three : GadgetAddCost 3 3
  | seven : GadgetAddCost 7 8
  | fourKPlusOne (k : ℕ) (hk : 1 ≤ k) :
      GadgetAddCost (4 * k + 1) (tAdd (2 * k) 1 + 3)
  | eightKPlusThree (k : ℕ) (hk : 1 ≤ k) :
      GadgetAddCost (8 * k + 3) (tAdd (2 * k) 2 + 9)
  | eightKPlusSeven (k : ℕ) (hk : 1 ≤ k) :
      GadgetAddCost (8 * k + 7) (tAdd k 3 + 19)

/-- The low slot in the `8k+3` pair uses a scalar at degree one and therefore costs
zero; all other low slots use the selected ordinary gadget. -/
inductive LowGadgetAddCost : ℕ → ℕ → Prop where
  | one : LowGadgetAddCost 1 0
  | ofGadget {d g : ℕ} (hd : 3 ≤ d) (source : GadgetAddCost d g) :
      LowGadgetAddCost d g

private theorem ceilLog2_succ_le_of_two_mul_le (m n : ℕ) (hm : 1 ≤ m)
    (h : 2 * m ≤ n) : ceilLog2 m + 1 ≤ ceilLog2 n := by
  rw [← ceilLog2_two_mul m hm]
  exact ceilLog2_mono h

namespace GadgetAddCost

/-- Every gadget ledger has the expected positive odd degree. -/
theorem odd_and_pos {d g : ℕ} (h : GadgetAddCost d g) : d % 2 = 1 ∧ 1 ≤ d := by
  cases h <;> omega

/-- Scaled form of `g_d ≤ 5d/4 + 8 ceil(log₂ d)`. -/
theorem sharp {d g : ℕ} (h : GadgetAddCost d g) :
    4 * g ≤ 5 * d + 32 * ceilLog2 d := by
  cases h with
  | one => omega
  | three => omega
  | seven => omega
  | fourKPlusOne k hk =>
      rw [tAdd_even_base k hk]
      have ht := tAdd_sharp_two k hk
      have hlog : ceilLog2 k + 1 ≤ ceilLog2 (4 * k + 1) :=
        ceilLog2_succ_le_of_two_mul_le k (4 * k + 1) hk (by omega)
      omega
  | eightKPlusThree k hk =>
      have ht := tAdd_sharp_two (2 * k) (by omega)
      have hlog : ceilLog2 (2 * k) + 1 ≤ ceilLog2 (8 * k + 3) :=
        ceilLog2_succ_le_of_two_mul_le (2 * k) (8 * k + 3) (by omega) (by omega)
      omega
  | eightKPlusSeven k hk =>
      have ht := tAdd_sharp_three k hk
      have hlog : ceilLog2 k + 1 ≤ ceilLog2 (8 * k + 7) :=
        ceilLog2_succ_le_of_two_mul_le k (8 * k + 7) hk (by omega)
      omega

/-- Coarse bound used only for the uniform `2n` theorem. -/
theorem uniform_two {d g : ℕ} (h : GadgetAddCost d g) : g ≤ 2 * d := by
  cases h with
  | one => omega
  | three => omega
  | seven => omega
  | fourKPlusOne k hk =>
      have ht := tAdd_uniform_one k hk
      omega
  | eightKPlusThree k hk =>
      have ht := tAdd_uniform_two (2 * k) (by omega)
      omega
  | eightKPlusSeven k hk =>
      rcases eq_or_ne k 1 with rfl | hk1
      · rw [tAdd_one]
        omega
      · have ht := tAdd_uniform_high k (by omega) 3 (by omega)
        ring_nf at ht ⊢
        omega

/-- Every gadget in residue class three modulo four saves at least three additions over
the elementary `2d` bound. -/
theorem mod_four_three {d g : ℕ} (h : GadgetAddCost d g) (hmod : d % 4 = 3) :
    g ≤ 2 * d - 3 := by
  cases h with
  | one => omega
  | three => omega
  | seven => omega
  | fourKPlusOne k hk => omega
  | eightKPlusThree k hk =>
      have ht := tAdd_uniform_two (2 * k) (by omega)
      omega
  | eightKPlusSeven k hk =>
      rcases eq_or_ne k 1 with rfl | hk1
      · rw [tAdd_one]
        omega
      · have ht := tAdd_uniform_high k (by omega) 3 (by omega)
        ring_nf at ht ⊢
        omega

/-- The selected ledger in degree `4k+1` is the corresponding `T` ledger. -/
theorem eq_fourKPlusOne {k g : ℕ} (hk : 1 ≤ k)
    (h : GadgetAddCost (4 * k + 1) g) :
    g = tAdd (2 * k) 1 + 3 := by
  generalize hdEq : 4 * k + 1 = d at h
  cases h with
  | one => omega
  | three => omega
  | seven => omega
  | fourKPlusOne k' hk' =>
      have hkEq : k' = k := by omega
      subst k'
      rfl
  | eightKPlusThree k' hk' => omega
  | eightKPlusSeven k' hk' => omega

/-- The selected ledger in degree `8k+3` is the known-powers ledger. -/
theorem eq_eightKPlusThree {k g : ℕ} (hk : 1 ≤ k)
    (h : GadgetAddCost (8 * k + 3) g) :
    g = tAdd (2 * k) 2 + 9 := by
  generalize hdEq : 8 * k + 3 = d at h
  cases h with
  | one => omega
  | three => omega
  | seven => omega
  | fourKPlusOne k' hk' => omega
  | eightKPlusThree k' hk' =>
      have hkEq : k' = k := by omega
      subst k'
      rfl
  | eightKPlusSeven k' hk' => omega

theorem eq_eightKPlusSeven {k g : ℕ} (hk : 1 ≤ k)
    (h : GadgetAddCost (8 * k + 7) g) :
    g = tAdd k 3 + 19 := by
  generalize hdEq : 8 * k + 7 = d at h
  cases h with
  | one => omega
  | three => omega
  | seven => omega
  | fourKPlusOne k' hk' => omega
  | eightKPlusThree k' hk' => omega
  | eightKPlusSeven k' hk' =>
      have hkEq : k' = k := by omega
      subst k'
      rfl

/-- In the stable range, residue seven saves thirteen additions over `2d`. -/
theorem eightKPlusSeven_linear {k g : ℕ} (hk : 2 ≤ k)
    (h : GadgetAddCost (8 * k + 7) g) : g ≤ 16 * k + 1 := by
  have heq := eq_eightKPlusSeven (by omega) h
  rw [heq]
  have ht := tAdd_uniform_high k hk 3 (by omega)
  ring_nf at ht ⊢
  omega

end GadgetAddCost

namespace LowGadgetAddCost

theorem sharp {d g : ℕ} (h : LowGadgetAddCost d g) :
    4 * g ≤ 5 * d + 32 * ceilLog2 d := by
  cases h with
  | one => omega
  | ofGadget hd source => exact source.sharp

theorem uniform_two {d g : ℕ} (h : LowGadgetAddCost d g) : g ≤ 2 * d := by
  cases h with
  | one => omega
  | ofGadget hd source => exact source.uniform_two

theorem mod_four_three {d g : ℕ} (h : LowGadgetAddCost d g)
    (hmod : d % 4 = 3) : g ≤ 2 * d - 3 := by
  cases h with
  | one => omega
  | ofGadget hd source => exact source.mod_four_three hmod

end LowGadgetAddCost

/-- Every positive odd degree has one selected auxiliary-gadget ledger. -/
theorem gadgetAddCost_exists (d : ℕ) (hd : 1 ≤ d) (hodd : d % 2 = 1) :
    ∃ g, GadgetAddCost d g := by
  rcases eq_or_ne d 1 with rfl | hd1
  · exact ⟨1, GadgetAddCost.one⟩
  rcases eq_or_ne d 3 with rfl | hd3
  · exact ⟨3, GadgetAddCost.three⟩
  rcases eq_or_ne d 7 with rfl | hd7
  · exact ⟨8, GadgetAddCost.seven⟩
  by_cases hfour : d % 4 = 1
  · let k := d / 4
    have hk : 1 ≤ k := by omega
    have hdform : d = 4 * k + 1 := by omega
    exact ⟨tAdd (2 * k) 1 + 3, hdform ▸ GadgetAddCost.fourKPlusOne k hk⟩
  · have hmod4 : d % 4 = 3 := by omega
    by_cases hthree : d % 8 = 3
    · let k := d / 8
      have hk : 1 ≤ k := by omega
      have hdform : d = 8 * k + 3 := by omega
      exact ⟨tAdd (2 * k) 2 + 9,
        hdform ▸ GadgetAddCost.eightKPlusThree k hk⟩
    · have hseven : d % 8 = 7 := by omega
      let k := d / 8
      have hk : 1 ≤ k := by omega
      have hdform : d = 8 * k + 7 := by omega
      exact ⟨tAdd k 3 + 19, hdform ▸ GadgetAddCost.eightKPlusSeven k hk⟩

theorem lowGadgetAddCost_exists (d : ℕ) (hd : 1 ≤ d) (hodd : d % 2 = 1) :
    ∃ g, LowGadgetAddCost d g := by
  rcases eq_or_ne d 1 with rfl | hd1
  · exact ⟨0, LowGadgetAddCost.one⟩
  obtain ⟨g, hg⟩ := gadgetAddCost_exists d hd hodd
  exact ⟨g, LowGadgetAddCost.ofGadget (by omega) hg⟩

/-- Combined gadget budget in the `8k+3` pair constructor.  This packages the only
parity split needed by the uniform proof. -/
theorem gadget_sum_eightKPlusThree (k g₁ g₂ : ℕ) (hk : 1 ≤ k)
    (high : GadgetAddCost (4 * k + 1) g₁)
    (low : LowGadgetAddCost (2 * k - 1) g₂) :
    g₁ + g₂ ≤ 12 * k - 3 := by
  rcases eq_or_ne k 1 with rfl | hk1
  · have hg₁ := GadgetAddCost.eq_fourKPlusOne (k := 1) (g := g₁) (by omega) high
    rw [hg₁, tAdd_even_base 1 (by omega), tAdd_one]
    cases low <;> omega
  by_cases heven : k % 2 = 0
  · have hg₁eq := GadgetAddCost.eq_fourKPlusOne hk high
    have ht := tAdd_uniform_two k hk
    have hg₁ : g₁ ≤ 8 * k + 2 := by
      rw [hg₁eq, tAdd_even_base k hk]
      omega
    have hmod : (2 * k - 1) % 4 = 3 := by omega
    have hg₂ := low.mod_four_three hmod
    omega
  · have hodd : k % 2 = 1 := by omega
    let r := (k - 1) / 2
    have hr : 1 ≤ r := by omega
    have hkform : k = 2 * r + 1 := by omega
    have hg₁eq := GadgetAddCost.eq_fourKPlusOne hk high
    have hg₁ : g₁ ≤ 8 * k - 1 := by
      rw [hg₁eq, tAdd_even_base k hk, hkform, tAdd_odd_base r hr]
      rcases eq_or_ne r 1 with hrEq | hr1
      · rw [hrEq, tAdd_one]
      · have ht := tAdd_uniform_high r (by omega) 3 (by omega)
        ring_nf at ht ⊢
        omega
    have hg₂ := low.uniform_two
    omega

/-- Combined gadget budget in the `8k+7` pair constructor. -/
theorem gadget_sum_eightKPlusSeven (k g₁ g₂ : ℕ) (hk : 2 ≤ k)
    (low : GadgetAddCost (2 * k + 1) g₁)
    (high : GadgetAddCost (4 * k + 3) g₂) :
    g₁ + g₂ ≤ 12 * k + 3 := by
  by_cases heven : k % 2 = 0
  · let r := k / 2
    have hr : 1 ≤ r := by omega
    have hkform : k = 2 * r := by omega
    have hg₁eq : g₁ = tAdd (2 * r) 1 + 3 := by
      apply GadgetAddCost.eq_fourKPlusOne hr
      simpa only [hkform, show 2 * (2 * r) + 1 = 4 * r + 1 by ring] using low
    have hg₂eq : g₂ = tAdd (2 * r) 2 + 9 := by
      apply GadgetAddCost.eq_eightKPlusThree hr
      simpa only [hkform, show 4 * (2 * r) + 3 = 8 * r + 3 by ring] using high
    rw [hkform, hg₁eq, tAdd_even_base r hr, hg₂eq, tAdd_even_two r hr]
    rcases eq_or_ne r 1 with hrEq | hr1
    · rw [hrEq]
      simp only [tAdd_one]
      omega
    · have ht2 := tAdd_uniform_two r hr
      have ht3 := tAdd_uniform_high r (by omega) 3 (by omega)
      ring_nf at ht3 ⊢
      omega
  · have hodd : k % 2 = 1 := by omega
    let r := (k - 1) / 2
    have hr : 1 ≤ r := by omega
    have hkform : k = 2 * r + 1 := by omega
    have hmod : (2 * k + 1) % 4 = 3 := by omega
    have hg₁ := low.mod_four_three hmod
    rcases eq_or_ne r 1 with hrEq | hr1
    · have hg₂eq : g₂ = tAdd 1 3 + 19 := by
        apply GadgetAddCost.eq_eightKPlusSeven (by omega)
        have hdeg : 4 * k + 3 = 15 := by omega
        simpa only [hdeg] using high
      rw [hg₂eq, tAdd_one]
      omega
    · have hr2 : 2 ≤ r := by omega
      have hg₂ : g₂ ≤ 16 * r + 1 := by
        apply GadgetAddCost.eightKPlusSeven_linear hr2
        simpa only [hkform, show 4 * (2 * r + 1) + 3 = 8 * r + 7 by ring] using high
      omega

end FastPoly.Cost
