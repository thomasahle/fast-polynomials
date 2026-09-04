import FastPoly.Cost.Additions.Gadgets

/-!
# Addition bounds for compatible pairs and complete polynomials

This module carries the selected gadget ledgers through the odd-degree recursion and
the final odd/even polynomial constructors. It proves the uniform 2n bound and the
sharper five-quarters bound with logarithmic overhead.
-/

namespace FastPoly.Cost

/-! ## Compatible-pair ledgers -/

/-- Exact, share-aware addition accounting for the optimized compatible-pair schedules.
The recursive constructors carry their gadget ledgers explicitly, but this numerical
relation is not itself a semantic realization theorem.  A circuit-level addition claim
must additionally identify the literal optimized circuit and prove its `gates.additions`
equals the ledger recorded here. -/
inductive PairAddCost : ℕ → ℕ → Prop where
  | three : PairAddCost 3 3
  | fourKPlusOne (k : ℕ) (hk : 1 ≤ k) :
      PairAddCost (4 * k + 1) (tAdd (2 * k) 1 + 2)
  | fifteen : PairAddCost 15 23
  | twentySeven : PairAddCost 27 43
  | thirtyOne : PairAddCost 31 43
  | eightKPlusThree (k a g₁ g₂ : ℕ) (hk : 1 ≤ k) (hk3 : k ≠ 3)
      (small : PairAddCost (2 * k + 1) a)
      (high : GadgetAddCost (4 * k + 1) g₁)
      (low : LowGadgetAddCost (2 * k - 1) g₂) :
      PairAddCost (8 * k + 3) (a + g₁ + g₂ + 7)
  | eightKPlusSeven (k a g₁ g₂ : ℕ) (hk : 2 ≤ k) (hk3 : k ≠ 3)
      (small : PairAddCost (2 * k + 1) a)
      (low : GadgetAddCost (2 * k + 1) g₁)
      (high : GadgetAddCost (4 * k + 3) g₂) :
      PairAddCost (8 * k + 7) (a + g₁ + g₂ + 6)

private theorem ceilLog2_eight_mul_add_three (k : ℕ) (hk : 1 ≤ k) :
    ceilLog2 (8 * k + 3) = ceilLog2 (2 * k + 1) + 2 := by
  calc
    ceilLog2 (8 * k + 3) = ceilLog2 (4 * k + 2) + 1 := by
      simpa only [show 2 * (4 * k + 1) + 1 = 8 * k + 3 by ring,
        show 4 * k + 1 + 1 = 4 * k + 2 by omega] using
        ceilLog2_two_mul_add_one (4 * k + 1) (by omega)
    _ = ceilLog2 (2 * k + 1) + 2 := by
      rw [show 4 * k + 2 = 2 * (2 * k + 1) by ring,
        ceilLog2_two_mul (2 * k + 1) (by omega)]

private theorem ceilLog2_small_add_two_le_eight_mul_add_seven (k : ℕ) (hk : 1 ≤ k) :
    ceilLog2 (2 * k + 1) + 2 ≤ ceilLog2 (8 * k + 7) := by
  calc
    ceilLog2 (2 * k + 1) + 2 ≤ ceilLog2 (2 * k + 2) + 2 := by
      exact Nat.add_le_add_right (ceilLog2_mono (by omega)) 2
    _ = ceilLog2 (8 * k + 7) := by
      calc
        ceilLog2 (2 * k + 2) + 2 = ceilLog2 (4 * k + 4) + 1 := by
          rw [show 4 * k + 4 = 2 * (2 * k + 2) by ring,
            ceilLog2_two_mul (2 * k + 2) (by omega)]
        _ = ceilLog2 (8 * k + 7) := by
          symm
          simpa only [show 2 * (4 * k + 3) + 1 = 8 * k + 7 by ring,
            show 4 * k + 3 + 1 = 4 * k + 4 by omega] using
            ceilLog2_two_mul_add_one (4 * k + 3) (by omega)

private theorem ceilLog2_two_le_of_four_le (n : ℕ) (hn : 4 ≤ n) :
    2 ≤ ceilLog2 n := by
  calc
    2 = ceilLog2 4 := by
      rw [ceilLog2, show 4 = 2 ^ 2 by rfl, Nat.clog_pow 2 2 (by omega)]
    _ ≤ ceilLog2 n := ceilLog2_mono hn

private theorem ceilLog2_two_le_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    2 ≤ ceilLog2 n := by
  rw [← ceilLog2_three]
  exact ceilLog2_mono hn

/-- The quadratic budget consumed at one recursive pair step.  Isolating this elementary
lemma keeps the main induction linear: two lost bits pay for both gadget logarithms. -/
private theorem quadratic_budget (u v : ℕ) (hdrop : u + 2 ≤ v) (hv : 4 ≤ v) :
    24 * u * u + 64 * v + 18 ≤ 24 * v * v := by
  let r := v - 2
  have hvform : v = r + 2 := by omega
  have hur : u ≤ r := by omega
  have hsquare : u * u ≤ r * r := Nat.mul_le_mul hur hur
  have hscaled : 24 * (u * u) ≤ 24 * (r * r) :=
    Nat.mul_le_mul_left 24 hsquare
  rw [hvform]
  calc
    24 * u * u + 64 * (r + 2) + 18
        ≤ 24 * (r * r) + 64 * (r + 2) + 18 := by
          have : 24 * u * u ≤ 24 * (r * r) := by simpa only [Nat.mul_assoc] using hscaled
          omega
    _ ≤ 24 * (r + 2) * (r + 2) := by ring_nf; omega

private theorem linear_budget (u v : ℕ) (huv : u ≤ v) (hv : 2 ≤ v) :
    32 * u + 7 ≤ 24 * v * v := by
  have hlin : 32 * u + 7 ≤ 32 * v + 7 := by omega
  have hsq : 2 * v ≤ v * v := Nat.mul_le_mul_right v hv
  calc
    32 * u + 7 ≤ 32 * v + 7 := hlin
    _ ≤ 48 * v := by omega
    _ = 24 * (2 * v) := by ring
    _ ≤ 24 * (v * v) := Nat.mul_le_mul_left 24 hsq
    _ = 24 * v * v := by ring

private theorem square_budget_four (v : ℕ) (hv : 2 ≤ v) :
    96 ≤ 24 * v * v := by
  have hsq : 4 ≤ v * v := Nat.mul_le_mul hv hv
  calc
    96 = 24 * 4 := by ring
    _ ≤ 24 * (v * v) := Nat.mul_le_mul_left 24 hsq
    _ = 24 * v * v := by ring

namespace PairAddCost

theorem odd_and_three_le {n a : ℕ} (h : PairAddCost n a) :
    n % 2 = 1 ∧ 3 ≤ n := by
  induction h <;> omega

/-- Scaled pair bound `a_n ≤ 5n/4 + 6 ceil(log₂ n)²`. -/
theorem sharp {n a : ℕ} (h : PairAddCost n a) :
    4 * a ≤ 5 * n + 24 * ceilLog2 n * ceilLog2 n := by
  induction h with
  | three => omega
  | fourKPlusOne k hk =>
      rw [tAdd_even_base k hk]
      have ht := tAdd_sharp_two k hk
      have hlog : ceilLog2 k ≤ ceilLog2 (4 * k + 1) :=
        ceilLog2_mono (by omega)
      have hL : 2 ≤ ceilLog2 (4 * k + 1) :=
        ceilLog2_two_le_of_four_le _ (by omega)
      have hbudget := linear_budget (ceilLog2 k) (ceilLog2 (4 * k + 1)) hlog hL
      omega
  | fifteen =>
      have hL := ceilLog2_two_le_of_four_le 15 (by omega)
      have hbudget := square_budget_four (ceilLog2 15) hL
      omega
  | twentySeven =>
      have hL := ceilLog2_two_le_of_four_le 27 (by omega)
      have hbudget := square_budget_four (ceilLog2 27) hL
      omega
  | thirtyOne =>
      have hL := ceilLog2_two_le_of_four_le 31 (by omega)
      have hbudget := square_budget_four (ceilLog2 31) hL
      omega
  | eightKPlusThree k a g₁ g₂ hk hk3 small high low ih =>
      have hg₁ := high.sharp
      have hg₂ := low.sharp
      have hdrop : ceilLog2 (2 * k + 1) + 2 ≤ ceilLog2 (8 * k + 3) := by
        rw [ceilLog2_eight_mul_add_three k hk]
      have hL : 4 ≤ ceilLog2 (8 * k + 3) := by
        have hu : 2 ≤ ceilLog2 (2 * k + 1) :=
          ceilLog2_two_le_of_three_le _ (by omega)
        omega
      have hquad := quadratic_budget (ceilLog2 (2 * k + 1))
        (ceilLog2 (8 * k + 3)) hdrop hL
      have hlog₁ : ceilLog2 (4 * k + 1) ≤ ceilLog2 (8 * k + 3) :=
        ceilLog2_mono (by omega)
      have hlog₂ : ceilLog2 (2 * k - 1) ≤ ceilLog2 (8 * k + 3) :=
        ceilLog2_mono (by omega)
      omega
  | eightKPlusSeven k a g₁ g₂ hk hk3 small low high ih =>
      have hg₁ := low.sharp
      have hg₂ := high.sharp
      have hdrop : ceilLog2 (2 * k + 1) + 2 ≤ ceilLog2 (8 * k + 7) :=
        ceilLog2_small_add_two_le_eight_mul_add_seven k (by omega)
      have hL : 4 ≤ ceilLog2 (8 * k + 7) := by
        have hu : 2 ≤ ceilLog2 (2 * k + 1) :=
          ceilLog2_two_le_of_three_le _ (by omega)
        omega
      have hquad := quadratic_budget (ceilLog2 (2 * k + 1))
        (ceilLog2 (8 * k + 7)) hdrop hL
      have hlog₁ : ceilLog2 (2 * k + 1) ≤ ceilLog2 (8 * k + 7) :=
        ceilLog2_mono (by omega)
      have hlog₂ : ceilLog2 (4 * k + 3) ≤ ceilLog2 (8 * k + 7) :=
        ceilLog2_mono (by omega)
      omega

/-- Uniform pair bound `a_n ≤ 2n-1`. -/
theorem uniform_two {n a : ℕ} (h : PairAddCost n a) : a ≤ 2 * n - 1 := by
  induction h with
  | three => omega
  | fourKPlusOne k hk =>
      have ht := tAdd_uniform_one k hk
      omega
  | fifteen => omega
  | twentySeven => omega
  | thirtyOne => omega
  | eightKPlusThree k a g₁ g₂ hk hk3 small high low ih =>
      have hg := gadget_sum_eightKPlusThree k g₁ g₂ hk high low
      omega
  | eightKPlusSeven k a g₁ g₂ hk hk3 small low high ih =>
      have hg := gadget_sum_eightKPlusSeven k g₁ g₂ hk low high
      omega

end PairAddCost

/-- Existence follows the same residue dispatch as `pairCost_exists`; no numerical
search is involved. -/
theorem pairAddCost_exists : ∀ n : ℕ, 3 ≤ n → n % 2 = 1 → n ≠ 7 →
    ∃ a, PairAddCost n a := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn3 hnodd hn7
      by_cases hfour : n % 4 = 1
      · let k := n / 4
        have hn : n = 4 * k + 1 := by omega
        have hk : 1 ≤ k := by omega
        exact ⟨tAdd (2 * k) 1 + 2, hn ▸ PairAddCost.fourKPlusOne k hk⟩
      · have hmod4 : n % 4 = 3 := by omega
        by_cases hthree : n % 8 = 3
        · let k := n / 8
          have hn : n = 8 * k + 3 := by omega
          rcases eq_or_ne k 0 with hk0 | hk0
          · have hn0 : n = 3 := by omega
            exact ⟨3, hn0 ▸ PairAddCost.three⟩
          · rcases eq_or_ne k 3 with hkEq3 | hk3
            · have hn27 : n = 27 := by omega
              exact ⟨43, hn27 ▸ PairAddCost.twentySeven⟩
            · have hk : 1 ≤ k := by omega
              obtain ⟨a, ha⟩ := ih (2 * k + 1) (by omega) (by omega) (by omega) (by omega)
              obtain ⟨g₁, hg₁⟩ := gadgetAddCost_exists (4 * k + 1) (by omega) (by omega)
              obtain ⟨g₂, hg₂⟩ := lowGadgetAddCost_exists (2 * k - 1) (by omega) (by omega)
              exact ⟨a + g₁ + g₂ + 7,
                hn ▸ PairAddCost.eightKPlusThree k a g₁ g₂ hk hk3 ha hg₁ hg₂⟩
        · have hseven : n % 8 = 7 := by omega
          let k := n / 8
          have hn : n = 8 * k + 7 := by omega
          rcases eq_or_ne k 0 with hk0 | hk0
          · exact False.elim (hn7 (by omega))
          · rcases eq_or_ne k 1 with hkEq1 | hk1
            · have hn15 : n = 15 := by omega
              exact ⟨23, hn15 ▸ PairAddCost.fifteen⟩
            · rcases eq_or_ne k 3 with hkEq3 | hk3
              · have hn31 : n = 31 := by omega
                exact ⟨43, hn31 ▸ PairAddCost.thirtyOne⟩
              · have hk : 2 ≤ k := by omega
                obtain ⟨a, ha⟩ := ih (2 * k + 1) (by omega) (by omega) (by omega) (by omega)
                obtain ⟨g₁, hg₁⟩ := gadgetAddCost_exists (2 * k + 1) (by omega) (by omega)
                obtain ⟨g₂, hg₂⟩ := gadgetAddCost_exists (4 * k + 3) (by omega) (by omega)
                exact ⟨a + g₁ + g₂ + 6,
                  hn ▸ PairAddCost.eightKPlusSeven k a g₁ g₂ hk hk3 ha hg₁ hg₂⟩

/-! ## Complete polynomial ledgers -/

/-- Exact addition ledger for the complete construction, including the optimized direct
cubic and affine-reparameterized septic. -/
inductive PolynomialAddCost : ℕ → ℕ → Prop where
  | linear : PolynomialAddCost 1 1
  | quadratic : PolynomialAddCost 2 2
  | cubic : PolynomialAddCost 3 3
  | septic : PolynomialAddCost 7 10
  | odd {n a : ℕ} (source : PairAddCost n a) : PolynomialAddCost n (a + 1)
  | evenLift {n a : ℕ} (source : PolynomialAddCost n a) (hodd : n % 2 = 1) :
      PolynomialAddCost (n + 1) (a + 1)

namespace PolynomialAddCost

/-- Scaled complete bound `A_n ≤ 5n/4 + 6 ceil(log₂ n)² + 1`. -/
theorem sharp {n a : ℕ} (h : PolynomialAddCost n a) :
    4 * a ≤ 5 * n + 24 * ceilLog2 n * ceilLog2 n + 4 := by
  induction h with
  | linear => omega
  | quadratic => omega
  | cubic => omega
  | septic =>
      have hL := ceilLog2_two_le_of_four_le 7 (by omega)
      have hbudget := square_budget_four (ceilLog2 7) hL
      omega
  | odd source =>
      have hp := source.sharp
      omega
  | @evenLift n a source hodd ih =>
      have hlog : ceilLog2 n ≤ ceilLog2 (n + 1) := ceilLog2_mono (by omega)
      have hsq : ceilLog2 n * ceilLog2 n ≤
          ceilLog2 (n + 1) * ceilLog2 (n + 1) :=
        Nat.mul_le_mul hlog hlog
      have hscaled : 24 * (ceilLog2 n * ceilLog2 n) ≤
          24 * (ceilLog2 (n + 1) * ceilLog2 (n + 1)) :=
        Nat.mul_le_mul_left 24 hsq
      have hscaled' : 24 * ceilLog2 n * ceilLog2 n ≤
          24 * ceilLog2 (n + 1) * ceilLog2 (n + 1) := by
        simpa only [Nat.mul_assoc] using hscaled
      omega

/-- Uniform complete bound `A_n ≤ 2n`. -/
theorem uniform_two {n a : ℕ} (h : PolynomialAddCost n a) : a ≤ 2 * n := by
  induction h with
  | linear => omega
  | quadratic => omega
  | cubic => omega
  | septic => omega
  | odd source =>
      have hp := source.uniform_two
      have hn := source.odd_and_three_le
      omega
  | @evenLift n a source hodd ih => omega

end PolynomialAddCost

/-- Every positive degree receives the exact addition ledger selected by the manuscript. -/
theorem polynomialAddCost_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ a, PolynomialAddCost n a := by
  rcases eq_or_ne n 1 with rfl | hn1
  · exact ⟨1, PolynomialAddCost.linear⟩
  rcases eq_or_ne n 2 with rfl | hn2
  · exact ⟨2, PolynomialAddCost.quadratic⟩
  rcases eq_or_ne n 3 with rfl | hn3eq
  · exact ⟨3, PolynomialAddCost.cubic⟩
  rcases eq_or_ne n 7 with rfl | hn7
  · exact ⟨10, PolynomialAddCost.septic⟩
  by_cases hodd : n % 2 = 1
  · obtain ⟨a, ha⟩ := pairAddCost_exists n (by omega) hodd hn7
    exact ⟨a + 1, PolynomialAddCost.odd ha⟩
  · let m := n - 1
    have hm : m % 2 = 1 := by omega
    rcases eq_or_ne m 3 with hm3 | hm3
    · exact ⟨4, show PolynomialAddCost n 4 by
        have hnform : n = 3 + 1 := by omega
        exact hnform ▸ PolynomialAddCost.evenLift PolynomialAddCost.cubic (by omega)⟩
    rcases eq_or_ne m 7 with hm7 | hm7
    · exact ⟨11, show PolynomialAddCost n 11 by
        have hnform : n = 7 + 1 := by omega
        exact hnform ▸ PolynomialAddCost.evenLift PolynomialAddCost.septic (by omega)⟩
    obtain ⟨a, ha⟩ := pairAddCost_exists m (by omega) hm hm7
    have hnform : n = m + 1 := by omega
    exact ⟨a + 2, hnform ▸ PolynomialAddCost.evenLift (PolynomialAddCost.odd ha) hm⟩

/-- Complete formal addition-count theorem.  The first inequality is uniform; the second
is the integer-scaled form of `5n/4 + 6 ceil(log₂ n)² + 1`. -/
theorem construction_addition_count (n : ℕ) (hn : 1 ≤ n) :
    ∃ a, PolynomialAddCost n a ∧ a ≤ 2 * n ∧
      4 * a ≤ 5 * n + 24 * ceilLog2 n * ceilLog2 n + 4 := by
  obtain ⟨a, ha⟩ := polynomialAddCost_exists n hn
  exact ⟨a, ha, ha.uniform_two, ha.sharp⟩

end FastPoly.Cost
