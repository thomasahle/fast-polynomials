import FastPoly.Cost.Gadgets

/-!
# The complete multiplication-count induction

`PairCost n c` is the numerical shadow of one branch of the paper's splittable-pair
construction.  It records the shared multiplication count `c`, but no decoding claim;
the latter belongs to Sections 5--6.  Every local summand below is justified by
`t_multiplication_count` or `lem:odd-gadgets-count`, formalized in `Cost.Gadgets`.

Keeping this accounting relation separate has two advantages.  It prevents a tree count
from accidentally charging a shared subcomputation twice, and lets the final construction
proof attach one constructor at exactly the point where it invokes the corresponding
decoding lemma.
-/

namespace FastPoly.Cost

/-- Exact multiplication accounting for the shared splittable pair. -/
inductive PairCost : ℕ → ℕ → Prop where
  /-- The degree-three pair has one product. -/
  | three : PairCost 3 1
  /-- At degree `4k+1`: one product for `H₂`, followed by `T_{2k,2}` at cost
  `2k-1`. -/
  | fourKPlusOne (k : ℕ) (hk : 1 ≤ k) : PairCost (4 * k + 1) (2 * k)
  /-- The three finite splittable bases. -/
  | fifteen : PairCost 15 7
  | twentySeven : PairCost 27 13
  | thirtyOne : PairCost 31 15
  /-- At degree `8k+3`: the smaller pair, gadgets of degrees `4k+1` and `2k-1`,
  and two outer products.  The excluded `k=3` branch is the degree-27 base. -/
  | eightKPlusThree (k c : ℕ) (hk : 1 ≤ k) (hk3 : k ≠ 3)
      (small : PairCost (2 * k + 1) c) :
      PairCost (8 * k + 3) (c + 2 * k + (k - 1) + 2)
  /-- At degree `8k+7`: the smaller pair, gadgets of degrees `2k+1` and `4k+3`,
  and two outer products.  The excluded `k=3` branch is the degree-31 base. -/
  | eightKPlusSeven (k c : ℕ) (hk : 2 ≤ k) (hk3 : k ≠ 3)
      (small : PairCost (2 * k + 1) c) :
      PairCost (8 * k + 7) (c + k + (2 * k + 1) + 2)

namespace PairCost

/-- Every cost derivation has an odd degree at least three. -/
theorem odd_and_three_le {n c : ℕ} (h : PairCost n c) : n % 2 = 1 ∧ 3 ≤ n := by
  induction h with
  | three => norm_num
  | fourKPlusOne k hk => omega
  | fifteen => norm_num
  | twentySeven => norm_num
  | thirtyOne => norm_num
  | eightKPlusThree k c hk hk3 small ih => omega
  | eightKPlusSeven k c hk hk3 small ih => omega

/-- The local cost identities compose: every derivation has shared cost `(n-1)/2`.
This is the formal version of the multiplication-count induction in
`thm:construction-count`. -/
theorem exact {n c : ℕ} (h : PairCost n c) : c = (n - 1) / 2 := by
  induction h with
  | three => norm_num
  | fourKPlusOne k hk => omega
  | fifteen => norm_num
  | twentySeven => norm_num
  | thirtyOne => norm_num
  | eightKPlusThree k c hk hk3 small ih => omega
  | eightKPlusSeven k c hk hk3 small ih => omega

/-- A degree determines at most one count. -/
theorem unique {n c₁ c₂ : ℕ} (h₁ : PairCost n c₁) (h₂ : PairCost n c₂) : c₁ = c₂ := by
  rw [h₁.exact, h₂.exact]

end PairCost

/-- Every odd degree `n ≥ 3`, except the direct septic base, has a cost derivation.
The proof follows exactly the construction's `4k+1`, `8k+3`, and `8k+7` dispatch. -/
theorem pairCost_exists : ∀ n : ℕ, 3 ≤ n → n % 2 = 1 → n ≠ 7 →
    ∃ c, PairCost n c := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn3 hnodd hn7
      by_cases hfour : n % 4 = 1
      · let k := n / 4
        have hn : n = 4 * k + 1 := by omega
        have hk : 1 ≤ k := by omega
        exact ⟨2 * k, hn ▸ PairCost.fourKPlusOne k hk⟩
      · have hmod4 : n % 4 = 3 := by omega
        by_cases hthree : n % 8 = 3
        · let k := n / 8
          have hn : n = 8 * k + 3 := by omega
          rcases eq_or_ne k 0 with hk0 | hk0
          · have hn0 : n = 3 := by omega
            exact ⟨1, hn0 ▸ PairCost.three⟩
          · rcases eq_or_ne k 3 with hkEq3 | hk3
            · have hn27 : n = 27 := by omega
              exact ⟨13, hn27 ▸ PairCost.twentySeven⟩
            · have hk : 1 ≤ k := by omega
              have hsmall : 2 * k + 1 < n := by omega
              have hsmall3 : 3 ≤ 2 * k + 1 := by omega
              have hsmallOdd : (2 * k + 1) % 2 = 1 := by omega
              have hsmall7 : 2 * k + 1 ≠ 7 := by omega
              obtain ⟨c, hc⟩ := ih (2 * k + 1) hsmall hsmall3 hsmallOdd hsmall7
              exact ⟨c + 2 * k + (k - 1) + 2,
                hn ▸ PairCost.eightKPlusThree k c hk hk3 hc⟩
        · have hseven : n % 8 = 7 := by omega
          let k := n / 8
          have hn : n = 8 * k + 7 := by omega
          rcases eq_or_ne k 0 with hkEq0 | hk0
          · have hn0 : n = 7 := by omega
            exact False.elim (hn7 hn0)
          · rcases eq_or_ne k 1 with hkEq1 | hk1
            · have hn15 : n = 15 := by omega
              exact ⟨7, hn15 ▸ PairCost.fifteen⟩
            · rcases eq_or_ne k 3 with hkEq3 | hk3
              · have hn31 : n = 31 := by omega
                exact ⟨15, hn31 ▸ PairCost.thirtyOne⟩
              · have hk : 2 ≤ k := by omega
                have hsmall : 2 * k + 1 < n := by omega
                have hsmall3 : 3 ≤ 2 * k + 1 := by omega
                have hsmallOdd : (2 * k + 1) % 2 = 1 := by omega
                have hsmall7 : 2 * k + 1 ≠ 7 := by omega
                obtain ⟨c, hc⟩ := ih (2 * k + 1) hsmall hsmall3 hsmallOdd hsmall7
                exact ⟨c + k + (2 * k + 1) + 2,
                  hn ▸ PairCost.eightKPlusSeven k c hk hk3 hc⟩

/-- Thus the shared pair construction exists with exactly `(n-1)/2` products. -/
theorem pair_construction_count (n : ℕ) (hn3 : 3 ≤ n) (hnodd : n % 2 = 1)
    (hn7 : n ≠ 7) :
    ∃ c, PairCost n c ∧ c = (n - 1) / 2 := by
  obtain ⟨c, hc⟩ := pairCost_exists n hn3 hnodd hn7
  exact ⟨c, hc, hc.exact⟩

/-- Cost derivations for complete odd-degree polynomials: normally one final product is
added to a shared pair; degree seven uses its direct four-product circuit. -/
inductive OddPolynomialCost : ℕ → ℕ → Prop where
  | fromPair {n c : ℕ} (pair : PairCost n c) : OddPolynomialCost n (c + 1)
  | seven : OddPolynomialCost 7 4

namespace OddPolynomialCost

theorem odd_and_three_le {n c : ℕ} (h : OddPolynomialCost n c) :
    n % 2 = 1 ∧ 3 ≤ n := by
  cases h with
  | fromPair pair => exact pair.odd_and_three_le
  | seven => norm_num

/-- Exact odd-degree cost, including the direct septic circuit. -/
theorem exact {n c : ℕ} (h : OddPolynomialCost n c) : c = (n + 1) / 2 := by
  cases h with
  | fromPair pair =>
      rw [pair.exact]
      rcases pair.odd_and_three_le with ⟨hodd, hn3⟩
      omega
  | seven => norm_num

end OddPolynomialCost

/-- Every odd degree at least three has a complete polynomial cost derivation. -/
theorem oddPolynomialCost_exists (n : ℕ) (hn3 : 3 ≤ n) (hnodd : n % 2 = 1) :
    ∃ c, OddPolynomialCost n c := by
  rcases eq_or_ne n 7 with rfl | hn7
  · exact ⟨4, OddPolynomialCost.seven⟩
  · obtain ⟨c, hc⟩ := pairCost_exists n hn3 hnodd hn7
    exact ⟨c + 1, OddPolynomialCost.fromPair hc⟩

/-- Full construction accounting.  The even constructor is precisely the paper's
`c₀+xQ` lift and charges its one new product. -/
inductive PolynomialCost : ℕ → ℕ → Prop where
  | linear : PolynomialCost 1 0
  | quadratic : PolynomialCost 2 1
  | odd {n c : ℕ} (source : OddPolynomialCost n c) : PolynomialCost n c
  | evenLift {n c : ℕ} (source : OddPolynomialCost n c) : PolynomialCost (n + 1) (c + 1)

namespace PolynomialCost

/-- For every degree at least three, the construction uses `floor(n/2)+1` products. -/
theorem exact_of_three_le {n c : ℕ} (h : PolynomialCost n c) (hn3 : 3 ≤ n) :
    c = n / 2 + 1 := by
  cases h with
  | linear => omega
  | quadratic => omega
  | odd source =>
      rw [source.exact]
      rcases source.odd_and_three_le with ⟨hodd, _⟩
      omega
  | evenLift source =>
      rw [source.exact]

end PolynomialCost

/-- Complete existence form of paper `thm:construction-count`.  This theorem is only the
gate-count half; the final construction theorem supplies the corresponding decoder. -/
theorem construction_count (n : ℕ) (hn : 1 ≤ n) :
    ∃ c, PolynomialCost n c ∧
      (n = 1 ∧ c = 0 ∨ n = 2 ∧ c = 1 ∨ 3 ≤ n ∧ c = n / 2 + 1) := by
  rcases eq_or_ne n 1 with rfl | hn1
  · exact ⟨0, PolynomialCost.linear, Or.inl ⟨rfl, rfl⟩⟩
  · rcases eq_or_ne n 2 with rfl | hn2
    · exact ⟨1, PolynomialCost.quadratic, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · have hn3 : 3 ≤ n := by omega
      by_cases hodd : n % 2 = 1
      · obtain ⟨c, hc⟩ := oddPolynomialCost_exists n hn3 hodd
        exact ⟨c, PolynomialCost.odd hc,
          Or.inr (Or.inr ⟨hn3, (PolynomialCost.odd hc).exact_of_three_le hn3⟩)⟩
      · let m := n - 1
        have hm3 : 3 ≤ m := by omega
        have hmodd : m % 2 = 1 := by omega
        obtain ⟨c, hc⟩ := oddPolynomialCost_exists m hm3 hmodd
        have hnform : n = m + 1 := by omega
        refine ⟨c + 1, hnform ▸ PolynomialCost.evenLift hc,
          Or.inr (Or.inr ⟨hn3, ?_⟩)⟩
        have hexact := (PolynomialCost.evenLift hc).exact_of_three_le (by omega)
        omega

end FastPoly.Cost
