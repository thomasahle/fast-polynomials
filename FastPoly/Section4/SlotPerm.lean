import FastPoly.Section4.KnownPowers
import Mathlib.Data.Nat.Log

/-!
# The Mersenne row→slot permutation `σ_k`

The pivot-slot map of the known-powers gadget `Q_{2^k-1}` (`lem:Q-unitriangular`):
row `r` of the coefficient map pivots parameter `α (sigma k r)`.  The band structure is
machine-verified at `k = 3, 4, 5` in `tools/mers_slot_table.py`:
head `(3,4)`; level bands `i = 2..k-2` ascending (`ah_i` then the `qh_i`-block via
`σ_i`); the `SP`-band (`δ = 5` then the block via `σ_{k-2}` shifted by `6`); descending
`(b_i, q_i)`-bands; and the top scalars `(2,1,0)`.
-/

namespace FastPoly

/-- Fuel-indexed row→slot permutation; fuel `≥ k` suffices. -/
def sigmaF : ℕ → ℕ → ℕ → ℕ
  | 0, _, r => r
  | f + 1, k, r =>
    if k ≤ 2 then r
    else if k = 3 then
      if r = 0 then 3 else if r = 1 then 4 else if r = 2 then 6
      else if r = 3 then 5 else if r = 4 then 2 else if r = 5 then 1 else 0
    else
      if r ≤ 1 then r + 3
      else if r < 2 ^ (k - 1) - 2 then
        if r = 2 ^ (Nat.log2 (r + 2)) - 2 then doff k (Nat.log2 (r + 2)) + 1
        else sigmaF f (Nat.log2 (r + 2)) (r - (2 ^ (Nat.log2 (r + 2)) - 1))
          + (doff k (Nat.log2 (r + 2)) + 2 + (2 ^ (Nat.log2 (r + 2) - 1) - 1))
      else if r < 3 * 2 ^ (k - 2) - 2 then
        if r = 2 ^ (k - 1) - 2 then 5
        else sigmaF f (k - 2) (r - (2 ^ (k - 1) - 1)) + 6
      else if r < 2 ^ k - 4 then
        if r - (3 * 2 ^ (k - 2) - 2)
            = 2 ^ (k - 2) - 2 ^ (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2)))) then
          doff k (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2))))
        else
          sigmaF f (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2))) - 1)
            (r - (3 * 2 ^ (k - 2) - 2)
              - (2 ^ (k - 2)
                - 2 ^ (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2))))) - 1)
          + (doff k (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2)))) + 2)
      else (2 ^ k - 2) - r

/-- The row→slot permutation of `Q_{2^k-1}`. -/
def sigma (k r : ℕ) : ℕ := sigmaF k k r


/-- One-step unfolding of `sigmaF` (definitional). -/
theorem sigmaF_succ (f k r : ℕ) :
    sigmaF (f + 1) k r =
      (if k ≤ 2 then r
      else if k = 3 then
        if r = 0 then 3 else if r = 1 then 4 else if r = 2 then 6
        else if r = 3 then 5 else if r = 4 then 2 else if r = 5 then 1 else 0
      else
        if r ≤ 1 then r + 3
        else if r < 2 ^ (k - 1) - 2 then
          if r = 2 ^ (Nat.log2 (r + 2)) - 2 then doff k (Nat.log2 (r + 2)) + 1
          else sigmaF f (Nat.log2 (r + 2)) (r - (2 ^ (Nat.log2 (r + 2)) - 1))
            + (doff k (Nat.log2 (r + 2)) + 2 + (2 ^ (Nat.log2 (r + 2) - 1) - 1))
        else if r < 3 * 2 ^ (k - 2) - 2 then
          if r = 2 ^ (k - 1) - 2 then 5
          else sigmaF f (k - 2) (r - (2 ^ (k - 1) - 1)) + 6
        else if r < 2 ^ k - 4 then
          if r - (3 * 2 ^ (k - 2) - 2)
              = 2 ^ (k - 2)
                - 2 ^ (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2)))) then
            doff k (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2))))
          else
            sigmaF f (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2))) - 1)
              (r - (3 * 2 ^ (k - 2) - 2)
                - (2 ^ (k - 2)
                  - 2 ^ (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2))))) - 1)
            + (doff k (Nat.clog 2 (2 ^ (k - 2) - (r - (3 * 2 ^ (k - 2) - 2)))) + 2)
        else (2 ^ k - 2) - r) := rfl

/-- Fuel irrelevance for `sigmaF`. -/
theorem sigmaF_fuel : ∀ k f f', k ≤ f → k ≤ f' → ∀ r, sigmaF f k r = sigmaF f' k r := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f f' hf hf' r
    match k, f, f', hf, hf' with
    | 0, 0, 0, _, _ => rfl
    | 0, 0, _ + 1, _, _ => rfl
    | 0, _ + 1, 0, _, _ => rfl
    | 0, _ + 1, _ + 1, _, _ => rfl
    | k + 1, 0, _, hf, _ => exact absurd hf (by omega)
    | k + 1, _ + 1, 0, _, hf' => exact absurd hf' (by omega)
    | k + 1, f + 1, f' + 1, hf, hf' =>
      rw [sigmaF_succ f (k + 1) r, sigmaF_succ f' (k + 1) r]
      rcases Nat.lt_or_ge k 2 with h2 | h2
      · rw [if_pos (by omega : k + 1 ≤ 2), if_pos (by omega : k + 1 ≤ 2)]
      · rw [if_neg (by omega : ¬ k + 1 ≤ 2), if_neg (by omega : ¬ k + 1 ≤ 2)]
        rcases eq_or_ne (k + 1) 3 with h3 | h3
        · rw [if_pos h3, if_pos h3]
        · rw [if_neg h3, if_neg h3]
          rcases Nat.lt_or_ge r 2 with hr | hr
          · rw [if_pos (by omega : r ≤ 1), if_pos (by omega : r ≤ 1)]
          · rw [if_neg (by omega : ¬ r ≤ 1), if_neg (by omega : ¬ r ≤ 1)]
            rcases Nat.lt_or_ge r (2 ^ (k + 1 - 1) - 2) with hr4 | hr4
            · rw [if_pos hr4, if_pos hr4]
              rcases eq_or_ne r (2 ^ (Nat.log2 (r + 2)) - 2) with heq | hne
              · rw [if_pos heq, if_pos heq]
              · rw [if_neg hne, if_neg hne]
                have hplt : r + 2 < 2 ^ (k + 1 - 1) := by omega
                have hilt : Nat.log2 (r + 2) < k + 1 - 1 :=
                  (Nat.log2_lt (by omega)).2 hplt
                rw [ih (Nat.log2 (r + 2)) (by omega) f f' (by omega) (by omega)]
            · rw [if_neg (by omega : ¬ r < 2 ^ (k + 1 - 1) - 2),
                if_neg (by omega : ¬ r < 2 ^ (k + 1 - 1) - 2)]
              rcases Nat.lt_or_ge r (3 * 2 ^ (k + 1 - 2) - 2) with hr5 | hr5
              · rw [if_pos hr5, if_pos hr5]
                rcases eq_or_ne r (2 ^ (k + 1 - 1) - 2) with heq | hne
                · rw [if_pos heq, if_pos heq]
                · rw [if_neg hne, if_neg hne]
                  rw [ih (k + 1 - 2) (by omega) f f' (by omega) (by omega)]
              · rw [if_neg (by omega : ¬ r < 3 * 2 ^ (k + 1 - 2) - 2),
                  if_neg (by omega : ¬ r < 3 * 2 ^ (k + 1 - 2) - 2)]
                rcases Nat.lt_or_ge r (2 ^ (k + 1) - 4) with hr6 | hr6
                · rw [if_pos hr6, if_pos hr6]
                  rcases eq_or_ne (r - (3 * 2 ^ (k + 1 - 2) - 2))
                      (2 ^ (k + 1 - 2) - 2 ^ (Nat.clog 2 (2 ^ (k + 1 - 2)
                        - (r - (3 * 2 ^ (k + 1 - 2) - 2))))) with heq | hne
                  · rw [if_pos heq, if_pos heq]
                  · rw [if_neg hne, if_neg hne]
                    have hle : 2 ^ (k + 1 - 2) - (r - (3 * 2 ^ (k + 1 - 2) - 2))
                        ≤ 2 ^ (k + 1 - 2) := Nat.sub_le _ _
                    have hclog : Nat.clog 2 (2 ^ (k + 1 - 2)
                        - (r - (3 * 2 ^ (k + 1 - 2) - 2))) ≤ k + 1 - 2 :=
                      (Nat.le_pow_iff_clog_le (by omega)).1 hle
                    rw [ih (Nat.clog 2 (2 ^ (k + 1 - 2)
                        - (r - (3 * 2 ^ (k + 1 - 2) - 2))) - 1) (by omega)
                      f f' (by omega) (by omega)]
                · rw [if_neg (by omega : ¬ r < 2 ^ (k + 1) - 4),
                    if_neg (by omega : ¬ r < 2 ^ (k + 1) - 4)]



-- Anchors against the machine-verified tables (`tools/mers_slot_table.py`).
example : sigma 3 0 = 3 := rfl
example : sigma 3 6 = 0 := rfl
example : sigma 4 2 = 10 := rfl
example : sigma 4 11 = 11 := rfl
example : sigma 5 9 = 30 := rfl
example : sigma 5 22 = 19 := rfl
example : sigma 5 27 = 15 := rfl

end FastPoly
