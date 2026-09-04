import FastPoly.Admissible

/-!
# Pivot slopes of the `R_{k,2^l}` stage tables

The explicit slope function `tLam k l : ℕ → ℤ` of `lem:Rk2l`(3) (tables R-even-table,
R-odd-table, R-odd-base-table): row `j` of the combined remainder `x·R⁽¹⁾ + R⁽²⁾` has the
affine pivot `tLam k l j • α j + F_j`.  Explicit-decoding rule: the decoder divides by
these integers, so they are named data, not existentials.

Layout for `k ≥ 2`, `b = (k-2)·2^l`, `d = (k-1)·2^l`:
* even `k`:   `[b+2^{l-1}, d) ↦ -k`, `[b, b+2^{l-1}) ↦ k/2`, `[0,b) ↦` inner table;
* odd `k`, `l ≥ 3`: `[b+2^{l-1}, d) ↦ -k(k-1)`, `[b+2^{l-2}, b+2^{l-1}) ↦ -(k-1)`,
  `[b, b+2^{l-2}) ↦ (k-1)/2`, `[2^l, b) ↦` inner shifted by `2^l`, `[0, 2^l) ↦ 1`;
* odd `k`, `l = 2` (shared base): `d-1 ↦ -k(k-1)`, `d-2 ↦ -(k-1)`, `{d-4, d-3} ↦ (k-1)/2`,
  `[4, b) ↦` inner shifted by `4`, `[0,4) ↦ 1`.
-/

namespace FastPoly

/-- Fuel-indexed slope table; fuel `≥ k` suffices. -/
def tLamF : ℕ → ℕ → ℕ → ℕ → ℤ
  | 0, _, _, _ => 1
  | f + 1, k, l, j =>
    if k ≤ 1 then 1
    else if k % 2 = 0 then
      if j < (k - 2) * 2 ^ l then tLamF f (k / 2) (l + 1) j
      else if j < (k - 2) * 2 ^ l + 2 ^ (l - 1) then ((k / 2 : ℕ) : ℤ)
      else -((k : ℕ) : ℤ)
    else
      if l ≤ 2 then
        if j < 4 then 1
        else if j < 4 * (k - 2) then tLamF f ((k - 1) / 2) 3 (j - 4)
        else if j < 4 * (k - 2) + 2 then (((k - 1) / 2 : ℕ) : ℤ)
        else if j < 4 * (k - 2) + 3 then -(((k - 1 : ℕ)) : ℤ)
        else -(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ))
      else
        if j < 2 ^ l then 1
        else if j < (k - 2) * 2 ^ l then tLamF f ((k - 1) / 2) (l + 1) (j - 2 ^ l)
        else if j < (k - 2) * 2 ^ l + 2 ^ (l - 2) then (((k - 1) / 2 : ℕ) : ℤ)
        else if j < (k - 2) * 2 ^ l + 2 ^ (l - 1) then -(((k - 1 : ℕ)) : ℤ)
        else -(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ))

/-- The slope table of `lem:Rk2l`. -/
def tLam (k l j : ℕ) : ℤ := tLamF k k l j

/-- One-step unfolding (definitional). -/
theorem tLamF_succ (f k l j : ℕ) :
    tLamF (f + 1) k l j =
      (if k ≤ 1 then 1
      else if k % 2 = 0 then
        if j < (k - 2) * 2 ^ l then tLamF f (k / 2) (l + 1) j
        else if j < (k - 2) * 2 ^ l + 2 ^ (l - 1) then ((k / 2 : ℕ) : ℤ)
        else -((k : ℕ) : ℤ)
      else
        if l ≤ 2 then
          if j < 4 then 1
          else if j < 4 * (k - 2) then tLamF f ((k - 1) / 2) 3 (j - 4)
          else if j < 4 * (k - 2) + 2 then (((k - 1) / 2 : ℕ) : ℤ)
          else if j < 4 * (k - 2) + 3 then -(((k - 1 : ℕ)) : ℤ)
          else -(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ))
        else
          if j < 2 ^ l then 1
          else if j < (k - 2) * 2 ^ l then tLamF f ((k - 1) / 2) (l + 1) (j - 2 ^ l)
          else if j < (k - 2) * 2 ^ l + 2 ^ (l - 2) then (((k - 1) / 2 : ℕ) : ℤ)
          else if j < (k - 2) * 2 ^ l + 2 ^ (l - 1) then -(((k - 1 : ℕ)) : ℤ)
          else -(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ))) := rfl

/-- Fuel irrelevance for the slope table. -/
theorem tLamF_fuel : ∀ k f f', k ≤ f → k ≤ f' → ∀ l j,
    tLamF f k l j = tLamF f' k l j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f f' hf hf' l j
    match k, f, f', hf, hf' with
    | 0, 0, 0, _, _ => rfl
    | 0, 0, _ + 1, _, _ => rfl
    | 0, _ + 1, 0, _, _ => rfl
    | 0, _ + 1, _ + 1, _, _ => rfl
    | k + 1, 0, _, hf, _ => exact absurd hf (by omega)
    | k + 1, _ + 1, 0, _, hf' => exact absurd hf' (by omega)
    | k + 1, f + 1, f' + 1, hf, hf' =>
      rw [tLamF_succ f (k + 1) l j, tLamF_succ f' (k + 1) l j]
      rcases Nat.lt_or_ge k 1 with h1 | h1
      · rw [if_pos (by omega : k + 1 ≤ 1), if_pos (by omega : k + 1 ≤ 1)]
      · rw [if_neg (by omega : ¬ k + 1 ≤ 1), if_neg (by omega : ¬ k + 1 ≤ 1)]
        rcases eq_or_ne ((k + 1) % 2) 0 with hpar | hpar
        · rw [if_pos hpar, if_pos hpar]
          rcases Nat.lt_or_ge j ((k + 1 - 2) * 2 ^ l) with hj | hj
          · rw [if_pos hj, if_pos hj]
            exact ih ((k + 1) / 2) (by omega) f f' (by omega) (by omega) (l + 1) j
          · rw [if_neg (by omega : ¬ j < (k + 1 - 2) * 2 ^ l),
              if_neg (by omega : ¬ j < (k + 1 - 2) * 2 ^ l)]
        · rw [if_neg hpar, if_neg hpar]
          rcases Nat.lt_or_ge l 3 with hl | hl
          · rw [if_pos (by omega : l ≤ 2), if_pos (by omega : l ≤ 2)]
            rcases Nat.lt_or_ge j 4 with hj4 | hj4
            · rw [if_pos hj4, if_pos hj4]
            · rw [if_neg (by omega : ¬ j < 4), if_neg (by omega : ¬ j < 4)]
              rcases Nat.lt_or_ge j (4 * (k + 1 - 2)) with hjb | hjb
              · rw [if_pos hjb, if_pos hjb]
                exact ih ((k + 1 - 1) / 2) (by omega) f f' (by omega) (by omega) 3 (j - 4)
              · rw [if_neg (by omega : ¬ j < 4 * (k + 1 - 2)),
                  if_neg (by omega : ¬ j < 4 * (k + 1 - 2))]
          · rw [if_neg (by omega : ¬ l ≤ 2), if_neg (by omega : ¬ l ≤ 2)]
            rcases Nat.lt_or_ge j (2 ^ l) with hjl | hjl
            · rw [if_pos hjl, if_pos hjl]
            · rw [if_neg (by omega : ¬ j < 2 ^ l), if_neg (by omega : ¬ j < 2 ^ l)]
              rcases Nat.lt_or_ge j ((k + 1 - 2) * 2 ^ l) with hjb | hjb
              · rw [if_pos hjb, if_pos hjb]
                exact ih ((k + 1 - 1) / 2) (by omega) f f' (by omega) (by omega) (l + 1)
                  (j - 2 ^ l)
              · rw [if_neg (by omega : ¬ j < (k + 1 - 2) * 2 ^ l),
                  if_neg (by omega : ¬ j < (k + 1 - 2) * 2 ^ l)]

end FastPoly
