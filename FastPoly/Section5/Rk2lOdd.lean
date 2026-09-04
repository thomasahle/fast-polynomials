import FastPoly.Section5.T
import FastPoly.Section5.Binomial
import FastPoly.Section5.UBinomial

/-!
# The odd branch of `lem:Rk2l`: step and power shape

Entry layer for the odd (`l ≥ 3`) branch: stepping the `T`-pair through `oddOut`, and the
odd-step powers as squares of the *shifted* bases `H + S⁽¹⁾₁` (resp. `H̃ + S⁽²⁾₁`) plus the
corrections `G₁ = S₃ - S₂²`, `G₂ = ζ - S̃₂²` (paper `R-odd-block-exp` uses exactly this
shape before the `U`-binomial split).
-/

namespace FastPoly

open Polynomial Finset

variable {A : Type*} [CommRing A] [Nontrivial A]
variable {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}

/-- Odd-branch corrections `G₁ = S₃ - S₂²` and `G₂ = ζ - S̃₂²`. -/
noncomputable def oG1 (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  oS3 Hp k l α - oS2 Hp k l α ^ 2

noncomputable def oG2 (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  C (α ((k - 2) * 2 ^ l)) - oS2t Hp k l α ^ 2

omit [Nontrivial A] in
/-- The odd-step power as a square of the shifted base plus correction. -/
theorem oddH_eq_sq_add (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) :
    oddH Hp k l α = (Hp l + tS1 Hp k l α) ^ 2 + oG1 Hp k l α := by
  unfold oddH oG1
  ring

omit [Nontrivial A] in
/-- The odd-step shifted power as a square plus correction. -/
theorem oddHt_eq_sq_add (Hp : ℕ → A[X]) (Ht : A[X]) (k l : ℕ) (α : ℕ → A) :
    oddHt Hp Ht k l α = (Ht + tS1t Hp k l α) ^ 2 + oG2 Hp k l α := by
  unfold oddHt oG2
  ring

omit [Nontrivial A] in
/-- Stepping the `T`-pair through the odd main branch. -/
theorem Tpair_odd_step (hpar : ¬ k % 2 = 0) (hk : 2 ≤ k) (hl : ¬ l ≤ 2) :
    Tpair Hp Ht k l α
      = oddOut Hp Ht k l α (Tpair (Function.update Hp (l + 1) (oddH Hp k l α))
          (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))) := by
  obtain ⟨g, rfl⟩ : ∃ g, k = g + 1 := ⟨k - 1, by omega⟩
  show TF (g + 1) (g + 1) l Hp Ht α = _
  rw [TF_succ_odd_main (by omega) hpar hl]
  exact congrArg (oddOut Hp Ht (g + 1) l α)
    (TF_fuel ((g + 1 - 1) / 2) g ((g + 1 - 1) / 2) (by omega) le_rfl (l + 1) _ _ _)

/-- **Odd remainder, first stage** (towards paper `R-odd-block-exp`): the raw split of
`R⁽¹⁾` through the step, with the inner power in shifted-square form. -/
theorem Rpair_odd_fst (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) :
    (Rpair Hp Ht k l α).1
      = (Hp l - (k - 1) • tS1 Hp k l α)
          * (((Hp l + tS1 Hp k l α) ^ 2 + oG1 Hp k l α) ^ ((k - 1) / 2)
            + (Rpair (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
                ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1)
        + peel Hp l (fun j => α (1 + j)) - Hp l ^ k := by
  have hupd : Function.update Hp (l + 1) (oddH Hp k l α) (l + 1) = oddH Hp k l α := by
    rw [update_last]
  obtain ⟨hsplit, -⟩ := Tpair_eq_pow_add_R
    (Hp := Function.update Hp (l + 1) (oddH Hp k l α)) (Ht := oddHt Hp Ht k l α)
    (k := (k - 1) / 2) (l := l + 1) (α := fun j => α (2 ^ l + j))
  show (Tpair Hp Ht k l α).1 - Hp l ^ k = _
  rw [Tpair_odd_step hpar (by omega) hl]
  show ((Hp l - (k - 1) • tS1 Hp k l α) * (Tpair (Function.update Hp (l + 1)
      (oddH Hp k l α)) (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
      (fun j => α (2 ^ l + j))).1 + peel Hp l (fun j => α (1 + j))) - Hp l ^ k = _
  rw [hsplit, hupd, oddH_eq_sq_add]

/-- **Odd remainder, first stage, second component**. -/
theorem Rpair_odd_snd (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) :
    (Rpair Hp Ht k l α).2
      = (Ht - (k - 1) • tS1t Hp k l α)
          * (((Ht + tS1t Hp k l α) ^ 2 + oG2 Hp k l α) ^ ((k - 1) / 2)
            + (Rpair (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
                ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2)
        + C (α 0) - Ht ^ k := by
  obtain ⟨-, hsplit⟩ := Tpair_eq_pow_add_R
    (Hp := Function.update Hp (l + 1) (oddH Hp k l α)) (Ht := oddHt Hp Ht k l α)
    (k := (k - 1) / 2) (l := l + 1) (α := fun j => α (2 ^ l + j))
  show (Tpair Hp Ht k l α).2 - Ht ^ k = _
  rw [Tpair_odd_step hpar (by omega) hl]
  show ((Ht - (k - 1) • tS1t Hp k l α) * (Tpair (Function.update Hp (l + 1)
      (oddH Hp k l α)) (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
      (fun j => α (2 ^ l + j))).2 + C (α 0)) - Ht ^ k = _
  rw [hsplit, oddHt_eq_sq_add]

/-- **Odd remainder, expanded** (paper `R-odd-block-exp`, first component): the binomial
expansion of the inner power distributed through the factor `L₁ = H - (k-1)S₁`.  The first
group `L₁(H+S₁)^{k-1} - H^k` is the `U`-binomial part (`-cU²H^{k-2} + E^U`), analyzed
separately. -/
theorem Rpair_odd_fst' (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) :
    (Rpair Hp Ht k l α).1
      = ((Hp l - (k - 1) • tS1 Hp k l α) * (Hp l + tS1 Hp k l α) ^ (k - 1) - Hp l ^ k)
        + ((k - 1) / 2) • ((Hp l - (k - 1) • tS1 Hp k l α)
            * (oG1 Hp k l α * (Hp l + tS1 Hp k l α) ^ (k - 3)))
        + (Hp l - (k - 1) • tS1 Hp k l α)
            * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α) ((k - 1) / 2)
        + (Hp l - (k - 1) • tS1 Hp k l α)
            * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
                ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1
        + peel Hp l (fun j => α (1 + j)) := by
  have hm1 : 1 ≤ (k - 1) / 2 := by omega
  have hpow := pow_add_eq ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α) hm1
  have he1 : ((Hp l + tS1 Hp k l α) ^ 2) ^ ((k - 1) / 2)
      = (Hp l + tS1 Hp k l α) ^ (k - 1) := by
    rw [← pow_mul]
    congr 1
    omega
  have he2 : ((Hp l + tS1 Hp k l α) ^ 2) ^ ((k - 1) / 2 - 1)
      = (Hp l + tS1 Hp k l α) ^ (k - 3) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [Rpair_odd_fst hpar hk hl, hpow, he1, he2]
  ring

/-- **Odd remainder, expanded, second component**. -/
theorem Rpair_odd_snd' (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) :
    (Rpair Hp Ht k l α).2
      = ((Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1) - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • tS1t Hp k l α)
            * (oG2 Hp k l α * (Ht + tS1t Hp k l α) ^ (k - 3)))
        + (Ht - (k - 1) • tS1t Hp k l α)
            * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α) ((k - 1) / 2)
        + (Ht - (k - 1) • tS1t Hp k l α)
            * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
                ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2
        + C (α 0) := by
  have hm1 : 1 ≤ (k - 1) / 2 := by omega
  have hpow := pow_add_eq ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α) hm1
  have he1 : ((Ht + tS1t Hp k l α) ^ 2) ^ ((k - 1) / 2)
      = (Ht + tS1t Hp k l α) ^ (k - 1) := by
    rw [← pow_mul]
    congr 1
    omega
  have he2 : ((Ht + tS1t Hp k l α) ^ 2) ^ ((k - 1) / 2 - 1)
      = (Ht + tS1t Hp k l α) ^ (k - 3) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [Rpair_odd_snd hpar hk hl, hpow, he1, he2]
  ring

/-- Top two coefficients of the odd correction `G₁ = S₃ - S₂²`:
degree `2^{l-1}`, leading `-1`, subleading `-2·[x^{2^{l-2}-1}]S₂`. -/
theorem oG1_top (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) :
    (oG1 Hp k l α).natDegree ≤ 2 ^ (l - 1) ∧
    (oG1 Hp k l α).coeff (2 ^ (l - 1)) = -1 ∧
    (oG1 Hp k l α).coeff (2 ^ (l - 1) - 1)
      = -(2 • (oS2 Hp k l α).coeff (2 ^ (l - 2) - 1)) := by
  obtain ⟨hs2m, hs2d⟩ := oS2_good (k := k) (α := α) hHp hl
  obtain ⟨-, hqd⟩ := peel_monic Hp (l - 2)
    (fun i' h1' hik => hHp i' h1' (by omega)) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 1 + j))
  have hoS3d : (oS3 Hp k l α).natDegree = 2 ^ (l - 2) - 1 := hqd
  have h1p : (1:ℕ) ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have h2l : 2 * 2 ^ (l - 2) = 2 ^ (l - 1) := by
    have hl1 : l - 2 + 1 = l - 1 := by omega
    calc 2 * 2 ^ (l - 2) = 2 ^ (l - 2 + 1) := by ring
    _ = 2 ^ (l - 1) := by rw [hl1]
  rw [← h2l]
  unfold oG1
  exact low_sub_sq_top hs2m hs2d h1p (by rw [hoS3d]; omega)

/-- Top two coefficients of the odd correction `G₂ = ζ - S̃₂²`. -/
theorem oG2_top (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) :
    (oG2 Hp k l α).natDegree ≤ 2 ^ (l - 1) ∧
    (oG2 Hp k l α).coeff (2 ^ (l - 1)) = -1 ∧
    (oG2 Hp k l α).coeff (2 ^ (l - 1) - 1)
      = -(2 • (oS2t Hp k l α).coeff (2 ^ (l - 2) - 1)) := by
  obtain ⟨hs2m, hs2d⟩ := oS2t_good (k := k) (α := α) hHp hl
  have h1p : (1:ℕ) ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have h2l : 2 * 2 ^ (l - 2) = 2 ^ (l - 1) := by
    have hl1 : l - 2 + 1 = l - 1 := by omega
    calc 2 * 2 ^ (l - 2) = 2 ^ (l - 2 + 1) := by ring
    _ = 2 ^ (l - 1) := by rw [hl1]
  rw [← h2l]
  unfold oG2
  exact low_sub_sq_top hs2m hs2d h1p (by rw [natDegree_C]; omega)

omit [Nontrivial A] in
/-- The `t = 2` coefficient of the `U`-binomial expansion in closed form:
`C(k-1,2) - (k-1)² = -C(k,2) = -k(k-1)/2`. -/
theorem cast_choose_two_sub_sq (k : ℕ) (hk : 1 ≤ k) :
    ((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X])
      = -((k.choose 2 : ℕ) : A[X]) := by
  have hnat : (k - 1).choose 2 + k.choose 2 = (k - 1) * (k - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Nat.choose_two_right, Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    have hab : (n + 1) * n = n * (n - 1) + 2 * n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rfl
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
    have hsum : n * (n - 1) + (n + 1) * n = 2 * (n * n) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rfl
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
    have heven : 2 ∣ n * (n - 1) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ⟨0, rfl⟩
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have := Nat.even_mul_succ_self m
        rcases this with ⟨w, hw⟩
        exact ⟨w, by rw [mul_comm (m + 1) m, hw]; ring⟩
    omega
  have hc : ((k - 1).choose 2 : A[X]) + ((k.choose 2 : ℕ) : A[X])
      = ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → A[X]) hnat
  rw [← hc]
  ring

omit [Nontrivial A] in
/-- Top two coefficients of the odd principal factor `U²·Hⁿ` (monic of degree
`2r + nD`, subleading `2σ + n·h`). -/
theorem sq_mul_pow_top {H U : A[X]} {D r n : ℕ} (hH : H.Monic) (hHd : H.natDegree = D)
    (hU : U.Monic) (hUd : U.natDegree = r) (hr1 : 1 ≤ r) (hD1 : 1 ≤ D) (hn : 1 ≤ n) :
    (U ^ 2 * H ^ n).natDegree = 2 * r + n * D ∧
    (U ^ 2 * H ^ n).coeff (2 * r + n * D) = 1 ∧
    (U ^ 2 * H ^ n).coeff (2 * r + n * D - 1)
      = 2 • U.coeff (r - 1) + n • H.coeff (D - 1) := by
  have hu2m : (U ^ 2).Monic := hU.pow 2
  have hu2d : (U ^ 2).natDegree = 2 * r := by rw [hU.natDegree_pow, hUd]
  have hhm : (H ^ n).Monic := hH.pow n
  have hhd : (H ^ n).natDegree = n * D := by rw [hH.natDegree_pow, hHd]
  have hm : (U ^ 2 * H ^ n).Monic := hu2m.mul hhm
  have hd : (U ^ 2 * H ^ n).natDegree = 2 * r + n * D := by
    rw [hu2m.natDegree_mul hhm, hu2d, hhd]
  have h1nd : 1 ≤ n * D := Nat.mul_pos (by omega) (by omega)
  refine ⟨hd, ?_, ?_⟩
  · rw [← hd]
    exact hm.coeff_natDegree
  · have hkey := monic_mul_coeff_sub_one hu2m hhm hu2d hhd (by omega) (by omega)
    rw [hkey, FastPoly.Monic.pow_coeff_sub_one hU hUd hr1 2 (by omega),
      FastPoly.Monic.pow_coeff_sub_one hH hHd hD1 n hn]

omit [Nontrivial A] in
/-- **Top two of the odd principal group** `L·(H+U)^n - H^{n+1}` (paper: the combination
of `-cU²H^{k-2}` and the suppressed `E^U`-tail at the two boundary rows): degree `≤ nD`,
leading `-C(n+1,2)`, subleading `-C(n+1,2)·(2σ + (n-1)h)`. -/
theorem uPrincipal_top {H U : A[X]} {D r n : ℕ}
    (hH : H.Monic) (hHd : H.natDegree = D) (hU : U.Monic) (hUd : U.natDegree = r)
    (h2r : 2 * r = D) (hr2 : 2 ≤ r) (hn : 2 ≤ n) :
    ((H - (n : A[X]) * U) * (H + U) ^ n - H ^ (n + 1)).natDegree ≤ n * D ∧
    ((H - (n : A[X]) * U) * (H + U) ^ n - H ^ (n + 1)).coeff (n * D)
      = -(((n + 1).choose 2 : ℕ) : A) ∧
    ((H - (n : A[X]) * U) * (H + U) ^ n - H ^ (n + 1)).coeff (n * D - 1)
      = -(((n + 1).choose 2 : ℕ) : A)
          * (2 • U.coeff (r - 1) + (n - 1) • H.coeff (D - 1)) := by
  have hX : (H - (n : A[X]) * U) * (H + U) ^ n - H ^ (n + 1)
      = ((n.choose 2 : A[X]) - (n : A[X]) * (n : A[X])) * (U ^ 2 * H ^ (n - 1))
        + uTail H U n := by
    rw [mul_pow_split H U (by omega : 2 ≤ n)]
    ring
  have hcoefC : ((n.choose 2 : A[X]) - (n : A[X]) * (n : A[X]))
      = C (-((((n + 1).choose 2 : ℕ)) : A)) := by
    have hkey := cast_choose_two_sub_sq (A := A) (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hkey
    rw [hkey, ← C_eq_natCast, ← map_neg]
  have hut : (uTail H U n).natDegree ≤ 3 * r + (n - 2) * D :=
    natDegree_uTail_le (le_of_eq hHd) (le_of_eq hUd) (by omega)
  obtain ⟨hMd, hMl, hMs⟩ := sq_mul_pow_top (n := n - 1) hH hHd hU hUd
    (by omega) (by omega) (by omega)
  have hidx : 2 * r + (n - 1) * D = n * D := by
    have h1 : (n - 1) * D + D = n * D := by
      have hn1 : n - 1 + 1 = n := by omega
      calc (n - 1) * D + D = (n - 1 + 1) * D := by ring
      _ = n * D := by rw [hn1]
    omega
  have h2D : (n - 2) * D + 2 * D = n * D := by
    have hn2 : n - 2 + 2 = n := by omega
    calc (n - 2) * D + 2 * D = (n - 2 + 2) * D := by ring
    _ = n * D := by rw [hn2]
  have hz1 : (uTail H U n).coeff (n * D) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hz2 : (uTail H U n).coeff (n * D - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hX]
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · rw [hcoefC]
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, hMd]
      omega
    · omega
  · rw [hX, coeff_add, hcoefC, coeff_C_mul, hz1, add_zero, ← hidx, hMl, mul_one]
  · rw [hX, coeff_add, hcoefC, coeff_C_mul, hz2, add_zero]
    have hidx1 : n * D - 1 = 2 * r + (n - 1) * D - 1 := by omega
    rw [hidx1, hMs]

/-- The odd multiplier `L₁ = H - (k-1)·S₁` is monic of degree `2^l`. -/
theorem oddL_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) :
    (Hp l - (k - 1) • tS1 Hp k l α).Monic ∧
    (Hp l - (k - 1) • tS1 Hp k l α).natDegree = 2 ^ l := by
  obtain ⟨hLm, hLd⟩ := hHp l (by omega) le_rfl
  obtain ⟨-, hs1d⟩ := tS1_good (k := k) (α := α) hHp (by omega)
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hle : (2:ℕ) ^ (l - 1 + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hda : (2:ℕ) ^ (l - 1 + 1) = 2 ^ (l - 1) + 2 ^ (l - 1) := by ring
  have hsm : ((k - 1) • tS1 Hp k l α).natDegree ≤ 2 ^ (l - 1) :=
    le_trans (natDegree_smul_le _ _) (le_of_eq hs1d)
  obtain ⟨hm, hd⟩ := monic_sub_low (e := (k - 1) • tS1 Hp k l α) hLm
    (Or.inr (by rw [hLd]; omega))
  exact ⟨hm, hd.trans hLd⟩

/-- The odd multiplier `L₂ = H̃ - (k-1)·S̃₁` is monic of degree `2^l`. -/
theorem oddLt_good (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) :
    (Ht - (k - 1) • tS1t Hp k l α).Monic ∧
    (Ht - (k - 1) • tS1t Hp k l α).natDegree = 2 ^ l := by
  obtain ⟨-, hs1d⟩ := tS1t_good (k := k) (α := α) hHp (by omega)
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hle : (2:ℕ) ^ (l - 1 + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hda : (2:ℕ) ^ (l - 1 + 1) = 2 ^ (l - 1) + 2 ^ (l - 1) := by ring
  have hsm : ((k - 1) • tS1t Hp k l α).natDegree ≤ 2 ^ (l - 1) :=
    le_trans (natDegree_smul_le _ _) (le_of_eq hs1d)
  obtain ⟨hm, hd⟩ := monic_sub_low (e := (k - 1) • tS1t Hp k l α) hHt
    (Or.inr (by rw [hdHt]; omega))
  exact ⟨hm, hd.trans hdHt⟩

omit [Nontrivial A] in
/-- **Generic odd-branch boundary assembly**: the five-group sum keeps the principal
group's degree bound and two boundary coefficients (all other groups are suppressed
below row `(k-1)D - 1`). -/
theorem odd_sum_top {L W G R' T H0 : A[X]} {D r k m : ℕ} {c0 c1 : A}
    (hLd : L.natDegree = D) (hWm : W.Monic) (hWd : W.natDegree = D)
    (hGd : G.natDegree ≤ r) (hR' : R'.natDegree ≤ (k - 3) * D)
    (hTd : T.natDegree ≤ D - 1)
    (h2r : 2 * r = D) (hr2 : 2 ≤ r) (hk : 3 ≤ k) (hme : 2 * m = k - 1)
    (hp1 : (L * W ^ (k - 1) - H0 ^ k).natDegree ≤ (k - 1) * D)
    (hp2 : (L * W ^ (k - 1) - H0 ^ k).coeff ((k - 1) * D) = c0)
    (hp3 : (L * W ^ (k - 1) - H0 ^ k).coeff ((k - 1) * D - 1) = c1) :
    (((L * W ^ (k - 1) - H0 ^ k) + m • (L * (G * W ^ (k - 3)))
        + L * binTail (W ^ 2) G m + L * R' + T).natDegree ≤ (k - 1) * D) ∧
    (((L * W ^ (k - 1) - H0 ^ k) + m • (L * (G * W ^ (k - 3)))
        + L * binTail (W ^ 2) G m + L * R' + T).coeff ((k - 1) * D) = c0) ∧
    (((L * W ^ (k - 1) - H0 ^ k) + m • (L * (G * W ^ (k - 3)))
        + L * binTail (W ^ 2) G m + L * R' + T).coeff ((k - 1) * D - 1) = c1) := by
  have h1r : (1:ℕ) ≤ r := by omega
  have hb1 : (k - 3) * D + D = (k - 2) * D := by
    have h3 : k - 3 + 1 = k - 2 := by omega
    calc (k - 3) * D + D = (k - 3 + 1) * D := by ring
    _ = (k - 2) * D := by rw [h3]
  have hb2 : (k - 2) * D + D = (k - 1) * D := by
    have h3 : k - 2 + 1 = k - 1 := by omega
    calc (k - 2) * D + D = (k - 2 + 1) * D := by ring
    _ = (k - 1) * D := by rw [h3]
  -- group G: ≤ (k-2)D + r
  have hWp : (W ^ (k - 3)).natDegree = (k - 3) * D := by
    rw [hWm.natDegree_pow, hWd]
  have hGrp : (m • (L * (G * W ^ (k - 3)))).natDegree ≤ (k - 2) * D + r := by
    refine le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le ?_)
    have hin := le_trans natDegree_mul_le (Nat.add_le_add hGd (le_of_eq hWp))
    omega
  -- group binTail: ≤ (k-2)D
  have hBrp : (L * binTail (W ^ 2) G m).natDegree ≤ (k - 2) * D := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · rw [binTail_eq_zero _ _ hm2, mul_zero, natDegree_zero]
      omega
    · obtain ⟨u, rfl⟩ : ∃ u, m = u + 2 := ⟨m - 2, by omega⟩
      have hbound := natDegree_binTail_le (P := W ^ 2) (E := G) (p := 2 * D) (e := r)
        (le_of_eq (by rw [hWm.natDegree_pow, hWd])) hGd (by omega) (u + 2)
      have hin := le_trans natDegree_mul_le (Nat.add_le_add (le_of_eq hLd) hbound)
      have hu2 : u + 2 - 2 = u := by omega
      rw [hu2] at hin
      have hk2 : k - 2 = 2 * u + 3 := by omega
      have hx : D + (2 * r + u * (2 * D)) + D = (2 * u + 3) * D := by
        have hDr : 2 * r = D := h2r
        calc D + (2 * r + u * (2 * D)) + D = 2 * r + (2 * u + 2) * D := by ring
        _ = (2 * u + 3) * D := by rw [hDr]; ring
      have hy : (k - 2) * D = (2 * u + 3) * D := by rw [hk2]
      omega
  -- group R': ≤ (k-2)D
  have hRrp : (L * R').natDegree ≤ (k - 2) * D := by
    have hin := le_trans natDegree_mul_le (Nat.add_le_add (le_of_eq hLd) hR')
    omega
  -- suppression at the two boundary rows
  have hDlt : D - 1 < (k - 1) * D - 1 := by
    have h2D : 2 * D ≤ (k - 1) * D := by
      have := Nat.mul_le_mul_right D (show 2 ≤ k - 1 by omega)
      omega
    omega
  have hGz1 : (m • (L * (G * W ^ (k - 3)))).coeff ((k - 1) * D) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hGz2 : (m • (L * (G * W ^ (k - 3)))).coeff ((k - 1) * D - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hBz1 : (L * binTail (W ^ 2) G m).coeff ((k - 1) * D) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hBz2 : (L * binTail (W ^ 2) G m).coeff ((k - 1) * D - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hRz1 : (L * R').coeff ((k - 1) * D) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hRz2 : (L * R').coeff ((k - 1) * D - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hTz1 : T.coeff ((k - 1) * D) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hTz2 : T.coeff ((k - 1) * D - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _)
      (max_le (le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _)
        (max_le hp1 ?_)) ?_)) ?_)) ?_)
    · omega
    · omega
    · omega
    · omega
  · rw [coeff_add, coeff_add, coeff_add, coeff_add, hp2, hGz1, hBz1, hRz1, hTz1]
    ring
  · rw [coeff_add, coeff_add, coeff_add, coeff_add, hp3, hGz2, hBz2, hRz2, hTz2]
    ring

/-- **`R-top-two-odd`** for the main branch (`l ≥ 3`): degree bound and the two boundary
coefficients of the odd-branch remainder pair. -/
theorem Rpair_odd_top (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l)
    (hR1 : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
        ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1.natDegree ≤ (k - 3) * 2 ^ l)
    (hR2 : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
        ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2.natDegree ≤ (k - 3) * 2 ^ l) :
    ((Rpair Hp Ht k l α).1.natDegree ≤ (k - 1) * 2 ^ l ∧
      (Rpair Hp Ht k l α).1.coeff ((k - 1) * 2 ^ l) = -((k.choose 2 : ℕ) : A) ∧
      (Rpair Hp Ht k l α).1.coeff ((k - 1) * 2 ^ l - 1)
        = -((k.choose 2 : ℕ) : A) * (2 • (tS1 Hp k l α).coeff (2 ^ (l - 1) - 1)
            + (k - 2) • (Hp l).coeff (2 ^ l - 1))) ∧
    ((Rpair Hp Ht k l α).2.natDegree ≤ (k - 1) * 2 ^ l ∧
      (Rpair Hp Ht k l α).2.coeff ((k - 1) * 2 ^ l) = -((k.choose 2 : ℕ) : A) ∧
      (Rpair Hp Ht k l α).2.coeff ((k - 1) * 2 ^ l - 1)
        = -((k.choose 2 : ℕ) : A) * (2 • (tS1t Hp k l α).coeff (2 ^ (l - 1) - 1)
            + (k - 2) • Ht.coeff (2 ^ l - 1))) := by
  obtain ⟨hLm, hLd⟩ := hHp l (by omega) le_rfl
  obtain ⟨hL1m, hL1d⟩ := oddL_good (k := k) (α := α) hHp hl
  obtain ⟨hL2m, hL2d⟩ := oddLt_good (k := k) (α := α) hHp hl hHt hdHt
  obtain ⟨hs1m, hs1d⟩ := tS1_good (k := k) (α := α) hHp (by omega)
  obtain ⟨hs1tm, hs1td⟩ := tS1t_good (k := k) (α := α) hHp (by omega)
  obtain ⟨hG1d, -, -⟩ := oG1_top (k := k) (α := α) hHp hl
  obtain ⟨hG2d, -, -⟩ := oG2_top (k := k) (α := α) hHp hl
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have h2l : 2 * 2 ^ (l - 1) = 2 ^ l := by
    have hl1 : l - 1 + 1 = l := by omega
    calc 2 * 2 ^ (l - 1) = 2 ^ (l - 1 + 1) := by ring
    _ = 2 ^ l := by rw [hl1]
  have h4r : (4:ℕ) ≤ 2 ^ (l - 1) := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (l - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨hWm, hWd⟩ := monic_add_low (e := tS1 Hp k l α) hLm
    (Or.inr (by rw [hs1d, hLd]; omega))
  obtain ⟨hWtm, hWtd⟩ := monic_add_low (e := tS1t Hp k l α) hHt
    (Or.inr (by rw [hs1td, hdHt]; omega))
  have hQd : (peel Hp l (fun j => α (1 + j))).natDegree ≤ 2 ^ l - 1 :=
    le_of_eq (peel_monic Hp l (fun i' h1' hik => hHp i' h1' (by omega)) (by omega)
      (fun j => α (1 + j))).2
  have hCd : (C (α 0) : A[X]).natDegree ≤ 2 ^ l - 1 := by
    rw [natDegree_C]
    omega
  have hme : 2 * ((k - 1) / 2) = k - 1 := by omega
  -- principal group facts, first component
  have hsm1 : (k - 1) • tS1 Hp k l α = ((k - 1 : ℕ) : A[X]) * tS1 Hp k l α := by
    rw [nsmul_eq_mul]
  have hsm2 : (k - 1) • tS1t Hp k l α = ((k - 1 : ℕ) : A[X]) * tS1t Hp k l α := by
    rw [nsmul_eq_mul]
  obtain ⟨hP1d, hP1l, hP1s⟩ := uPrincipal_top (D := 2 ^ l) (r := 2 ^ (l - 1)) (n := k - 1)
    hLm hLd hs1m hs1d h2l (by omega) (by omega)
  obtain ⟨hP2d, hP2l, hP2s⟩ := uPrincipal_top (D := 2 ^ l) (r := 2 ^ (l - 1)) (n := k - 1)
    hHt hdHt hs1tm hs1td h2l (by omega) (by omega)
  rw [show k - 1 + 1 = k from by omega] at hP1d hP1l hP1s hP2d hP2l hP2s
  rw [show k - 1 - 1 = k - 2 from by omega] at hP1s hP2s
  rw [← hsm1] at hP1d hP1l hP1s
  rw [← hsm2] at hP2d hP2l hP2s
  have hout1 := odd_sum_top (H0 := Hp l) (c0 := -((k.choose 2 : ℕ) : A))
    hL1d hWm (hWd.trans hLd) hG1d hR1 hQd h2l (by omega) hk hme hP1d hP1l hP1s
  have hout2 := odd_sum_top (H0 := Ht) (c0 := -((k.choose 2 : ℕ) : A))
    hL2d hWtm (hWtd.trans hdHt) hG2d hR2 hCd h2l (by omega) hk hme hP2d hP2l hP2s
  obtain ⟨ho1d, ho1l, ho1s⟩ := hout1
  obtain ⟨ho2d, ho2l, ho2s⟩ := hout2
  have hdec1 := Rpair_odd_fst' (Hp := Hp) (Ht := Ht) (k := k) (l := l) (α := α)
    hpar hk (by omega)
  have hdec2 := Rpair_odd_snd' (Hp := Hp) (Ht := Ht) (k := k) (l := l) (α := α)
    hpar hk (by omega)
  exact ⟨⟨by rw [hdec1]; exact ho1d, by rw [hdec1]; exact ho1l, by rw [hdec1]; exact ho1s⟩,
    ⟨by rw [hdec2]; exact ho2d, by rw [hdec2]; exact ho2l, by rw [hdec2]; exact ho2s⟩⟩

section oddBase

/-- Shared odd-base correction `G = w - (x+v)²` (so `H₈ = (H₄+S₁)² + G`). -/
noncomputable def obG (k : ℕ) (α : ℕ → A) : A[X] :=
  C (α (4 * (k - 2) + 1)) - (X + C (α (4 * (k - 2) + 2))) ^ 2

omit [Nontrivial A] in
/-- The octic core as a shifted square plus correction. -/
theorem obH8_eq_sq_add (Hp : ℕ → A[X]) (k : ℕ) (α : ℕ → A) :
    obH8 Hp k α = (Hp 2 + obS1 Hp k α) ^ 2 + obG k α := by
  unfold obH8 obG
  ring

omit [Nontrivial A] in
/-- Stepping the `T`-pair through the shared odd base (`l = 2`). -/
theorem Tpair_oddbase_step (hpar : ¬ k % 2 = 0) (hk : 2 ≤ k) :
    Tpair Hp Ht k 2 α
      = obOut Hp Ht k α (Tpair (Function.update Hp 3 (obH8 Hp k α))
          (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3 (fun j => α (4 + j))) := by
  obtain ⟨g, rfl⟩ : ∃ g, k = g + 1 := ⟨k - 1, by omega⟩
  show TF (g + 1) (g + 1) 2 Hp Ht α = _
  rw [TF_succ_odd_base (by omega) hpar (by omega)]
  exact congrArg (obOut Hp Ht (g + 1) α)
    (TF_fuel ((g + 1 - 1) / 2) g ((g + 1 - 1) / 2) (by omega) le_rfl 3 _ _ _)

/-- **Shared odd-base remainder, expanded, first component**: same five-group shape as
the odd main branch, at `D = 4`, `r = 2`, with `W = H₄ + S₁` and the `Q₃` low block. -/
theorem Rpair_oddbase_fst' (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) :
    (Rpair Hp Ht k 2 α).1
      = ((Hp 2 - (k - 1) • obS1 Hp k α) * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Hp 2 ^ k)
        + ((k - 1) / 2) • ((Hp 2 - (k - 1) • obS1 Hp k α)
            * (obG k α * (Hp 2 + obS1 Hp k α) ^ (k - 3)))
        + (Hp 2 - (k - 1) • obS1 Hp k α)
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) ((k - 1) / 2)
        + (Hp 2 - (k - 1) • obS1 Hp k α)
            * (Rpair (Function.update Hp 3 (obH8 Hp k α))
                (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
                (fun j => α (4 + j))).1
        + Q₃ (Hp 1) (α 1) (α 2) (α 3) := by
  have hupd : Function.update Hp 3 (obH8 Hp k α) 3 = obH8 Hp k α := by
    rw [update_last]
  obtain ⟨hsplit, -⟩ := Tpair_eq_pow_add_R
    (Hp := Function.update Hp 3 (obH8 Hp k α))
    (Ht := obH8 Hp k α + C (α (4 * (k - 2)))) (k := (k - 1) / 2) (l := 3)
    (α := fun j => α (4 + j))
  have hm1 : 1 ≤ (k - 1) / 2 := by omega
  have hpow := pow_add_eq ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) hm1
  have he1 : ((Hp 2 + obS1 Hp k α) ^ 2) ^ ((k - 1) / 2)
      = (Hp 2 + obS1 Hp k α) ^ (k - 1) := by
    rw [← pow_mul]
    congr 1
    omega
  have he2 : ((Hp 2 + obS1 Hp k α) ^ 2) ^ ((k - 1) / 2 - 1)
      = (Hp 2 + obS1 Hp k α) ^ (k - 3) := by
    rw [← pow_mul]
    congr 1
    omega
  show (Tpair Hp Ht k 2 α).1 - Hp 2 ^ k = _
  rw [Tpair_oddbase_step hpar (by omega)]
  show ((Hp 2 - (k - 1) • obS1 Hp k α) * (Tpair (Function.update Hp 3 (obH8 Hp k α))
      (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
      (fun j => α (4 + j))).1 + Q₃ (Hp 1) (α 1) (α 2) (α 3)) - Hp 2 ^ k = _
  rw [hsplit, hupd, obH8_eq_sq_add, hpow, he1, he2]
  ring

/-- **Shared odd-base remainder, expanded, second component** (the shared product:
`H̃₄ + S̃₁ = H₄ + S₁` as polynomials). -/
theorem Rpair_oddbase_snd' (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) :
    (Rpair Hp Ht k 2 α).2
      = ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * ((obG k α + C (α (4 * (k - 2)))) * (Hp 2 + obS1 Hp k α) ^ (k - 3)))
        + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
                ((k - 1) / 2)
        + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Rpair (Function.update Hp 3 (obH8 Hp k α))
                (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
                (fun j => α (4 + j))).2
        + C (α 0) := by
  obtain ⟨-, hsplit⟩ := Tpair_eq_pow_add_R
    (Hp := Function.update Hp 3 (obH8 Hp k α))
    (Ht := obH8 Hp k α + C (α (4 * (k - 2)))) (k := (k - 1) / 2) (l := 3)
    (α := fun j => α (4 + j))
  have hm1 : 1 ≤ (k - 1) / 2 := by omega
  have hpow := pow_add_eq ((Hp 2 + obS1 Hp k α) ^ 2)
    (obG k α + C (α (4 * (k - 2)))) hm1
  have he1 : ((Hp 2 + obS1 Hp k α) ^ 2) ^ ((k - 1) / 2)
      = (Hp 2 + obS1 Hp k α) ^ (k - 1) := by
    rw [← pow_mul]
    congr 1
    omega
  have he2 : ((Hp 2 + obS1 Hp k α) ^ 2) ^ ((k - 1) / 2 - 1)
      = (Hp 2 + obS1 Hp k α) ^ (k - 3) := by
    rw [← pow_mul]
    congr 1
    omega
  have htilde : obH8 Hp k α + C (α (4 * (k - 2)))
      = (Hp 2 + obS1 Hp k α) ^ 2 + (obG k α + C (α (4 * (k - 2)))) := by
    rw [obH8_eq_sq_add]
    ring
  show (Tpair Hp Ht k 2 α).2 - Ht ^ k = _
  rw [Tpair_oddbase_step hpar (by omega)]
  show ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * (Tpair
      (Function.update Hp 3 (obH8 Hp k α)) (obH8 Hp k α + C (α (4 * (k - 2))))
      ((k - 1) / 2) 3 (fun j => α (4 + j))).2 + C (α 0)) - Ht ^ k = _
  rw [hsplit, htilde, hpow, he1, he2]
  ring

end oddBase

/-- **`R-top-two` at the shared odd base** (`l = 2`): the scalar-difference hypothesis
makes the tilde factor `S₁ - ρ` monic, and both components share the product base
`W = H₄ + S₁`. -/
theorem Rpair_oddbase_top (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ 2)
    (hsd : ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hR1 : (Rpair (Function.update Hp 3 (obH8 Hp k α)) (obH8 Hp k α + C (α (4 * (k - 2))))
        ((k - 1) / 2) 3 (fun j => α (4 + j))).1.natDegree ≤ (k - 3) * 2 ^ 2)
    (hR2 : (Rpair (Function.update Hp 3 (obH8 Hp k α)) (obH8 Hp k α + C (α (4 * (k - 2))))
        ((k - 1) / 2) 3 (fun j => α (4 + j))).2.natDegree ≤ (k - 3) * 2 ^ 2) :
    ((Rpair Hp Ht k 2 α).1.natDegree ≤ (k - 1) * 2 ^ 2 ∧
      (Rpair Hp Ht k 2 α).1.coeff ((k - 1) * 2 ^ 2) = -((k.choose 2 : ℕ) : A) ∧
      (Rpair Hp Ht k 2 α).1.coeff ((k - 1) * 2 ^ 2 - 1)
        = -((k.choose 2 : ℕ) : A) * (2 • (obS1 Hp k α).coeff (2 - 1)
            + (k - 2) • (Hp 2).coeff (2 ^ 2 - 1))) ∧
    ((Rpair Hp Ht k 2 α).2.natDegree ≤ (k - 1) * 2 ^ 2 ∧
      (Rpair Hp Ht k 2 α).2.coeff ((k - 1) * 2 ^ 2) = -((k.choose 2 : ℕ) : A) ∧
      (Rpair Hp Ht k 2 α).2.coeff ((k - 1) * 2 ^ 2 - 1)
        = -((k.choose 2 : ℕ) : A) * (2 • (obS1 Hp k α - (Ht - Hp 2)).coeff (2 - 1)
            + (k - 2) • Ht.coeff (2 ^ 2 - 1))) := by
  obtain ⟨ρ, hρ⟩ := hsd
  obtain ⟨h2m, h2d⟩ := hHp 2 (by omega) le_rfl
  have h1g := hHp 1 (by omega) (by omega)
  obtain ⟨hbm, hbd⟩ := obS1_good (k := k) (α := α) h1g
  -- the tilde factor is monic of degree 2 under hsd
  have hU2 : (obS1 Hp k α - (Ht - Hp 2)).Monic ∧
      (obS1 Hp k α - (Ht - Hp 2)).natDegree = 2 := by
    rw [hρ]
    obtain ⟨hm', hd'⟩ := monic_sub_low (e := C ρ) hbm
      (Or.inr (by rw [natDegree_C, hbd]; omega))
    exact ⟨hm', hd'.trans hbd⟩
  obtain ⟨hU2m, hU2d⟩ := hU2
  -- W-factors: both sides share H₄ + S₁
  obtain ⟨hWm, hWd⟩ := monic_add_low (e := obS1 Hp k α) h2m
    (Or.inr (by rw [hbd, h2d]; omega))
  have hWd' : (Hp 2 + obS1 Hp k α).natDegree = 2 ^ 2 := hWd.trans h2d
  have hWt : Ht + (obS1 Hp k α - (Ht - Hp 2)) = Hp 2 + obS1 Hp k α := by ring
  -- L-degrees
  have hsm : ((k - 1) • obS1 Hp k α).natDegree ≤ 2 :=
    le_trans (natDegree_smul_le _ _) (le_of_eq hbd)
  obtain ⟨hL1m, hL1d⟩ := monic_sub_low (e := (k - 1) • obS1 Hp k α) h2m
    (Or.inr (by rw [h2d]; omega))
  have hL1d' : (Hp 2 - (k - 1) • obS1 Hp k α).natDegree = 2 ^ 2 := hL1d.trans h2d
  have hsm2 : ((k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree ≤ 2 :=
    le_trans (natDegree_smul_le _ _) (le_of_eq hU2d)
  obtain ⟨hL2m, hL2d⟩ := monic_sub_low (e := (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) hHt
    (Or.inr (by rw [hdHt]; omega))
  have hL2d' : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree = 2 ^ 2 :=
    hL2d.trans hdHt
  -- G-degrees
  have hXvd : ((X + C (α (4 * (k - 2) + 2)) : A[X]) ^ 2).natDegree = 2 := by
    rw [(monic_X_add_C _).natDegree_pow, natDegree_X_add_C]
  have hG1d : (obG k α).natDegree ≤ 2 := by
    unfold obG
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ (le_of_eq hXvd))
    rw [natDegree_C]
    omega
  have hG2d : (obG k α + C (α (4 * (k - 2)))).natDegree ≤ 2 := by
    refine le_trans (natDegree_add_le _ _) (max_le hG1d ?_)
    rw [natDegree_C]
    omega
  -- low blocks
  have hQd : (Q₃ (Hp 1) (α 1) (α 2) (α 3)).natDegree ≤ 2 ^ 2 - 1 :=
    le_of_eq (peel_monic Hp 2 (fun i' h1' hik => by
      have hi1' : i' = 1 := by omega
      subst hi1'
      exact h1g) (by omega) (fun j => α (1 + j))).2
  have hCd : (C (α 0) : A[X]).natDegree ≤ 2 ^ 2 - 1 := by
    rw [natDegree_C]
    omega
  have hme : 2 * ((k - 1) / 2) = k - 1 := by omega
  -- principal groups via the U-binomial engine
  have hsm1e : (k - 1) • obS1 Hp k α = ((k - 1 : ℕ) : A[X]) * obS1 Hp k α := by
    rw [nsmul_eq_mul]
  have hsm2e : (k - 1) • (obS1 Hp k α - (Ht - Hp 2))
      = ((k - 1 : ℕ) : A[X]) * (obS1 Hp k α - (Ht - Hp 2)) := by
    rw [nsmul_eq_mul]
  obtain ⟨hP1d, hP1l, hP1s⟩ := uPrincipal_top (D := 2 ^ 2) (r := 2) (n := k - 1)
    h2m h2d hbm hbd (by norm_num) (by omega) (by omega)
  obtain ⟨hP2d, hP2l, hP2s⟩ := uPrincipal_top (D := 2 ^ 2) (r := 2) (n := k - 1)
    hHt hdHt hU2m hU2d (by norm_num) (by omega) (by omega)
  rw [show k - 1 + 1 = k from by omega] at hP1d hP1l hP1s hP2d hP2l hP2s
  rw [show k - 1 - 1 = k - 2 from by omega] at hP1s hP2s
  rw [← hsm1e] at hP1d hP1l hP1s
  rw [← hsm2e] at hP2d hP2l hP2s
  rw [hWt] at hP2d hP2l hP2s
  have hout1 := odd_sum_top (H0 := Hp 2) (c0 := -((k.choose 2 : ℕ) : A))
    hL1d' hWm hWd' hG1d hR1 hQd (by norm_num) (by omega) hk hme hP1d hP1l hP1s
  have hout2 := odd_sum_top (H0 := Ht) (c0 := -((k.choose 2 : ℕ) : A))
    hL2d' hWm hWd' hG2d hR2 hCd (by norm_num) (by omega) hk hme hP2d hP2l hP2s
  obtain ⟨ho1d, ho1l, ho1s⟩ := hout1
  obtain ⟨ho2d, ho2l, ho2s⟩ := hout2
  have hdec1 := Rpair_oddbase_fst' (Hp := Hp) (Ht := Ht) (k := k) (α := α) hpar hk
  have hdec2 := Rpair_oddbase_snd' (Hp := Hp) (Ht := Ht) (k := k) (α := α) hpar hk
  exact ⟨⟨by rw [hdec1]; exact ho1d, by rw [hdec1]; exact ho1l, by rw [hdec1]; exact ho1s⟩,
    ⟨by rw [hdec2]; exact ho2d, by rw [hdec2]; exact ho2l, by rw [hdec2]; exact ho2s⟩⟩

end FastPoly
