import FastPoly.Section5.T
import FastPoly.Section5.Binomial

/-!
# The even branch of `lem:Rk2l`: remainder decomposition

Paper tag `R-even-exp`: for even `k = 2m` at level `l ≥ 2`,

  `R⁽¹⁾_{k,2^l} = m·(S⁽¹⁾₂ - (S⁽¹⁾₁)²)·H^{k-2} + binTail(H², E₁, m) + R⁽¹⁾_{m,2^{l+1}}`

and the analogue for the second component with the shifted power.  This is the exact
identity behind the degree claim `lem:Rk2l`(2) and the top-two invariant `R-top-two-even`;
the stage-table pivots read coefficients off the three displayed summands.
-/

namespace FastPoly

open Polynomial Finset

variable {A : Type*} [CommRing A] [Nontrivial A]
variable {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}

/-- Even-branch first-order correction, first component: `E₁ = S⁽¹⁾₂ - (S⁽¹⁾₁)²`. -/
noncomputable def eE1 (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  eS2 Hp k l α - tS1 Hp k l α ^ 2

/-- Even-branch first-order correction, second component: `E₂ = σ - (S⁽²⁾₁)²`. -/
noncomputable def eE2 (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) : A[X] :=
  C (α ((k - 2) * 2 ^ l)) - tS1t Hp k l α ^ 2

omit [Nontrivial A] in
/-- The even-step power as a square plus correction. -/
theorem evenH_eq_sq_add (Hp : ℕ → A[X]) (k l : ℕ) (α : ℕ → A) :
    evenH Hp k l α = Hp l ^ 2 + eE1 Hp k l α := by
  unfold evenH eE1
  ring

omit [Nontrivial A] in
/-- The even-step shifted power as a square plus correction. -/
theorem evenHt_eq_sq_add (Hp : ℕ → A[X]) (Ht : A[X]) (k l : ℕ) (α : ℕ → A) :
    evenHt Hp Ht k l α = Ht ^ 2 + eE2 Hp k l α := by
  unfold evenHt eE2
  ring

omit [Nontrivial A] in
/-- Stepping the `T`-pair through the even main branch. -/
theorem Tpair_even_step (hpar : k % 2 = 0) (hk : 2 ≤ k) (hl : ¬ l ≤ 1) :
    Tpair Hp Ht k l α
      = Tpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
          (k / 2) (l + 1) α := by
  obtain ⟨g, rfl⟩ : ∃ g, k = g + 1 := ⟨k - 1, by omega⟩
  show TF (g + 1) (g + 1) l Hp Ht α = _
  rw [TF_succ_even_main (by omega) hpar hl]
  exact TF_fuel ((g + 1) / 2) g ((g + 1) / 2) (by omega) le_rfl (l + 1) _ _ _

/-- **Even remainder decomposition, first component** (paper `R-even-exp`). -/
theorem Rpair_even_fst (hpar : k % 2 = 0) (hk : 2 ≤ k) (hl : ¬ l ≤ 1) :
    (Rpair Hp Ht k l α).1
      = (k / 2) • (eE1 Hp k l α * Hp l ^ (k - 2))
        + binTail (Hp l ^ 2) (eE1 Hp k l α) (k / 2)
        + (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
            (k / 2) (l + 1) α).1 := by
  have hupd : Function.update Hp (l + 1) (evenH Hp k l α) (l + 1) = evenH Hp k l α := by
    rw [update_last]
  have hm1 : 1 ≤ k / 2 := by omega
  have hpow := pow_add_eq (Hp l ^ 2) (eE1 Hp k l α) hm1
  have he1 : (Hp l ^ 2) ^ (k / 2) = Hp l ^ k := by
    rw [← pow_mul]
    congr 1
    omega
  have he2 : (Hp l ^ 2) ^ (k / 2 - 1) = Hp l ^ (k - 2) := by
    rw [← pow_mul]
    congr 1
    omega
  have hkey : evenH Hp k l α ^ (k / 2)
      = Hp l ^ k + (k / 2) • (eE1 Hp k l α * Hp l ^ (k - 2))
        + binTail (Hp l ^ 2) (eE1 Hp k l α) (k / 2) := by
    rw [evenH_eq_sq_add, hpow, he1, he2]
  show (Tpair Hp Ht k l α).1 - Hp l ^ k = _
  rw [Tpair_even_step hpar hk hl]
  show _ = _ + _ + ((Tpair (Function.update Hp (l + 1) (evenH Hp k l α))
      (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1
      - Function.update Hp (l + 1) (evenH Hp k l α) (l + 1) ^ (k / 2))
  rw [hupd]
  obtain ⟨hsplit, -⟩ := Tpair_eq_pow_add_R
    (Hp := Function.update Hp (l + 1) (evenH Hp k l α)) (Ht := evenHt Hp Ht k l α)
    (k := k / 2) (l := l + 1) (α := α)
  rw [hsplit, hupd, hkey]
  ring

/-- **Even remainder decomposition, second component** (paper `R-even-exp`). -/
theorem Rpair_even_snd (hpar : k % 2 = 0) (hk : 2 ≤ k) (hl : ¬ l ≤ 1) :
    (Rpair Hp Ht k l α).2
      = (k / 2) • (eE2 Hp k l α * Ht ^ (k - 2))
        + binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2)
        + (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
            (k / 2) (l + 1) α).2 := by
  have hm1 : 1 ≤ k / 2 := by omega
  have hpow := pow_add_eq (Ht ^ 2) (eE2 Hp k l α) hm1
  have he1 : (Ht ^ 2) ^ (k / 2) = Ht ^ k := by
    rw [← pow_mul]
    congr 1
    omega
  have he2 : (Ht ^ 2) ^ (k / 2 - 1) = Ht ^ (k - 2) := by
    rw [← pow_mul]
    congr 1
    omega
  have hkey : evenHt Hp Ht k l α ^ (k / 2)
      = Ht ^ k + (k / 2) • (eE2 Hp k l α * Ht ^ (k - 2))
        + binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2) := by
    rw [evenHt_eq_sq_add, hpow, he1, he2]
  show (Tpair Hp Ht k l α).2 - Ht ^ k = _
  rw [Tpair_even_step hpar hk hl]
  obtain ⟨-, hsplit⟩ := Tpair_eq_pow_add_R
    (Hp := Function.update Hp (l + 1) (evenH Hp k l α)) (Ht := evenHt Hp Ht k l α)
    (k := k / 2) (l := l + 1) (α := α)
  rw [hsplit, hkey]
  ring

section topTwo

/-- Top two coefficients of the even first-component correction `E₁ = S₂ - S₁²`:
degree `2^l`, leading `-1`, subleading `-2σ₁`. -/
theorem eE1_top (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l) :
    (eE1 Hp k l α).natDegree ≤ 2 ^ l ∧
    (eE1 Hp k l α).coeff (2 ^ l) = -1 ∧
    (eE1 Hp k l α).coeff (2 ^ l - 1)
      = -(2 • (tS1 Hp k l α).coeff (2 ^ (l - 1) - 1)) := by
  obtain ⟨hs1m, hs1d⟩ := tS1_good (k := k) (α := α) hHp hl
  obtain ⟨-, hqd⟩ := peel_monic Hp (l - 1)
    (fun i' h1' hik => hHp i' h1' (by omega)) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 1 + j))
  have heS2d : (eS2 Hp k l α).natDegree = 2 ^ (l - 1) - 1 := hqd
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have h2l : 2 * 2 ^ (l - 1) = 2 ^ l := by
    have hl1 : l - 1 + 1 = l := by omega
    calc 2 * 2 ^ (l - 1) = 2 ^ (l - 1 + 1) := by ring
    _ = 2 ^ l := by rw [hl1]
  rw [← h2l]
  unfold eE1
  exact low_sub_sq_top hs1m hs1d h1p (by rw [heS2d]; omega)

/-- Top two coefficients of the even second-component correction `E₂ = σ - S̃₁²`. -/
theorem eE2_top (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l) :
    (eE2 Hp k l α).natDegree ≤ 2 ^ l ∧
    (eE2 Hp k l α).coeff (2 ^ l) = -1 ∧
    (eE2 Hp k l α).coeff (2 ^ l - 1)
      = -(2 • (tS1t Hp k l α).coeff (2 ^ (l - 1) - 1)) := by
  obtain ⟨hs1m, hs1d⟩ := tS1t_good (k := k) (α := α) hHp hl
  have h1p : (1:ℕ) ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have h2l : 2 * 2 ^ (l - 1) = 2 ^ l := by
    have hl1 : l - 1 + 1 = l := by omega
    calc 2 * 2 ^ (l - 1) = 2 ^ (l - 1 + 1) := by ring
    _ = 2 ^ l := by rw [hl1]
  rw [← h2l]
  unfold eE2
  exact low_sub_sq_top hs1m hs1d h1p (by rw [natDegree_C]; omega)

end topTwo

/-- **Generic top-two extraction** for the even-branch shape
`m•(E·Bᵉ) + binTail(B², E, m) + R'` with `e + 2 = 2m`: the two boundary coefficients
at `(e+1)·D` and `(e+1)·D - 1` are `-m` and `-m·(s + e·[x^{D-1}]B)`. -/
theorem even_sum_top {B E R' : A[X]} {m e D : ℕ} {s : A}
    (hB : B.Monic) (hBd : B.natDegree = D) (hD2 : 2 ≤ D)
    (hEd : E.natDegree ≤ D) (hE1 : E.coeff D = -1) (hE2 : E.coeff (D - 1) = -s)
    (hm : 1 ≤ m) (he : e + 2 = 2 * m)
    (hR' : R'.natDegree ≤ e * D) :
    ((m • (E * B ^ e) + binTail (B ^ 2) E m + R').coeff ((e + 1) * D) = -(m : A)) ∧
    ((m • (E * B ^ e) + binTail (B ^ 2) E m + R').coeff ((e + 1) * D - 1)
      = -(m : A) * (s + (e : A) * B.coeff (D - 1))) := by
  have hqm : (B ^ e).Monic := hB.pow e
  have hqd : (B ^ e).natDegree = e * D := by rw [hB.natDegree_pow, hBd]
  have hd1 : (e + 1) * D = e * D + D := by ring
  have hcmD := coeff_mul_monic E (B ^ e) hqm D
  have hcmD1 := coeff_mul_monic E (B ^ e) hqm (D - 1)
  rw [hqd] at hcmD hcmD1
  have hsumD : ∑ j ∈ Finset.range (e * D), (B ^ e).coeff j * E.coeff (e * D + D - j)
      = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjr := Finset.mem_range.1 hj
    have hz : E.coeff (e * D + D - j) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, mul_zero]
  have hsumD1 : ∑ j ∈ Finset.range (e * D),
      (B ^ e).coeff j * E.coeff (e * D + (D - 1) - j)
      = (e : A) * B.coeff (D - 1) * (-1) := by
    rcases Nat.eq_zero_or_pos e with rfl | hepos
    · simp
    · have h1eD : 1 ≤ e * D := Nat.mul_pos hepos (by omega)
      rw [Finset.sum_eq_single_of_mem (e * D - 1) (Finset.mem_range.2 (by omega))]
      · have hidx : e * D + (D - 1) - (e * D - 1) = D := by omega
        have hsubl : (B ^ e).coeff (e * D - 1) = e • B.coeff (D - 1) :=
          FastPoly.Monic.pow_coeff_sub_one hB hBd (by omega) e hepos
        rw [hidx, hsubl, hE1, nsmul_eq_mul]
      · intro j hj hne
        have hjr := Finset.mem_range.1 hj
        have hz : E.coeff (e * D + (D - 1) - j) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hz, mul_zero]
  have hTd : (binTail (B ^ 2) E m).natDegree ≤ e * D := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · rw [binTail_eq_zero _ _ hm2, natDegree_zero]
      omega
    · obtain ⟨u, rfl⟩ : ∃ u, m = u + 2 := ⟨m - 2, by omega⟩
      have heu : e = 2 * u + 2 := by omega
      calc (binTail (B ^ 2) E (u + 2)).natDegree
          ≤ 2 * D + (u + 2 - 2) * (2 * D) :=
            natDegree_binTail_le (le_of_eq (by rw [hB.natDegree_pow, hBd])) hEd
              (by omega) (u + 2)
        _ = e * D := by
            rw [show u + 2 - 2 = u from by omega, heu]
            ring
  have hT1 : (binTail (B ^ 2) E m).coeff (e * D + D) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hT2 : (binTail (B ^ 2) E m).coeff (e * D + (D - 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hR1 : R'.coeff (e * D + D) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hR2 : R'.coeff (e * D + (D - 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  constructor
  · rw [coeff_add, coeff_add, coeff_smul, hd1, hcmD, hsumD, hE1, hT1, hR1]
    rw [nsmul_eq_mul]
    ring
  · have hd2 : (e + 1) * D - 1 = e * D + (D - 1) := by omega
    rw [coeff_add, coeff_add, coeff_smul, hd2, hcmD1, hsumD1, hE2, hT2, hR2]
    rw [nsmul_eq_mul]
    ring

/-- Total degree bound for the even-branch sum shape. -/
theorem even_sum_deg {B E R' : A[X]} {m e D : ℕ}
    (hB : B.Monic) (hBd : B.natDegree = D)
    (hEd : E.natDegree ≤ D) (hm : 1 ≤ m) (he : e + 2 = 2 * m) (hD2 : 2 ≤ D)
    (hR' : R'.natDegree ≤ e * D) :
    (m • (E * B ^ e) + binTail (B ^ 2) E m + R').natDegree ≤ (e + 1) * D := by
  have hqd : (B ^ e).natDegree = e * D := by rw [hB.natDegree_pow, hBd]
  have hd1 : (e + 1) * D = e * D + D := by ring
  have hA : (m • (E * B ^ e)).natDegree ≤ (e + 1) * D := by
    refine le_trans (natDegree_smul_le _ _) (le_trans natDegree_mul_le ?_)
    omega
  have hTd : (binTail (B ^ 2) E m).natDegree ≤ e * D := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · rw [binTail_eq_zero _ _ hm2, natDegree_zero]
      omega
    · obtain ⟨u, rfl⟩ : ∃ u, m = u + 2 := ⟨m - 2, by omega⟩
      have heu : e = 2 * u + 2 := by omega
      calc (binTail (B ^ 2) E (u + 2)).natDegree
          ≤ 2 * D + (u + 2 - 2) * (2 * D) :=
            natDegree_binTail_le (le_of_eq (by rw [hB.natDegree_pow, hBd])) hEd
              (by omega) (u + 2)
        _ = e * D := by
            rw [show u + 2 - 2 = u from by omega, heu]
            ring
  refine le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _)
    (max_le hA ?_)) ?_)
  · omega
  · omega

/-- **`R-top-two-even`**: degree bound and the two boundary coefficients of the even-branch
remainder pair, given the inner remainder's degree bound. -/
theorem Rpair_even_top (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l) (hpar : k % 2 = 0) (hk : 2 ≤ k)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l)
    (hR1 : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
        (k / 2) (l + 1) α).1.natDegree ≤ (k - 2) * 2 ^ l)
    (hR2 : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
        (k / 2) (l + 1) α).2.natDegree ≤ (k - 2) * 2 ^ l) :
    ((Rpair Hp Ht k l α).1.natDegree ≤ (k - 1) * 2 ^ l ∧
      (Rpair Hp Ht k l α).1.coeff ((k - 1) * 2 ^ l) = -((k / 2 : ℕ) : A) ∧
      (Rpair Hp Ht k l α).1.coeff ((k - 1) * 2 ^ l - 1)
        = -((k / 2 : ℕ) : A) * (2 • (tS1 Hp k l α).coeff (2 ^ (l - 1) - 1)
            + ((k - 2 : ℕ) : A) * (Hp l).coeff (2 ^ l - 1))) ∧
    ((Rpair Hp Ht k l α).2.natDegree ≤ (k - 1) * 2 ^ l ∧
      (Rpair Hp Ht k l α).2.coeff ((k - 1) * 2 ^ l) = -((k / 2 : ℕ) : A) ∧
      (Rpair Hp Ht k l α).2.coeff ((k - 1) * 2 ^ l - 1)
        = -((k / 2 : ℕ) : A) * (2 • (tS1t Hp k l α).coeff (2 ^ (l - 1) - 1)
            + ((k - 2 : ℕ) : A) * Ht.coeff (2 ^ l - 1))) := by
  have hD2 : (2:ℕ) ≤ 2 ^ l := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
  have hi1 : (k - 2 + 1) * 2 ^ l = (k - 1) * 2 ^ l := by
    have hk21 : k - 2 + 1 = k - 1 := by omega
    rw [hk21]
  obtain ⟨hLm, hLd⟩ := hHp l (by omega) le_rfl
  obtain ⟨hE1d, hE1c, hE1c2⟩ := eE1_top (k := k) (α := α) hHp hl
  obtain ⟨hE2d, hE2c, hE2c2⟩ := eE2_top (k := k) (α := α) hHp hl
  have hdec1 := Rpair_even_fst (Hp := Hp) (Ht := Ht) (k := k) (l := l) (α := α)
    hpar hk (by omega)
  have hdec2 := Rpair_even_snd (Hp := Hp) (Ht := Ht) (k := k) (l := l) (α := α)
    hpar hk (by omega)
  obtain ⟨ho11, ho12⟩ := even_sum_top (B := Hp l) (E := eE1 Hp k l α)
    (R' := (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
      (k / 2) (l + 1) α).1) (m := k / 2) (e := k - 2) (D := 2 ^ l)
    (s := 2 • (tS1 Hp k l α).coeff (2 ^ (l - 1) - 1))
    hLm hLd hD2 hE1d hE1c hE1c2 (by omega) (by omega) hR1
  obtain ⟨ho21, ho22⟩ := even_sum_top (B := Ht) (E := eE2 Hp k l α)
    (R' := (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
      (k / 2) (l + 1) α).2) (m := k / 2) (e := k - 2) (D := 2 ^ l)
    (s := 2 • (tS1t Hp k l α).coeff (2 ^ (l - 1) - 1))
    hHt hdHt hD2 hE2d hE2c hE2c2 (by omega) (by omega) hR2
  have hg1 := even_sum_deg (B := Hp l) (E := eE1 Hp k l α)
    (R' := (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
      (k / 2) (l + 1) α).1) (m := k / 2) (e := k - 2) (D := 2 ^ l)
    hLm hLd hE1d (by omega) (by omega) hD2 hR1
  have hg2 := even_sum_deg (B := Ht) (E := eE2 Hp k l α)
    (R' := (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
      (k / 2) (l + 1) α).2) (m := k / 2) (e := k - 2) (D := 2 ^ l)
    hHt hdHt hE2d (by omega) (by omega) hD2 hR2
  rw [hi1] at ho11 ho12 ho21 ho22 hg1 hg2
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [hdec1]
    exact hg1
  · rw [hdec1]
    exact ho11
  · rw [hdec1]
    exact ho12
  · rw [hdec2]
    exact hg2
  · rw [hdec2]
    exact ho21
  · rw [hdec2]
    exact ho22

end FastPoly
