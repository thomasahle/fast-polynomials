import FastPoly.Section5.Rk2lTriMaster

/-!
# `lem:causal-perturbed-T`

The even `T`-call over a perturbed top power `Ĥ = H + Q` and its scalar shift
`H̃ = Ĥ + δ` yields a compatible pair, with `Q` and `δ` causally recoverable.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {Hp : ℕ → A[X]} {l M : ℕ} {α : ℕ → A}

/-- **`lem:Rk2l` + `lem:triangular-implies-compatible`**: the `T`-pair is a
compatible pair of degree `k·2^l` on the window `range ((k-1)·2^l)`. -/
theorem Tpair_compatiblePair (hk : 1 ≤ k) (hl : 2 ≤ l)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hsd : l = 2 → ¬ k % 2 = 0 → 3 ≤ k → ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ k → IsUnit (((n : ℕ) : ℤ) : R)) :
    CompatiblePair K (Tpair Hp Ht k l α).1 (Tpair Hp Ht k l α).2 (k * 2 ^ l)
      (Finset.range ((k - 1) * 2 ^ l)) := by
  have htri := Rk2l_triangular k hk l Hp Ht α K hl hHp hHt hdHt hKt hsd hadm
  obtain ⟨⟨hm1, hd1⟩, hm2, hd2⟩ := Tpair_good (Hp := Hp) (Ht := Ht) (α := α)
    hk (by omega) (fun _ _ => by omega)
    (fun i h1 h2 => ⟨(hHp i h1 h2).1, (hHp i h1 h2).2.1⟩) hHt hdHt
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  refine htri.toCompatiblePair ?_ ?_ hm1 hd1 hm2 hd2 ?_
  · intro j
    have hdiff : (Tpair Hp Ht k l α).1.coeff j - (Rpair Hp Ht k l α).1.coeff j
        = (Hp l ^ k).coeff j := by
      show _ - ((Tpair Hp Ht k l α).1 - Hp l ^ k).coeff j = _
      rw [coeff_sub]
      ring
    rw [hdiff]
    exact coeff_mem_pow hMK k j
  · intro j
    have hdiff : (Tpair Hp Ht k l α).2.coeff j - (Rpair Hp Ht k l α).2.coeff j
        = (Ht ^ k).coeff j := by
      show _ - ((Tpair Hp Ht k l α).2 - Ht ^ k).coeff j = _
      rw [coeff_sub]
      ring
    rw [hdiff]
    exact coeff_mem_pow hKt k j
  · have h := Nat.mul_le_mul_right (2 ^ l) (show k - 1 ≤ k from by omega)
    omega

/-- The `binTail` of a perturbed power `(H + Q)^M` vanishes strictly above
`(M-1)·2^l - 2` when `deg H = 2^l` and `deg Q = 2^(l-1) - 1`. -/
private theorem perturbed_binTail_zero₁ {P Q : A[X]} (hl : 2 ≤ l) (hM : 2 ≤ M)
    (hPd : P.natDegree = 2 ^ l) (hQd : Q.natDegree = 2 ^ (l - 1) - 1) :
    ∀ m, (M - 1) * 2 ^ l - 2 < m → (binTail P Q M).coeff m = 0 := by
  intro m hm
  refine coeff_eq_zero_of_natDegree_lt ?_
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hbt := natDegree_binTail_le (le_of_eq hPd) (le_of_eq hQd) (by omega) M
  have hsum : 2 * (2 ^ (l - 1) - 1) + (M - 2) * 2 ^ l ≤ (M - 1) * 2 ^ l - 2 := by
    have hb : (M - 2) * 2 ^ l + 2 ^ l = (M - 1) * 2 ^ l := by
      have h1 : M - 2 + 1 = M - 1 := by omega
      calc (M - 2) * 2 ^ l + 2 ^ l = (M - 2 + 1) * 2 ^ l := by ring
        _ = (M - 1) * 2 ^ l := by rw [h1]
    omega
  omega

/-- The `binTail` of a scalar shift `(Ĥ + C δ)^M` vanishes strictly above
`(M-2)·2^l` when `deg Ĥ = 2^l`. -/
private theorem perturbed_binTail_zero₂ {P : A[X]} (δ : A)
    (hPd : P.natDegree = 2 ^ l) :
    ∀ m, (M - 2) * 2 ^ l < m → (binTail P (C δ) M).coeff m = 0 := by
  intro m hm
  refine coeff_eq_zero_of_natDegree_lt ?_
  have hbt := natDegree_binTail_le (le_of_eq hPd)
    (le_of_eq (natDegree_C δ)) (by omega) M
  omega

/-- Shared prelude of the three perturbed-call theorems (`perturbed_Q_vis`,
`perturbed_delta_vis`, `causal_perturbed_T`): band arithmetic, goodness of the
perturbed top power `Ĥ = H + Q` and of its scalar shift `H̃ = Ĥ + C δ`, goodness
of the updated tower, the power/remainder split of the perturbed `T`-pair, and
the remainder degree/leading-coefficient facts.  Destructure with
`obtain ⟨hp1, hp0, hple, hp2le, hd2, hNd, hQdeg, hHhm, hHhd, htower2, hHtim,
hHtid, hupdl, hsp₁, hsp₂, hRd₁, hRd₂, hRl₁, hRl₂, hb21⟩`. -/
private theorem perturbed_call_facts {Q : A[X]} {δ : A} (hl : 2 ≤ l) (hM : 2 ≤ M)
    (hpar : M % 2 = 0)
    (hHpg : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hQm : Q.Monic) (hQd : Q.natDegree = 2 ^ (l - 1) - 1) :
    1 ≤ 2 ^ (l - 1) ∧ 1 ≤ 2 ^ l ∧
    2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l ∧ 2 ≤ 2 ^ (l - 1) ∧
    2 ^ l ≤ (M - 1) * 2 ^ l ∧ M * 2 ^ l = (M - 1) * 2 ^ l + 2 ^ l ∧
    Q.degree < (Hp l).degree ∧
    (Hp l + Q).Monic ∧ (Hp l + Q).natDegree = 2 ^ l ∧
    (∀ i, 1 ≤ i → i ≤ l →
      ((Function.update Hp l (Hp l + Q)) i).Monic ∧
      ((Function.update Hp l (Hp l + Q)) i).natDegree = 2 ^ i) ∧
    (Hp l + Q + C δ).Monic ∧ (Hp l + Q + C δ).natDegree = 2 ^ l ∧
    Function.update Hp l (Hp l + Q) l = Hp l + Q ∧
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
      = (Hp l + Q) ^ M
        + (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1 ∧
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2
      = (Hp l + Q + C δ) ^ M
        + (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2 ∧
    (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1.natDegree
      ≤ (M - 1) * 2 ^ l ∧
    (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2.natDegree
      ≤ (M - 1) * 2 ^ l ∧
    (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1.coeff
      ((M - 1) * 2 ^ l) = -((gammaZ M : ℕ) : A) ∧
    (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2.coeff
      ((M - 1) * 2 ^ l) = -((gammaZ M : ℕ) : A) ∧
    (M - 2) * 2 ^ l + 2 ^ l = (M - 1) * 2 ^ l := by
  obtain ⟨hMm, hMd⟩ := hHpg l (by omega) le_rfl
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hp2le : 2 ≤ 2 ^ (l - 1) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 from by omega)
      (show 1 ≤ l - 1 from by omega)
    have h2e : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  have hd2 : 2 ^ l ≤ (M - 1) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ M - 1 from by omega)
    omega
  have hNd : M * 2 ^ l = (M - 1) * 2 ^ l + 2 ^ l := by
    have : M = (M - 1) + 1 := by omega
    calc M * 2 ^ l = ((M - 1) + 1) * 2 ^ l := by rw [← this]
    _ = (M - 1) * 2 ^ l + 2 ^ l := by ring
  -- the perturbed top power
  have hQdeg : Q.degree < (Hp l).degree := by
    rw [degree_eq_natDegree hQm.ne_zero, degree_eq_natDegree hMm.ne_zero, hMd, hQd]
    exact_mod_cast (by omega : 2 ^ (l - 1) - 1 < 2 ^ l)
  have hHhm : (Hp l + Q).Monic := hMm.add_of_left hQdeg
  have hHhd : (Hp l + Q).natDegree = 2 ^ l := by
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hQdeg), hMd]
  -- tower facts for the perturbed call
  have htower2 : ∀ i, 1 ≤ i → i ≤ l →
      ((Function.update Hp l (Hp l + Q)) i).Monic ∧
      ((Function.update Hp l (Hp l + Q)) i).natDegree = 2 ^ i := by
    intro i h1 hi
    rcases Nat.lt_or_ge i l with hlt | hge
    · have hne : i ≠ l := by omega
      have hupd : Function.update Hp l (Hp l + Q) i = Hp i := by
        rw [update_ne _ hne]
      rw [hupd]
      exact hHpg i h1 (by omega)
    · have hie : i = l := by omega
      subst hie
      have hupd : Function.update Hp i (Hp i + Q) i = Hp i + Q := by
        rw [update_last]
      rw [hupd]
      exact ⟨hHhm, hHhd⟩
  have hHtim : (Hp l + Q + C δ).Monic := by
    refine hHhm.add_of_left (lt_of_le_of_lt degree_C_le ?_)
    rw [degree_eq_natDegree hHhm.ne_zero, hHhd]
    exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  have hHtid : (Hp l + Q + C δ).natDegree = 2 ^ l := by
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt
      (lt_of_le_of_lt degree_C_le (by
        rw [degree_eq_natDegree hHhm.ne_zero, hHhd]
        exact_mod_cast Nat.pos_of_ne_zero (by positivity)))), hHhd]
  -- the power/remainder split for the perturbed call
  obtain ⟨hsp₁, hsp₂⟩ := Tpair_eq_pow_add_R
    (Hp := Function.update Hp l (Hp l + Q)) (Ht := Hp l + Q + C δ)
    (k := M) (l := l) (α := α)
  have hupdl : Function.update Hp l (Hp l + Q) l = Hp l + Q := by
    rw [update_last]
  rw [hupdl] at hsp₁
  -- remainder degree bound
  obtain ⟨hRd₁, hRd₂⟩ := Rk2l_deg M (by omega) l
    (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) α (by omega) htower2
    hHtim hHtid (fun _ hodd => absurd hpar (by omega))
  -- remainder lead is a known constant
  obtain ⟨hRl₁, hRl₂⟩ := Rk2l_lead M (by omega) l
    (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) α (by omega) htower2
    hHtim hHtid (fun _ hodd => absurd hpar (by omega))
  have hb21 : (M - 2) * 2 ^ l + 2 ^ l = (M - 1) * 2 ^ l := by
    have h1 : M - 2 + 1 = M - 1 := by omega
    calc (M - 2) * 2 ^ l + 2 ^ l = (M - 2 + 1) * 2 ^ l := by ring
      _ = (M - 1) * 2 ^ l := by rw [h1]
  exact ⟨hp1, hp0, hple, hp2le, hd2, hNd, hQdeg, hHhm, hHhd, htower2, hHtim,
    hHtid, hupdl, hsp₁, hsp₂, hRd₁, hRd₂, hRl₁, hRl₂, hb21⟩

/-- Recovery of the perturbation coefficients (`perturbed-power-pivot`): each `Q`
coefficient is visible at its causal cutoff. -/
theorem perturbed_Q_vis {Q : A[X]} {δ : A} (hl : 2 ≤ l) (hM : 2 ≤ M)
    (hpar : M % 2 = 0)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hQm : Q.Monic) (hQd : Q.natDegree = 2 ^ (l - 1) - 1)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ M → IsUnit (((n : ℕ) : ℤ) : R)) :
    ∀ q, Q.coeff q ∈ Vis R K
      (combined (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
        (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
      (Finset.range (M * 2 ^ l - 2 ^ (l - 1)))
      ((M - 1) * 2 ^ l + q + 1) := by
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  obtain ⟨hp1, hp0, hple, hp2le, hd2, hNd, hQdeg, hHhm, hHhd, htower2, hHtim,
      hHtid, hupdl, hsp₁, hsp₂, hRd₁, hRd₂, hRl₁, hRl₂, hb21⟩ :=
    perturbed_call_facts (α := α) (δ := δ) hl hM hpar
      (fun i h1 h2 => ⟨(hHp i h1 h2).1, (hHp i h1 h2).2.1⟩) hQm hQd
  -- the binomial split of the perturbed power
  have hpow := pow_add_eq (Hp l) Q (m := M) (by omega)
  have hbinz := perturbed_binTail_zero₁ hl hM hMd hQd
  -- the tilde-power split
  have htpow := pow_add_eq (Hp l + Q) (C δ) (m := M) (by omega)
  have htbinz := perturbed_binTail_zero₂ (M := M) δ hHhd
  -- the M-unit
  obtain ⟨u, hu⟩ := hadm M (by omega) le_rfl
  have hMA : algebraMap R A (↑u : R) = ((M : ℕ) : A) := by
    rw [hu, map_intCast, Int.cast_natCast]
  -- main descending induction
  have main : ∀ fuel q, 2 ^ (l - 1) - 1 - q ≤ fuel → Q.coeff q ∈ Vis R K
      (combined (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
        (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
      (Finset.range (M * 2 ^ l - 2 ^ (l - 1)))
      ((M - 1) * 2 ^ l + q + 1) := by
    intro fuel
    induction fuel with
    | zero =>
      intro q hf
      have hq : 2 ^ (l - 1) - 1 ≤ q := by omega
      rcases eq_or_lt_of_le hq with heq | hlt
      · rw [← heq, ← hQd, hQm.coeff_natDegree]
        exact known_mem_Vis (Subalgebra.one_mem _)
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        exact known_mem_Vis (Subalgebra.zero_mem _)
    | succ fuel ih =>
      intro q hf
      rcases Nat.lt_or_ge q (2 ^ (l - 1) - 1) with hq | hq
      swap
      · exact ih q (by omega)
      -- the pivot row for `q_q`
      set Ψ := combined
        (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
        (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2 with hΨ
      set V := Vis R K Ψ (Finset.range (M * 2 ^ l - 2 ^ (l - 1)))
        ((M - 1) * 2 ^ l + q + 1) with hV
      -- higher Q-coefficients are already visible
      have hhi : ∀ u', q < u' → Q.coeff u' ∈ V := by
        intro u' hu'
        refine Vis_antitone_cutoff (by omega) (ih u' (by omega))
      -- the rest sums of the two boundary reads are visible
      have hrest : ∀ m, (M - 1) * 2 ^ l + q ≤ m →
          (∑ x ∈ (Finset.antidiagonal m).filter
            (fun x : ℕ × ℕ => x.2 ≠ (M - 1) * 2 ^ l),
            Q.coeff x.1 * (Hp l ^ (M - 1)).coeff x.2) ∈ V := by
        intro m hm
        refine Subalgebra.sum_mem _ fun x hx => ?_
        obtain ⟨hxa, hxne⟩ := Finset.mem_filter.1 hx
        have hxa' : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hxa
        rcases Nat.lt_or_ge ((M - 1) * 2 ^ l) x.2 with hg2 | hl2
        · rw [show (Hp l ^ (M - 1)).coeff x.2 = 0 from
            coeff_eq_zero_of_natDegree_lt (by
              rw [hMm.natDegree_pow, hMd]
              exact hg2), mul_zero]
          exact Subalgebra.zero_mem _
        · have hx1 : q < x.1 := by omega
          exact Subalgebra.mul_mem _ (hhi x.1 hx1)
            (known_mem_Vis (coeff_mem_pow hMK (M - 1) x.2))
      -- boundary reads of the Q·H^{M-1} block
      have hbord : ∀ m', q ≤ m' → (Q * Hp l ^ (M - 1)).coeff ((M - 1) * 2 ^ l + m')
          = Q.coeff m'
            + ∑ x ∈ (Finset.antidiagonal ((M - 1) * 2 ^ l + m')).filter
                (fun x : ℕ × ℕ => x.2 ≠ (M - 1) * 2 ^ l),
              Q.coeff x.1 * (Hp l ^ (M - 1)).coeff x.2 := by
        intro m' hm'
        have h := mul_coeff_boundary (P := Q) (L := Hp l ^ (M - 1))
          (D := (M - 1) * 2 ^ l) (hMm.pow _)
          (by rw [hMm.natDegree_pow, hMd]) m'
        exact h
      -- membership of the pivot row coefficient
      have hrowG : (M - 1) * 2 ^ l + q + 1
          ∈ Finset.range (M * 2 ^ l - 2 ^ (l - 1)) := by
        refine Finset.mem_range.2 ?_
        omega
      have hΨmem : Ψ.coeff ((M - 1) * 2 ^ l + q + 1) ∈ V :=
        coeff_mem_Vis hrowG le_rfl
      -- second-component read is fully visible
      have hS₂V : (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
          M l α).2.coeff ((M - 1) * 2 ^ l + q + 1) ∈ V := by
        rw [hsp₂, coeff_add]
        refine Subalgebra.add_mem _ ?_ ?_
        · -- the tilde power
          rw [htpow, coeff_add, coeff_add, coeff_smul,
            show (C δ * (Hp l + Q) ^ (M - 1)).coeff ((M - 1) * 2 ^ l + q + 1)
              = 0 from by
              rw [coeff_C_mul,
                show ((Hp l + Q) ^ (M - 1)).coeff ((M - 1) * 2 ^ l + q + 1) = 0
                  from coeff_eq_zero_of_natDegree_lt (by
                    rw [hHhm.natDegree_pow, hHhd]
                    omega), mul_zero],
            smul_zero, add_zero, htbinz _ (by omega), add_zero, hpow,
            coeff_add, coeff_add, coeff_smul, hbinz _ (by omega), add_zero,
            show (M - 1) * 2 ^ l + q + 1 = (M - 1) * 2 ^ l + (q + 1) from by omega,
            hbord (q + 1) (by omega)]
          refine Subalgebra.add_mem _
            (known_mem_Vis (coeff_mem_pow hMK M _)) ?_
          refine nsmul_mem (Subalgebra.add_mem _ (hhi (q + 1) (by omega)) ?_) M
          exact hrest _ (by omega)
        · -- the second remainder vanishes here
          rw [show (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
              M l α).2.coeff ((M - 1) * 2 ^ l + q + 1) = 0 from
            coeff_eq_zero_of_natDegree_lt (by omega)]
          exact Subalgebra.zero_mem _
      -- first-remainder read is visible (a known constant or zero)
      have hR₁V : (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
          M l α).1.coeff ((M - 1) * 2 ^ l + q) ∈ V := by
        rcases Nat.eq_zero_or_pos q with hq0 | hqpos
        · subst hq0
          rw [Nat.add_zero, hRl₁]
          exact known_mem_Vis (Subalgebra.neg_mem _ (Subalgebra.natCast_mem _ _))
        · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
          exact Subalgebra.zero_mem _
      -- solve the pivot
      have hMQV : ((M : ℕ) : A) * Q.coeff q ∈ V := by
        have hkey : ((M : ℕ) : A) * Q.coeff q
            = Ψ.coeff ((M - 1) * 2 ^ l + q + 1)
              - (Hp l ^ M).coeff ((M - 1) * 2 ^ l + q)
              - ((M : ℕ) : A) * (∑ x ∈ (Finset.antidiagonal
                  ((M - 1) * 2 ^ l + q)).filter
                  (fun x : ℕ × ℕ => x.2 ≠ (M - 1) * 2 ^ l),
                Q.coeff x.1 * (Hp l ^ (M - 1)).coeff x.2)
              - (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
                  M l α).1.coeff ((M - 1) * 2 ^ l + q)
              - (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
                  M l α).2.coeff ((M - 1) * 2 ^ l + q + 1) := by
          have hcO : Ψ.coeff ((M - 1) * 2 ^ l + q + 1)
              = (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
                  M l α).1.coeff ((M - 1) * 2 ^ l + q)
                + (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
                    M l α).2.coeff ((M - 1) * 2 ^ l + q + 1) := by
            rw [hΨ, show (M - 1) * 2 ^ l + q + 1 = ((M - 1) * 2 ^ l + q) + 1
              from rfl, coeff_combined]
          rw [hcO, hsp₁, coeff_add, hpow, coeff_add, coeff_add, coeff_smul,
            hbinz _ (by omega), add_zero, hbord q le_rfl]
          simp only [nsmul_eq_mul]
          ring
        rw [hkey]
        refine Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
          (Subalgebra.sub_mem _ hΨmem
            (known_mem_Vis (coeff_mem_pow hMK M _)))
          (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
            (hrest _ (by omega)))) hR₁V) hS₂V
      have hkey2 : Q.coeff q
          = algebraMap R A (↑u⁻¹ : R) * (((M : ℕ) : A) * Q.coeff q) := by
        rw [← hMA, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      rw [hkey2]
      exact Subalgebra.mul_mem _ (algebraMap_mem_Vis _) hMQV
  intro q
  exact main (2 ^ (l - 1) - 1 - q) q le_rfl
/-- Recovery of the scalar shift: `δ` is visible at cutoff `d = (M-1)·2^l`. -/
theorem perturbed_delta_vis {Q : A[X]} {δ : A} (hl : 2 ≤ l) (hM : 2 ≤ M)
    (hpar : M % 2 = 0)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hQm : Q.Monic) (hQd : Q.natDegree = 2 ^ (l - 1) - 1)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ M → IsUnit (((n : ℕ) : ℤ) : R)) :
    δ ∈ Vis R K
      (combined (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
        (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
      (Finset.range (M * 2 ^ l - 2 ^ (l - 1)))
      ((M - 1) * 2 ^ l) := by
  have hQvis := perturbed_Q_vis (K := K) (α := α) (δ := δ) hl hM hpar hHp hQm hQd hadm
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  obtain ⟨hp1, hp0, hple, hp2le, hd2, hNd, hQdeg, hHhm, hHhd, htower2, hHtim,
      hHtid, hupdl, hsp₁, hsp₂, hRd₁, hRd₂, hRl₁, hRl₂, hb21⟩ :=
    perturbed_call_facts (α := α) (δ := δ) hl hM hpar
      (fun i h1 h2 => ⟨(hHp i h1 h2).1, (hHp i h1 h2).2.1⟩) hQm hQd
  have hpow := pow_add_eq (Hp l) Q (m := M) (by omega)
  have htpow := pow_add_eq (Hp l + Q) (C δ) (m := M) (by omega)
  have htbinz := perturbed_binTail_zero₂ (M := M) δ hHhd
  obtain ⟨u, hu⟩ := hadm M (by omega) le_rfl
  have hMA : algebraMap R A (↑u : R) = ((M : ℕ) : A) := by
    rw [hu, map_intCast, Int.cast_natCast]
  set Ψ := combined
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2 with hΨ
  set V := Vis R K Ψ (Finset.range (M * 2 ^ l - 2 ^ (l - 1)))
    ((M - 1) * 2 ^ l) with hV
  have hQV : ∀ u', Q.coeff u' ∈ V :=
    fun u' => Vis_antitone_cutoff (by omega) (hQvis u')
  have hHhV : ∀ a, (Hp l + Q).coeff a ∈ V := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ (known_mem_Vis (hMK a)) (hQV a)
  have hHhMV : ∀ m, ((Hp l + Q) ^ M).coeff m ∈ V :=
    coeff_mem_pow hHhV M
  -- boundary coefficients of the remainders are known
  have hK2' : ((Function.update Hp l (Hp l + Q)) l).coeff (2 ^ l - 1) ∈ K := by
    rw [hupdl, coeff_add,
      show Q.coeff (2 ^ l - 1) = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      add_zero]
    exact hMK _
  have hK1' : ((Function.update Hp l (Hp l + Q)) (l - 1)).coeff (2 ^ (l - 1) - 1)
      ∈ K := by
    have hne : l - 1 ≠ l := by omega
    have hupd : Function.update Hp l (Hp l + Q) (l - 1) = Hp (l - 1) := by
      rw [update_ne _ hne]
    rw [hupd]
    exact (hHp (l - 1) (by omega) (by omega)).2.2 _
  have hKt2' : (Hp l + Q + C δ).coeff (2 ^ l - 1) ∈ K := by
    rw [coeff_add, coeff_add, coeff_C, if_neg (by omega),
      show Q.coeff (2 ^ l - 1) = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (hMK _)
      (Subalgebra.zero_mem _)) (Subalgebra.zero_mem _)
  obtain ⟨-, hRs₁, -, -⟩ := Rk2l_top_two (K := K) (α := α) hM (by omega)
    htower2 hHtim hHtid (fun _ hodd => absurd hpar (by omega)) hK1' hK2' hKt2'
  -- the pivot row for δ
  have hrowG : (M - 1) * 2 ^ l ∈ Finset.range (M * 2 ^ l - 2 ^ (l - 1)) := by
    refine Finset.mem_range.2 ?_
    omega
  have hΨmem : Ψ.coeff ((M - 1) * 2 ^ l) ∈ V := coeff_mem_Vis hrowG le_rfl
  have hlead : ((Hp l + Q) ^ (M - 1)).coeff ((M - 1) * 2 ^ l) = 1 := by
    have h := (hHhm.pow (M - 1)).coeff_natDegree
    rw [hHhm.natDegree_pow, hHhd] at h
    exact h
  have hMδV : ((M : ℕ) : A) * δ ∈ V := by
    have hkey : ((M : ℕ) : A) * δ
        = Ψ.coeff ((M - 1) * 2 ^ l)
          - (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
              M l α).1.coeff ((M - 1) * 2 ^ l - 1)
          - ((Hp l + Q) ^ M).coeff ((M - 1) * 2 ^ l)
          - (binTail (Hp l + Q) (C δ) M).coeff ((M - 1) * 2 ^ l)
          - (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
              M l α).2.coeff ((M - 1) * 2 ^ l) := by
      have hcO : Ψ.coeff ((M - 1) * 2 ^ l)
          = (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
              M l α).1.coeff ((M - 1) * 2 ^ l - 1)
            + (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
                M l α).2.coeff ((M - 1) * 2 ^ l) := by
        rw [hΨ, show (M - 1) * 2 ^ l = ((M - 1) * 2 ^ l - 1) + 1 from by omega,
          coeff_combined, show ((M - 1) * 2 ^ l - 1) + 1 = (M - 1) * 2 ^ l from
            by omega]
      rw [hcO, hsp₂, coeff_add, htpow, coeff_add, coeff_add, coeff_smul,
        coeff_C_mul, hlead, mul_one]
      simp only [nsmul_eq_mul]
      ring
    rw [hkey]
    refine Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
      (Subalgebra.sub_mem _ hΨmem ?_) (hHhMV _)) ?_) ?_
    · rw [hsp₁, coeff_add]
      exact Subalgebra.add_mem _ (hHhMV _) (known_mem_Vis hRs₁)
    · rw [htbinz _ (by omega)]
      exact Subalgebra.zero_mem _
    · rw [hRl₂]
      exact known_mem_Vis (Subalgebra.neg_mem _ (Subalgebra.natCast_mem _ _))
  have hkey2 : δ = algebraMap R A (↑u⁻¹ : R) * (((M : ℕ) : A) * δ) := by
    rw [← hMA, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [hkey2]
  exact Subalgebra.mul_mem _ (algebraMap_mem_Vis _) hMδV


set_option maxHeartbeats 800000 in
/-- **`lem:causal-perturbed-T`**: the even `T`-call over the perturbed top power is a
compatible pair on `range (N - r)`. -/
theorem causal_perturbed_T {Q : A[X]} {δ : A} (hl : 2 ≤ l) (hM : 2 ≤ M)
    (hpar : M % 2 = 0)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hQm : Q.Monic) (hQd : Q.natDegree = 2 ^ (l - 1) - 1)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ M → IsUnit (((n : ℕ) : ℤ) : R)) :
    CompatiblePair K
      (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
      (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2
      (M * 2 ^ l) (Finset.range (M * 2 ^ l - 2 ^ (l - 1))) := by
  have hQvis := perturbed_Q_vis (K := K) (α := α) (δ := δ) hl hM hpar hHp hQm hQd hadm
  have hδvis := perturbed_delta_vis (K := K) (α := α) (δ := δ) hl hM hpar hHp hQm
    hQd hadm
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  obtain ⟨hp1, hp0, hple, hp2le, hd2, hNd, hQdeg, hHhm, hHhd, htower2, hHtim,
      hHtid, hupdl, hsp₁, hsp₂, hRd₁, hRd₂, hRl₁, hRl₂, hb21⟩ :=
    perturbed_call_facts (α := α) (δ := δ) hl hM hpar
      (fun i h1 h2 => ⟨(hHp i h1 h2).1, (hHp i h1 h2).2.1⟩) hQm hQd
  set Vd := Vis R K
    (combined
      (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
      (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
    (Finset.range (M * 2 ^ l - 2 ^ (l - 1))) ((M - 1) * 2 ^ l) with hVd
  -- the perturbed data lives in `Vd`
  have hQVd : ∀ u', Q.coeff u' ∈ Vd :=
    fun u' => Vis_antitone_cutoff (by omega) (hQvis u')
  have hHhVd : ∀ a, (Hp l + Q).coeff a ∈ Vd := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ (known_mem_Vis (hMK a)) (hQVd a)
  have hHtiVd : ∀ a, (Hp l + Q + C δ).coeff a ∈ Vd := by
    intro a
    rw [coeff_add, coeff_C]
    refine Subalgebra.add_mem _ (hHhVd a) ?_
    split
    · exact hδvis
    · exact Subalgebra.zero_mem _
  have htowerVd : ∀ i, 1 ≤ i → i ≤ l →
      ((Function.update Hp l (Hp l + Q)) i).Monic ∧
      ((Function.update Hp l (Hp l + Q)) i).natDegree = 2 ^ i ∧
      (∀ j, ((Function.update Hp l (Hp l + Q)) i).coeff j ∈ Vd) := by
    intro i h1 hi
    rcases Nat.lt_or_ge i l with hlt | hge
    · have hne : i ≠ l := by omega
      have hupd : Function.update Hp l (Hp l + Q) i = Hp i := by
        rw [update_ne _ hne]
      rw [hupd]
      exact ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1,
        fun j => known_mem_Vis ((hHp i h1 (by omega)).2.2 j)⟩
    · have hie : i = l := by omega
      subst hie
      rw [hupdl]
      exact ⟨hHhm, hHhd, hHhVd⟩
  -- the triangular certificate over `Vd`
  have hcert := Rk2l_triangular M (by omega) l
    (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) α Vd (by omega)
    htowerVd hHtim hHtid hHtiVd (fun _ hodd => absurd hpar (by omega)) hadm
  obtain ⟨⟨hTm₁, hTd₁⟩, hTm₂, hTd₂⟩ := Tpair_good
    (Hp := Function.update Hp l (Hp l + Q)) (Ht := Hp l + Q + C δ) (α := α)
    (k := M) (l := l)
    (by omega) (by omega) (fun _ _ => by omega)
    (fun i h1 hi => ⟨(htowerVd i h1 hi).1, (htowerVd i h1 hi).2.1⟩) hHtim hHtid
  have hcompatVd := hcert.toCompatiblePair
    (T₁ := (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1)
    (T₂ := (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
    (N := M * 2 ^ l)
    (by
      intro j
      have hdiff : (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
            M l α).1.coeff j
          - (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
              M l α).1.coeff j
          = ((Hp l + Q) ^ M).coeff j := by
        show _ - ((Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
            M l α).1 - (Function.update Hp l (Hp l + Q)) l ^ M).coeff j = _
        rw [coeff_sub, hupdl]
        ring
      rw [hdiff]
      exact coeff_mem_pow hHhVd M j)
    (by
      intro j
      have hdiff : (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
            M l α).2.coeff j
          - (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
              M l α).2.coeff j
          = ((Hp l + Q + C δ) ^ M).coeff j := by
        show _ - ((Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
            M l α).2 - (Hp l + Q + C δ) ^ M).coeff j = _
        rw [coeff_sub]
        ring
      rw [hdiff]
      exact coeff_mem_pow hHtiVd M j)
    hTm₁ hTd₁ hTm₂ hTd₂
    (by
      have h := Nat.mul_le_mul_right (2 ^ l) (show M - 1 ≤ M from by omega)
      omega)
  -- upgrade the low rows to the honest context
  have hVdle : ∀ t, t ≤ (M - 1) * 2 ^ l →
      Vis R Vd (combined
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
        (Finset.range ((M - 1) * 2 ^ l)) t
      ≤ Vis R K (combined
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
          (Finset.range (M * 2 ^ l - 2 ^ (l - 1))) t := by
    intro t ht
    refine Vis_le ?_ ?_
    · rw [hVd]
      exact Vis_antitone_cutoff ht
    · intro i hi hti
      refine coeff_mem_Vis ?_ hti
      refine Finset.mem_range.2 ?_
      have := Finset.mem_range.1 hi
      omega
  -- high rows: only the perturbed power contributes, causally
  have hQHfine : ∀ j, (M - 1) * 2 ^ l ≤ j →
      (Q * Hp l ^ (M - 1)).coeff j ∈ Vis R K (combined
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
        (Finset.range (M * 2 ^ l - 2 ^ (l - 1))) (j + 1) := by
    intro j hj
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge ((M - 1) * 2 ^ l) x.2 with hg2 | hl2
    · rw [show (Hp l ^ (M - 1)).coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          rw [hMm.natDegree_pow, hMd]
          exact hg2), mul_zero]
      exact Subalgebra.zero_mem _
    · refine Subalgebra.mul_mem _ ?_
        (known_mem_Vis (coeff_mem_pow hMK (M - 1) x.2))
      exact Vis_antitone_cutoff (by omega) (hQvis x.1)
  have hpow := pow_add_eq (Hp l) Q (m := M) (by omega)
  have hbinz := perturbed_binTail_zero₁ hl hM hMd hQd
  have hHhMfine : ∀ j, (M - 1) * 2 ^ l ≤ j →
      ((Hp l + Q) ^ M).coeff j ∈ Vis R K (combined
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
        (Finset.range (M * 2 ^ l - 2 ^ (l - 1))) (j + 1) := by
    intro j hj
    rw [hpow, coeff_add, coeff_add, coeff_smul, hbinz _ (by omega), add_zero]
    exact Subalgebra.add_mem _ (known_mem_Vis (coeff_mem_pow hMK M j))
      (nsmul_mem (hQHfine j hj) M)
  have htpow := pow_add_eq (Hp l + Q) (C δ) (m := M) (by omega)
  have htbinz := perturbed_binTail_zero₂ (M := M) δ hHhd
  refine
    { mem₁ := ?_
      mem₂ := ?_
      monic₁ := hTm₁
      monic₂ := hTm₂
      natDegree₁ := hTd₁
      natDegree₂ := hTd₂
      window := ?_ }
  · intro j
    rcases Nat.lt_or_ge j ((M - 1) * 2 ^ l) with hjlt | hjge
    · exact hVdle (j + 1) (by omega) (hcompatVd.mem₁ j)
    · have h1 := hHhMfine j hjge
      have h2 : (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
          M l α).1.coeff j ∈ Vis R K (combined
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).1
    (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ) M l α).2)
          (Finset.range (M * 2 ^ l - 2 ^ (l - 1))) (j + 1) := by
        rcases eq_or_lt_of_le hjge with heq | hlt
        · rw [← heq, hRl₁]
          exact known_mem_Vis (Subalgebra.neg_mem _ (Subalgebra.natCast_mem _ _))
        · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
          exact Subalgebra.zero_mem _
      have hTco : (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
          M l α).1.coeff j
          = ((Hp l + Q) ^ M).coeff j
            + (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
                M l α).1.coeff j := by
        rw [hsp₁, coeff_add]
      rw [hTco]
      exact Subalgebra.add_mem _ h1 h2
  · intro j
    rcases Nat.lt_or_ge j ((M - 1) * 2 ^ l) with hjlt | hjge
    · exact hVdle j (by omega) (hcompatVd.mem₂ j)
    · rcases eq_or_lt_of_le hjge with heq | hlt
      · exact hVdle j (by omega) (hcompatVd.mem₂ j)
      · have hTco : (Tpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
            M l α).2.coeff j = ((Hp l + Q) ^ M).coeff j := by
          rw [hsp₂, coeff_add, htpow, coeff_add, coeff_add, coeff_smul,
            htbinz _ (by omega), add_zero,
            show (C δ * (Hp l + Q) ^ (M - 1)).coeff j = 0 from by
              rw [coeff_C_mul,
                show ((Hp l + Q) ^ (M - 1)).coeff j = 0 from
                  coeff_eq_zero_of_natDegree_lt (by
                    rw [hHhm.natDegree_pow, hHhd]
                    omega), mul_zero],
            smul_zero, add_zero,
            show (Rpair (Function.update Hp l (Hp l + Q)) (Hp l + Q + C δ)
                M l α).2.coeff j = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
            add_zero]
        rw [hTco]
        have h1 := hHhMfine j hjge
        exact Vis_antitone_cutoff (by omega) h1
  · intro x hx
    have := Finset.mem_range.1 hx
    refine Finset.mem_range.2 ?_
    omega

end FastPoly
