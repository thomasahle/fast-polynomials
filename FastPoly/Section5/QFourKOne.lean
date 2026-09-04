import FastPoly.Section5.FourKPlusOne

/-!
# `lem:Q4k+1-from-H2`: the `Q_{4k+1}` gadget over a given quadratic

`Q_{4k+1} = (x+β)·S⁽¹⁾ + S⁽²⁾` over the shifted tower `Ĥ₂ = H₂ + γ`.  Since
`Ĥ₂ = crownH2 (H₂.coeff 1) (H₂.coeff 0 + γ)` (`crownH2_shift`), the internal call is
the `4k+1` crown; the five parameters `β, γ, a, e, ρ` decode from the top five rows
with slopes `1, 2k, -2k, k, k` (`q4k1_param_vis`).
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {k : ℕ} {α : ℕ → A}

omit [CommRing R] [Algebra R A] [Nontrivial A] in
/-- Normal form of a monic quadratic. -/
theorem monic_deg_two_eq {P : A[X]} (hm : P.Monic) (hd : P.natDegree = 2) :
    P = (X + C (P.coeff 1)) * X + C (P.coeff 0) := by
  ext n
  rcases n with _ | _ | _ | m
  · rw [coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero, coeff_C, if_pos rfl,
      zero_add]
  · rw [coeff_add, mul_comm, coeff_X_mul, coeff_add, coeff_X_zero, coeff_C,
      coeff_C]
    norm_num
  · have hc2 : P.coeff 2 = 1 := by
      rw [← hd, hm.coeff_natDegree]
    rw [show (0 : ℕ) + 1 + 1 = 2 from rfl, hc2, coeff_add, mul_comm,
      coeff_X_mul, coeff_add, coeff_X_one, coeff_C, coeff_C]
    norm_num
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_add, mul_comm,
      coeff_X_mul, coeff_add, coeff_C, coeff_C,
      show (X : A[X]).coeff (m + 1 + 1) = 0 from
        Polynomial.coeff_X_of_ne_one (by omega)]
    norm_num

/-- The shifted quadratic is again a crown quadratic. -/
theorem crownH2_shift {P : A[X]} (hm : P.Monic) (hd : P.natDegree = 2) (γ : A) :
    P + C γ = crownH2 (P.coeff 1) (P.coeff 0 + γ) := by
  conv_lhs => rw [monic_deg_two_eq hm hd]
  unfold crownH2
  rw [map_add]
  ring


section q4k1

variable {H2 : A[X]} {γ ρ a e β : A}

/-- The `Q_{4k+1}` gadget over a given quadratic. -/
noncomputable def q4k1 (H2 : A[X]) (γ ρ a e β : A) (k : ℕ) (α : ℕ → A) : A[X] :=
  (X + C β) * (Tpair (crownHp (H2.coeff 1) (H2.coeff 0 + γ) a e)
      (crownH4 (H2.coeff 1) (H2.coeff 0 + γ) a e + C ρ) k 2 α).1
    + (Tpair (crownHp (H2.coeff 1) (H2.coeff 0 + γ) a e)
        (crownH4 (H2.coeff 1) (H2.coeff 0 + γ) a e + C ρ) k 2 α).2

/-- Reads of the `Q_{4k+1}` gadget: row `m ≥ 1`. -/
theorem q4k1_coeff (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (α : ℕ → A) :
    (q4k1 H2 γ ρ a e β k α).coeff m
      = (Tpair (crownHp (H2.coeff 1) (H2.coeff 0 + γ) a e)
          (crownH4 (H2.coeff 1) (H2.coeff 0 + γ) a e + C ρ) k 2 α).1.coeff (m - 1)
        + β * (Tpair (crownHp (H2.coeff 1) (H2.coeff 0 + γ) a e)
            (crownH4 (H2.coeff 1) (H2.coeff 0 + γ) a e + C ρ) k 2 α).1.coeff m
        + (Tpair (crownHp (H2.coeff 1) (H2.coeff 0 + γ) a e)
            (crownH4 (H2.coeff 1) (H2.coeff 0 + γ) a e + C ρ) k 2 α).2.coeff m := by
  unfold q4k1
  rw [coeff_add, add_mul, coeff_add, coeff_C_mul,
    show m = (m - 1) + 1 from by omega, coeff_X_mul,
    show (m - 1) + 1 = m from by omega]

/-- Row-zero read. -/
theorem q4k1_coeff_zero (k : ℕ) (α : ℕ → A) :
    (q4k1 H2 γ ρ a e β k α).coeff 0
      = β * (Tpair (crownHp (H2.coeff 1) (H2.coeff 0 + γ) a e)
          (crownH4 (H2.coeff 1) (H2.coeff 0 + γ) a e + C ρ) k 2 α).1.coeff 0
        + (Tpair (crownHp (H2.coeff 1) (H2.coeff 0 + γ) a e)
            (crownH4 (H2.coeff 1) (H2.coeff 0 + γ) a e + C ρ) k 2 α).2.coeff 0 := by
  unfold q4k1
  rw [coeff_add, add_mul, coeff_add, coeff_C_mul, mul_coeff_zero, coeff_X_zero,
    zero_mul, zero_add]

variable {K : Subalgebra R A} {k : ℕ} {α : ℕ → A}

/-- Monicity and degree of the `Q_{4k+1}` gadget. -/
theorem q4k1_good (hk : 1 ≤ k) (γ ρ a e β : A) :
    (q4k1 H2 γ ρ a e β k α).Monic
    ∧ (q4k1 H2 γ ρ a e β k α).natDegree = 4 * k + 1 := by
  set b' : A := H2.coeff 1 with hb'
  set c' : A := H2.coeff 0 + γ with hc'
  obtain ⟨hH2m', hH2d'⟩ := crownH2_monic (A := A) (b := b') (c := c')
  obtain ⟨hH4m, hH4d⟩ := crownH4_monic (A := A) (b := b') (c := c') (a := a) (e := e)
  obtain ⟨hHtm, hHtd⟩ := crownH4t_good (b := b') (c := c') (a := a) (e := e) ρ
  have htower := crownHp_good (b := b') (c := c') (a := a) (e := e)
  obtain ⟨⟨hT1m, hT1d⟩, hT2m, hT2d⟩ := Tpair_good
    (Hp := crownHp b' c' a e) (Ht := crownH4 b' c' a e + C ρ) (α := α)
    hk (by omega) (fun _ _ => by omega) htower hHtm (by rw [hHtd]; norm_num)
  have hXTm : ((X + C β)
      * (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1).Monic :=
    (monic_X_add_C β).mul hT1m
  have hXTd : ((X + C β)
      * (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1).natDegree
      = k * 2 ^ 2 + 1 := by
    rw [(monic_X_add_C β).natDegree_mul hT1m, natDegree_X_add_C, hT1d]
    omega
  have hdlt : ((Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).2).degree
      < ((X + C β)
        * (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1).degree := by
    rw [degree_eq_natDegree hT2m.ne_zero, degree_eq_natDegree hXTm.ne_zero,
      hT2d, hXTd]
    exact_mod_cast Nat.lt_succ_self _
  have hP : q4k1 H2 γ ρ a e β k α
      = (X + C β) * (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1
        + (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).2 := by
    unfold q4k1
    rfl
  constructor
  · rw [hP]
    exact hXTm.add_of_left hdlt
  · rw [hP, natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hdlt), hXTd]
    ring
set_option maxHeartbeats 1000000 in
/-- Recovery of the five `Q_{4k+1}` parameters at their causal cutoffs, given the
quadratic. -/
theorem q4k1_param_vis (hk : 1 ≤ k)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k → IsUnit (((n : ℕ) : ℤ) : R))
    (hH2m : H2.Monic) (hH2d : H2.natDegree = 2) (hH2K : ∀ j, H2.coeff j ∈ K)
    (γ ρ a e β : A) :
    β ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k)
    ∧ γ ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 1)
    ∧ a ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 2)
    ∧ e ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 3)
    ∧ ρ ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) := by
  set b' : A := H2.coeff 1 with hb'
  set c' : A := H2.coeff 0 + γ with hc'
  obtain ⟨hH2m', hH2d'⟩ := crownH2_monic (A := A) (b := b') (c := c')
  obtain ⟨hH4m, hH4d⟩ := crownH4_monic (A := A) (b := b') (c := c') (a := a) (e := e)
  obtain ⟨hHtm, hHtd⟩ := crownH4t_good (b := b') (c := c') (a := a) (e := e) ρ
  have htower := crownHp_good (b := b') (c := c') (a := a) (e := e)
  obtain ⟨hsp₁, hsp₂⟩ := Tpair_eq_pow_add_R
    (Hp := crownHp b' c' a e) (Ht := crownH4 b' c' a e + C ρ) (k := k) (l := 2)
    (α := α)
  rw [show crownHp b' c' a e 2 = crownH4 b' c' a e from crownHp_two] at hsp₁
  obtain ⟨hRd₁, hRd₂⟩ := Rk2l_deg k (by omega) 2 (crownHp b' c' a e)
    (crownH4 b' c' a e + C ρ) α (by omega) htower hHtm hHtd
    (fun _ _ _ => ⟨ρ, crownHp_sd ρ⟩)
  obtain ⟨⟨hTm₁, hTd₁⟩, hTm₂, hTd₂⟩ := Tpair_good
    (Hp := crownHp b' c' a e) (Ht := crownH4 b' c' a e + C ρ) (α := α)
    (k := k) (l := 2) (by omega) (by omega) (fun _ _ => by omega) htower hHtm hHtd
  have hTd₁' : (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
      k 2 α).1.natDegree = 4 * k := by
    rw [hTd₁]
    ring
  have hTd₂' : (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
      k 2 α).2.natDegree = 4 * k := by
    rw [hTd₂]
    ring
  have hT₁top : (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
      k 2 α).1.coeff (4 * k) = 1 := by
    rw [← hTd₁', hTm₁.coeff_natDegree]
  have hT₂top : (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
      k 2 α).2.coeff (4 * k) = 1 := by
    rw [← hTd₂', hTm₂.coeff_natDegree]
  -- the high-row reads: remainders vanish, tilde matches the base power
  have htpow := pow_add_eq (crownH4 b' c' a e) (C ρ) (m := k) hk
  have htbinz : ∀ m, (k - 2) * 4 < m →
      (binTail (crownH4 b' c' a e) (C ρ) k).coeff m = 0 := by
    intro m hm
    refine coeff_eq_zero_of_natDegree_lt ?_
    have hbt := natDegree_binTail_le (le_of_eq hH4d)
      (le_of_eq (natDegree_C ρ)) (by omega) k
    omega
  have hVco : ∀ m, 4 * (k - 1) < m →
      (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).2.coeff m
      = (crownH4 b' c' a e ^ k).coeff m := by
    intro m hm
    rw [hsp₂, coeff_add,
      show (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).2.coeff m
        = 0 from coeff_eq_zero_of_natDegree_lt (by
          have h2 : (2 : ℕ) ^ 2 = 4 := by norm_num
          omega), add_zero, htpow, coeff_add, coeff_add, coeff_smul,
      show (C ρ * crownH4 b' c' a e ^ (k - 1)).coeff m = 0 from by
        rw [coeff_C_mul,
          show (crownH4 b' c' a e ^ (k - 1)).coeff m = 0 from
            coeff_eq_zero_of_natDegree_lt (by
              rw [hH4m.natDegree_pow, hH4d]
              omega), mul_zero],
      smul_zero, add_zero, htbinz m (by omega), add_zero]
  have hUAz : ∀ m, 4 * (k - 1) < m →
      (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1.coeff m
      = (crownH4 b' c' a e ^ k).coeff m := by
    intro m hm
    rw [hsp₁, coeff_add,
      show (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1.coeff m
        = 0 from coeff_eq_zero_of_natDegree_lt (by
          have h2 : (2 : ℕ) ^ 2 = 4 := by norm_num
          omega), add_zero]
  -- known base data
  have hbK : ∀ t, b' ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) t := fun t => known_mem_Vis (hH2K 1)
  have hc0K : ∀ t, H2.coeff 0 ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) t := fun t => known_mem_Vis (hH2K 0)
  -- crown instances (the `S`-hypotheses only need known data at each level)
  have hStriv : ∀ t : ℕ, ∀ j, 3 < j → (crownH4 b' c' a e).coeff j ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) t := by
    intro t j hj
    rcases Nat.lt_or_ge 4 j with h4 | h4
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · rw [show j = 4 from by omega, ← hH4d, hH4m.coeff_natDegree]
      exact Subalgebra.one_mem _
  have hP4k1V : ∀ t : ℕ, (crownH4 b' c' a e ^ k).coeff (4 * k - 1) ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) t := by
    intro t
    have hcrown1 := pow_coeff_crown hH4m hH4d (t := 1) (by omega) (by omega)
      (hStriv t) k hk
    rw [show k * 4 - 1 = 4 * k - 1 from by omega, crownH4_coeff_three] at hcrown1
    have hrecomb : (crownH4 b' c' a e ^ k).coeff (4 * k - 1)
        = ((crownH4 b' c' a e ^ k).coeff (4 * k - 1)
            - ((k : ℕ) : A) * (b' + b'))
          + ((k : ℕ) : A) * (b' + b') := by
      ring
    rw [hrecomb]
    exact Subalgebra.add_mem _ hcrown1
      (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
        (Subalgebra.add_mem _ (hbK t) (hbK t)))
  -- β
  have hβ : β ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k) := by
    have hrowG : 4 * k ∈ Finset.range (4 * k + 2) := Finset.mem_range.2 (by omega)
    have hΨmem := coeff_mem_Vis (K := K) (t := 4 * k)
      (Φ := q4k1 H2 γ ρ a e β k α) hrowG le_rfl
    have hkey : β = (q4k1 H2 γ ρ a e β k α).coeff (4 * k)
        - (crownH4 b' c' a e ^ k).coeff (4 * k - 1) - 1 := by
      rw [q4k1_coeff (4 * k) (by omega) k α, hUAz _ (by omega), hT₁top, hVco _
        (by omega), mul_one,
        show (crownH4 b' c' a e ^ k).coeff (4 * k)
          = 1 from by
          rw [show 4 * k = k * 4 from by ring,
            ← show (crownH4 b' c' a e ^ k).natDegree = k * 4 from by
              rw [hH4m.natDegree_pow, hH4d], (hH4m.pow k).coeff_natDegree]]
      ring
    have hfin := Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hΨmem (hP4k1V _))
      (Subalgebra.one_mem (Vis R K (q4k1 H2 γ ρ a e β k α)
        (Finset.range (4 * k + 2)) (4 * k)))
    rw [← hkey] at hfin
    exact hfin
  -- c' = H2.coeff 0 + γ from the second row, then γ
  have hc'V : c' ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 1) := by
    have hβV : β ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 1) := Vis_antitone_cutoff (by omega) hβ
    have hS2 : ∀ j, 2 < j → (crownH4 b' c' a e).coeff j ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 1) := by
      intro j hj
      rcases Nat.lt_or_ge 3 j with h3 | h3
      · exact hStriv _ j h3
      · rw [show j = 3 from by omega, crownH4_coeff_three]
        exact Subalgebra.add_mem _ (hbK _) (hbK _)
    have hcrown2 := pow_coeff_crown hH4m hH4d (t := 2) (by omega) (by omega)
      hS2 k hk
    rw [show k * 4 - 2 = 4 * k - 2 from by omega, crownH4_coeff_two] at hcrown2
    have hrowG : 4 * k - 1 ∈ Finset.range (4 * k + 2) := Finset.mem_range.2 (by omega)
    have hΨmem := coeff_mem_Vis (K := K) (t := 4 * k - 1)
      (Φ := q4k1 H2 γ ρ a e β k α) hrowG le_rfl
    obtain ⟨u, hu⟩ := hadm (2 * k) (by omega) le_rfl
    have hMA : algebraMap R A (↑u : R) = ((2 * k : ℕ) : A) := by
      rw [hu, map_intCast, Int.cast_natCast]
    have h2kc : ((2 * k : ℕ) : A) * c' ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 1) := by
      have hkey : ((2 * k : ℕ) : A) * c'
          = (q4k1 H2 γ ρ a e β k α).coeff (4 * k - 1)
            - ((crownH4 b' c' a e ^ k).coeff (4 * k - 2)
              - ((k : ℕ) : A) * (b' * b' + (c' + c') - 1))
            - β * (crownH4 b' c' a e ^ k).coeff (4 * k - 1)
            - (crownH4 b' c' a e ^ k).coeff (4 * k - 1)
            - ((k : ℕ) : A) * (b' * b') + ((k : ℕ) : A) := by
        rw [q4k1_coeff (4 * k - 1) (by omega) k α,
          show 4 * k - 1 - 1 = 4 * k - 2 from by omega,
          hUAz (4 * k - 2) (by omega), hUAz (4 * k - 1) (by omega),
          hVco (4 * k - 1) (by omega)]
        push_cast
        ring
      rw [hkey]
      exact Subalgebra.add_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
        (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hΨmem hcrown2)
          (Subalgebra.mul_mem _ hβV (hP4k1V _))) (hP4k1V _))
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.mul_mem _ (hbK _) (hbK _))))
        (Subalgebra.natCast_mem _ _)
    have hkey2 : c' = algebraMap R A (↑u⁻¹ : R) * (((2 * k : ℕ) : A) * c') := by
      rw [← hMA, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    have hfin := Subalgebra.mul_mem _
      (algebraMap_mem_Vis (K := K) (↑u⁻¹ : R)) h2kc
    rw [← hkey2] at hfin
    exact hfin
  have hγv : γ ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 1) := by
    have hkeyγ : γ = c' - H2.coeff 0 := by
      rw [hc']
      ring
    have hfin := Subalgebra.sub_mem _ hc'V (hc0K (4 * k - 1))
    rw [← hkeyγ] at hfin
    exact hfin
  -- a from the third row
  have hav : a ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 2) := by
    have hβV : β ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 2) := Vis_antitone_cutoff (by omega) hβ
    have hcV : c' ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 2) := Vis_antitone_cutoff (by omega) hc'V
    have hS2 : ∀ j, 1 < j → (crownH4 b' c' a e).coeff j ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 2) := by
      intro j hj
      rcases Nat.lt_or_ge 3 j with h3 | h3
      · exact hStriv _ j h3
      · rcases Nat.lt_or_ge j 3 with h2 | h2
        · rw [show j = 2 from by omega, crownH4_coeff_two]
          exact Subalgebra.sub_mem _ (Subalgebra.add_mem _
            (Subalgebra.mul_mem _ (hbK _) (hbK _))
            (Subalgebra.add_mem _ hcV hcV)) (Subalgebra.one_mem _)
        · rw [show j = 3 from by omega, crownH4_coeff_three]
          exact Subalgebra.add_mem _ (hbK _) (hbK _)
    have hcrown2' := pow_coeff_crown hH4m hH4d (t := 2) (by omega) (by omega)
      (fun j hj => hS2 j (by omega)) k hk
    have hcrown3 := pow_coeff_crown hH4m hH4d (t := 3) (by omega) (by omega)
      hS2 k hk
    rw [show k * 4 - 2 = 4 * k - 2 from by omega, crownH4_coeff_two] at hcrown2'
    rw [show k * 4 - 3 = 4 * k - 3 from by omega, crownH4_coeff_one] at hcrown3
    have hP4k2V : (crownH4 b' c' a e ^ k).coeff (4 * k - 2) ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 2) := by
      have hrecomb : (crownH4 b' c' a e ^ k).coeff (4 * k - 2)
          = ((crownH4 b' c' a e ^ k).coeff (4 * k - 2)
              - ((k : ℕ) : A) * (b' * b' + (c' + c') - 1))
            + ((k : ℕ) : A) * (b' * b' + (c' + c') - 1) := by
        ring
      rw [hrecomb]
      exact Subalgebra.add_mem _ hcrown2'
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.sub_mem _ (Subalgebra.add_mem _
            (Subalgebra.mul_mem _ (hbK _) (hbK _))
            (Subalgebra.add_mem _ hcV hcV)) (Subalgebra.one_mem _)))
    have hrowG : 4 * k - 2 ∈ Finset.range (4 * k + 2) := Finset.mem_range.2 (by omega)
    have hΨmem := coeff_mem_Vis (K := K) (t := 4 * k - 2)
      (Φ := q4k1 H2 γ ρ a e β k α) hrowG le_rfl
    obtain ⟨u, hu⟩ := hadm (2 * k) (by omega) le_rfl
    have hMA : algebraMap R A (↑u : R) = ((2 * k : ℕ) : A) := by
      rw [hu, map_intCast, Int.cast_natCast]
    have h2ka : ((2 * k : ℕ) : A) * a ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 2) := by
      have hkey : ((2 * k : ℕ) : A) * a
          = ((k : ℕ) : A) * (b' * c' + b' * c')
            + ((crownH4 b' c' a e ^ k).coeff (4 * k - 3)
              - ((k : ℕ) : A) * (b' * c' + b' * c' - (a + a)))
            + β * (crownH4 b' c' a e ^ k).coeff (4 * k - 2)
            + (crownH4 b' c' a e ^ k).coeff (4 * k - 2)
            - (q4k1 H2 γ ρ a e β k α).coeff (4 * k - 2) := by
        rw [q4k1_coeff (4 * k - 2) (by omega) k α,
          show 4 * k - 2 - 1 = 4 * k - 3 from by omega,
          hUAz (4 * k - 3) (by omega), hUAz (4 * k - 2) (by omega),
          hVco (4 * k - 2) (by omega)]
        push_cast
        ring
      rw [hkey]
      exact Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _
          (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
            (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hbK _) hcV)
              (Subalgebra.mul_mem _ (hbK _) hcV)))
          hcrown3)
        (Subalgebra.mul_mem _ hβV hP4k2V)) hP4k2V) hΨmem
    have hkey2 : a = algebraMap R A (↑u⁻¹ : R) * (((2 * k : ℕ) : A) * a) := by
      rw [← hMA, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    have hfin := Subalgebra.mul_mem _
      (algebraMap_mem_Vis (K := K) (↑u⁻¹ : R)) h2ka
    rw [← hkey2] at hfin
    exact hfin
  -- e from the fourth row
  have hev : e ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 3) := by
    have hβV : β ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 3) := Vis_antitone_cutoff (by omega) hβ
    have hcV : c' ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 3) := Vis_antitone_cutoff (by omega) hc'V
    have haV : a ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 3) := Vis_antitone_cutoff (by omega) hav
    have hS3 : ∀ j, 0 < j → (crownH4 b' c' a e).coeff j ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 3) := by
      intro j hj
      rcases Nat.lt_or_ge 3 j with h3 | h3
      · exact hStriv _ j h3
      · rcases Nat.lt_or_ge j 2 with h2 | h2
        · rw [show j = 1 from by omega, crownH4_coeff_one]
          exact Subalgebra.sub_mem _ (Subalgebra.add_mem _
            (Subalgebra.mul_mem _ (hbK _) hcV) (Subalgebra.mul_mem _ (hbK _) hcV))
            (Subalgebra.add_mem _ haV haV)
        · rcases Nat.lt_or_ge j 3 with h2' | h3'
          · rw [show j = 2 from by omega, crownH4_coeff_two]
            exact Subalgebra.sub_mem _ (Subalgebra.add_mem _
              (Subalgebra.mul_mem _ (hbK _) (hbK _))
              (Subalgebra.add_mem _ hcV hcV)) (Subalgebra.one_mem _)
          · rw [show j = 3 from by omega, crownH4_coeff_three]
            exact Subalgebra.add_mem _ (hbK _) (hbK _)
    have hcrown3' := pow_coeff_crown hH4m hH4d (t := 3) (by omega) (by omega)
      (fun j hj => hS3 j (by omega)) k hk
    have hcrown4 := pow_coeff_crown hH4m hH4d (t := 4) (by omega) (by omega)
      hS3 k hk
    rw [show k * 4 - 3 = 4 * k - 3 from by omega, crownH4_coeff_one] at hcrown3'
    rw [show k * 4 - 4 = 4 * k - 4 from by omega, crownH4_coeff_zero] at hcrown4
    have hP4k3V : (crownH4 b' c' a e ^ k).coeff (4 * k - 3) ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 3) := by
      have hrecomb : (crownH4 b' c' a e ^ k).coeff (4 * k - 3)
          = ((crownH4 b' c' a e ^ k).coeff (4 * k - 3)
              - ((k : ℕ) : A) * (b' * c' + b' * c' - (a + a)))
            + ((k : ℕ) : A) * (b' * c' + b' * c' - (a + a)) := by
        ring
      rw [hrecomb]
      exact Subalgebra.add_mem _ hcrown3'
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.sub_mem _ (Subalgebra.add_mem _
            (Subalgebra.mul_mem _ (hbK _) hcV) (Subalgebra.mul_mem _ (hbK _) hcV))
            (Subalgebra.add_mem _ haV haV)))
    have hAd : (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1.coeff
        (4 * k - 4) ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 3) := by
      rcases eq_or_lt_of_le hk with hk1 | hk2
      · rw [← hk1, Rpair_one]
        rw [show ((0, 0) : A[X] × A[X]).1 = 0 from rfl, coeff_zero]
        exact Subalgebra.zero_mem _
      · obtain ⟨hRl₁, -⟩ := Rk2l_lead k (by omega) 2 (crownHp b' c' a e)
          (crownH4 b' c' a e + C ρ) α (by omega) htower hHtm hHtd
          (fun _ _ _ => ⟨ρ, crownHp_sd ρ⟩)
        rw [show (k - 1) * 2 ^ 2 = 4 * k - 4 from by
          have h2 : (2 : ℕ) ^ 2 = 4 := by norm_num
          rw [h2]
          omega] at hRl₁
        rw [hRl₁]
        exact Subalgebra.neg_mem _ (Subalgebra.natCast_mem _ _)
    have hUco : (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
        k 2 α).1.coeff (4 * k - 4)
        = (crownH4 b' c' a e ^ k).coeff (4 * k - 4)
          + (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1.coeff
            (4 * k - 4) := by
      rw [hsp₁, coeff_add]
    have hrowG : 4 * k - 3 ∈ Finset.range (4 * k + 2) := Finset.mem_range.2 (by omega)
    have hΨmem := coeff_mem_Vis (K := K) (t := 4 * k - 3)
      (Φ := q4k1 H2 γ ρ a e β k α) hrowG le_rfl
    obtain ⟨u, hu⟩ := hadm k (by omega) (by omega)
    have hMA : algebraMap R A (↑u : R) = ((k : ℕ) : A) := by
      rw [hu, map_intCast, Int.cast_natCast]
    have hke : ((k : ℕ) : A) * e ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 3) := by
      have hkey : ((k : ℕ) : A) * e
          = (q4k1 H2 γ ρ a e β k α).coeff (4 * k - 3)
            - (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1.coeff
              (4 * k - 4)
            - ((crownH4 b' c' a e ^ k).coeff (4 * k - 4)
              - ((k : ℕ) : A) * (c' * c' - a * a + e))
            - β * (crownH4 b' c' a e ^ k).coeff (4 * k - 3)
            - (crownH4 b' c' a e ^ k).coeff (4 * k - 3)
            - ((k : ℕ) : A) * (c' * c') + ((k : ℕ) : A) * (a * a) := by
        rw [q4k1_coeff (4 * k - 3) (by omega) k α,
          show 4 * k - 3 - 1 = 4 * k - 4 from by omega,
          hUco, hUAz (4 * k - 3) (by omega), hVco (4 * k - 3) (by omega)]
        push_cast
        ring
      rw [hkey]
      exact Subalgebra.add_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
        (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
          hΨmem hAd) hcrown4) (Subalgebra.mul_mem _ hβV hP4k3V)) hP4k3V)
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.mul_mem _ hcV hcV)))
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.mul_mem _ haV haV))
    have hkey2 : e = algebraMap R A (↑u⁻¹ : R) * (((k : ℕ) : A) * e) := by
      rw [← hMA, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    have hfin := Subalgebra.mul_mem _
      (algebraMap_mem_Vis (K := K) (↑u⁻¹ : R)) hke
    rw [← hkey2] at hfin
    exact hfin
  -- ρ from the boundary row
  have hρv : ρ ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) := by
    have hβV : β ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) := Vis_antitone_cutoff (by omega) hβ
    have hcV : c' ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) := Vis_antitone_cutoff (by omega) hc'V
    have haV : a ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) := Vis_antitone_cutoff (by omega) hav
    have heV : e ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) := Vis_antitone_cutoff (by omega) hev
    have hH4V : ∀ j, (crownH4 b' c' a e).coeff j ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) := by
      intro j
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        rw [crownH4_coeff_zero]
        exact Subalgebra.add_mem _ (Subalgebra.sub_mem _
          (Subalgebra.mul_mem _ hcV hcV) (Subalgebra.mul_mem _ haV haV)) heV
      · rcases Nat.lt_or_ge 3 j with h3 | h3
        · exact hStriv _ j h3
        · rcases Nat.lt_or_ge j 2 with h2 | h2
          · rw [show j = 1 from by omega, crownH4_coeff_one]
            exact Subalgebra.sub_mem _ (Subalgebra.add_mem _
              (Subalgebra.mul_mem _ (hbK _) hcV)
              (Subalgebra.mul_mem _ (hbK _) hcV))
              (Subalgebra.add_mem _ haV haV)
          · rcases Nat.lt_or_ge j 3 with h2' | h3'
            · rw [show j = 2 from by omega, crownH4_coeff_two]
              exact Subalgebra.sub_mem _ (Subalgebra.add_mem _
                (Subalgebra.mul_mem _ (hbK _) (hbK _))
                (Subalgebra.add_mem _ hcV hcV)) (Subalgebra.one_mem _)
            · rw [show j = 3 from by omega, crownH4_coeff_three]
              exact Subalgebra.add_mem _ (hbK _) (hbK _)
    have hH4kV : ∀ m, (crownH4 b' c' a e ^ k).coeff m ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) :=
      coeff_mem_pow hH4V k
    obtain ⟨u, hu⟩ := hadm k (by omega) (by omega)
    have hMA : algebraMap R A (↑u : R) = ((k : ℕ) : A) := by
      rw [hu, map_intCast, Int.cast_natCast]
    have hlead : (crownH4 b' c' a e ^ (k - 1)).coeff (4 * (k - 1)) = 1 := by
      have h := (hH4m.pow (k - 1)).coeff_natDegree
      rw [hH4m.natDegree_pow, hH4d,
        show (k - 1) * 4 = 4 * (k - 1) from by ring] at h
      exact h
    have hkρ : ((k : ℕ) : A) * ρ ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) := by
      rcases eq_or_lt_of_le hk with hk1 | hk2
      · have hk1' : k = 1 := hk1.symm
        subst hk1'
        have hrowG : 0 ∈ Finset.range (4 * 1 + 2) := Finset.mem_range.2 (by omega)
        have hΨmem := coeff_mem_Vis (K := K) (t := 4 * 1 - 4)
          (Φ := q4k1 H2 γ ρ a e β 1 α) hrowG (by omega)
        have hkey : ((1 : ℕ) : A) * ρ
            = (q4k1 H2 γ ρ a e β 1 α).coeff 0
              - β * (crownH4 b' c' a e ^ 1).coeff 0
              - (crownH4 b' c' a e ^ 1).coeff 0 := by
          rw [q4k1_coeff_zero, hsp₁, hsp₂, coeff_add, coeff_add,
            show (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) 1 2 α).1
              = 0 from by rw [Rpair_one],
            show (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) 1 2 α).2
              = 0 from by rw [Rpair_one]]
          simp only [coeff_zero, add_zero, pow_one]
          rw [coeff_add, coeff_C]
          norm_num
        rw [hkey]
        exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hΨmem
          (Subalgebra.mul_mem _ hβV (hH4kV 0))) (hH4kV 0)
      · obtain ⟨-, hRs₁, -, -⟩ := Rk2l_top_two
          (K := Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2))
            (4 * k - 4))
          (α := α) hk2 (by omega) htower hHtm hHtd
          (fun _ _ _ => ⟨ρ, crownHp_sd ρ⟩)
          (by
            rw [show (2 : ℕ) ^ (2 - 1) - 1 = 1 from by norm_num,
              show crownHp b' c' a e (2 - 1) = crownH2 b' c' from rfl,
              crownH2_coeff_one]
            exact hbK _)
          (by
            rw [show (2 : ℕ) ^ 2 - 1 = 3 from by norm_num, crownHp_two,
              crownH4_coeff_three]
            exact Subalgebra.add_mem _ (hbK _) (hbK _))
          (by
            rw [show (2 : ℕ) ^ 2 - 1 = 3 from by norm_num, coeff_add,
              crownH4_coeff_three, coeff_C, if_neg (by omega)]
            exact Subalgebra.add_mem _ (Subalgebra.add_mem _ (hbK _) (hbK _))
              (Subalgebra.zero_mem _))
        rw [show (k - 1) * 2 ^ 2 - 1 = 4 * k - 5 from by
          have h2 : (2 : ℕ) ^ 2 = 4 := by norm_num
          rw [h2]
          omega] at hRs₁
        obtain ⟨-, hRl₂⟩ := Rk2l_lead k (by omega) 2 (crownHp b' c' a e)
          (crownH4 b' c' a e + C ρ) α (by omega) htower hHtm hHtd
          (fun _ _ _ => ⟨ρ, crownHp_sd ρ⟩)
        rw [show (k - 1) * 2 ^ 2 = 4 * k - 4 from by
          have h2 : (2 : ℕ) ^ 2 = 4 := by norm_num
          rw [h2]
          omega] at hRl₂
        have hrowG : 4 * k - 4 ∈ Finset.range (4 * k + 2) :=
          Finset.mem_range.2 (by omega)
        have hΨmem := coeff_mem_Vis (K := K) (t := 4 * k - 4)
          (Φ := q4k1 H2 γ ρ a e β k α) hrowG le_rfl
        have hUco : (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
            k 2 α).1.coeff (4 * k - 5)
            = (crownH4 b' c' a e ^ k).coeff (4 * k - 5)
              + (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
                  k 2 α).1.coeff (4 * k - 5) := by
          rw [hsp₁, coeff_add]
        have hUcoD : (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
            k 2 α).1.coeff (4 * k - 4)
            = (crownH4 b' c' a e ^ k).coeff (4 * k - 4)
              + (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
                  k 2 α).1.coeff (4 * k - 4) := by
          rw [hsp₁, coeff_add]
        have hAlead : (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
            k 2 α).1.coeff (4 * k - 4) ∈ Vis R K (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) (4 * k - 4) := by
          obtain ⟨hRl₁, -⟩ := Rk2l_lead k (by omega) 2 (crownHp b' c' a e)
            (crownH4 b' c' a e + C ρ) α (by omega) htower hHtm hHtd
            (fun _ _ _ => ⟨ρ, crownHp_sd ρ⟩)
          rw [show (k - 1) * 2 ^ 2 = 4 * k - 4 from by
            have h2 : (2 : ℕ) ^ 2 = 4 := by norm_num
            rw [h2]
            omega] at hRl₁
          rw [hRl₁]
          exact Subalgebra.neg_mem _ (Subalgebra.natCast_mem _ _)
        have hVco' : (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
            k 2 α).2.coeff (4 * k - 4)
            = (crownH4 b' c' a e ^ k).coeff (4 * k - 4) + ((k : ℕ) : A) * ρ
              + (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
                  k 2 α).2.coeff (4 * k - 4) := by
          rw [hsp₂, coeff_add, htpow, coeff_add, coeff_add, coeff_smul,
            htbinz _ (by omega), add_zero, coeff_C_mul,
            show 4 * k - 4 = 4 * (k - 1) from by omega, hlead, mul_one]
          simp only [nsmul_eq_mul]
        have hkey : ((k : ℕ) : A) * ρ
            = (q4k1 H2 γ ρ a e β k α).coeff (4 * k - 4)
              - (crownH4 b' c' a e ^ k).coeff (4 * k - 5)
              - (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
                  k 2 α).1.coeff (4 * k - 5)
              - β * ((crownH4 b' c' a e ^ k).coeff (4 * k - 4)
                + (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
                    k 2 α).1.coeff (4 * k - 4))
              - (crownH4 b' c' a e ^ k).coeff (4 * k - 4)
              - (Rpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ)
                  k 2 α).2.coeff (4 * k - 4) := by
          rw [q4k1_coeff (4 * k - 4) (by omega) k α,
            show 4 * k - 4 - 1 = 4 * k - 5 from by omega,
            hUco, hUcoD, hVco']
          ring
        rw [hkey, hRl₂]
        exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
          (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hΨmem (hH4kV _)) hRs₁)
          (Subalgebra.mul_mem _ hβV (Subalgebra.add_mem _ (hH4kV _) hAlead)))
          (hH4kV _))
          (Subalgebra.neg_mem _ (Subalgebra.natCast_mem _ _))
    have hkey2 : ρ = algebraMap R A (↑u⁻¹ : R) * (((k : ℕ) : A) * ρ) := by
      rw [← hMA, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    have hfin := Subalgebra.mul_mem _
      (algebraMap_mem_Vis (K := K) (↑u⁻¹ : R)) hkρ
    rw [← hkey2] at hfin
    exact hfin
  exact ⟨hβ, hγv, hav, hev, hρv⟩

end q4k1

end FastPoly
