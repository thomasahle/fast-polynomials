import FastPoly.Section5.Rk2lTri

/-!
# `lem:Rk2l`(3): the even main branch certificate
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}

omit [Nontrivial A] in
/-- `tLam`, even main branch: inner rows inherit the half-degree table. -/
theorem tLam_even_inner (hpar : k % 2 = 0) (hk : 4 ≤ k) {j : ℕ}
    (hj : j < (k - 2) * 2 ^ l) : tLam k l j = tLam (k / 2) (l + 1) j := by
  show tLamF k k l j = tLamF (k / 2) (k / 2) (l + 1) j
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  exact tLamF_fuel ((f + 1) / 2) f ((f + 1) / 2) (by omega) (by omega) (l + 1) j

omit [Nontrivial A] in
theorem tLam_even_mid (hpar : k % 2 = 0) (hk : 4 ≤ k) {j : ℕ}
    (h1 : (k - 2) * 2 ^ l ≤ j) (h2 : j < (k - 2) * 2 ^ l + 2 ^ (l - 1)) :
    tLam k l j = ((k / 2 : ℕ) : ℤ) := by
  show tLamF k k l j = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_pos (by omega), if_neg (by omega),
    if_pos (by omega)]

omit [Nontrivial A] in
theorem tLam_even_hi (hpar : k % 2 = 0) (hk : 4 ≤ k) {j : ℕ}
    (h1 : (k - 2) * 2 ^ l + 2 ^ (l - 1) ≤ j) :
    tLam k l j = -((k : ℕ) : ℤ) := by
  show tLamF k k l j = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_pos (by omega),
    if_neg (Nat.not_lt.mpr (le_trans (Nat.le_add_right _ _) h1)),
    if_neg (Nat.not_lt.mpr h1)]


/-- `rSlot`, even main branch: inner rows inherit the half-degree map. -/
theorem rSlot_even_inner (hpar : k % 2 = 0) (hk : 4 ≤ k) {r : ℕ}
    (hr : r < (k - 2) * 2 ^ l) :
    rSlot (A := A) k l α r = rSlot (k / 2) (l + 1) α r := by
  show rSlotF k k l α r = rSlotF (k / 2) (k / 2) (l + 1) α r
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_pos (by omega)]
  exact rSlotF_fuel ((f + 1) / 2) f ((f + 1) / 2) (by omega) (by omega) (l + 1) α r

omit [Nontrivial A] in
/-- `rSlot`, even main band values. -/
theorem rSlot_even_b0 (hpar : k % 2 = 0) (hk : 4 ≤ k) :
    rSlot (A := A) k l α ((k - 2) * 2 ^ l) = α ((k - 2) * 2 ^ l) := by
  show rSlotF k k l α ((k - 2) * 2 ^ l) = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  unfold rSlotF
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
    if_pos rfl]

omit [Nontrivial A] in
theorem rSlot_even_eS2 (hpar : k % 2 = 0) (hk : 4 ≤ k) {r : ℕ}
    (h1 : (k - 2) * 2 ^ l < r) (h2 : r < (k - 2) * 2 ^ l + 2 ^ (l - 1)) :
    rSlot (A := A) k l α r
      = peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 1 + j))
          (r - (k - 2) * 2 ^ l - 1) := by
  show rSlotF k k l α r = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  unfold rSlotF
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega)]

omit [Nontrivial A] in
theorem rSlot_even_delta (hpar : k % 2 = 0) (hk : 4 ≤ k) :
    rSlot (A := A) k l α ((k - 2) * 2 ^ l + 2 ^ (l - 1))
      = α ((k - 2) * 2 ^ l + 2 ^ (l - 1)) := by
  show rSlotF k k l α ((k - 2) * 2 ^ l + 2 ^ (l - 1)) = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  unfold rSlotF
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos rfl]

omit [Nontrivial A] in
theorem rSlot_even_tS1 (hpar : k % 2 = 0) (hk : 4 ≤ k) {r : ℕ}
    (h1 : (k - 2) * 2 ^ l + 2 ^ (l - 1) < r) :
    rSlot (A := A) k l α r
      = peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
          (r - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1) := by
  show rSlotF k k l α r = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  unfold rSlotF
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]


omit [Nontrivial A] in
/-- The even band of `rSlot k l` agrees with the shifted `k = 2` map. -/
theorem rSlot_even_band_eq (hpar : k % 2 = 0) (hk : 4 ≤ k) (hl : 2 ≤ l) {t : ℕ} :
    rSlot (A := A) k l α ((k - 2) * 2 ^ l + t)
      = rSlot 2 l (fun j => α ((k - 2) * 2 ^ l + j)) t := by
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [Nat.add_zero, rSlot_even_b0 hpar hk, rSlot_two_zero]
    rfl
  · rcases Nat.lt_or_ge t (2 ^ (l - 1)) with h1 | h1
    · rw [rSlot_even_eS2 hpar hk (by omega) (by omega),
        rSlot_two_eS2 (by omega) (by omega)]
      congr 1
      · funext j; congr 1; omega
      · omega
    · rcases Nat.eq_or_lt_of_le h1 with heq | h2
      · rw [← heq, rSlot_even_delta hpar hk, rSlot_two_delta]
      · rw [rSlot_even_tS1 hpar hk (by omega), rSlot_two_tS1 h2]
        congr 1
        · funext j; congr 1; omega
        · omega

omit [Nontrivial A] in
/-- High coefficients of `binTail` are known: at and above its degree bound the only
survivor is the leading coefficient of the monic `q = 2` term. -/
theorem binTail_coeff_high {K : Subalgebra R A} {P E : A[X]} {p e m : ℕ}
    (hPm : P.Monic) (hPd : P.natDegree = p)
    (hE2m : (E ^ 2).Monic) (hE2d : (E ^ 2).natDegree = 2 * e)
    (hEd : E.natDegree ≤ e) (hep : e < p) :
    ∀ j, 2 * e + (m - 2) * p ≤ j → (binTail P E m).coeff j ∈ K := by
  intro j hj
  show (∑ q ∈ Finset.Icc 2 m, E ^ q * P ^ (m - q) * ((m.choose q : ℕ) : A[X])).coeff j
    ∈ K
  rw [Polynomial.finset_sum_coeff]
  refine Subalgebra.sum_mem _ fun q hq => ?_
  obtain ⟨hq2, hqm⟩ := Finset.mem_Icc.1 hq
  rw [← Polynomial.C_eq_natCast, coeff_mul_C]
  refine Subalgebra.mul_mem _ ?_ (Subalgebra.natCast_mem _ _)
  rcases Nat.lt_or_ge 2 q with hq3 | hq3
  · -- higher terms vanish at or above the bound
    obtain ⟨d, rfl⟩ : ∃ d, q = d + 2 := ⟨q - 2, by omega⟩
    have hde : d * e < d * p := mul_lt_mul_of_pos_left hep (by omega : 0 < d)
    have h1 : (E ^ (d + 2) * P ^ (m - (d + 2))).natDegree
        ≤ (d + 2) * e + (m - (d + 2)) * p := by
      refine le_trans (natDegree_mul_le) ?_
      have he : (E ^ (d + 2)).natDegree ≤ (d + 2) * e :=
        le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hEd)
      have hp : (P ^ (m - (d + 2))).natDegree ≤ (m - (d + 2)) * p :=
        le_trans natDegree_pow_le (Nat.mul_le_mul_left _ (le_of_eq hPd))
      omega
    have hb1 : (d + 2) * e = d * e + 2 * e := by ring
    have hb2 : (m - 2) * p = (m - (d + 2)) * p + d * p := by
      have hmd : m - 2 = (m - (d + 2)) + d := by omega
      rw [hmd, Nat.add_mul]
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Subalgebra.zero_mem _
  · -- q = 2: the term is monic of degree exactly the bound
    have hq2' : q = 2 := by omega
    subst hq2'
    have hm2 : (E ^ 2 * P ^ (m - 2)).Monic := hE2m.mul (hPm.pow _)
    have hd2 : (E ^ 2 * P ^ (m - 2)).natDegree = 2 * e + (m - 2) * p := by
      rw [hE2m.natDegree_mul (hPm.pow _), hE2d, hPm.natDegree_pow, hPd]
    rcases Nat.lt_or_ge (2 * e + (m - 2) * p) j with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · have hj' : j = 2 * e + (m - 2) * p := by omega
      rw [hj', ← hd2, hm2.coeff_natDegree]
      exact Subalgebra.one_mem _


/-- Window transport for the correction pair's coefficients into the even band. -/
theorem eE_window
    (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : k % 2 = 0) (hk : 4 ≤ k) (hl : 2 ≤ l) (h2 : IsUnit (2 : R)) :
    (∀ lo i, lo ≤ (k - 2) * 2 ^ l + i + 1 →
      (eE1 Hp k l α).coeff i ∈ K ⊔ adjoin R
        ((rSlot k l α (A := A)) '' Set.Ico lo ((k - 1) * 2 ^ l)))
    ∧ (∀ lo i, lo ≤ (k - 2) * 2 ^ l + i →
      (eE2 Hp k l α).coeff i ∈ K ⊔ adjoin R
        ((rSlot k l α (A := A)) '' Set.Ico lo ((k - 1) * 2 ^ l))) := by
  have hcert := eE_cert (Hp := Hp) (α := α) (k := k) hHp hl h2
  have hp2 : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  constructor
  · intro lo i hlo
    have h1 := hcert.supp₁ i
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) h1
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    rw [← rSlot_even_band_eq hpar hk hl]
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨(k - 2) * 2 ^ l + g, ⟨by omega, by omega⟩, rfl⟩)
  · intro lo i hlo
    have h1 := hcert.supp₂ i
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) h1
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    rw [← rSlot_even_band_eq hpar hk hl]
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨(k - 2) * 2 ^ l + g, ⟨by omega, by omega⟩, rfl⟩)

/-- Supports of the even-step remainder pair, first component. -/
theorem even_supp₁
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : k % 2 = 0) (hk : 4 ≤ k) (hl : 2 ≤ l) (h2 : IsUnit (2 : R))
    (hin : ∀ j, (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
            Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
        ⊔ adjoin R ((rSlot (k / 2) (l + 1) α (A := A)) ''
          Set.Ico (j + 1) ((k - 2) * 2 ^ l)))
    (hind : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.natDegree ≤ (k - 2) * 2 ^ l)
    (htop : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.coeff ((k - 2) * 2 ^ l) ∈ K) :
    ∀ j, (Rpair Hp Ht k l α).1.coeff j
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)) := by
  obtain ⟨heE1V, heE2V⟩ := eE_window (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  obtain ⟨hnegm, hnegd⟩ := eE1_neg_monic (α := α) (k := k)
    (fun i h1 h2 => hHp i h1 (by omega)) hl
  have hEeq : (eE1 Hp k l α) ^ 2 = (tS1 Hp k l α ^ 2 - eS2 Hp k l α) ^ 2 := by
    unfold eE1
    ring
  have hEneg : eE1 Hp k l α = -(tS1 Hp k l α ^ 2 - eS2 Hp k l α) := by
    unfold eE1
    ring
  have heE1d : (eE1 Hp k l α).natDegree = 2 ^ l := by
    rw [hEneg, natDegree_neg, hnegd]
  have hE2m : ((eE1 Hp k l α) ^ 2).Monic := by
    rw [hEeq]
    exact hnegm.pow 2
  have hE2d : ((eE1 Hp k l α) ^ 2).natDegree = 2 * 2 ^ l := by
    rw [hEeq, hnegm.natDegree_pow, hnegd]
  have hp21 : (2 : ℕ) ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hb0 : 2 * 2 ^ l + (k / 2 - 2) * 2 ^ (l + 1) = (k - 2) * 2 ^ l := by
    rw [hp21]
    have h1 : k / 2 - 2 + 2 = k / 2 := by omega
    have h2' : (k / 2 - 2) * (2 * 2 ^ l) + 2 * (2 * 2 ^ l) = (k / 2) * (2 * 2 ^ l) := by
      rw [← Nat.add_mul, h1]
    have h3 : (k / 2) * (2 * 2 ^ l) = k * 2 ^ l := by
      have : k / 2 * 2 = k := by omega
      calc (k / 2) * (2 * 2 ^ l) = (k / 2 * 2) * 2 ^ l := by ring
        _ = k * 2 ^ l := by rw [this]
    have h4 : (k - 2) * 2 ^ l + 2 * 2 ^ l = k * 2 ^ l := by
      have : k - 2 + 2 = k := by omega
      rw [← Nat.add_mul, this]
    omega
  intro j
  rw [Rpair_even_fst hpar (by omega) (by omega)]
  set γ := rSlot k l α (A := A) with hγ
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)) with hV
  rw [coeff_add, coeff_add]
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_
  · -- smul E-term
    rw [coeff_smul, nsmul_eq_mul]
    refine Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _)) ?_
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge ((k - 2) * 2 ^ l) x.2 with hgt | hle
    · rw [show (Hp l ^ (k - 2)).coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          rw [hMm.natDegree_pow, hMd]
          exact hgt), mul_zero]
      exact Subalgebra.zero_mem _
    · exact Subalgebra.mul_mem _ (heE1V (j + 1) x.1 (by omega))
        ((le_sup_left : K ≤ _) (coeff_mem_pow hMK (k - 2) x.2))
  · -- binTail term
    rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l) with hjb | hjb
    · have hsub : j + 1 ≤ (k - 2) * 2 ^ l := by omega
      refine SetLike.le_def.1 (sup_le_sup_left
        (adjoin_mono (Set.image_mono (Set.Ico_subset_Ico hsub le_rfl))) K) ?_
      refine coeff_mem_binTail (S := K ⊔ adjoin R (γ ''
        Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
        (fun i => (le_sup_left : K ≤ _) (coeff_mem_pow hMK 2 i))
        (fun i => heE1V ((k - 2) * 2 ^ l) i (by omega)) (k / 2) j
    · have hjbound : 2 * 2 ^ l + (k / 2 - 2) * 2 ^ (l + 1) ≤ j := by omega
      have hep' : 2 ^ l < 2 ^ (l + 1) := by
        have h1 : 1 ≤ (2 : ℕ) ^ l := Nat.one_le_pow _ _ (by omega)
        rw [hp21]
        omega
      refine (le_sup_left : K ≤ _) ?_
      exact binTail_coeff_high (p := 2 ^ (l + 1)) (e := 2 ^ l) (m := k / 2)
        (hMm.pow 2) (by rw [hMm.natDegree_pow, hMd, hp21])
        hE2m (by rw [hE2d]) (le_of_eq heE1d) hep' j hjbound
  · -- inner term
    rcases Nat.lt_or_ge ((k - 2) * 2 ^ l) j with hjgt | hjle
    · rw [show (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.coeff j = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · rcases eq_or_lt_of_le hjle with heqj | hjlt
      · rw [show j = (k - 2) * 2 ^ l from heqj]
        exact (le_sup_left : K ≤ _) htop
      · refine mem_sup_adjoin_pair ?_ ?_ (hin j)
        · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
          exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
        · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
          rw [← rSlot_even_inner hpar hk hg2]
          exact ⟨g, ⟨by omega, by omega⟩, rfl⟩

/-- Supports of the even-step remainder pair, second component. -/
theorem even_supp₂
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : k % 2 = 0) (hk : 4 ≤ k) (hl : 2 ≤ l) (h2 : IsUnit (2 : R))
    (hin : ∀ j, (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
            Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
        ⊔ adjoin R ((rSlot (k / 2) (l + 1) α (A := A)) ''
          Set.Ico j ((k - 2) * 2 ^ l)))
    (hind : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.natDegree ≤ (k - 2) * 2 ^ l) :
    ∀ j, (Rpair Hp Ht k l α).2.coeff j
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico j ((k - 1) * 2 ^ l)) := by
  obtain ⟨heE1V, heE2V⟩ := eE_window (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨hnegm, hnegd⟩ := eE2_neg_monic (α := α) (k := k)
    (fun i h1 h2 => hHp i h1 (by omega)) hl
  have hEeq : (eE2 Hp k l α) ^ 2
      = (tS1t Hp k l α ^ 2 - C (α ((k - 2) * 2 ^ l))) ^ 2 := by
    unfold eE2
    ring
  have hEneg : eE2 Hp k l α = -(tS1t Hp k l α ^ 2 - C (α ((k - 2) * 2 ^ l))) := by
    unfold eE2
    ring
  have heE2d : (eE2 Hp k l α).natDegree = 2 ^ l := by
    rw [hEneg, natDegree_neg, hnegd]
  have hE2m : ((eE2 Hp k l α) ^ 2).Monic := by
    rw [hEeq]
    exact hnegm.pow 2
  have hE2d : ((eE2 Hp k l α) ^ 2).natDegree = 2 * 2 ^ l := by
    rw [hEeq, hnegm.natDegree_pow, hnegd]
  have hp21 : (2 : ℕ) ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hb0 : 2 * 2 ^ l + (k / 2 - 2) * 2 ^ (l + 1) = (k - 2) * 2 ^ l := by
    rw [hp21]
    have h1 : k / 2 - 2 + 2 = k / 2 := by omega
    have h2' : (k / 2 - 2) * (2 * 2 ^ l) + 2 * (2 * 2 ^ l) = (k / 2) * (2 * 2 ^ l) := by
      rw [← Nat.add_mul, h1]
    have h3 : (k / 2) * (2 * 2 ^ l) = k * 2 ^ l := by
      have : k / 2 * 2 = k := by omega
      calc (k / 2) * (2 * 2 ^ l) = (k / 2 * 2) * 2 ^ l := by ring
        _ = k * 2 ^ l := by rw [this]
    have h4 : (k - 2) * 2 ^ l + 2 * 2 ^ l = k * 2 ^ l := by
      have : k - 2 + 2 = k := by omega
      rw [← Nat.add_mul, this]
    omega
  intro j
  rw [Rpair_even_snd hpar (by omega) (by omega)]
  set γ := rSlot k l α (A := A) with hγ
  set V := K ⊔ adjoin R (γ '' Set.Ico j ((k - 1) * 2 ^ l)) with hV
  rw [coeff_add, coeff_add]
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_
  · rw [coeff_smul, nsmul_eq_mul]
    refine Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _)) ?_
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge ((k - 2) * 2 ^ l) x.2 with hgt | hle
    · rw [show (Ht ^ (k - 2)).coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          rw [hHt.natDegree_pow, hdHt]
          exact hgt), mul_zero]
      exact Subalgebra.zero_mem _
    · exact Subalgebra.mul_mem _ (heE2V j x.1 (by omega))
        ((le_sup_left : K ≤ _) (coeff_mem_pow hKt (k - 2) x.2))
  · rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l) with hjb | hjb
    · have hsub : j ≤ (k - 2) * 2 ^ l := by omega
      refine SetLike.le_def.1 (sup_le_sup_left
        (adjoin_mono (Set.image_mono (Set.Ico_subset_Ico hsub le_rfl))) K) ?_
      refine coeff_mem_binTail (S := K ⊔ adjoin R (γ ''
        Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
        (fun i => (le_sup_left : K ≤ _) (coeff_mem_pow hKt 2 i))
        (fun i => heE2V ((k - 2) * 2 ^ l) i (by omega)) (k / 2) j
    · have hjbound : 2 * 2 ^ l + (k / 2 - 2) * 2 ^ (l + 1) ≤ j := by omega
      have hep' : 2 ^ l < 2 ^ (l + 1) := by
        have h1 : 1 ≤ (2 : ℕ) ^ l := Nat.one_le_pow _ _ (by omega)
        rw [hp21]
        omega
      refine (le_sup_left : K ≤ _) ?_
      exact binTail_coeff_high (p := 2 ^ (l + 1)) (e := 2 ^ l) (m := k / 2)
        (hHt.pow 2) (by rw [hHt.natDegree_pow, hdHt, hp21])
        hE2m (by rw [hE2d]) (le_of_eq heE2d) hep' j hjbound
  · rcases Nat.lt_or_ge ((k - 2) * 2 ^ l) j with hjgt | hjle
    · rw [show (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.coeff j = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · refine mem_sup_adjoin_pair ?_ ?_ (hin j)
      · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
        exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
      · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
        rw [← rSlot_even_inner hpar hk hg2]
        exact ⟨g, ⟨by omega, by omega⟩, rfl⟩


/-- Low rows of the even-step certificate: the inner pivot passes through, with the
correction terms strictly windowed. -/
theorem even_pivot_low
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : k % 2 = 0) (hk : 4 ≤ k) (hl : 2 ≤ l) (h2 : IsUnit (2 : R))
    (hin : CoeffTriangular (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
        Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
      (rSlot (k / 2) (l + 1) α)
      (fun j => ((tLam (k / 2) (l + 1) j : ℤ) : R)) ((k - 2) * 2 ^ l)
      (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1
      (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2) :
    ∀ j, j < (k - 2) * 2 ^ l → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k l α (A := A)) '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)),
      (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff j
        = algebraMap R A (((tLam k l j : ℤ) : R)) * (rSlot k l α (A := A)) j + F := by
  obtain ⟨heE1V, heE2V⟩ := eE_window (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  intro j hj
  set γ := rSlot k l α (A := A) with hγ
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)) with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  -- strict-window memberships of the correction terms
  have hA₁V : ∀ m, m + 1 ≤ j → j < (k - 2) * 2 ^ l →
      ((k / 2) • (eE1 Hp k l α * Hp l ^ (k - 2))).coeff m ∈ V := by
    intro m hm hjb
    rw [coeff_smul, nsmul_eq_mul]
    refine Subalgebra.mul_mem _ (hKV _ (Subalgebra.natCast_mem _ _)) ?_
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge ((k - 2) * 2 ^ l) x.2 with hgt | hle
    · rw [show (Hp l ^ (k - 2)).coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by rw [hMm.natDegree_pow, hMd]; exact hgt),
        mul_zero]
      exact Subalgebra.zero_mem _
    · exact Subalgebra.mul_mem _ (heE1V (j + 1) x.1 (by omega))
        (hKV _ (coeff_mem_pow hMK (k - 2) x.2))
  have hA₂V : ∀ m, m ≤ j → j < (k - 2) * 2 ^ l →
      ((k / 2) • (eE2 Hp k l α * Ht ^ (k - 2))).coeff m ∈ V := by
    intro m hm hjb
    rw [coeff_smul, nsmul_eq_mul]
    refine Subalgebra.mul_mem _ (hKV _ (Subalgebra.natCast_mem _ _)) ?_
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge ((k - 2) * 2 ^ l) x.2 with hgt | hle
    · rw [show (Ht ^ (k - 2)).coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by rw [hHt.natDegree_pow, hdHt]; exact hgt),
        mul_zero]
      exact Subalgebra.zero_mem _
    · exact Subalgebra.mul_mem _ (heE2V (j + 1) x.1 (by omega))
        (hKV _ (coeff_mem_pow hKt (k - 2) x.2))
  have hB₁V : ∀ m, m < (k - 2) * 2 ^ l → j < (k - 2) * 2 ^ l →
      (binTail (Hp l ^ 2) (eE1 Hp k l α) (k / 2)).coeff m ∈ V := by
    intro m hm hjb
    refine SetLike.le_def.1 (sup_le_sup_left
      (adjoin_mono (Set.image_mono (Set.Ico_subset_Ico
        (show j + 1 ≤ (k - 2) * 2 ^ l from by omega) le_rfl))) K) ?_
    exact coeff_mem_binTail (S := K ⊔ adjoin R (γ ''
        Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
      (fun i => (le_sup_left : K ≤ _) (coeff_mem_pow hMK 2 i))
      (fun i => heE1V ((k - 2) * 2 ^ l) i (by omega)) (k / 2) m
  have hB₂V : ∀ m, m < (k - 2) * 2 ^ l → j < (k - 2) * 2 ^ l →
      (binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2)).coeff m ∈ V := by
    intro m hm hjb
    refine SetLike.le_def.1 (sup_le_sup_left
      (adjoin_mono (Set.image_mono (Set.Ico_subset_Ico
        (show j + 1 ≤ (k - 2) * 2 ^ l from by omega) le_rfl))) K) ?_
    exact coeff_mem_binTail (S := K ⊔ adjoin R (γ ''
        Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
      (fun i => (le_sup_left : K ≤ _) (coeff_mem_pow hKt 2 i))
      (fun i => heE2V ((k - 2) * 2 ^ l) i (by omega)) (k / 2) m
  -- inner pivot and its transport
  obtain ⟨F', hF', hFe⟩ := hin.pivot j hj
  have hF'V : F' ∈ V := by
    rw [hV]
    refine mem_sup_adjoin_pair ?_ ?_ hF'
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      rw [← rSlot_even_inner hpar hk hg2]
      exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
  -- assemble by cases on the row
  cases j with
  | zero =>
    refine ⟨((k / 2) • (eE2 Hp k l α * Ht ^ (k - 2))).coeff 0
      + (binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2)).coeff 0 + F', ?_, ?_⟩
    · exact Subalgebra.add_mem _ (Subalgebra.add_mem _
        (hA₂V 0 le_rfl hj) (hB₂V 0 (by omega) hj)) hF'V
    · rw [coeff_combined_zero] at hFe ⊢
      rw [show (Rpair Hp Ht k l α).2
          = (k / 2) • (eE2 Hp k l α * Ht ^ (k - 2))
            + binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2)
            + (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
                (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2
          from Rpair_even_snd hpar (by omega) (by omega),
        coeff_add, coeff_add, hFe, tLam_even_inner hpar hk hj, hγ,
        rSlot_even_inner hpar hk hj]
      ring
  | succ t =>
    have hcO : (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff (t + 1)
        = (Rpair Hp Ht k l α).1.coeff t + (Rpair Hp Ht k l α).2.coeff (t + 1) :=
      coeff_combined _ _ t
    have hcI : (combined
        (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
          (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1
        (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
          (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2).coeff (t + 1)
        = _ + _ := coeff_combined _ _ t
    refine ⟨((k / 2) • (eE1 Hp k l α * Hp l ^ (k - 2))).coeff t
      + (binTail (Hp l ^ 2) (eE1 Hp k l α) (k / 2)).coeff t
      + (((k / 2) • (eE2 Hp k l α * Ht ^ (k - 2))).coeff (t + 1)
        + (binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2)).coeff (t + 1)) + F', ?_, ?_⟩
    · exact Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
        (hA₁V t (by omega) hj) (hB₁V t (by omega) hj))
        (Subalgebra.add_mem _ (hA₂V (t + 1) le_rfl hj) (hB₂V (t + 1) (by omega) hj)))
        hF'V
    · rw [hcO,
        show (Rpair Hp Ht k l α).1
          = (k / 2) • (eE1 Hp k l α * Hp l ^ (k - 2))
            + binTail (Hp l ^ 2) (eE1 Hp k l α) (k / 2)
            + (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
                (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1
          from Rpair_even_fst hpar (by omega) (by omega),
        show (Rpair Hp Ht k l α).2
          = (k / 2) • (eE2 Hp k l α * Ht ^ (k - 2))
            + binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2)
            + (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
                (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2
          from Rpair_even_snd hpar (by omega) (by omega),
        coeff_add, coeff_add, coeff_add, coeff_add]
      rw [coeff_combined] at hFe
      rw [tLam_even_inner hpar hk hj, hγ, rSlot_even_inner hpar hk hj]
      linear_combination hFe
omit [Nontrivial A] in
/-- Sub-high coefficients of `binTail` are known when the block's top coefficients are. -/
theorem binTail_coeff_subhigh {K : Subalgebra R A} {P E : A[X]} {p e m : ℕ}
    (hPd : P.natDegree ≤ p) (hPK : ∀ i, P.coeff i ∈ K)
    (hEd : E.natDegree ≤ e) (hEK : ∀ i, e - 1 ≤ i → E.coeff i ∈ K)
    (hgap : e + 2 ≤ p) :
    ∀ j, 2 * e + (m - 2) * p - 1 ≤ j → (binTail P E m).coeff j ∈ K := by
  intro j hj
  show (∑ q ∈ Finset.Icc 2 m, E ^ q * P ^ (m - q) * ((m.choose q : ℕ) : A[X])).coeff j
    ∈ K
  rw [Polynomial.finset_sum_coeff]
  refine Subalgebra.sum_mem _ fun q hq => ?_
  obtain ⟨hq2, hqm⟩ := Finset.mem_Icc.1 hq
  rw [← Polynomial.C_eq_natCast, coeff_mul_C]
  refine Subalgebra.mul_mem _ ?_ (Subalgebra.natCast_mem _ _)
  rcases Nat.lt_or_ge 2 q with hq3 | hq3
  · -- q ≥ 3 vanishes below the sub-high line
    obtain ⟨d, rfl⟩ : ∃ d, q = d + 3 := ⟨q - 3, by omega⟩
    have h1 : (E ^ (d + 3) * P ^ (m - (d + 3))).natDegree
        ≤ (d + 3) * e + (m - (d + 3)) * p := by
      refine le_trans (natDegree_mul_le) ?_
      have he : (E ^ (d + 3)).natDegree ≤ (d + 3) * e :=
        le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hEd)
      have hp : (P ^ (m - (d + 3))).natDegree ≤ (m - (d + 3)) * p :=
        le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hPd)
      omega
    have hb1 : (d + 3) * e = (d + 1) * e + 2 * e := by ring
    have hb2 : (m - 2) * p = (m - (d + 3)) * p + (d + 1) * p := by
      have hmd : m - 2 = (m - (d + 3)) + (d + 1) := by omega
      rw [hmd, Nat.add_mul]
    have hbe : (d + 1) * (e + 2) = (d + 1) * e + (d + 1) * 2 := by ring
    have hle : (d + 1) * (e + 2) ≤ (d + 1) * p := Nat.mul_le_mul_left _ hgap
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Subalgebra.zero_mem _
  · -- q = 2: expand the square against the known window
    have hq2' : q = 2 := by omega
    subst hq2'
    have hE2K : ∀ a, 2 * e - 1 ≤ a → (E ^ 2).coeff a ∈ K := by
      intro a ha
      rw [sq, coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = a := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge e x.1 with hgt1 | hle1
      · rw [show E.coeff x.1 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
          zero_mul]
        exact Subalgebra.zero_mem _
      · rcases Nat.lt_or_ge e x.2 with hgt2 | hle2
        · rw [show E.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
            mul_zero]
          exact Subalgebra.zero_mem _
        · exact Subalgebra.mul_mem _ (hEK x.1 (by omega)) (hEK x.2 (by omega))
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (2 * e) x.1 with hgt1 | hle1
    · rw [show (E ^ 2).coeff x.1 = 0 from coeff_eq_zero_of_natDegree_lt (by
        have : (E ^ 2).natDegree ≤ 2 * e :=
          le_trans natDegree_pow_le (by omega)
        omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge ((m - 2) * p) x.2 with hgt2 | hle2
      · rw [show (P ^ (m - 2)).coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by
          have : (P ^ (m - 2)).natDegree ≤ (m - 2) * p :=
            le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hPd)
          omega), mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hE2K x.1 (by omega))
          (coeff_mem_pow hPK (m - 2) x.2)

/-- Band rows of the even-step certificate, via the shift engine on the correction
pair. -/
theorem even_pivot_band
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : k % 2 = 0) (hk : 4 ≤ k) (hl : 2 ≤ l) (h2 : IsUnit (2 : R))
    (hind₁ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.natDegree ≤ (k - 2) * 2 ^ l)
    (hind₂ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.natDegree ≤ (k - 2) * 2 ^ l)
    (htop₁₁ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.coeff ((k - 2) * 2 ^ l) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.coeff ((k - 2) * 2 ^ l - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.coeff ((k - 2) * 2 ^ l) ∈ K) :
    ∀ j, (k - 2) * 2 ^ l ≤ j → j < (k - 1) * 2 ^ l → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k l α (A := A)) '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)),
      (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff j
        = algebraMap R A (((tLam k l j : ℤ) : R)) * (rSlot k l α (A := A)) j + F := by
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  have hcert := eE_cert (Hp := Hp) (α := α) (k := k)
    (fun i h1 h2 => hHp i h1 (by omega)) hl h2
  obtain ⟨hneg1m, hneg1d⟩ := eE1_neg_monic (α := α) (k := k)
    (fun i h1 h2 => hHp i h1 (by omega)) hl
  obtain ⟨hneg2m, hneg2d⟩ := eE2_neg_monic (α := α) (k := k)
    (fun i h1 h2 => hHp i h1 (by omega)) hl
  have hE1neg : eE1 Hp k l α = -(tS1 Hp k l α ^ 2 - eS2 Hp k l α) := by
    unfold eE1
    ring
  have hE2neg : eE2 Hp k l α = -(tS1t Hp k l α ^ 2 - C (α ((k - 2) * 2 ^ l))) := by
    unfold eE2
    ring
  have heE1d : (eE1 Hp k l α).natDegree = 2 ^ l := by rw [hE1neg, natDegree_neg, hneg1d]
  have heE2d : (eE2 Hp k l α).natDegree = 2 ^ l := by rw [hE2neg, natDegree_neg, hneg2d]
  have heE1K : ∀ i, 2 ^ l - 1 ≤ i → (eE1 Hp k l α).coeff i ∈ K := by
    intro i hi
    refine mem_of_sup_adjoin_empty ?_ (hcert.supp₁ i)
    rw [Set.image_eq_empty]
    exact Set.Ico_eq_empty (by omega)
  have heE2K : ∀ i, 2 ^ l ≤ i → (eE2 Hp k l α).coeff i ∈ K := by
    intro i hi
    refine mem_of_sup_adjoin_empty ?_ (hcert.supp₂ i)
    rw [Set.image_eq_empty]
    exact Set.Ico_eq_empty (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hp21 : (2 : ℕ) ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  have hb0 : 2 * 2 ^ l + (k / 2 - 2) * 2 ^ (l + 1) = (k - 2) * 2 ^ l := by
    rw [hp21]
    have h1 : k / 2 - 2 + 2 = k / 2 := by omega
    have h2' : (k / 2 - 2) * (2 * 2 ^ l) + 2 * (2 * 2 ^ l) = (k / 2) * (2 * 2 ^ l) := by
      rw [← Nat.add_mul, h1]
    have h3 : (k / 2) * (2 * 2 ^ l) = k * 2 ^ l := by
      have : k / 2 * 2 = k := by omega
      calc (k / 2) * (2 * 2 ^ l) = (k / 2 * 2) * 2 ^ l := by ring
        _ = k * 2 ^ l := by rw [this]
    have h4 : (k - 2) * 2 ^ l + 2 * 2 ^ l = k * 2 ^ l := by
      have : k - 2 + 2 = k := by omega
      rw [← Nat.add_mul, this]
    omega
  -- the shift engine on the correction pair
  have hL₁m : (Hp l ^ (k - 2)).Monic := hMm.pow _
  have hL₂m : (Ht ^ (k - 2)).Monic := hHt.pow _
  have hL₁d : (Hp l ^ (k - 2)).natDegree = (k - 2) * 2 ^ l := by
    rw [hMm.natDegree_pow, hMd]
  have hL₂d : (Ht ^ (k - 2)).natDegree = (k - 2) * 2 ^ l := by
    rw [hHt.natDegree_pow, hdHt]
  intro j hj1 hj2
  obtain ⟨t', rfl⟩ : ∃ t', j = (k - 2) * 2 ^ l + t' := ⟨j - (k - 2) * 2 ^ l, by omega⟩
  have ht' : t' < 2 ^ l := by omega
  obtain ⟨F₀, hF₀, hsheq⟩ := CoeffTriangular.shift_pivot hcert (by omega : 1 ≤ (k - 2) * 2 ^ l)
    hL₁m hL₁d hL₂m hL₂d (fun i => coeff_mem_pow hMK (k - 2) i)
    (fun i => coeff_mem_pow hKt (k - 2) i) t' ht'
  set γ := rSlot k l α (A := A) with hγ
  set V := K ⊔ adjoin R (γ '' Set.Ico ((k - 2) * 2 ^ l + t' + 1) ((k - 1) * 2 ^ l))
    with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  have hF₀V : F₀ ∈ V := by
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF₀
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    rw [← rSlot_even_band_eq hpar hk hl]
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨(k - 2) * 2 ^ l + g, ⟨by omega, by omega⟩, rfl⟩)
  -- known parts
  have hp4 : (4 : ℕ) ≤ 2 ^ l := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 from by omega) (show 2 ≤ l from hl)
    have h2e : (2 : ℕ) ^ 2 = 4 := by norm_num
    omega
  have hgap' : 2 ^ l + 2 ≤ 2 ^ (l + 1) := by rw [hp21]; omega
  have hB₁K : (binTail (Hp l ^ 2) (eE1 Hp k l α) (k / 2)).coeff
      ((k - 2) * 2 ^ l + t' - 1) ∈ K := by
    have hbnd₁ : 2 * 2 ^ l + (k / 2 - 2) * 2 ^ (l + 1) - 1
        ≤ (k - 2) * 2 ^ l + t' - 1 := by omega
    exact binTail_coeff_subhigh (p := 2 ^ (l + 1)) (e := 2 ^ l) (m := k / 2)
      (by rw [hMm.natDegree_pow, hMd, hp21]) (coeff_mem_pow hMK 2)
      (le_of_eq heE1d) heE1K hgap' ((k - 2) * 2 ^ l + t' - 1) hbnd₁
  have hB₂K : (binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2)).coeff
      ((k - 2) * 2 ^ l + t') ∈ K := by
    have hE2m : ((eE2 Hp k l α) ^ 2).Monic := by
      have : (eE2 Hp k l α) ^ 2 = (tS1t Hp k l α ^ 2 - C (α ((k - 2) * 2 ^ l))) ^ 2 := by
        unfold eE2
        ring
      rw [this]
      exact hneg2m.pow 2
    have hE2d : ((eE2 Hp k l α) ^ 2).natDegree = 2 * 2 ^ l := by
      have : (eE2 Hp k l α) ^ 2 = (tS1t Hp k l α ^ 2 - C (α ((k - 2) * 2 ^ l))) ^ 2 := by
        unfold eE2
        ring
      rw [this, hneg2m.natDegree_pow, hneg2d]
    have hep' : 2 ^ l < 2 ^ (l + 1) := by rw [hp21]; omega
    exact binTail_coeff_high (p := 2 ^ (l + 1)) (e := 2 ^ l) (m := k / 2)
      (hHt.pow 2) (by rw [hHt.natDegree_pow, hdHt, hp21])
      hE2m (by rw [hE2d]) (le_of_eq heE2d) hep' _ (by omega)
  have hI₁K : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
      (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.coeff
      ((k - 2) * 2 ^ l + t' - 1) ∈ K := by
    rcases Nat.lt_or_ge ((k - 2) * 2 ^ l) ((k - 2) * 2 ^ l + t' - 1) with hgt | hle
    · have hz : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
          (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.natDegree
          < (k - 2) * 2 ^ l + t' - 1 := by omega
      rw [coeff_eq_zero_of_natDegree_lt hz]
      exact Subalgebra.zero_mem _
    · rcases (by omega : (k - 2) * 2 ^ l + t' - 1 = (k - 2) * 2 ^ l
          ∨ (k - 2) * 2 ^ l + t' - 1 = (k - 2) * 2 ^ l - 1) with heq | heq
      · rw [heq]
        exact htop₁₁
      · rw [heq]
        exact htop₁₂
  have hI₂K : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
      (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.coeff
      ((k - 2) * 2 ^ l + t') ∈ K := by
    rcases Nat.eq_zero_or_pos t' with rfl | ht'p
    · rw [Nat.add_zero]
      exact htop₂₁
    · have hz : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
          (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.natDegree
          < (k - 2) * 2 ^ l + t' := by omega
      rw [coeff_eq_zero_of_natDegree_lt hz]
      exact Subalgebra.zero_mem _
  -- slope and slot bridges
  have hslot : γ ((k - 2) * 2 ^ l + t')
      = rSlot 2 l (fun j => α ((k - 2) * 2 ^ l + j)) t' :=
    rSlot_even_band_eq hpar hk hl
  have hslope : algebraMap R A (((tLam k l ((k - 2) * 2 ^ l + t') : ℤ) : R))
      = ((k / 2 : ℕ) : A) * algebraMap R A (((tLam 2 l t' : ℤ) : R)) := by
    rcases Nat.lt_or_ge t' (2 ^ (l - 1)) with hmid | hhi
    · rw [tLam_even_mid hpar hk (by omega) (by omega), tLam_two_lo hmid,
        Int.cast_natCast, map_natCast, Int.cast_one, map_one, mul_one]
    · rw [tLam_even_hi hpar hk (by omega), tLam_two_hi hhi]
      have hcast : ((k / 2 : ℕ) : A) * 2 = ((k : ℕ) : A) := by
        have hnat : k / 2 * 2 = k := by omega
        calc ((k / 2 : ℕ) : A) * 2 = ((k / 2 * 2 : ℕ) : A) := by push_cast; ring
          _ = _ := by rw [hnat]
      rw [show (((-(k : ℕ) : ℤ) : R)) = -(((k : ℕ) : ℤ) : R) from by push_cast; ring,
        show (((-2 : ℤ)) : R) = -(((2 : ℕ) : ℤ) : R) from by push_cast; ring,
        map_neg, map_neg, Int.cast_natCast, Int.cast_natCast, map_natCast,
        map_natCast]
      rw [show ((2 : ℕ) : A) = (2 : A) from by norm_num]
      calc -((k : ℕ) : A) = -(((k / 2 : ℕ) : A) * 2) := by rw [hcast]
        _ = ((k / 2 : ℕ) : A) * -2 := by ring
  -- coefficient decomposition
  have hj1' : 1 ≤ (k - 2) * 2 ^ l + t' := by omega
  have hcO : (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff
      ((k - 2) * 2 ^ l + t')
      = (Rpair Hp Ht k l α).1.coeff ((k - 2) * 2 ^ l + t' - 1)
        + (Rpair Hp Ht k l α).2.coeff ((k - 2) * 2 ^ l + t') := by
    obtain ⟨s, hs⟩ : ∃ s, (k - 2) * 2 ^ l + t' = s + 1 :=
      ⟨(k - 2) * 2 ^ l + t' - 1, by omega⟩
    rw [hs, coeff_combined, Nat.add_sub_cancel]
  have hcL : (combined (Hp l ^ (k - 2) * eE1 Hp k l α)
      (Ht ^ (k - 2) * eE2 Hp k l α)).coeff ((k - 2) * 2 ^ l + t')
      = (Hp l ^ (k - 2) * eE1 Hp k l α).coeff ((k - 2) * 2 ^ l + t' - 1)
        + (Ht ^ (k - 2) * eE2 Hp k l α).coeff ((k - 2) * 2 ^ l + t') := by
    obtain ⟨s, hs⟩ : ∃ s, (k - 2) * 2 ^ l + t' = s + 1 :=
      ⟨(k - 2) * 2 ^ l + t' - 1, by omega⟩
    rw [hs, coeff_combined, Nat.add_sub_cancel]
  refine ⟨((k / 2 : ℕ) : A) * F₀
    + ((binTail (Hp l ^ 2) (eE1 Hp k l α) (k / 2)).coeff ((k - 2) * 2 ^ l + t' - 1)
      + (binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2)).coeff ((k - 2) * 2 ^ l + t')
      + (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
          (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.coeff
          ((k - 2) * 2 ^ l + t' - 1)
      + (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
          (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.coeff
          ((k - 2) * 2 ^ l + t')), ?_, ?_⟩
  · exact Subalgebra.add_mem _
      (Subalgebra.mul_mem _ (hKV _ (Subalgebra.natCast_mem _ _)) hF₀V)
      (hKV _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
        hB₁K hB₂K) hI₁K) hI₂K))
  · rw [hcO,
      show (Rpair Hp Ht k l α).1
        = (k / 2) • (eE1 Hp k l α * Hp l ^ (k - 2))
          + binTail (Hp l ^ 2) (eE1 Hp k l α) (k / 2)
          + (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
              (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1
        from Rpair_even_fst hpar (by omega) (by omega),
      show (Rpair Hp Ht k l α).2
        = (k / 2) • (eE2 Hp k l α * Ht ^ (k - 2))
          + binTail (Ht ^ 2) (eE2 Hp k l α) (k / 2)
          + (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
              (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2
        from Rpair_even_snd hpar (by omega) (by omega),
      coeff_add, coeff_add, coeff_add, coeff_add, coeff_smul, coeff_smul,
      nsmul_eq_mul, nsmul_eq_mul, hslope, hslot,
      mul_comm (eE1 Hp k l α) (Hp l ^ (k - 2)),
      mul_comm (eE2 Hp k l α) (Ht ^ (k - 2))]
    rw [hcL] at hsheq
    linear_combination ((k / 2 : ℕ) : A) * hsheq

/-- **`lem:Rk2l`(3), even main step**: the stage-table certificate propagates through
one even halving. -/
theorem Rk2l_tri_even_step
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : k % 2 = 0) (hk : 4 ≤ k) (hl : 2 ≤ l)
    (h2 : IsUnit (2 : R)) (hu2 : IsUnit (((k / 2 : ℕ) : ℤ) : R))
    (huk : IsUnit (((k : ℕ) : ℤ) : R))
    (hin : CoeffTriangular (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
        Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
      (rSlot (k / 2) (l + 1) α)
      (fun j => ((tLam (k / 2) (l + 1) j : ℤ) : R)) ((k - 2) * 2 ^ l)
      (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1
      (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2)
    (hind₁ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.natDegree ≤ (k - 2) * 2 ^ l)
    (hind₂ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.natDegree ≤ (k - 2) * 2 ^ l)
    (htop₁₁ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.coeff ((k - 2) * 2 ^ l) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).1.coeff ((k - 2) * 2 ^ l - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp (l + 1) (evenH Hp k l α))
        (evenHt Hp Ht k l α) (k / 2) (l + 1) α).2.coeff ((k - 2) * 2 ^ l) ∈ K) :
    CoeffTriangular K (rSlot k l α) (fun j => ((tLam k l j : ℤ) : R))
      ((k - 1) * 2 ^ l) (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2 where
  unit j hj := by
    rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l) with hlow | hband
    · rw [tLam_even_inner hpar hk hlow]
      exact hin.unit j hlow
    · rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l + 2 ^ (l - 1)) with hmid | hhi
      · rw [tLam_even_mid hpar hk hband hmid]
        exact hu2
      · rw [tLam_even_hi hpar hk hhi,
          show ((((-(k : ℕ) : ℤ)) : R)) = -(((k : ℕ) : ℤ) : R) from by push_cast; ring]
        exact huk.neg
  supp₁ := even_supp₁ hHp hpar hk hl h2 (fun j => hin.supp₁ j) hind₁ htop₁₁
  supp₂ := even_supp₂ hHp hHt hdHt hKt hpar hk hl h2 (fun j => hin.supp₂ j) hind₂
  pivot j hj := by
    rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l) with hlow | hband
    · exact even_pivot_low hHp hHt hdHt hKt hpar hk hl h2 hin j hlow
    · exact even_pivot_band hHp hHt hdHt hKt hpar hk hl h2 hind₁ hind₂
        htop₁₁ htop₁₂ htop₂₁ j hband hj

end FastPoly
