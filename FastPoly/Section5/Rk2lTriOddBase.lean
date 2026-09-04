import FastPoly.Section5.Rk2lTriOdd

/-!
# `lem:Rk2l`(3): the shared odd base branch (`l = 2`)

The base certificate mirrors the odd main branch at `(D, r) = (4, 2)`: a `Q₃` head
(rows `0..3`, slope `1`), inherited inner rows `[4, 4(k-2))`, the 3-row `G`-pair band
(slopes `(k-1)/2, (k-1)/2, -(k-1)`), and the principal `u`-pivot at the top row
(slope `-k(k-1)`).  The scalar-difference hypothesis `Ht - H₄ = C ρ` enters exactly
where the tilde-side multiplier must be monic.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {Hp : ℕ → A[X]} {Ht : A[X]} {k : ℕ} {α : ℕ → A}

/-! ### Value lemmas at the odd base `l = 2` -/

omit [Nontrivial A] in
theorem rSlot_ob_low (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) {r : ℕ} (hr : r < 4) :
    rSlot (A := A) k 2 α r = α r := by
  show rSlotF k k 2 α r = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar,
    if_pos (by omega), if_pos hr]

omit [Nontrivial A] in
theorem rSlot_ob_inner (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) {r : ℕ}
    (h1 : 4 ≤ r) (h2 : r < 4 * (k - 2)) :
    rSlot (A := A) k 2 α r = rSlot ((k - 1) / 2) 3 (fun j => α (4 + j)) (r - 4) := by
  show rSlotF k k 2 α r = rSlotF ((k - 1) / 2) ((k - 1) / 2) 3 _ (r - 4)
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar,
    if_pos (by omega), if_neg (Nat.not_lt.mpr h1), if_pos h2]
  exact rSlotF_fuel ((f + 1 - 1) / 2) f ((f + 1 - 1) / 2) (by omega) (by omega) 3 _ (r - 4)

omit [Nontrivial A] in
theorem rSlot_ob_band (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) {r : ℕ}
    (hr : 4 * (k - 2) ≤ r) :
    rSlot (A := A) k 2 α r = α r := by
  show rSlotF k k 2 α r = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar,
    if_pos (by omega), if_neg (by omega), if_neg (Nat.not_lt.mpr hr)]

theorem tLam_ob_low (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) {j : ℕ} (hj : j < 4) :
    tLam k 2 j = 1 := by
  show tLamF k k 2 j = 1
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_pos (by omega), if_pos hj]

theorem tLam_ob_inner (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) {j : ℕ}
    (h1 : 4 ≤ j) (h2 : j < 4 * (k - 2)) :
    tLam k 2 j = tLam ((k - 1) / 2) 3 (j - 4) := by
  show tLamF k k 2 j = tLamF ((k - 1) / 2) ((k - 1) / 2) 3 (j - 4)
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_pos (by omega),
    if_neg (Nat.not_lt.mpr h1), if_pos h2]
  exact tLamF_fuel ((f + 1 - 1) / 2) f ((f + 1 - 1) / 2) (by omega) (by omega) 3 (j - 4)

theorem tLam_ob_mid (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) {j : ℕ}
    (h1 : 4 * (k - 2) ≤ j) (h2 : j < 4 * (k - 2) + 2) :
    tLam k 2 j = (((k - 1) / 2 : ℕ) : ℤ) := by
  show tLamF k k 2 j = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_pos (by omega),
    if_neg (by omega), if_neg (Nat.not_lt.mpr h1), if_pos h2]

theorem tLam_ob_v (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) {j : ℕ}
    (h1 : 4 * (k - 2) + 2 ≤ j) (h2 : j < 4 * (k - 2) + 3) :
    tLam k 2 j = -(((k - 1 : ℕ)) : ℤ) := by
  show tLamF k k 2 j = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_pos (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (Nat.not_lt.mpr h1), if_pos h2]

theorem tLam_ob_hi (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) {j : ℕ}
    (h1 : 4 * (k - 2) + 3 ≤ j) :
    tLam k 2 j = -(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ)) := by
  show tLamF k k 2 j = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_pos (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (Nat.not_lt.mpr h1)]

/-! ### Block certificates at the base -/

/-- One-row certificate for `S₁ = H₂ + (x + u)` at the base offsets. -/
theorem obS1_block_cert
    (h1 : (Hp 1).Monic ∧ (Hp 1).natDegree = 2 ∧ (∀ j, (Hp 1).coeff j ∈ K)) :
    CoeffTriangular K (fun _ => α (4 * (k - 2) + 3)) (fun _ => (1 : R)) 1 0
      (obS1 Hp k α - X ^ 2) := by
  obtain ⟨hm, hd, hK⟩ := h1
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  have hco : ∀ j, (obS1 Hp k α - X ^ 2).coeff j
      = ((Hp 1).coeff j - (X ^ 2 : A[X]).coeff j + (X : A[X]).coeff j)
        + (C (α (4 * (k - 2) + 3)) : A[X]).coeff j := by
    intro j
    show (Hp 1 + (X + C (α (4 * (k - 2) + 3))) - X ^ 2).coeff j = _
    rw [coeff_sub, coeff_add, coeff_add]
    ring
  have hKp : ∀ j, (Hp 1).coeff j - (X ^ 2 : A[X]).coeff j + (X : A[X]).coeff j ∈ K := by
    intro j
    refine Subalgebra.add_mem _ (Subalgebra.sub_mem _ (hK j) ?_) ?_
    · rw [coeff_X_pow]
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · rw [Polynomial.coeff_X]
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
  refine
    { unit := fun j hj => isUnit_one
      supp₁ := fun j => by rw [coeff_zero]; exact Subalgebra.zero_mem _
      supp₂ := ?_
      pivot := ?_ }
  · intro j
    rw [hco]
    refine Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hKp j)) ?_
    rw [coeff_C]
    split
    · rename_i hj0
      subst hj0
      exact (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨0, ⟨le_rfl, by omega⟩, rfl⟩)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro j hj
    match j, hj with
    | 0, _ =>
      refine ⟨(Hp 1).coeff 0 - (X ^ 2 : A[X]).coeff 0 + (X : A[X]).coeff 0,
        (le_sup_left : K ≤ _) (hKp 0), ?_⟩
      rw [hcomb0, hco, coeff_C_zero, map_one, one_mul]
      ring

/-! ### The base correction pair certificate (3 rows) -/

theorem obG_coeff (j : ℕ) :
    (obG k α).coeff j
      = (C (α (4 * (k - 2) + 1)) : A[X]).coeff j
        - ((X ^ 2 : A[X]).coeff j
          + ((C (α (4 * (k - 2) + 2)) * X : A[X]).coeff j
            + (C (α (4 * (k - 2) + 2)) * X : A[X]).coeff j)
          + (C (α (4 * (k - 2) + 2)) * C (α (4 * (k - 2) + 2)) : A[X]).coeff j) := by
  have hsq : ((X + C (α (4 * (k - 2) + 2))) ^ 2 : A[X])
      = X ^ 2 + (C (α (4 * (k - 2) + 2)) * X + C (α (4 * (k - 2) + 2)) * X)
        + C (α (4 * (k - 2) + 2)) * C (α (4 * (k - 2) + 2)) := by
    ring
  show (C (α (4 * (k - 2) + 1)) - (X + C (α (4 * (k - 2) + 2))) ^ 2).coeff j = _
  rw [coeff_sub, hsq, coeff_add, coeff_add, coeff_add]

theorem obG_coeff_zero :
    (obG k α).coeff 0 = α (4 * (k - 2) + 1)
      - α (4 * (k - 2) + 2) * α (4 * (k - 2) + 2) := by
  rw [obG_coeff, coeff_C_zero, coeff_X_pow, coeff_C_mul, Polynomial.coeff_X_zero,
    ← Polynomial.C_mul, coeff_C_zero]
  norm_num

theorem obG_coeff_one :
    (obG k α).coeff 1 = -(α (4 * (k - 2) + 2) + α (4 * (k - 2) + 2)) := by
  rw [obG_coeff, coeff_C, coeff_X_pow, coeff_C_mul, Polynomial.coeff_X_one,
    ← Polynomial.C_mul, coeff_C]
  norm_num

theorem obG_coeff_two : (obG k α).coeff 2 = -1 := by
  rw [obG_coeff, coeff_C, coeff_X_pow, coeff_C_mul,
    show (X : A[X]).coeff 2 = 0 from Polynomial.coeff_X_of_ne_one (by omega),
    ← Polynomial.C_mul, coeff_C]
  norm_num

theorem obG_coeff_high {j : ℕ} (hj : 3 ≤ j) : (obG k α).coeff j = 0 := by
  rw [obG_coeff, coeff_C, coeff_X_pow, coeff_C_mul,
    show (X : A[X]).coeff j = 0 from Polynomial.coeff_X_of_ne_one (by omega),
    ← Polynomial.C_mul, coeff_C]
  simp only [if_neg (by omega : ¬ j = 0), if_neg (by omega : ¬ j = 2)]
  norm_num

omit [Nontrivial A] in
theorem obG_natDegree_le : (obG k α).natDegree ≤ 2 := by
  show (C (α (4 * (k - 2) + 1)) - (X + C (α (4 * (k - 2) + 2))) ^ 2).natDegree ≤ 2
  refine le_trans (natDegree_sub_le _ _) ?_
  simp only [natDegree_C, max_le_iff]
  constructor
  · omega
  · refine le_trans natDegree_pow_le ?_
    have h : (X + C (α (4 * (k - 2) + 2)) : A[X]).natDegree ≤ 1 := by
      refine le_trans (natDegree_add_le _ _) ?_
      simp only [natDegree_C, max_le_iff]
      exact ⟨natDegree_X_le, by omega⟩
    omega

/-- The 3-row certificate for the base correction pair `(G, G + β₀)`. -/
theorem obG_cert (h2 : IsUnit (2 : R)) :
    CoeffTriangular K (fun t => α (4 * (k - 2) + t))
      (fun t => if t = 2 then (-2 : R) else 1) 3
      (obG k α) (obG k α + C (α (4 * (k - 2)))) := by
  refine
    { unit := ?_
      supp₁ := ?_
      supp₂ := ?_
      pivot := ?_ }
  · intro j hj
    split
    · exact h2.neg
    · exact isUnit_one
  · intro j
    match j with
    | 0 =>
      rw [obG_coeff_zero]
      refine Subalgebra.sub_mem _ ?_ (Subalgebra.mul_mem _ ?_ ?_) <;>
        exact (le_sup_right : adjoin R _ ≤ _)
          (subset_adjoin ⟨_, ⟨by omega, by omega⟩, rfl⟩)
    | 1 =>
      rw [obG_coeff_one]
      refine Subalgebra.neg_mem _ (Subalgebra.add_mem _ ?_ ?_) <;>
        exact (le_sup_right : adjoin R _ ≤ _)
          (subset_adjoin ⟨2, ⟨by omega, by omega⟩, rfl⟩)
    | 2 =>
      rw [obG_coeff_two]
      exact (le_sup_left : K ≤ _) (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
    | (n + 3) =>
      rw [obG_coeff_high (by omega)]
      exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro j
    rw [coeff_add]
    refine Subalgebra.add_mem _ ?_ ?_
    · match j with
      | 0 =>
        rw [obG_coeff_zero]
        refine Subalgebra.sub_mem _ ?_ (Subalgebra.mul_mem _ ?_ ?_) <;>
          exact (le_sup_right : adjoin R _ ≤ _)
            (subset_adjoin ⟨_, ⟨by omega, by omega⟩, rfl⟩)
      | 1 =>
        rw [obG_coeff_one]
        refine Subalgebra.neg_mem _ (Subalgebra.add_mem _ ?_ ?_) <;>
          exact (le_sup_right : adjoin R _ ≤ _)
            (subset_adjoin ⟨2, ⟨by omega, by omega⟩, rfl⟩)
      | 2 =>
        rw [obG_coeff_two]
        exact (le_sup_left : K ≤ _) (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
      | (n + 3) =>
        rw [obG_coeff_high (by omega)]
        exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
    · rw [coeff_C]
      split
      · rename_i hj0
        subst hj0
        exact (le_sup_right : adjoin R _ ≤ _)
          (subset_adjoin ⟨0, ⟨le_rfl, by omega⟩, rfl⟩)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro j hj
    match j, hj with
    | 0, _ =>
      refine ⟨(obG k α).coeff 0, ?_, ?_⟩
      · rw [obG_coeff_zero]
        refine Subalgebra.sub_mem _ ?_ (Subalgebra.mul_mem _ ?_ ?_) <;>
          exact (le_sup_right : adjoin R _ ≤ _)
            (subset_adjoin ⟨_, ⟨by omega, by omega⟩, rfl⟩)
      · rw [coeff_combined_zero, coeff_add, coeff_C, if_pos rfl,
          if_neg (by omega : ¬ (0 : ℕ) = 2), map_one, one_mul, Nat.add_zero]
        ring
    | 1, _ =>
      refine ⟨-(α (4 * (k - 2) + 2) * α (4 * (k - 2) + 2))
        + -(α (4 * (k - 2) + 2) + α (4 * (k - 2) + 2)), ?_, ?_⟩
      · have hv : α (4 * (k - 2) + 2)
            ∈ K ⊔ adjoin R ((fun t => α (4 * (k - 2) + t)) '' Set.Ico (1 + 1) 3) :=
          (le_sup_right : adjoin R _ ≤ _)
            (subset_adjoin ⟨2, ⟨by omega, by omega⟩, rfl⟩)
        exact Subalgebra.add_mem _
          (Subalgebra.neg_mem _ (Subalgebra.mul_mem _ hv hv))
          (Subalgebra.neg_mem _ (Subalgebra.add_mem _ hv hv))
      · have hcO : (combined (obG k α) (obG k α + C (α (4 * (k - 2))))).coeff 1
            = (obG k α).coeff 0 + (obG k α + C (α (4 * (k - 2)))).coeff 1 := by
          rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_combined]
        rw [hcO, coeff_add, coeff_C, if_neg (by omega : ¬ (1 : ℕ) = 0),
          if_neg (by omega : ¬ (1 : ℕ) = 2), map_one, one_mul, obG_coeff_zero,
          obG_coeff_one]
        ring
    | 2, _ =>
      refine ⟨(-1 : A), (le_sup_left : K ≤ _)
        (Subalgebra.neg_mem _ (Subalgebra.one_mem _)), ?_⟩
      have hcO : (combined (obG k α) (obG k α + C (α (4 * (k - 2))))).coeff 2
          = (obG k α).coeff 1 + (obG k α + C (α (4 * (k - 2)))).coeff 2 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, coeff_combined]
      rw [hcO, coeff_add, coeff_C, if_neg (by omega : ¬ (2 : ℕ) = 0),
        if_pos rfl, obG_coeff_one, obG_coeff_two]
      have h2c : algebraMap R A (-2 : R) = -2 := by
        rw [map_neg, map_ofNat]
      rw [h2c]
      ring
    | (n + 3), h => exact absurd h (by omega)


/-! ### Degree facts and window toolkit at the base -/

/-- Degree/monicity facts for the base multipliers (no scalar-difference needed). -/
theorem ob_deg_facts
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K)) :
    (obS1 Hp k α).Monic ∧ (obS1 Hp k α).natDegree = 2
      ∧ (Hp 2 + obS1 Hp k α).Monic ∧ (Hp 2 + obS1 Hp k α).natDegree = 4
      ∧ (Hp 2 - (k - 1) • obS1 Hp k α).Monic
      ∧ (Hp 2 - (k - 1) • obS1 Hp k α).natDegree = 4 := by
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
  obtain ⟨hbm, hbd⟩ := obS1_good (Hp := Hp) (k := k) (α := α) ⟨h1m, by rw [h1d]⟩
  have hlt : (obS1 Hp k α).degree < (Hp 2).degree := by
    rw [degree_eq_natDegree hbm.ne_zero, degree_eq_natDegree h2m.ne_zero, h2d, hbd]
    exact_mod_cast (by omega : 2 < 2 ^ 2)
  have hsmul : ((k - 1) • obS1 Hp k α).degree < (Hp 2).degree :=
    lt_of_le_of_lt (degree_smul_le _ _) hlt
  refine ⟨hbm, hbd, h2m.add_of_left hlt, ?_, ?_, ?_⟩
  · rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hlt), h2d]
    norm_num
  · have := h2m.add_of_left (q := -((k - 1) • obS1 Hp k α)) (by
      rw [degree_neg]
      exact hsmul)
    simpa [sub_eq_add_neg] using this
  · rw [sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        exact hsmul)), h2d]
    norm_num

/-- Window facts for the base blocks (mirrors `odd_windows`). -/
theorem ob_windows
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) :
    (∀ lo a, lo ≤ 4 * (k - 2) + 3 →
      (obS1 Hp k α).coeff a
        ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico lo (4 * (k - 1))))
    ∧ (∀ lo i', lo ≤ 4 * (k - 2) + i' + 1 →
      (obG k α).coeff i'
        ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico lo (4 * (k - 1))))
    ∧ (∀ lo a, lo ≤ a + 1 →
      (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff a
        ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico lo (4 * (k - 1)))) := by
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  have hb3lt : 4 * (k - 2) + 3 < 4 * (k - 1) := by omega
  have hlow : ∀ t, t < 4 → rSlot (A := A) k 2 α t = α t :=
    fun t ht => rSlot_ob_low hpar hk ht
  have hband : ∀ t, 4 * (k - 2) ≤ t → rSlot (A := A) k 2 α t = α t :=
    fun t ht => rSlot_ob_band hpar hk ht
  have hmem : ∀ lo t, lo ≤ t → t < 4 * (k - 1) → rSlot (A := A) k 2 α t = α t →
      α t ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico lo (4 * (k - 1))) := by
    intro lo t h1 h2 hv
    exact (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨h1, h2⟩, hv⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro lo a hlo
    show (Hp 1 + (X + C (α (4 * (k - 2) + 3)))).coeff a ∈ _
    rw [coeff_add, coeff_add]
    refine Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h1K a))
      (Subalgebra.add_mem _ ?_ ?_)
    · rw [Polynomial.coeff_X]
      split
      · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
    · rw [coeff_C]
      split
      · exact hmem lo _ (by omega) (by omega) (hband _ (by omega))
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro lo i' hlo
    match i' with
    | 0 =>
      rw [obG_coeff_zero]
      have hw := hmem lo (4 * (k - 2) + 1) (by omega) (by omega)
        (hband _ (by omega))
      have hv := hmem lo (4 * (k - 2) + 2) (by omega) (by omega)
        (hband _ (by omega))
      exact Subalgebra.sub_mem _ hw (Subalgebra.mul_mem _ hv hv)
    | 1 =>
      rw [obG_coeff_one]
      have hv := hmem lo (4 * (k - 2) + 2) (by omega) (by omega)
        (hband _ (by omega))
      exact Subalgebra.neg_mem _ (Subalgebra.add_mem _ hv hv)
    | 2 =>
      rw [obG_coeff_two]
      exact (le_sup_left : K ≤ _) (Subalgebra.neg_mem _ (Subalgebra.one_mem _))
    | (n + 3) =>
      rw [obG_coeff_high (by omega)]
      exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro lo a hlo
    have h1d' : (Hp 1).natDegree = 2 := by rw [h1d]; norm_num
    match a, hlo with
    | 0, hlo =>
      have hs1 := hmem lo 1 (by omega) (by omega) (hlow 1 (by omega))
      have hs2 := hmem lo 2 (by omega) (by omega) (hlow 2 (by omega))
      have hs3 := hmem lo 3 (by omega) (by omega) (hlow 3 (by omega))
      rw [Q₃_coeff_zero]
      exact Subalgebra.add_mem _ hs1 (Subalgebra.mul_mem _ hs3
        (Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h1K 0)) hs2))
    | 1, hlo =>
      have hs2 := hmem lo 2 (by omega) (by omega) (hlow 2 (by omega))
      have hs3 := hmem lo 3 (by omega) (by omega) (hlow 3 (by omega))
      rw [Q₃_coeff_one]
      exact Subalgebra.add_mem _ hs2 (Subalgebra.add_mem _
        ((le_sup_left : K ≤ _) (h1K 0))
        (Subalgebra.mul_mem _ hs3 ((le_sup_left : K ≤ _) (h1K 1))))
    | 2, hlo =>
      have hs3 := hmem lo 3 (by omega) (by omega) (hlow 3 (by omega))
      rw [Q₃_coeff_two (α 1) (α 2) (α 3) h1m h1d']
      exact Subalgebra.add_mem _ hs3 ((le_sup_left : K ≤ _) (h1K 1))
    | (n + 3), hlo =>
      have hHm' : (Hp 1 + C (α 2)).Monic := by
        refine h1m.add_of_left (lt_of_le_of_lt degree_C_le ?_)
        rw [degree_eq_natDegree h1m.ne_zero, h1d]
        exact_mod_cast (by norm_num : (0 : ℕ) < 2 ^ 1)
      rcases Nat.lt_or_ge (n + 3) 4 with h4 | h4
      · rw [show n + 3 = 3 from by omega]
        have hd : ((X + C (α 3)) * (Hp 1 + C (α 2))).natDegree = 3 := by
          rw [(monic_X_add_C _).natDegree_mul hHm', natDegree_X_add_C,
            natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt
              (lt_of_le_of_lt degree_C_le (by
                rw [degree_eq_natDegree h1m.ne_zero, h1d]
                exact_mod_cast (by norm_num : (0 : ℕ) < 2 ^ 1)))), h1d]
          norm_num
        have hlead := ((monic_X_add_C (α 3)).mul hHm').coeff_natDegree
        rw [hd] at hlead
        have hc3 : (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 3 = 1 := by
          show ((X + C (α 3)) * (Hp 1 + C (α 2)) + C (α 1)).coeff 3 = 1
          rw [coeff_add, coeff_C, if_neg (by omega : ¬ (3 : ℕ) = 0), add_zero,
            hlead]
        rw [hc3]
        exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · have hz : (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff (n + 3) = 0 := by
          refine coeff_eq_zero_of_natDegree_lt ?_
          show ((X + C (α 3)) * (Hp 1 + C (α 2)) + C (α 1)).natDegree < n + 3
          refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
          simp only [natDegree_C, max_le_iff]
          have hmul := natDegree_mul_le (p := X + C (α 3)) (q := Hp 1 + C (α 2))
          have hX : (X + C (α 3) : A[X]).natDegree ≤ 1 := by
            refine le_trans (natDegree_add_le _ _) ?_
            simp only [natDegree_C, max_le_iff]
            exact ⟨natDegree_X_le, by omega⟩
          have hH : (Hp 1 + C (α 2)).natDegree ≤ 2 := by
            refine le_trans (natDegree_add_le _ _) ?_
            simp only [natDegree_C, max_le_iff]
            omega
          omega
        rw [hz]
        exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)


/-- `W·inner` is fully known at and above row `b₀ - 1` at the base. -/
theorem ob_winner_high_K
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hdHt : Ht.natDegree = 4) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (hind₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.natDegree ≤ 4 * (k - 3))
    (hind₂ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.natDegree ≤ 4 * (k - 3))
    (htop₁₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff (4 * (k - 3)) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff (4 * (k - 3) - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.coeff (4 * (k - 3)) ∈ K) :
    (∀ m, 4 * (k - 2) - 1 ≤ m → ((Hp 2 - (k - 1) • obS1 Hp k α)
      * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1).coeff m ∈ K)
    ∧ (∀ m, 4 * (k - 2) ≤ m → ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
      * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2).coeff m ∈ K) := by
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
  obtain ⟨hbm, hbd⟩ := obS1_good (Hp := Hp) (k := k) (α := α) ⟨h1m, by rw [h1d]⟩
  have h2d' : (Hp 2).natDegree = 4 := by rw [h2d]; norm_num
  have hW₁K : ∀ a, 3 ≤ a → (Hp 2 - (k - 1) • obS1 Hp k α).coeff a ∈ K := by
    intro a ha
    rw [coeff_sub, coeff_smul,
      show (obS1 Hp k α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      smul_zero, sub_zero]
    exact h2K a
  have hW₂K : ∀ a, 3 ≤ a →
      (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).coeff a ∈ K := by
    intro a ha
    rw [coeff_sub, coeff_smul, nsmul_eq_mul, coeff_sub, coeff_sub,
      show (obS1 Hp k α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]
    refine Subalgebra.sub_mem _ (hKt a) (Subalgebra.mul_mem _
      (Subalgebra.natCast_mem _ _) ?_)
    exact Subalgebra.sub_mem _ (Subalgebra.zero_mem _)
      (Subalgebra.sub_mem _ (hKt a) (h2K a))
  have hW₁z : ∀ a, 4 < a → (Hp 2 - (k - 1) • obS1 Hp k α).coeff a = 0 := by
    intro a ha
    rw [coeff_sub, coeff_smul,
      show (Hp 2).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      show (obS1 Hp k α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      smul_zero, sub_zero]
  have hW₂z : ∀ a, 4 < a →
      (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).coeff a = 0 := by
    intro a ha
    rw [coeff_sub, coeff_smul, coeff_sub, coeff_sub,
      show Ht.coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      show (Hp 2).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      show (obS1 Hp k α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  constructor
  · intro m hm
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (4 * (k - 3)) x.2 with hgt | hle
    · rw [show (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge x.2 (4 * (k - 3) - 1) with hlo | hhi
      · rw [hW₁z x.1 (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · rcases eq_or_lt_of_le hhi with heq | hlt2
        · rw [show x.2 = 4 * (k - 3) - 1 from heq.symm]
          exact Subalgebra.mul_mem _ (hW₁K x.1 (by omega)) htop₁₂
        · rw [show x.2 = 4 * (k - 3) from by omega]
          exact Subalgebra.mul_mem _ (hW₁K x.1 (by omega)) htop₁₁
  · intro m hm
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (4 * (k - 3)) x.2 with hgt | hle
    · rw [show (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge x.2 (4 * (k - 3)) with hlo | hhi
      · rw [hW₂z x.1 (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · rw [show x.2 = 4 * (k - 3) from by omega]
        exact Subalgebra.mul_mem _ (hW₂K x.1 (by omega)) htop₂₁


/-- Supports of the base remainder pair, first component. -/
theorem ob_supp₁
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (hin : ∀ j, (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
            Set.Ico (4 * (k - 2)) (4 * (k - 1))))
        ⊔ adjoin R ((rSlot ((k - 1) / 2) 3 (fun j => α (4 + j)) (A := A)) ''
          Set.Ico (j + 1) (4 * (k - 3))))
    (hind : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.natDegree ≤ 4 * (k - 3))
    (htop : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff (4 * (k - 3)) ∈ K) :
    ∀ j, (Rpair Hp Ht k 2 α).1.coeff j
      ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico (j + 1) (4 * (k - 1))) := by
  obtain ⟨hobS1V, hobGVi, hQ₃V⟩ := ob_windows (α := α) hHp hpar hk
  obtain ⟨hbm, hbd, hUm, hUd, hW1m, hW1d⟩ := ob_deg_facts (α := α) hHp
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
  have h2d' : (Hp 2).natDegree = 4 := by rw [h2d]; norm_num
  have hb2 : 4 + (k - 3) * 4 = 4 * (k - 2) := by omega
  intro j
  set γ := rSlot k 2 α (A := A) with hγ
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) (4 * (k - 1))) with hV
  have hWV : ∀ lo a, lo ≤ 4 * (k - 2) + 3 →
      (Hp 2 - (k - 1) • obS1 Hp k α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo (4 * (k - 1))) := by
    intro lo a hlo
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (h2K a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (hobS1V lo a hlo))
  have hUV : ∀ lo a, lo ≤ 4 * (k - 2) + 3 →
      (Hp 2 + obS1 Hp k α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo (4 * (k - 1))) := by
    intro lo a hlo
    rw [coeff_add]
    exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h2K a)) (hobS1V lo a hlo)
  have hLd : ((Hp 2 - (k - 1) • obS1 Hp k α)
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)).natDegree = 4 * (k - 2) := by
    rw [hW1m.natDegree_mul (hUm.pow _), hW1d, hUm.natDegree_pow, hUd]
    omega
  have hLV : ∀ lo a, lo ≤ 4 * (k - 2) + 3 →
      ((Hp 2 - (k - 1) • obS1 Hp k α)
        * (Hp 2 + obS1 Hp k α) ^ (k - 3)).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo (4 * (k - 1))) := by
    intro lo a hlo
    exact coeff_mem_mul (fun i => hWV lo i hlo)
      (coeff_mem_pow (fun i => hUV lo i hlo) (k - 3)) a
  -- top rows of the principal are fully known
  have hobS1sqK : ∀ a, 3 ≤ a → (obS1 Hp k α ^ 2).coeff a ∈ K := by
    intro a ha
    rw [sq, coeff_mul]
    refine Subalgebra.sum_mem _ fun y hy => ?_
    have hya : y.1 + y.2 = a := Finset.mem_antidiagonal.1 hy
    have hc : ∀ i : ℕ, 1 ≤ i → (obS1 Hp k α).coeff i ∈ K := by
      intro i hi
      show (Hp 1 + (X + C (α (4 * (k - 2) + 3)))).coeff i ∈ K
      rw [coeff_add, coeff_add, coeff_C, if_neg (by omega)]
      refine Subalgebra.add_mem _ (h1K i)
        (Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _))
      rw [Polynomial.coeff_X]
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    rcases Nat.lt_or_ge 2 y.1 with hg1 | hl1
    · rw [show (obS1 Hp k α).coeff y.1 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge 2 y.2 with hg2 | hl2
      · rw [show (obS1 Hp k α).coeff y.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hc y.1 (by omega)) (hc y.2 (by omega))
  have hprinTopK : ∀ a, 4 * (k - 1) - 1 ≤ a →
      ((Hp 2 - (k - 1) • obS1 Hp k α) * (Hp 2 + obS1 Hp k α) ^ (k - 1)
        - Hp 2 ^ k).coeff a ∈ K := by
    intro a ha
    have hsplit := mul_pow_split (Hp 2) (obS1 Hp k α) (n := k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at hsplit
    have hPeq : (Hp 2 - (k - 1) • obS1 Hp k α) * (Hp 2 + obS1 Hp k α) ^ (k - 1)
        - Hp 2 ^ k
        = (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
            * (obS1 Hp k α ^ 2 * Hp 2 ^ (k - 1 - 1))
          + uTail (Hp 2) (obS1 Hp k α) (k - 1) := by
      rw [show Hp 2 - (k - 1) • obS1 Hp k α
          = Hp 2 - ((k - 1 : ℕ) : A[X]) * obS1 Hp k α from by rw [nsmul_eq_mul],
        hsplit]
      ring
    rw [hPeq, coeff_add,
      show (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
        = C ((((k - 1).choose 2 : ℕ) : A) - ((k - 1 : ℕ) : A) * ((k - 1 : ℕ) : A))
      from by rw [map_sub, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast],
      coeff_C_mul]
    refine Subalgebra.add_mem _ (Subalgebra.mul_mem _
      (Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _)
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.natCast_mem _ _))) ?_) ?_
    · rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = a := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge ((k - 1 - 1) * 4) x.2 with hg2 | hl2
      · rw [show (Hp 2 ^ (k - 1 - 1)).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by
            rw [h2m.natDegree_pow, h2d']
            exact hg2), mul_zero]
        exact Subalgebra.zero_mem _
      · have hx1 : 3 ≤ x.1 := by omega
        exact Subalgebra.mul_mem _ (hobS1sqK x.1 hx1)
          (coeff_mem_pow h2K (k - 1 - 1) x.2)
    · rw [show (uTail (Hp 2) (obS1 Hp k α) (k - 1)).coeff a = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          refine lt_of_le_of_lt (natDegree_uTail_le (le_of_eq h2d')
            (le_of_eq hbd) (by omega)) ?_
          omega)]
      exact Subalgebra.zero_mem _
  -- decomposition
  have hd₁ : (Rpair Hp Ht k 2 α).1
      = ((Hp 2 - (k - 1) • obS1 Hp k α) * (Hp 2 + obS1 Hp k α) ^ (k - 1)
          - Hp 2 ^ k)
        + ((k - 1) / 2) • ((Hp 2 - (k - 1) • obS1 Hp k α)
            * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α)
        + (Hp 2 - (k - 1) • obS1 Hp k α)
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) ((k - 1) / 2)
        + (Hp 2 - (k - 1) • obS1 Hp k α) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1
        + Q₃ (Hp 1) (α 1) (α 2) (α 3) := by
    rw [Rpair_oddbase_fst' hpar hk]
    ring
  rw [hd₁]
  simp only [coeff_add, coeff_smul]
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
    (Subalgebra.add_mem _ ?_ ?_) ?_) ?_) ?_
  · -- principal
    rcases Nat.lt_or_ge j (4 * (k - 1) - 1) with hjlt | hjge
    · rw [coeff_sub]
      exact Subalgebra.sub_mem _
        (coeff_mem_mul (fun i => hWV (j + 1) i (by omega))
          (coeff_mem_pow (fun i => hUV (j + 1) i (by omega)) (k - 1)) j)
        ((le_sup_left : K ≤ _) (coeff_mem_pow h2K k j))
    · exact (le_sup_left : K ≤ _) (hprinTopK j hjge)
  · -- oG-band term
    refine nsmul_mem ?_ _
    rcases Nat.lt_or_ge (4 * (k - 2) + 2) j with hjgt | hjle
    · rw [show ((Hp 2 - (k - 1) • obS1 Hp k α)
          * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α).coeff j = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          refine lt_of_le_of_lt natDegree_mul_le ?_
          have := obG_natDegree_le (k := k) (α := α)
          omega)]
      exact Subalgebra.zero_mem _
    · rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge (4 * (k - 2)) x.1 with hg1 | hl1
      · rw [show ((Hp 2 - (k - 1) • obS1 Hp k α)
            * (Hp 2 + obS1 Hp k α) ^ (k - 3)).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hLV (j + 1) x.1 (by omega))
          (hobGVi (j + 1) x.2 (by omega))
  · -- binomial tail
    rcases Nat.lt_or_ge (4 * (k - 2)) j with hjgt | hjle
    · rcases Nat.lt_or_ge k 5 with hk5 | hk5
      · rw [show binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) ((k - 1) / 2)
            = 0 from by
          show (∑ q ∈ Finset.Icc 2 ((k - 1) / 2), _) = 0
          rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty], mul_zero,
          coeff_zero]
        exact Subalgebra.zero_mem _
      · rw [show ((Hp 2 - (k - 1) • obS1 Hp k α)
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) ((k - 1) / 2)).coeff j
            = 0 from coeff_eq_zero_of_natDegree_lt (by
          have hUsq : ((Hp 2 + obS1 Hp k α) ^ 2).natDegree ≤ 8 := by
            have h := natDegree_pow_le (p := Hp 2 + obS1 Hp k α) (n := 2)
            omega
          have hbt : (binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α)
              ((k - 1) / 2)).natDegree
              ≤ 2 * 2 + ((k - 1) / 2 - 2) * 8 :=
            natDegree_binTail_le hUsq obG_natDegree_le (by omega) _
          have hm8 : ((k - 1) / 2 - 2) * 8 = 4 * (k - 5) := by omega
          have h := natDegree_mul_le (p := Hp 2 - (k - 1) • obS1 Hp k α)
            (q := binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) ((k - 1) / 2))
          omega)]
        exact Subalgebra.zero_mem _
    · refine coeff_mem_mul (fun i => hWV (j + 1) i (by omega))
        (coeff_mem_binTail
          (coeff_mem_pow (fun i => hUV (j + 1) i (by omega)) 2)
          (fun i => hobGVi (j + 1) i (by omega)) ((k - 1) / 2)) j
  · -- W · inner
    rcases Nat.lt_or_ge (4 * (k - 2)) j with hgt | hle
    · rw [show ((Hp 2 - (k - 1) • obS1 Hp k α) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1).coeff j = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          refine lt_of_le_of_lt (natDegree_mul_le) ?_
          omega)]
      exact Subalgebra.zero_mem _
    · rcases eq_or_lt_of_le hle with heqj | hltj
      · rw [coeff_mul]
        refine Subalgebra.sum_mem _ fun x hx => ?_
        have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
        rcases Nat.lt_or_ge (4 * (k - 3)) x.2 with hgt2 | hle2
        · rw [show (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff x.2 = 0 from
            coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
          exact Subalgebra.zero_mem _
        · rcases eq_or_lt_of_le hle2 with heq2 | hlt2
          · rw [show x.2 = 4 * (k - 3) from heq2]
            exact Subalgebra.mul_mem _ (hWV (j + 1) x.1 (by omega))
              ((le_sup_left : K ≤ _) htop)
          · rw [show (Hp 2 - (k - 1) • obS1 Hp k α).coeff x.1 = 0 from
              coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
            exact Subalgebra.zero_mem _
      · rw [coeff_mul]
        refine Subalgebra.sum_mem _ fun x hx => ?_
        have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
        rcases Nat.lt_or_ge 4 x.1 with hgt1 | hle1
        · rw [show (Hp 2 - (k - 1) • obS1 Hp k α).coeff x.1 = 0 from
            coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
          exact Subalgebra.zero_mem _
        · refine Subalgebra.mul_mem _ (hWV (j + 1) x.1 (by omega)) ?_
          refine mem_sup_adjoin_pair ?_ ?_ (hin x.2)
          · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
            exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
          · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
            refine ⟨4 + g, ⟨by omega, by omega⟩, ?_⟩
            rw [hγ, rSlot_ob_inner hpar hk (by omega) (by omega),
              Nat.add_sub_cancel_left]
  · -- the Q₃ head
    exact hQ₃V (j + 1) j (by omega)


/-- Supports of the base remainder pair, second component. -/
theorem ob_supp₂
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 4) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hsd : ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (hin : ∀ j, (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
            Set.Ico (4 * (k - 2)) (4 * (k - 1))))
        ⊔ adjoin R ((rSlot ((k - 1) / 2) 3 (fun j => α (4 + j)) (A := A)) ''
          Set.Ico j (4 * (k - 3))))
    (hind : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.natDegree ≤ 4 * (k - 3)) :
    ∀ j, (Rpair Hp Ht k 2 α).2.coeff j
      ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico j (4 * (k - 1))) := by
  obtain ⟨hobS1V, hobGVi, hQ₃V⟩ := ob_windows (α := α) hHp hpar hk
  obtain ⟨hbm, hbd, hUm, hUd, hW1m, hW1d⟩ := ob_deg_facts (α := α) hHp
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
  obtain ⟨ρ, hρ⟩ := hsd
  have h2d' : (Hp 2).natDegree = 4 := by rw [h2d]; norm_num
  have hρK : ρ ∈ K := by
    have h0 := congrArg (fun P : A[X] => P.coeff 0) hρ
    simp only [coeff_sub, coeff_C_zero] at h0
    rw [← h0]
    exact Subalgebra.sub_mem _ (hKt 0) (h2K 0)
  have hobS1cK : ∀ i : ℕ, 1 ≤ i → (obS1 Hp k α).coeff i ∈ K := by
    intro i hi
    show (Hp 1 + (X + C (α (4 * (k - 2) + 3)))).coeff i ∈ K
    rw [coeff_add, coeff_add, coeff_C, if_neg (by omega)]
    refine Subalgebra.add_mem _ (h1K i)
      (Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _))
    rw [Polynomial.coeff_X]
    split
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  intro j
  set γ := rSlot k 2 α (A := A) with hγ
  set V := K ⊔ adjoin R (γ '' Set.Ico j (4 * (k - 1))) with hV
  have hW₂V : ∀ lo a, lo ≤ 4 * (k - 2) + 3 →
      (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo (4 * (k - 1))) := by
    intro lo a hlo
    rw [coeff_sub, coeff_smul, nsmul_eq_mul, coeff_sub, coeff_sub]
    refine Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (Subalgebra.sub_mem _ (hobS1V lo a hlo)
          (Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
            ((le_sup_left : K ≤ _) (h2K a)))))
  have hUV : ∀ lo a, lo ≤ 4 * (k - 2) + 3 →
      (Hp 2 + obS1 Hp k α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo (4 * (k - 1))) := by
    intro lo a hlo
    rw [coeff_add]
    exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h2K a)) (hobS1V lo a hlo)
  have hW₂dle : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree ≤ 4 := by
    have hb := natDegree_sub_le Ht (Hp 2)
    have ha := natDegree_sub_le (obS1 Hp k α) (Ht - Hp 2)
    have h2 : ((k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree
        ≤ (obS1 Hp k α - (Ht - Hp 2)).natDegree := natDegree_smul_le _ _
    have h3 := natDegree_sub_le Ht ((k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
    have hf : (obS1 Hp k α).natDegree = 2 := hbd
    omega
  have hobG₂Vi : ∀ lo i', lo ≤ 4 * (k - 2) + i' →
      (obG k α + C (α (4 * (k - 2)))).coeff i'
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo (4 * (k - 1))) := by
    intro lo i' hlo
    rw [coeff_add]
    refine Subalgebra.add_mem _ (hobGVi lo i' (by omega)) ?_
    rw [coeff_C]
    split
    · exact (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨4 * (k - 2), ⟨by omega, by omega⟩,
          rSlot_ob_band hpar hk (by omega)⟩)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  -- principal top rows are fully known (uses the scalar difference)
  have hW₂eq : Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))
      = Ht - (k - 1) • (obS1 Hp k α - C ρ) := by rw [hρ]
  have hUeq : Hp 2 + obS1 Hp k α = Ht + (obS1 Hp k α - C ρ) := by
    linear_combination -hρ
  have hU₂m : (obS1 Hp k α - C ρ).Monic := by
    have := hbm.add_of_left (q := -(C ρ)) (by
      rw [degree_neg]
      refine lt_of_le_of_lt degree_C_le ?_
      rw [degree_eq_natDegree hbm.ne_zero, hbd]
      exact_mod_cast (by norm_num : (0 : ℕ) < 2))
    simpa [sub_eq_add_neg] using this
  have hU₂d : (obS1 Hp k α - C ρ).natDegree = 2 := by
    rw [sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        refine lt_of_le_of_lt degree_C_le ?_
        rw [degree_eq_natDegree hbm.ne_zero, hbd]
        exact_mod_cast (by norm_num : (0 : ℕ) < 2))), hbd]
  have hU₂cK : ∀ i : ℕ, 1 ≤ i → (obS1 Hp k α - C ρ).coeff i ∈ K := by
    intro i hi
    rw [coeff_sub, coeff_C, if_neg (by omega), sub_zero]
    exact hobS1cK i hi
  have hU₂sqK : ∀ a, 3 ≤ a → ((obS1 Hp k α - C ρ) ^ 2).coeff a ∈ K := by
    intro a ha
    rw [sq, coeff_mul]
    refine Subalgebra.sum_mem _ fun y hy => ?_
    have hya : y.1 + y.2 = a := Finset.mem_antidiagonal.1 hy
    rcases Nat.lt_or_ge 2 y.1 with hg1 | hl1
    · rw [show (obS1 Hp k α - C ρ).coeff y.1 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge 2 y.2 with hg2 | hl2
      · rw [show (obS1 Hp k α - C ρ).coeff y.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hU₂cK y.1 (by omega)) (hU₂cK y.2 (by omega))
  have hprinTop₂K : ∀ a, 4 * (k - 1) - 1 ≤ a →
      ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
        * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k).coeff a ∈ K := by
    intro a ha
    have hsplit := mul_pow_split Ht (obS1 Hp k α - C ρ) (n := k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at hsplit
    have hPeq : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
        * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k
        = (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
            * ((obS1 Hp k α - C ρ) ^ 2 * Ht ^ (k - 1 - 1))
          + uTail Ht (obS1 Hp k α - C ρ) (k - 1) := by
      rw [hW₂eq, hUeq,
        show Ht - (k - 1) • (obS1 Hp k α - C ρ)
          = Ht - ((k - 1 : ℕ) : A[X]) * (obS1 Hp k α - C ρ) from by
          rw [nsmul_eq_mul],
        hsplit]
      ring
    rw [hPeq, coeff_add,
      show (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
        = C ((((k - 1).choose 2 : ℕ) : A) - ((k - 1 : ℕ) : A) * ((k - 1 : ℕ) : A))
      from by rw [map_sub, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast],
      coeff_C_mul]
    refine Subalgebra.add_mem _ (Subalgebra.mul_mem _
      (Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _)
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.natCast_mem _ _))) ?_) ?_
    · rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = a := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge ((k - 1 - 1) * 4) x.2 with hg2 | hl2
      · rw [show (Ht ^ (k - 1 - 1)).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by
            rw [hHt.natDegree_pow, hdHt]
            exact hg2), mul_zero]
        exact Subalgebra.zero_mem _
      · have hx1 : 3 ≤ x.1 := by omega
        exact Subalgebra.mul_mem _ (hU₂sqK x.1 hx1)
          (coeff_mem_pow hKt (k - 1 - 1) x.2)
    · rw [show (uTail Ht (obS1 Hp k α - C ρ) (k - 1)).coeff a = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          refine lt_of_le_of_lt (natDegree_uTail_le (le_of_eq hdHt)
            (le_of_eq hU₂d) (by omega)) ?_
          omega)]
      exact Subalgebra.zero_mem _
  -- decomposition
  have hd₂ : (Rpair Hp Ht k 2 α).2
      = ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Hp 2 + obS1 Hp k α) ^ (k - 3) * (obG k α + C (α (4 * (k - 2)))))
        + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
              ((k - 1) / 2)
        + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2
        + C (α 0) := by
    rw [Rpair_oddbase_snd' hpar hk]
    ring
  rw [hd₂]
  simp only [coeff_add, coeff_smul]
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
    (Subalgebra.add_mem _ ?_ ?_) ?_) ?_) ?_
  · -- principal
    rcases Nat.lt_or_ge j (4 * (k - 1) - 1) with hjlt | hjge
    · rw [coeff_sub]
      exact Subalgebra.sub_mem _
        (coeff_mem_mul (fun i => hW₂V j i (by omega))
          (coeff_mem_pow (fun i => hUV j i (by omega)) (k - 1)) j)
        ((le_sup_left : K ≤ _) (coeff_mem_pow hKt k j))
    · exact (le_sup_left : K ≤ _) (hprinTop₂K j hjge)
  · -- oG-band term
    refine nsmul_mem ?_ _
    rcases Nat.lt_or_ge (4 * (k - 2) + 2) j with hjgt | hjle
    · rw [show ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * (Hp 2 + obS1 Hp k α) ^ (k - 3)
          * (obG k α + C (α (4 * (k - 2))))).coeff j = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          have hL2le : ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
              * (Hp 2 + obS1 Hp k α) ^ (k - 3)).natDegree ≤ 4 * (k - 2) := by
            refine le_trans natDegree_mul_le ?_
            have hp : ((Hp 2 + obS1 Hp k α) ^ (k - 3)).natDegree
                ≤ (k - 3) * 4 := by
              refine le_trans natDegree_pow_le ?_
              exact Nat.mul_le_mul_left _ (le_of_eq hUd)
            omega
          have hG2le : (obG k α + C (α (4 * (k - 2)))).natDegree ≤ 2 := by
            refine le_trans (natDegree_add_le _ _) ?_
            simp only [natDegree_C, max_le_iff]
            exact ⟨obG_natDegree_le, by omega⟩
          refine lt_of_le_of_lt natDegree_mul_le ?_
          omega)]
      exact Subalgebra.zero_mem _
    · rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge (4 * (k - 2)) x.1 with hg1 | hl1
      · rw [show ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Hp 2 + obS1 Hp k α) ^ (k - 3)).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by
            have hp : ((Hp 2 + obS1 Hp k α) ^ (k - 3)).natDegree
                ≤ (k - 3) * 4 := by
              refine le_trans natDegree_pow_le ?_
              exact Nat.mul_le_mul_left _ (le_of_eq hUd)
            have h := natDegree_mul_le
              (p := Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
              (q := (Hp 2 + obS1 Hp k α) ^ (k - 3))
            omega), zero_mul]
        exact Subalgebra.zero_mem _
      · refine Subalgebra.mul_mem _
          (coeff_mem_mul (fun i => hW₂V j i (by omega))
            (coeff_mem_pow (fun i => hUV j i (by omega)) (k - 3)) x.1)
          (hobG₂Vi j x.2 (by omega))
  · -- binomial tail
    rcases Nat.lt_or_ge (4 * (k - 2)) j with hjgt | hjle
    · rcases Nat.lt_or_ge k 5 with hk5 | hk5
      · rw [show binTail ((Hp 2 + obS1 Hp k α) ^ 2)
            (obG k α + C (α (4 * (k - 2)))) ((k - 1) / 2) = 0 from by
          show (∑ q ∈ Finset.Icc 2 ((k - 1) / 2), _) = 0
          rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty], mul_zero,
          coeff_zero]
        exact Subalgebra.zero_mem _
      · rw [show ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
              ((k - 1) / 2)).coeff j = 0 from coeff_eq_zero_of_natDegree_lt (by
          have hUsq : ((Hp 2 + obS1 Hp k α) ^ 2).natDegree ≤ 8 := by
            have h := natDegree_pow_le (p := Hp 2 + obS1 Hp k α) (n := 2)
            omega
          have hG2le : (obG k α + C (α (4 * (k - 2)))).natDegree ≤ 2 := by
            refine le_trans (natDegree_add_le _ _) ?_
            simp only [natDegree_C, max_le_iff]
            exact ⟨obG_natDegree_le, by omega⟩
          have hbt : (binTail ((Hp 2 + obS1 Hp k α) ^ 2)
              (obG k α + C (α (4 * (k - 2)))) ((k - 1) / 2)).natDegree
              ≤ 2 * 2 + ((k - 1) / 2 - 2) * 8 :=
            natDegree_binTail_le hUsq hG2le (by omega) _
          have hm8 : ((k - 1) / 2 - 2) * 8 = 4 * (k - 5) := by omega
          have h := natDegree_mul_le
            (p := Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            (q := binTail ((Hp 2 + obS1 Hp k α) ^ 2)
              (obG k α + C (α (4 * (k - 2)))) ((k - 1) / 2))
          omega)]
        exact Subalgebra.zero_mem _
    · refine coeff_mem_mul (fun i => hW₂V j i (by omega))
        (coeff_mem_binTail
          (coeff_mem_pow (fun i => hUV j i (by omega)) 2)
          (fun i => hobG₂Vi j i (by omega)) ((k - 1) / 2)) j
  · -- W · inner
    rcases Nat.lt_or_ge (4 * (k - 2)) j with hgt | hle
    · rw [show ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2).coeff j
          = 0 from coeff_eq_zero_of_natDegree_lt (by
          refine lt_of_le_of_lt (natDegree_mul_le) ?_
          omega)]
      exact Subalgebra.zero_mem _
    · rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge 4 x.1 with hgt1 | hle1
      · rw [show (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · refine Subalgebra.mul_mem _ (hW₂V j x.1 (by omega)) ?_
        refine mem_sup_adjoin_pair ?_ ?_ (hin x.2)
        · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
          exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
        · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
          refine ⟨4 + g, ⟨by omega, by omega⟩, ?_⟩
          rw [hγ, rSlot_ob_inner hpar hk (by omega) (by omega),
            Nat.add_sub_cancel_left]
  · -- the constant α₀
    rw [coeff_C]
    split
    · rename_i hj0
      subst hj0
      exact (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨0, ⟨le_rfl, by omega⟩, rSlot_ob_low hpar hk (by omega)⟩)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)


/-- High coefficients of the `Q₃` head are known. -/
theorem Q₃_high_K
    (h1 : (Hp 1).Monic ∧ (Hp 1).natDegree = 2 ∧ (∀ j, (Hp 1).coeff j ∈ K)) :
    ∀ a, 3 ≤ a → (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff a ∈ K := by
  obtain ⟨h1m, h1d, h1K⟩ := h1
  intro a ha
  have hHm' : (Hp 1 + C (α 2)).Monic := by
    refine h1m.add_of_left (lt_of_le_of_lt degree_C_le ?_)
    rw [degree_eq_natDegree h1m.ne_zero, h1d]
    exact_mod_cast (by norm_num : (0 : ℕ) < 2)
  rcases Nat.lt_or_ge a 4 with h4 | h4
  · rw [show a = 3 from by omega]
    have hd : ((X + C (α 3)) * (Hp 1 + C (α 2))).natDegree = 3 := by
      rw [(monic_X_add_C _).natDegree_mul hHm', natDegree_X_add_C,
        natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt
          (lt_of_le_of_lt degree_C_le (by
            rw [degree_eq_natDegree h1m.ne_zero, h1d]
            exact_mod_cast (by norm_num : (0 : ℕ) < 2)))), h1d]
    have hlead := ((monic_X_add_C (α 3)).mul hHm').coeff_natDegree
    rw [hd] at hlead
    show ((X + C (α 3)) * (Hp 1 + C (α 2)) + C (α 1)).coeff 3 ∈ K
    rw [coeff_add, coeff_C, if_neg (by omega : ¬ (3 : ℕ) = 0), add_zero, hlead]
    exact Subalgebra.one_mem _
  · have hz : (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff a = 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      show ((X + C (α 3)) * (Hp 1 + C (α 2)) + C (α 1)).natDegree < a
      refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
      simp only [natDegree_C, max_le_iff]
      have hmul := natDegree_mul_le (p := X + C (α 3)) (q := Hp 1 + C (α 2))
      have hX : (X + C (α 3) : A[X]).natDegree ≤ 1 := by
        refine le_trans (natDegree_add_le _ _) ?_
        simp only [natDegree_C, max_le_iff]
        exact ⟨natDegree_X_le, by omega⟩
      have hH : (Hp 1 + C (α 2)).natDegree ≤ 2 := by
        refine le_trans (natDegree_add_le _ _) ?_
        simp only [natDegree_C, max_le_iff]
        omega
      omega
    rw [hz]
    exact Subalgebra.zero_mem _

/-- The non-head parts of the base pair live above the head window. -/
theorem ob_rest_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (hin₁ : ∀ j, (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
            Set.Ico (4 * (k - 2)) (4 * (k - 1))))
        ⊔ adjoin R ((rSlot ((k - 1) / 2) 3 (fun j => α (4 + j)) (A := A)) ''
          Set.Ico (j + 1) (4 * (k - 3))))
    (hin₂ : ∀ j, (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
            Set.Ico (4 * (k - 2)) (4 * (k - 1))))
        ⊔ adjoin R ((rSlot ((k - 1) / 2) 3 (fun j => α (4 + j)) (A := A)) ''
          Set.Ico j (4 * (k - 3)))) :
    (∀ m, ((Rpair Hp Ht k 2 α).1 - Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff m
      ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico 4 (4 * (k - 1))))
    ∧ (∀ m, ((Rpair Hp Ht k 2 α).2 - C (α 0)).coeff m
      ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico 4 (4 * (k - 1)))) := by
  obtain ⟨hobS1V, hobGVi, hQ₃V⟩ := ob_windows (α := α) hHp hpar hk
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
  set γ := rSlot k 2 α (A := A) with hγ
  set S := K ⊔ adjoin R (γ '' Set.Ico 4 (4 * (k - 1))) with hS
  have hWS : ∀ a, (Hp 2 - (k - 1) • obS1 Hp k α).coeff a ∈ S := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (h2K a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (hobS1V 4 a (by omega)))
  have hW₂S : ∀ a, (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).coeff a ∈ S := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul, coeff_sub, coeff_sub]
    refine Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (Subalgebra.sub_mem _ (hobS1V 4 a (by omega))
          (Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
            ((le_sup_left : K ≤ _) (h2K a)))))
  have hUS : ∀ a, (Hp 2 + obS1 Hp k α).coeff a ∈ S := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h2K a)) (hobS1V 4 a (by omega))
  have hGS : ∀ a, (obG k α).coeff a ∈ S := fun a => hobGVi 4 a (by omega)
  have hG₂S : ∀ a, (obG k α + C (α (4 * (k - 2)))).coeff a ∈ S := by
    intro a
    rw [coeff_add]
    refine Subalgebra.add_mem _ (hGS a) ?_
    rw [coeff_C]
    split
    · exact (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨4 * (k - 2), ⟨by omega, by omega⟩,
          rSlot_ob_band hpar hk (by omega)⟩)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  have hI₁S : ∀ b, (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff b ∈ S := by
    intro b
    refine mem_sup_adjoin_pair ?_ ?_ (hin₁ b)
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      refine ⟨4 + g, ⟨by omega, by omega⟩, ?_⟩
      rw [hγ, rSlot_ob_inner hpar hk (by omega) (by omega),
        Nat.add_sub_cancel_left]
  have hI₂S : ∀ b, (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.coeff b ∈ S := by
    intro b
    refine mem_sup_adjoin_pair ?_ ?_ (hin₂ b)
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      refine ⟨4 + g, ⟨by omega, by omega⟩, ?_⟩
      rw [hγ, rSlot_ob_inner hpar hk (by omega) (by omega),
        Nat.add_sub_cancel_left]
  constructor
  · intro m
    have hdec : (Rpair Hp Ht k 2 α).1 - Q₃ (Hp 1) (α 1) (α 2) (α 3)
        = ((Hp 2 - (k - 1) • obS1 Hp k α) * (Hp 2 + obS1 Hp k α) ^ (k - 1)
            - Hp 2 ^ k)
          + ((k - 1) / 2) • ((Hp 2 - (k - 1) • obS1 Hp k α)
              * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α)
          + (Hp 2 - (k - 1) • obS1 Hp k α)
              * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) ((k - 1) / 2)
          + (Hp 2 - (k - 1) • obS1 Hp k α) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1 := by
      rw [Rpair_oddbase_fst' hpar hk]
      ring
    rw [hdec]
    simp only [coeff_add, coeff_smul]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_) ?_
    · rw [coeff_sub]
      exact Subalgebra.sub_mem _
        (coeff_mem_mul hWS (coeff_mem_pow hUS (k - 1)) m)
        ((le_sup_left : K ≤ _) (coeff_mem_pow h2K k m))
    · exact nsmul_mem (coeff_mem_mul (coeff_mem_mul hWS
        (coeff_mem_pow hUS (k - 3))) hGS m) _
    · exact coeff_mem_mul hWS
        (coeff_mem_binTail (coeff_mem_pow hUS 2) hGS ((k - 1) / 2)) m
    · exact coeff_mem_mul hWS hI₁S m
  · intro m
    have hdec : (Rpair Hp Ht k 2 α).2 - C (α 0)
        = ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k)
          + ((k - 1) / 2) • ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
              * (Hp 2 + obS1 Hp k α) ^ (k - 3) * (obG k α + C (α (4 * (k - 2)))))
          + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
              * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
                ((k - 1) / 2)
          + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2 := by
      rw [Rpair_oddbase_snd' hpar hk]
      ring
    rw [hdec]
    simp only [coeff_add, coeff_smul]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_) ?_
    · rw [coeff_sub]
      exact Subalgebra.sub_mem _
        (coeff_mem_mul hW₂S (coeff_mem_pow hUS (k - 1)) m)
        ((le_sup_left : K ≤ _) (coeff_mem_pow hKt k m))
    · exact nsmul_mem (coeff_mem_mul (coeff_mem_mul hW₂S
        (coeff_mem_pow hUS (k - 3))) hG₂S m) _
    · exact coeff_mem_mul hW₂S
        (coeff_mem_binTail (coeff_mem_pow hUS 2) hG₂S ((k - 1) / 2)) m
    · exact coeff_mem_mul hW₂S hI₂S m


/-- Head rows of the base certificate: `α₀` and the `Q₃` parameters, slope 1. -/
theorem ob_pivot_low
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (hrest₁ : ∀ m, ((Rpair Hp Ht k 2 α).1 - Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff m
      ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico 4 (4 * (k - 1))))
    (hrest₂ : ∀ m, ((Rpair Hp Ht k 2 α).2 - C (α 0)).coeff m
      ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) '' Set.Ico 4 (4 * (k - 1)))) :
    ∀ j, j < 4 → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k 2 α (A := A)) '' Set.Ico (j + 1) (4 * (k - 1))),
      (combined (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2).coeff j
        = algebraMap R A (((tLam k 2 j : ℤ) : R)) * (rSlot k 2 α (A := A)) j + F := by
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  have hd4 : 4 ≤ 4 * (k - 1) := by omega
  intro j hj
  set γ := rSlot k 2 α (A := A) with hγ
  have htr : ∀ x : A, x ∈ K ⊔ adjoin R (γ '' Set.Ico 4 (4 * (k - 1)))
      → x ∈ K ⊔ adjoin R (γ '' Set.Ico (j + 1) (4 * (k - 1))) := by
    intro x hx
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hx
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨g, ⟨by omega, hg2⟩, rfl⟩)
  have hslot : ∀ t, t < 4 → γ t = α t := fun t ht => rSlot_ob_low hpar hk ht
  have hsmem : ∀ t, j + 1 ≤ t → t < 4 →
      α t ∈ K ⊔ adjoin R (γ '' Set.Ico (j + 1) (4 * (k - 1))) := by
    intro t h1 h2
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨t, ⟨h1, by omega⟩, hslot t h2⟩)
  match j, hj with
  | 0, _ =>
    refine ⟨((Rpair Hp Ht k 2 α).2 - C (α 0)).coeff 0, htr _ (hrest₂ 0), ?_⟩
    rw [coeff_combined_zero, tLam_ob_low hpar hk (by omega), Int.cast_one,
      map_one, one_mul, hslot 0 (by omega), coeff_sub, coeff_C_zero]
    ring
  | 1, _ =>
    refine ⟨α 3 * ((Hp 1).coeff 0 + α 2)
      + ((Rpair Hp Ht k 2 α).1 - Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 0
      + ((Rpair Hp Ht k 2 α).2 - C (α 0)).coeff 1, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.mul_mem _ (hsmem 3 (by omega) (by omega))
          (Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h1K 0))
            (hsmem 2 (by omega) (by omega))))
        (htr _ (hrest₁ 0))) (htr _ (hrest₂ 1))
    · have hcO : (combined (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2).coeff 1
          = (Rpair Hp Ht k 2 α).1.coeff 0 + (Rpair Hp Ht k 2 α).2.coeff 1 := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_combined]
      have hr₁ : (Rpair Hp Ht k 2 α).1.coeff 0
          = (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 0
            + ((Rpair Hp Ht k 2 α).1 - Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 0 := by
        rw [coeff_sub]
        ring
      have hr₂ : (Rpair Hp Ht k 2 α).2.coeff 1
          = ((Rpair Hp Ht k 2 α).2 - C (α 0)).coeff 1 := by
        rw [coeff_sub, coeff_C, if_neg (by omega : ¬ (1 : ℕ) = 0)]
        ring
      rw [hcO, hr₁, hr₂, Q₃_coeff_zero, tLam_ob_low hpar hk (by omega),
        Int.cast_one, map_one, one_mul, hslot 1 (by omega)]
      ring
  | 2, _ =>
    refine ⟨((Hp 1).coeff 0 + α 3 * (Hp 1).coeff 1)
      + ((Rpair Hp Ht k 2 α).1 - Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 1
      + ((Rpair Hp Ht k 2 α).2 - C (α 0)).coeff 2, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h1K 0))
          (Subalgebra.mul_mem _ (hsmem 3 (by omega) (by omega))
            ((le_sup_left : K ≤ _) (h1K 1))))
        (htr _ (hrest₁ 1))) (htr _ (hrest₂ 2))
    · have hcO : (combined (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2).coeff 2
          = (Rpair Hp Ht k 2 α).1.coeff 1 + (Rpair Hp Ht k 2 α).2.coeff 2 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, coeff_combined]
      have hr₁ : (Rpair Hp Ht k 2 α).1.coeff 1
          = (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 1
            + ((Rpair Hp Ht k 2 α).1 - Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 1 := by
        rw [coeff_sub]
        ring
      have hr₂ : (Rpair Hp Ht k 2 α).2.coeff 2
          = ((Rpair Hp Ht k 2 α).2 - C (α 0)).coeff 2 := by
        rw [coeff_sub, coeff_C, if_neg (by omega : ¬ (2 : ℕ) = 0)]
        ring
      rw [hcO, hr₁, hr₂, Q₃_coeff_one, tLam_ob_low hpar hk (by omega),
        Int.cast_one, map_one, one_mul, hslot 2 (by omega)]
      ring
  | 3, _ =>
    have h1d' : (Hp 1).natDegree = 2 := by rw [h1d]; norm_num
    refine ⟨(Hp 1).coeff 1
      + ((Rpair Hp Ht k 2 α).1 - Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 2
      + ((Rpair Hp Ht k 2 α).2 - C (α 0)).coeff 3, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.add_mem _
        ((le_sup_left : K ≤ _) (h1K 1))
        (htr _ (hrest₁ 2))) (htr _ (hrest₂ 3))
    · have hcO : (combined (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2).coeff 3
          = (Rpair Hp Ht k 2 α).1.coeff 2 + (Rpair Hp Ht k 2 α).2.coeff 3 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, coeff_combined]
      have hr₁ : (Rpair Hp Ht k 2 α).1.coeff 2
          = (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 2
            + ((Rpair Hp Ht k 2 α).1 - Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff 2 := by
        rw [coeff_sub]
        ring
      have hr₂ : (Rpair Hp Ht k 2 α).2.coeff 3
          = ((Rpair Hp Ht k 2 α).2 - C (α 0)).coeff 3 := by
        rw [coeff_sub, coeff_C, if_neg (by omega : ¬ (3 : ℕ) = 0)]
        ring
      rw [hcO, hr₁, hr₂, Q₃_coeff_two (α 1) (α 2) (α 3) h1m h1d',
        tLam_ob_low hpar hk (by omega), Int.cast_one, map_one, one_mul,
        hslot 3 (by omega)]
      ring


/-- Inner rows of the base certificate: the inner pivot passes through the monic
multipliers, with all corrections windowed. -/
theorem ob_pivot_inner
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 4) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hsd : ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (hin : CoeffTriangular (K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
        Set.Ico (4 * (k - 2)) (4 * (k - 1))))
      (rSlot ((k - 1) / 2) 3 (fun j => α (4 + j)))
      (fun j => ((tLam ((k - 1) / 2) 3 j : ℤ) : R)) (4 * (k - 3))
      (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1
      (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2) :
    ∀ j, 4 ≤ j → j < 4 * (k - 2) → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k 2 α (A := A)) '' Set.Ico (j + 1) (4 * (k - 1))),
      (combined (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2).coeff j
        = algebraMap R A (((tLam k 2 j : ℤ) : R)) * (rSlot k 2 α (A := A)) j + F := by
  obtain ⟨hobS1V, hobGVi, hQ₃V⟩ := ob_windows (α := α) hHp hpar hk
  obtain ⟨hbm, hbd, hUm, hUd, hW1m, hW1d⟩ := ob_deg_facts (α := α) hHp
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
  obtain ⟨ρ, hρ⟩ := hsd
  have h2d' : (Hp 2).natDegree = 4 := by rw [h2d]; norm_num
  have hQ₃K := Q₃_high_K (Hp := Hp) (α := α) ⟨h1m, by rw [h1d]; norm_num, h1K⟩
  -- the tilde multiplier is monic of degree 4 under the scalar difference
  have hW₂eq : Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))
      = Ht - (k - 1) • (obS1 Hp k α - C ρ) := by rw [hρ]
  have hU₂deg : (obS1 Hp k α - C ρ).degree < Ht.degree := by
    have hU₂d : (obS1 Hp k α - C ρ).natDegree = 2 := by
      rw [sub_eq_add_neg,
        natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
          rw [degree_neg]
          refine lt_of_le_of_lt degree_C_le ?_
          rw [degree_eq_natDegree hbm.ne_zero, hbd]
          exact_mod_cast (by norm_num : (0 : ℕ) < 2))), hbd]
    have hU₂ne : (obS1 Hp k α - C ρ) ≠ 0 := by
      intro h0
      rw [h0] at hU₂d
      simp at hU₂d
    rw [degree_eq_natDegree hU₂ne, degree_eq_natDegree hHt.ne_zero, hdHt, hU₂d]
    exact_mod_cast (by norm_num : (2 : ℕ) < 4)
  have hW2m : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).Monic := by
    rw [hW₂eq]
    have := hHt.add_of_left (q := -((k - 1) • (obS1 Hp k α - C ρ))) (by
      rw [degree_neg]
      exact lt_of_le_of_lt (degree_smul_le _ _) hU₂deg)
    simpa [sub_eq_add_neg] using this
  have hW2d : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree = 4 := by
    rw [hW₂eq, sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        exact lt_of_le_of_lt (degree_smul_le _ _) hU₂deg)), hdHt]
  intro j hj1 hj2
  set γ := rSlot k 2 α (A := A) with hγ
  set K' := K ⊔ adjoin R (γ '' Set.Ico (4 * (k - 2))
    (4 * (k - 1))) with hK'
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) (4 * (k - 1))) with hV
  have hK'V : ∀ x : A, x ∈ K' → x ∈ V := by
    intro x hx
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hx
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨g, ⟨by omega, hg2⟩, rfl⟩)
  have hW1K' : ∀ a, (Hp 2 - (k - 1) • obS1 Hp k α).coeff a ∈ K' := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    refine Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (h2K a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _)) ?_)
    exact hobS1V (4 * (k - 2)) a (by omega)
  have hW2K' : ∀ a, (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).coeff a ∈ K' := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul, coeff_sub, coeff_sub]
    refine Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (Subalgebra.sub_mem _ (hobS1V (4 * (k - 2)) a (by omega))
          (Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
            ((le_sup_left : K ≤ _) (h2K a)))))
  obtain ⟨F', hF', hFe⟩ := CoeffTriangular.shift_pivot
    hin (by omega) hW1m hW1d hW2m hW2d
    hW1K' hW2K' (j - 4) (by omega)
  have hidx : 4 + (j - 4) = j := by omega
  rw [hidx] at hFe
  have hF'V : F' ∈ V := by
    refine SetLike.le_def.1 (sup_le ?_ (adjoin_le ?_)) hF'
    · intro x hx
      exact hK'V x hx
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hv : γ (4 + g)
          = rSlot ((k - 1) / 2) 3 (fun j => α (4 + j)) g := by
        rw [hγ, rSlot_ob_inner hpar hk (by omega) (by omega),
          Nat.add_sub_cancel_left]
      exact hv ▸ (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨4 + g, ⟨by omega, by omega⟩, rfl⟩)
  -- correction blankets over the fixed band-window
  have hWb : ∀ a, (Hp 2 - (k - 1) • obS1 Hp k α).coeff a
      ∈ K ⊔ adjoin R (γ '' Set.Ico (4 * (k - 2)) (4 * (k - 1))) := hW1K'
  have hhi₁ : ∀ m', (((Hp 2 - (k - 1) • obS1 Hp k α)
        * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Hp 2 ^ k)
      + ((k - 1) / 2) • ((Hp 2 - (k - 1) • obS1 Hp k α)
          * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α)
      + (Hp 2 - (k - 1) • obS1 Hp k α)
          * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α)
            ((k - 1) / 2)).coeff m'
      ∈ K ⊔ adjoin R (γ '' Set.Ico (4 * (k - 2)) (4 * (k - 1))) := by
    intro m'
    have hUb : ∀ a, (Hp 2 + obS1 Hp k α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico (4 * (k - 2)) (4 * (k - 1))) := by
      intro a
      rw [coeff_add]
      exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h2K a))
        (hobS1V (4 * (k - 2)) a (by omega))
    have hGb : ∀ a, (obG k α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico (4 * (k - 2)) (4 * (k - 1))) :=
      fun a => hobGVi (4 * (k - 2)) a (by omega)
    simp only [coeff_add, coeff_smul]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_
    · rw [coeff_sub]
      exact Subalgebra.sub_mem _
        (coeff_mem_mul hWb (coeff_mem_pow hUb (k - 1)) m')
        ((le_sup_left : K ≤ _) (coeff_mem_pow h2K k m'))
    · exact nsmul_mem (coeff_mem_mul (coeff_mem_mul hWb
        (coeff_mem_pow hUb (k - 3))) hGb m') _
    · exact coeff_mem_mul hWb
        (coeff_mem_binTail (coeff_mem_pow hUb 2) hGb ((k - 1) / 2)) m'
  have hhi₂ : ∀ m', (((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
        * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k)
      + ((k - 1) / 2) • ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * (Hp 2 + obS1 Hp k α) ^ (k - 3) * (obG k α + C (α (4 * (k - 2)))))
      + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
            ((k - 1) / 2)).coeff m'
      ∈ K ⊔ adjoin R (γ '' Set.Ico (4 * (k - 2)) (4 * (k - 1))) := by
    intro m'
    have hUb : ∀ a, (Hp 2 + obS1 Hp k α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico (4 * (k - 2)) (4 * (k - 1))) := by
      intro a
      rw [coeff_add]
      exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h2K a))
        (hobS1V (4 * (k - 2)) a (by omega))
    have hGb : ∀ a, (obG k α + C (α (4 * (k - 2)))).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico (4 * (k - 2)) (4 * (k - 1))) := by
      intro a
      rw [coeff_add]
      refine Subalgebra.add_mem _ (hobGVi (4 * (k - 2)) a (by omega)) ?_
      rw [coeff_C]
      split
      · exact (le_sup_right : adjoin R _ ≤ _)
          (subset_adjoin ⟨4 * (k - 2), ⟨by omega, by omega⟩,
            rSlot_ob_band hpar hk (by omega)⟩)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
    simp only [coeff_add, coeff_smul]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_
    · rw [coeff_sub]
      exact Subalgebra.sub_mem _
        (coeff_mem_mul hW2K' (coeff_mem_pow hUb (k - 1)) m')
        ((le_sup_left : K ≤ _) (coeff_mem_pow hKt k m'))
    · exact nsmul_mem (coeff_mem_mul (coeff_mem_mul hW2K'
        (coeff_mem_pow hUb (k - 3))) hGb m') _
    · exact coeff_mem_mul hW2K'
        (coeff_mem_binTail (coeff_mem_pow hUb 2) hGb ((k - 1) / 2)) m'
  have hhiV₁ : ∀ m', (((Hp 2 - (k - 1) • obS1 Hp k α)
        * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Hp 2 ^ k)
      + ((k - 1) / 2) • ((Hp 2 - (k - 1) • obS1 Hp k α)
          * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α)
      + (Hp 2 - (k - 1) • obS1 Hp k α)
          * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α)
            ((k - 1) / 2)).coeff m' ∈ V := fun m' => hK'V _ (hhi₁ m')
  have hhiV₂ : ∀ m', (((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
        * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k)
      + ((k - 1) / 2) • ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * (Hp 2 + obS1 Hp k α) ^ (k - 3) * (obG k α + C (α (4 * (k - 2)))))
      + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
            ((k - 1) / 2)).coeff m' ∈ V := fun m' => hK'V _ (hhi₂ m')
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  refine ⟨F' + ((((Hp 2 - (k - 1) • obS1 Hp k α)
        * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Hp 2 ^ k)
      + ((k - 1) / 2) • ((Hp 2 - (k - 1) • obS1 Hp k α)
          * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α)
      + (Hp 2 - (k - 1) • obS1 Hp k α)
          * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α)
            ((k - 1) / 2)).coeff t
      + (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff t
      + (((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Hp 2 + obS1 Hp k α) ^ (k - 3) * (obG k α + C (α (4 * (k - 2)))))
        + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
              ((k - 1) / 2)).coeff (t + 1)), ?_, ?_⟩
  · refine Subalgebra.add_mem _ hF'V (Subalgebra.add_mem _ (Subalgebra.add_mem _
      (hhiV₁ t) ((le_sup_left : K ≤ _) (hQ₃K t (by omega)))) (hhiV₂ (t + 1)))
  · rw [coeff_combined] at hFe ⊢
    have hd₁ : (Rpair Hp Ht k 2 α).1
        = (((Hp 2 - (k - 1) • obS1 Hp k α) * (Hp 2 + obS1 Hp k α) ^ (k - 1)
            - Hp 2 ^ k)
          + ((k - 1) / 2) • ((Hp 2 - (k - 1) • obS1 Hp k α)
              * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α)
          + (Hp 2 - (k - 1) • obS1 Hp k α)
              * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) ((k - 1) / 2))
          + (Hp 2 - (k - 1) • obS1 Hp k α) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1
          + Q₃ (Hp 1) (α 1) (α 2) (α 3) := by
      rw [Rpair_oddbase_fst' hpar hk]
      ring
    have hd₂ : (Rpair Hp Ht k 2 α).2
        = (((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k)
          + ((k - 1) / 2) • ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
              * (Hp 2 + obS1 Hp k α) ^ (k - 3) * (obG k α + C (α (4 * (k - 2)))))
          + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
              * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
                ((k - 1) / 2))
          + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2
          + C (α 0) := by
      rw [Rpair_oddbase_snd' hpar hk]
      ring
    have hCz : (C (α 0) : A[X]).coeff (t + 1) = 0 := by
      rw [coeff_C, if_neg (by omega)]
    rw [hd₁, hd₂]
    simp only [coeff_add]
    rw [hCz, tLam_ob_inner hpar hk (by omega) (by omega), hγ,
      rSlot_ob_inner hpar hk (by omega) (by omega)]
    linear_combination hFe


/-- Band rows `b₀, b₀+1, b₀+2` of the base certificate, from the 3-row `G`-pair
certificate through the monic multipliers. -/
theorem ob_pivot_band
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 4) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hsd : ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (h2 : IsUnit (2 : R))
    (hind₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.natDegree ≤ 4 * (k - 3))
    (hind₂ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.natDegree ≤ 4 * (k - 3))
    (htop₁₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff (4 * (k - 3)) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff (4 * (k - 3) - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.coeff (4 * (k - 3)) ∈ K) :
    ∀ j, 4 * (k - 2) ≤ j → j < 4 * (k - 2) + 3 → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k 2 α (A := A)) '' Set.Ico (j + 1) (4 * (k - 1))),
      (combined (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2).coeff j
        = algebraMap R A (((tLam k 2 j : ℤ) : R)) * (rSlot k 2 α (A := A)) j + F := by
  obtain ⟨hobS1V, hobGVi, hQ₃V⟩ := ob_windows (α := α) hHp hpar hk
  obtain ⟨hbm, hbd, hUm, hUd, hW1m, hW1d⟩ := ob_deg_facts (α := α) hHp
  obtain ⟨hWI₁K, hWI₂K⟩ := ob_winner_high_K (α := α) hHp hdHt hKt hpar hk
    hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
  obtain ⟨ρ, hρ⟩ := hsd
  have h2d' : (Hp 2).natDegree = 4 := by rw [h2d]; norm_num
  have hQ₃K := Q₃_high_K (Hp := Hp) (α := α) ⟨h1m, by rw [h1d]; norm_num, h1K⟩
  -- the tilde multiplier is monic of degree 4 under the scalar difference
  have hW₂eq : Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))
      = Ht - (k - 1) • (obS1 Hp k α - C ρ) := by rw [hρ]
  have hU₂deg : (obS1 Hp k α - C ρ).degree < Ht.degree := by
    have hU₂d : (obS1 Hp k α - C ρ).natDegree = 2 := by
      rw [sub_eq_add_neg,
        natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
          rw [degree_neg]
          refine lt_of_le_of_lt degree_C_le ?_
          rw [degree_eq_natDegree hbm.ne_zero, hbd]
          exact_mod_cast (by norm_num : (0 : ℕ) < 2))), hbd]
    have hU₂ne : (obS1 Hp k α - C ρ) ≠ 0 := by
      intro h0
      rw [h0] at hU₂d
      simp at hU₂d
    rw [degree_eq_natDegree hU₂ne, degree_eq_natDegree hHt.ne_zero, hdHt, hU₂d]
    exact_mod_cast (by norm_num : (2 : ℕ) < 4)
  have hW2m : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).Monic := by
    rw [hW₂eq]
    have := hHt.add_of_left (q := -((k - 1) • (obS1 Hp k α - C ρ))) (by
      rw [degree_neg]
      exact lt_of_le_of_lt (degree_smul_le _ _) hU₂deg)
    simpa [sub_eq_add_neg] using this
  have hW2d : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree = 4 := by
    rw [hW₂eq, sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        exact lt_of_le_of_lt (degree_smul_le _ _) hU₂deg)), hdHt]
  set γ := rSlot k 2 α (A := A) with hγ
  -- multipliers
  have hL1m : ((Hp 2 - (k - 1) • obS1 Hp k α)
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)).Monic := hW1m.mul (hUm.pow _)
  have hL1d : ((Hp 2 - (k - 1) • obS1 Hp k α)
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)).natDegree = 4 * (k - 2) := by
    rw [hW1m.natDegree_mul (hUm.pow _), hW1d, hUm.natDegree_pow, hUd]
    omega
  have hL2m : ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)).Monic := hW2m.mul (hUm.pow _)
  have hL2d : ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)).natDegree = 4 * (k - 2) := by
    rw [hW2m.natDegree_mul (hUm.pow _), hW2d, hUm.natDegree_pow, hUd]
    omega
  -- multiplier coefficients over the enlarged subalgebra
  set K' := K ⊔ adjoin R (γ '' Set.Ico (4 * (k - 2) + 3)
    (4 * (k - 1))) with hK'
  have hobS1K' : ∀ a, (obS1 Hp k α).coeff a ∈ K' :=
    fun a => hobS1V (4 * (k - 2) + 3) a le_rfl
  have hW1K' : ∀ a, (Hp 2 - (k - 1) • obS1 Hp k α).coeff a ∈ K' := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (h2K a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (hobS1K' a))
  have hW2K' : ∀ a, (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).coeff a ∈ K' := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul, coeff_sub, coeff_sub]
    refine Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (Subalgebra.sub_mem _ (hobS1K' a)
          (Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
            ((le_sup_left : K ≤ _) (h2K a)))))
  have hUK' : ∀ a, (Hp 2 + obS1 Hp k α).coeff a ∈ K' := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h2K a)) (hobS1K' a)
  have hL1K' : ∀ a, ((Hp 2 - (k - 1) • obS1 Hp k α)
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)).coeff a ∈ K' :=
    coeff_mem_mul hW1K' (coeff_mem_pow hUK' (k - 3))
  have hL2K' : ∀ a, ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)).coeff a ∈ K' :=
    coeff_mem_mul hW2K' (coeff_mem_pow hUK' (k - 3))
  -- binomial tails vanish at these rows
  have hBz : ∀ (W' : A[X]) (G' : A[X]), W'.natDegree ≤ 4 → G'.natDegree ≤ 2 →
      ∀ m', 4 * (k - 3) < m' →
      (W' * binTail ((Hp 2 + obS1 Hp k α) ^ 2) G' ((k - 1) / 2)).coeff m' = 0 := by
    intro W' G' hW' hG' m' hm'
    rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · rw [show binTail ((Hp 2 + obS1 Hp k α) ^ 2) G' ((k - 1) / 2) = 0 from by
        show (∑ q ∈ Finset.Icc 2 ((k - 1) / 2), _) = 0
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty], mul_zero,
        coeff_zero]
    · refine coeff_eq_zero_of_natDegree_lt ?_
      have hUsq : ((Hp 2 + obS1 Hp k α) ^ 2).natDegree ≤ 8 := by
        have h := natDegree_pow_le (p := Hp 2 + obS1 Hp k α) (n := 2)
        omega
      have hbt : (binTail ((Hp 2 + obS1 Hp k α) ^ 2) G' ((k - 1) / 2)).natDegree
          ≤ 2 * 2 + ((k - 1) / 2 - 2) * 8 :=
        natDegree_binTail_le hUsq hG' (by omega) _
      have hm8 : ((k - 1) / 2 - 2) * 8 = 4 * (k - 5) := by omega
      have h := natDegree_mul_le (p := W')
        (q := binTail ((Hp 2 + obS1 Hp k α) ^ 2) G' ((k - 1) / 2))
      omega
  have hW₂dle : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree ≤ 4 :=
    le_of_eq hW2d
  have hG₂le : (obG k α + C (α (4 * (k - 2)))).natDegree ≤ 2 := by
    refine le_trans (natDegree_add_le _ _) ?_
    simp only [natDegree_C, max_le_iff]
    exact ⟨obG_natDegree_le, by omega⟩
  -- the lifted 3-row certificate
  have hGc := (obG_cert (k := k) (α := α) h2).mono_left
    (le_sup_left : K ≤ K')
  intro j hj1 hj2
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) (4 * (k - 1))) with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  have hK'V : ∀ x : A, x ∈ K' → x ∈ V := by
    intro x hx
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hx
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨g, ⟨by omega, hg2⟩, rfl⟩)
  obtain ⟨t, rfl⟩ : ∃ t, j = 4 * (k - 2) + t := ⟨j - 4 * (k - 2), by omega⟩
  have ht : t < 3 := by omega
  obtain ⟨F₀, hF₀, hsheq⟩ := CoeffTriangular.shift_pivot hGc
    (by omega : 1 ≤ 4 * (k - 2)) hL1m hL1d hL2m hL2d hL1K' hL2K' t ht
  have hF₀V : F₀ ∈ V := by
    refine SetLike.le_def.1 (sup_le ?_ (adjoin_le ?_)) hF₀
    · intro x hx
      exact hK'V x hx
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      exact (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨4 * (k - 2) + g, ⟨by omega, by omega⟩,
          rSlot_ob_band hpar hk (by omega)⟩)
  -- principal corrections are windowed at these rows
  have hprin₁V : ∀ m', ((Hp 2 - (k - 1) • obS1 Hp k α)
      * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Hp 2 ^ k).coeff m' ∈ V := by
    intro m'
    rw [coeff_sub]
    exact Subalgebra.sub_mem _
      (coeff_mem_mul (fun i => hK'V _ (hW1K' i))
        (coeff_mem_pow (fun i => hK'V _ (hUK' i)) (k - 1)) m')
      (hKV _ (coeff_mem_pow h2K k m'))
  have hprin₂V : ∀ m', ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
      * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k).coeff m' ∈ V := by
    intro m'
    rw [coeff_sub]
    exact Subalgebra.sub_mem _
      (coeff_mem_mul (fun i => hK'V _ (hW2K' i))
        (coeff_mem_pow (fun i => hK'V _ (hUK' i)) (k - 1)) m')
      (hKV _ (coeff_mem_pow hKt k m'))
  -- slope bridge
  have hmk : (k - 1) / 2 * 2 = k - 1 := by omega
  have hslope : algebraMap R A (((tLam k 2 (4 * (k - 2) + t) : ℤ) : R))
      = (((k - 1) / 2 : ℕ) : A)
        * algebraMap R A (if t = 2 then (-2 : R) else 1) := by
    rcases Nat.lt_or_ge t 2 with hmid | hhi
    · rw [tLam_ob_mid hpar hk (by omega) (by omega), if_neg (by omega),
        Int.cast_natCast, map_natCast, map_one, mul_one]
    · have ht2 : t = 2 := by omega
      subst ht2
      rw [tLam_ob_v hpar hk (by omega) (by omega), if_pos rfl]
      have hcast : (((k - 1) / 2 : ℕ) : A) * 2 = ((k - 1 : ℕ) : A) := by
        calc (((k - 1) / 2 : ℕ) : A) * 2 = (((k - 1) / 2 * 2 : ℕ) : A) := by
              push_cast; ring
          _ = _ := by rw [hmk]
      rw [show (((-(k - 1 : ℕ) : ℤ)) : R) = -(((k - 1 : ℕ) : ℤ) : R) from by
          push_cast; ring,
        map_neg, Int.cast_natCast, map_natCast,
        show algebraMap R A (-2 : R) = -2 from by rw [map_neg, map_ofNat]]
      calc -((k - 1 : ℕ) : A) = -((((k - 1) / 2 : ℕ) : A) * 2) := by rw [hcast]
        _ = (((k - 1) / 2 : ℕ) : A) * -2 := by ring
  have hslot : γ (4 * (k - 2) + t) = α (4 * (k - 2) + t) := by
    rw [hγ]
    exact rSlot_ob_band hpar hk (by omega)
  -- decompose the combined coefficient
  have hcO : (combined (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2).coeff
      (4 * (k - 2) + t)
      = (Rpair Hp Ht k 2 α).1.coeff (4 * (k - 2) + t - 1)
        + (Rpair Hp Ht k 2 α).2.coeff (4 * (k - 2) + t) := by
    obtain ⟨s', hs'⟩ : ∃ s', 4 * (k - 2) + t = s' + 1 :=
      ⟨4 * (k - 2) + t - 1, by omega⟩
    rw [hs', coeff_combined, Nat.add_sub_cancel]
  have hcL : (combined ((Hp 2 - (k - 1) • obS1 Hp k α)
        * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α)
      ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
        * (Hp 2 + obS1 Hp k α) ^ (k - 3) * (obG k α + C (α (4 * (k - 2)))))).coeff
      (4 * (k - 2) + t)
      = ((Hp 2 - (k - 1) • obS1 Hp k α)
          * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α).coeff
          (4 * (k - 2) + t - 1)
        + ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Hp 2 + obS1 Hp k α) ^ (k - 3)
            * (obG k α + C (α (4 * (k - 2))))).coeff (4 * (k - 2) + t) := by
    obtain ⟨s', hs'⟩ : ∃ s', 4 * (k - 2) + t = s' + 1 :=
      ⟨4 * (k - 2) + t - 1, by omega⟩
    rw [hs', coeff_combined, Nat.add_sub_cancel]
  have hd₁ : (Rpair Hp Ht k 2 α).1
      = ((Hp 2 - (k - 1) • obS1 Hp k α) * (Hp 2 + obS1 Hp k α) ^ (k - 1)
          - Hp 2 ^ k)
        + ((k - 1) / 2) • ((Hp 2 - (k - 1) • obS1 Hp k α)
            * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α)
        + (Hp 2 - (k - 1) • obS1 Hp k α)
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) ((k - 1) / 2)
        + (Hp 2 - (k - 1) • obS1 Hp k α) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1
        + Q₃ (Hp 1) (α 1) (α 2) (α 3) := by
    rw [Rpair_oddbase_fst' hpar hk]
    ring
  have hd₂ : (Rpair Hp Ht k 2 α).2
      = ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Hp 2 + obS1 Hp k α) ^ (k - 3) * (obG k α + C (α (4 * (k - 2)))))
        + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
              ((k - 1) / 2)
        + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2
        + C (α 0) := by
    rw [Rpair_oddbase_snd' hpar hk]
    ring
  have hCz : (C (α 0) : A[X]).coeff (4 * (k - 2) + t) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  refine ⟨(((k - 1) / 2 : ℕ) : A) * F₀
    + (((Hp 2 - (k - 1) • obS1 Hp k α) * (Hp 2 + obS1 Hp k α) ^ (k - 1)
        - Hp 2 ^ k).coeff (4 * (k - 2) + t - 1)
      + ((Hp 2 - (k - 1) • obS1 Hp k α) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1).coeff (4 * (k - 2) + t - 1)
      + (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff (4 * (k - 2) + t - 1)
      + (((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k).coeff (4 * (k - 2) + t)
        + ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2).coeff (4 * (k - 2) + t))), ?_, ?_⟩
  · refine Subalgebra.add_mem _
      (Subalgebra.mul_mem _ (hKV _ (Subalgebra.natCast_mem _ _)) hF₀V)
      (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
        (hprin₁V _)
        (hKV _ (hWI₁K _ (by omega))))
        (hKV _ (hQ₃K _ (by omega))))
      (Subalgebra.add_mem _ (hprin₂V _)
        (hKV _ (hWI₂K _ (by omega)))))
  · rw [hcO, hd₁, hd₂]
    simp only [coeff_add, coeff_smul]
    rw [hCz, hslope, hslot,
      hBz _ _ (le_of_eq hW1d) obG_natDegree_le _ (by omega),
      hBz _ _ hW₂dle hG₂le _ (by omega)]
    rw [hcL] at hsheq
    simp only [nsmul_eq_mul] at hsheq ⊢
    linear_combination (((k - 1) / 2 : ℕ) : A) * hsheq


/-- The top row `b₀ + 3` of the base certificate: the `u`-pivot from the principal,
slope `-k(k-1)`. -/
theorem ob_pivot_principal
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 4) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hsd : ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (hind₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.natDegree ≤ 4 * (k - 3))
    (hind₂ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.natDegree ≤ 4 * (k - 3))
    (htop₁₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff (4 * (k - 3)) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff (4 * (k - 3) - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.coeff (4 * (k - 3)) ∈ K) :
    ∀ j, 4 * (k - 2) + 3 ≤ j → j < 4 * (k - 1) → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k 2 α (A := A)) '' Set.Ico (j + 1) (4 * (k - 1))),
      (combined (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2).coeff j
        = algebraMap R A (((tLam k 2 j : ℤ) : R)) * (rSlot k 2 α (A := A)) j + F := by
  obtain ⟨hbm, hbd, hUm, hUd, hW1m, hW1d⟩ := ob_deg_facts (α := α) hHp
  obtain ⟨hWI₁K, hWI₂K⟩ := ob_winner_high_K (α := α) hHp hdHt hKt hpar hk
    hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁
  obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
  obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
  obtain ⟨ρ, hρ⟩ := hsd
  have h2d' : (Hp 2).natDegree = 4 := by rw [h2d]; norm_num
  have hQ₃K := Q₃_high_K (Hp := Hp) (α := α) ⟨h1m, by rw [h1d]; norm_num, h1K⟩
  have hobS1cK : ∀ i : ℕ, 1 ≤ i → (obS1 Hp k α).coeff i ∈ K := by
    intro i hi
    show (Hp 1 + (X + C (α (4 * (k - 2) + 3)))).coeff i ∈ K
    rw [coeff_add, coeff_add, coeff_C, if_neg (by omega)]
    refine Subalgebra.add_mem _ (h1K i)
      (Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _))
    rw [Polynomial.coeff_X]
    split
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  have hρK : ρ ∈ K := by
    have h0 := congrArg (fun P : A[X] => P.coeff 0) hρ
    simp only [coeff_sub, coeff_C_zero] at h0
    rw [← h0]
    exact Subalgebra.sub_mem _ (hKt 0) (h2K 0)
  -- W₂ degree bound (no monicity needed here)
  have hW₂dle : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree ≤ 4 := by
    have hb := natDegree_sub_le Ht (Hp 2)
    have ha := natDegree_sub_le (obS1 Hp k α) (Ht - Hp 2)
    have h2 : ((k - 1) • (obS1 Hp k α - (Ht - Hp 2))).natDegree
        ≤ (obS1 Hp k α - (Ht - Hp 2)).natDegree := natDegree_smul_le _ _
    have h3 := natDegree_sub_le Ht ((k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
    have hf : (obS1 Hp k α).natDegree = 2 := hbd
    omega
  -- exposure of the principal at row b₀+2 (first component)
  have hcert := obS1_block_cert (Hp := Hp) (K := K) (k := k) (α := α)
    ⟨h1m, by rw [h1d]; norm_num, h1K⟩
  obtain ⟨F₁, hF₁, hFe₁⟩ := principal_expose (K := K) h2m h2d' h2K hbm hbd
    hcert (by norm_num) (by norm_num) (by norm_num) (by omega : 2 ≤ k - 1)
    0 (by norm_num)
  have hF₁K : F₁ ∈ K := by
    refine mem_of_sup_adjoin_empty ?_ hF₁
    rw [Set.image_eq_empty]
    exact Set.Ico_eq_empty (by omega)
  rw [show k - 1 + 1 = k from by omega] at hFe₁
  rw [show (k - 1 - 1) * 4 + 2 + 0 = 4 * (k - 2) + 2 from by omega] at hFe₁
  -- G-term lead at the read row is known
  have hL1d : ((Hp 2 - (k - 1) • obS1 Hp k α)
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)).natDegree = 4 * (k - 2) := by
    rw [hW1m.natDegree_mul (hUm.pow _), hW1d, hUm.natDegree_pow, hUd]
    omega
  have hlead : ((Hp 2 - (k - 1) • obS1 Hp k α)
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)).coeff (4 * (k - 2)) = 1 := by
    have h := (hW1m.mul (hUm.pow (k - 3))).coeff_natDegree
    rw [hL1d] at h
    exact h
  have hGtopK : ((Hp 2 - (k - 1) • obS1 Hp k α)
      * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α).coeff (4 * (k - 2) + 2) ∈ K := by
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = 4 * (k - 2) + 2 := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge 2 x.2 with hg2 | hl2
    · rw [obG_coeff_high (by omega), mul_zero]
      exact Subalgebra.zero_mem _
    · rcases eq_or_lt_of_le hl2 with heq2 | hlt2
      · rw [show x.2 = 2 from heq2] at hxa ⊢
        rw [show x.1 = 4 * (k - 2) from by omega, hlead, obG_coeff_two, one_mul]
        exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
      · rw [show ((Hp 2 - (k - 1) • obS1 Hp k α)
            * (Hp 2 + obS1 Hp k α) ^ (k - 3)).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
  -- second-component principal is fully known at the top row
  have hU₂cK : ∀ i : ℕ, 1 ≤ i → (obS1 Hp k α - C ρ).coeff i ∈ K := by
    intro i hi
    rw [coeff_sub, coeff_C, if_neg (by omega), sub_zero]
    exact hobS1cK i hi
  have hU₂d : (obS1 Hp k α - C ρ).natDegree = 2 := by
    rw [sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        refine lt_of_le_of_lt degree_C_le ?_
        rw [degree_eq_natDegree hbm.ne_zero, hbd]
        exact_mod_cast (by norm_num : (0 : ℕ) < 2))), hbd]
  have hU₂sqK : ∀ a, 3 ≤ a → ((obS1 Hp k α - C ρ) ^ 2).coeff a ∈ K := by
    intro a ha
    rw [sq, coeff_mul]
    refine Subalgebra.sum_mem _ fun y hy => ?_
    have hya : y.1 + y.2 = a := Finset.mem_antidiagonal.1 hy
    rcases Nat.lt_or_ge 2 y.1 with hg1 | hl1
    · rw [show (obS1 Hp k α - C ρ).coeff y.1 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge 2 y.2 with hg2 | hl2
      · rw [show (obS1 Hp k α - C ρ).coeff y.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hU₂cK y.1 (by omega)) (hU₂cK y.2 (by omega))
  have hW₂eq : Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))
      = Ht - (k - 1) • (obS1 Hp k α - C ρ) := by rw [hρ]
  have hUeq : Hp 2 + obS1 Hp k α = Ht + (obS1 Hp k α - C ρ) := by
    linear_combination -hρ
  have hprinTop₂K : ∀ a, 4 * (k - 1) - 1 ≤ a →
      ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
        * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k).coeff a ∈ K := by
    intro a ha
    have hsplit := mul_pow_split Ht (obS1 Hp k α - C ρ) (n := k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at hsplit
    have hPeq : (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
        * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k
        = (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
            * ((obS1 Hp k α - C ρ) ^ 2 * Ht ^ (k - 1 - 1))
          + uTail Ht (obS1 Hp k α - C ρ) (k - 1) := by
      rw [hW₂eq, hUeq,
        show Ht - (k - 1) • (obS1 Hp k α - C ρ)
          = Ht - ((k - 1 : ℕ) : A[X]) * (obS1 Hp k α - C ρ) from by
          rw [nsmul_eq_mul],
        hsplit]
      ring
    rw [hPeq, coeff_add,
      show (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
        = C ((((k - 1).choose 2 : ℕ) : A) - ((k - 1 : ℕ) : A) * ((k - 1 : ℕ) : A))
      from by rw [map_sub, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast],
      coeff_C_mul]
    refine Subalgebra.add_mem _ (Subalgebra.mul_mem _
      (Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _)
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.natCast_mem _ _))) ?_) ?_
    · rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = a := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge ((k - 1 - 1) * 4) x.2 with hg2 | hl2
      · rw [show (Ht ^ (k - 1 - 1)).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by
            rw [hHt.natDegree_pow, hdHt]
            exact hg2), mul_zero]
        exact Subalgebra.zero_mem _
      · have hx1 : 3 ≤ x.1 := by omega
        exact Subalgebra.mul_mem _ (hU₂sqK x.1 hx1)
          (coeff_mem_pow hKt (k - 1 - 1) x.2)
    · rw [show (uTail Ht (obS1 Hp k α - C ρ) (k - 1)).coeff a = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          refine lt_of_le_of_lt (natDegree_uTail_le (le_of_eq hdHt)
            (le_of_eq hU₂d) (by omega)) ?_
          omega)]
      exact Subalgebra.zero_mem _
  -- binomial tails vanish
  have hBz : ∀ (W' : A[X]) (G' : A[X]), W'.natDegree ≤ 4 → G'.natDegree ≤ 2 →
      ∀ m', 4 * (k - 3) < m' →
      (W' * binTail ((Hp 2 + obS1 Hp k α) ^ 2) G' ((k - 1) / 2)).coeff m' = 0 := by
    intro W' G' hW' hG' m' hm'
    rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · rw [show binTail ((Hp 2 + obS1 Hp k α) ^ 2) G' ((k - 1) / 2) = 0 from by
        show (∑ q ∈ Finset.Icc 2 ((k - 1) / 2), _) = 0
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty], mul_zero,
        coeff_zero]
    · refine coeff_eq_zero_of_natDegree_lt ?_
      have hUsq : ((Hp 2 + obS1 Hp k α) ^ 2).natDegree ≤ 8 := by
        have h := natDegree_pow_le (p := Hp 2 + obS1 Hp k α) (n := 2)
        omega
      have hbt : (binTail ((Hp 2 + obS1 Hp k α) ^ 2) G' ((k - 1) / 2)).natDegree
          ≤ 2 * 2 + ((k - 1) / 2 - 2) * 8 :=
        natDegree_binTail_le hUsq hG' (by omega) _
      have hm8 : ((k - 1) / 2 - 2) * 8 = 4 * (k - 5) := by omega
      have h := natDegree_mul_le (p := W')
        (q := binTail ((Hp 2 + obS1 Hp k α) ^ 2) G' ((k - 1) / 2))
      omega
  have hG₂le : (obG k α + C (α (4 * (k - 2)))).natDegree ≤ 2 := by
    refine le_trans (natDegree_add_le _ _) ?_
    simp only [natDegree_C, max_le_iff]
    exact ⟨obG_natDegree_le, by omega⟩
  -- the second G-term vanishes at the top row
  have hG₂z : ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
      * (Hp 2 + obS1 Hp k α) ^ (k - 3)
      * (obG k α + C (α (4 * (k - 2))))).coeff (4 * (k - 2) + 3) = 0 := by
    refine coeff_eq_zero_of_natDegree_lt ?_
    have hp : ((Hp 2 + obS1 Hp k α) ^ (k - 3)).natDegree ≤ (k - 3) * 4 := by
      refine le_trans natDegree_pow_le ?_
      exact Nat.mul_le_mul_left _ (le_of_eq hUd)
    have hL := natDegree_mul_le
      (p := Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
      (q := (Hp 2 + obS1 Hp k α) ^ (k - 3))
    have h := natDegree_mul_le
      (p := (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
        * (Hp 2 + obS1 Hp k α) ^ (k - 3))
      (q := obG k α + C (α (4 * (k - 2))))
    omega
  intro j hj1 hj2
  have hjeq : j = 4 * (k - 2) + 3 := by omega
  subst hjeq
  set γ := rSlot k 2 α (A := A) with hγ
  -- slope bridge
  have hslope : algebraMap R A (((tLam k 2 (4 * (k - 2) + 3) : ℤ) : R))
      = -((k * (k - 1) : ℕ) : A) := by
    rw [tLam_ob_hi hpar hk (by omega),
      show (((-(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ))) : ℤ) : R)
        = -(((k * (k - 1) : ℕ) : ℤ) : R) from by push_cast; ring,
      map_neg, Int.cast_natCast, map_natCast]
  have hslot : γ (4 * (k - 2) + 3) = α (4 * (k - 2) + 3) := by
    rw [hγ]
    exact rSlot_ob_band hpar hk (by omega)
  have hcO : (combined (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2).coeff
      (4 * (k - 2) + 3)
      = (Rpair Hp Ht k 2 α).1.coeff (4 * (k - 2) + 2)
        + (Rpair Hp Ht k 2 α).2.coeff (4 * (k - 2) + 3) := by
    rw [show 4 * (k - 2) + 3 = (4 * (k - 2) + 2) + 1 from by omega, coeff_combined]
  have hd₁ : (Rpair Hp Ht k 2 α).1
      = ((Hp 2 - (k - 1) • obS1 Hp k α) * (Hp 2 + obS1 Hp k α) ^ (k - 1)
          - Hp 2 ^ k)
        + ((k - 1) / 2) • ((Hp 2 - (k - 1) • obS1 Hp k α)
            * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α)
        + (Hp 2 - (k - 1) • obS1 Hp k α)
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α) ((k - 1) / 2)
        + (Hp 2 - (k - 1) • obS1 Hp k α) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1
        + Q₃ (Hp 1) (α 1) (α 2) (α 3) := by
    rw [Rpair_oddbase_fst' hpar hk]
    ring
  have hd₂ : (Rpair Hp Ht k 2 α).2
      = ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Hp 2 + obS1 Hp k α) ^ (k - 3) * (obG k α + C (α (4 * (k - 2)))))
        + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * binTail ((Hp 2 + obS1 Hp k α) ^ 2) (obG k α + C (α (4 * (k - 2))))
              ((k - 1) / 2)
        + (Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2))) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2
        + C (α 0) := by
    rw [Rpair_oddbase_snd' hpar hk]
    ring
  have hCz : (C (α 0) : A[X]).coeff (4 * (k - 2) + 3) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  refine ⟨(((k - 1) / 2 : ℕ) : A) * ((Hp 2 - (k - 1) • obS1 Hp k α)
        * (Hp 2 + obS1 Hp k α) ^ (k - 3) * obG k α).coeff (4 * (k - 2) + 2)
      + ((Hp 2 - (k - 1) • obS1 Hp k α) * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1).coeff (4 * (k - 2) + 2)
      + (Q₃ (Hp 1) (α 1) (α 2) (α 3)).coeff (4 * (k - 2) + 2)
      + (((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
          * (Hp 2 + obS1 Hp k α) ^ (k - 1) - Ht ^ k).coeff (4 * (k - 2) + 3)
        + ((Ht - (k - 1) • (obS1 Hp k α - (Ht - Hp 2)))
            * (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2).coeff (4 * (k - 2) + 3))
      + F₁, ?_, ?_⟩
  · refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
      (Subalgebra.add_mem _
        ((le_sup_left : K ≤ _) (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          hGtopK))
        ((le_sup_left : K ≤ _) (hWI₁K _ (by omega))))
      ((le_sup_left : K ≤ _) (hQ₃K _ (by omega))))
      (Subalgebra.add_mem _
        ((le_sup_left : K ≤ _) (hprinTop₂K _ (by omega)))
        ((le_sup_left : K ≤ _) (hWI₂K _ (by omega)))))
      ((le_sup_left : K ≤ _) hF₁K)
  · rw [hcO, hd₁, hd₂]
    simp only [coeff_add, coeff_smul]
    rw [hCz, hslope, hslot,
      hBz _ _ (le_of_eq hW1d) obG_natDegree_le _ (by omega),
      hBz _ _ hW₂dle hG₂le _ (by omega), hG₂z]
    simp only [nsmul_eq_mul] at hFe₁ ⊢
    linear_combination hFe₁


/-- **Odd base branch step** (`l = 2`): the full triangular certificate for the
level-`(k, 2)` remainder pair, assembled from the inner `((k-1)/2, 3)` certificate. -/
theorem Rk2l_tri_oddbase_step
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 4) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hsd : ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k)
    (h2 : IsUnit (2 : R)) (hum : IsUnit ((((k - 1) / 2 : ℕ) : ℤ) : R))
    (huk : IsUnit (((k : ℕ) : ℤ) : R)) (huk1 : IsUnit (((k - 1 : ℕ) : ℤ) : R))
    (hin : CoeffTriangular (K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
        Set.Ico (4 * (k - 2)) (4 * (k - 1))))
      (rSlot ((k - 1) / 2) 3 (fun j => α (4 + j)))
      (fun j => ((tLam ((k - 1) / 2) 3 j : ℤ) : R)) (4 * (k - 3))
      (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1
      (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2)
    (hind₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.natDegree ≤ 4 * (k - 3))
    (hind₂ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.natDegree ≤ 4 * (k - 3))
    (htop₁₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff (4 * (k - 3)) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).1.coeff (4 * (k - 3) - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp 3 (obH8 Hp k α))
        (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
        (fun j => α (4 + j))).2.coeff (4 * (k - 3)) ∈ K) :
    CoeffTriangular K (rSlot k 2 α) (fun j => ((tLam k 2 j : ℤ) : R))
      (4 * (k - 1)) (Rpair Hp Ht k 2 α).1 (Rpair Hp Ht k 2 α).2 where
  unit j hj := by
    rcases Nat.lt_or_ge j 4 with hlow | h1
    · rw [tLam_ob_low hpar hk hlow, Int.cast_one]
      exact isUnit_one
    · rcases Nat.lt_or_ge j (4 * (k - 2)) with hinn | hb
      · rw [tLam_ob_inner hpar hk h1 hinn]
        exact hin.unit _ (by omega)
      · rcases Nat.lt_or_ge j (4 * (k - 2) + 2) with hm1 | hm
        · rw [tLam_ob_mid hpar hk hb hm1]
          exact hum
        · rcases Nat.lt_or_ge j (4 * (k - 2) + 3) with hm2 | hhi
          · rw [tLam_ob_v hpar hk hm hm2,
              show (((-(k - 1 : ℕ) : ℤ)) : R) = -(((k - 1 : ℕ) : ℤ) : R) from by
                push_cast; ring]
            exact huk1.neg
          · rw [tLam_ob_hi hpar hk hhi,
              show (((-(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ))) : ℤ) : R)
                = -((((k : ℕ) : ℤ) : R) * (((k - 1 : ℕ) : ℤ) : R)) from by
                push_cast; ring]
            exact (huk.mul huk1).neg
  supp₁ := ob_supp₁ hHp hpar hk (fun j => hin.supp₁ j) hind₁ htop₁₁
  supp₂ := ob_supp₂ hHp hHt hdHt hKt hsd hpar hk (fun j => hin.supp₂ j) hind₂
  pivot j hj := by
    rcases Nat.lt_or_ge j 4 with hlow | h1
    · obtain ⟨hrest₁, hrest₂⟩ := ob_rest_mem hHp hKt hpar hk
        (fun j => hin.supp₁ j) (fun j => hin.supp₂ j)
      exact ob_pivot_low hHp hpar hk hrest₁ hrest₂ j hlow
    · rcases Nat.lt_or_ge j (4 * (k - 2)) with hinn | hb
      · exact ob_pivot_inner hHp hHt hdHt hKt hsd hpar hk hin j h1 hinn
      · rcases Nat.lt_or_ge j (4 * (k - 2) + 3) with hband | hpr
        · exact ob_pivot_band hHp hHt hdHt hKt hsd hpar hk h2
            hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁ j hb hband
        · exact ob_pivot_principal hHp hHt hdHt hKt hsd hpar hk
            hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁ j hpr hj

end FastPoly
