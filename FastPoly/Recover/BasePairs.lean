import FastPoly.Recover.Context

/-!
# Base compatible pairs

The leaf pairs of the construction tree (paper `lem:compatible-auxhead-deg2`,
`lem:compatible-monic-plus-constants`, `lem:compatible-aux-add-left`): scalar shifts of a
known monic polynomial, constants added to a power, and the block-triangular pair
`(H + Q, H + b)`.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]

section basepairs

variable {K : Subalgebra R A}

/-- Adding a constant to a monic polynomial of positive degree. -/
theorem monic_add_C {H : A[X]} (hH : H.Monic) (hpos : 0 < H.natDegree) (b : A) :
    (H + C b).Monic ∧ (H + C b).natDegree = H.natDegree := by
  have hdeg : (C b).degree < H.degree := by
    refine lt_of_le_of_lt degree_C_le ?_
    rw [degree_eq_natDegree hH.ne_zero]
    exact_mod_cast hpos
  refine ⟨hH.add_of_left hdeg, ?_⟩
  have := degree_add_eq_left_of_degree_lt hdeg
  exact natDegree_eq_of_degree_eq_some (by rw [this, degree_eq_natDegree hH.ne_zero])

/-- **Scalar shifts of a known monic polynomial** (paper `lem:compatible-auxhead-deg2`,
stated for any degree `≥ 2`): `(H + b₁, H + b₂)` is compatible on `{0, 1}` given `H`. -/
theorem compatiblePair_shifts {H : A[X]} {h : ℕ} (hH : H.Monic) (hd : H.natDegree = h)
    (h2 : 2 ≤ h) (hK : ∀ j, H.coeff j ∈ K) (b₁ b₂ : A) :
    CompatiblePair K (H + C b₁) (H + C b₂) h ({0, 1} : Finset ℕ) := by
  have hco : ∀ (b : A) (j : ℕ), (H + C b).coeff j = H.coeff j + if j = 0 then b else 0 := by
    intro b j
    rw [coeff_add, coeff_C]
  set φ := combined (H + C b₁) (H + C b₂) with hφ
  have hφ1 : φ.coeff 1 = (H.coeff 0 + b₁) + H.coeff 1 := by
    rw [hφ, show (1 : ℕ) = 0 + 1 from rfl, coeff_combined, hco, hco]
    simp
  have hφ0 : φ.coeff 0 = H.coeff 0 + b₂ := by
    rw [hφ, coeff_combined_zero, hco]
    simp
  have hmem : ∀ i ∈ ({0, 1} : Finset ℕ), i ∈ ({0, 1} : Finset ℕ) := fun i hi => hi
  refine
    { mem₁ := ?_
      mem₂ := ?_
      monic₁ := (monic_add_C hH (by omega) b₁).1
      monic₂ := (monic_add_C hH (by omega) b₂).1
      natDegree₁ := by rw [(monic_add_C hH (by omega) b₁).2, hd]
      natDegree₂ := by rw [(monic_add_C hH (by omega) b₂).2, hd]
      window := by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact Finset.mem_range.2 (by omega)
        · rw [Finset.mem_singleton.1 hi]
          exact Finset.mem_range.2 (by omega) }
  · intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- (H + b₁).coeff 0 = φ.coeff 1 - H.coeff 1
      have hkey : (H + C b₁).coeff 0 = φ.coeff 1 - H.coeff 1 := by
        rw [hco, hφ1]; simp
      rw [hkey]
      exact Subalgebra.sub_mem _
        (coeff_mem_Vis (by simp) (by omega)) (known_mem_Vis (hK 1))
    · have hkey : (H + C b₁).coeff j = H.coeff j := by rw [hco, if_neg (by omega), add_zero]
      rw [hkey]
      exact known_mem_Vis (hK j)
  · intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hkey : (H + C b₂).coeff 0 = φ.coeff 0 := by rw [hco, hφ0]; simp
      rw [hkey]
      exact coeff_mem_Vis (by simp) (by omega)
    · have hkey : (H + C b₂).coeff j = H.coeff j := by rw [hco, if_neg (by omega), add_zero]
      rw [hkey]
      exact known_mem_Vis (hK j)

/-- **Constants added to a power** (paper `lem:compatible-monic-plus-constants`):
`(Xⁿ + u, Xⁿ + v)` is compatible on `{0, 1}`. -/
theorem compatiblePair_pow_add_consts {N : ℕ} (h2 : 2 ≤ N) (u v : A) :
    CompatiblePair K (X ^ N + C u) (X ^ N + C v) N ({0, 1} : Finset ℕ) := by
  have hXN : (X ^ N : A[X]).Monic := monic_X_pow N
  have hdX : (X ^ N : A[X]).natDegree = N := natDegree_X_pow N
  have hco : ∀ (b : A) (j : ℕ),
      ((X ^ N : A[X]) + C b).coeff j = (if j = N then 1 else 0) + if j = 0 then b else 0 := by
    intro b j
    rw [coeff_add, coeff_C, coeff_X_pow]
  set φ := combined ((X ^ N : A[X]) + C u) ((X ^ N : A[X]) + C v) with hφ
  have hφ1 : φ.coeff 1 = u := by
    rw [hφ, show (1 : ℕ) = 0 + 1 from rfl, coeff_combined, hco, hco]
    rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega)]
    ring
  have hφ0 : φ.coeff 0 = v := by
    rw [hφ, coeff_combined_zero, hco, if_neg (by omega), if_pos rfl]
    ring
  refine
    { mem₁ := ?_
      mem₂ := ?_
      monic₁ := (monic_add_C hXN (by omega) u).1
      monic₂ := (monic_add_C hXN (by omega) v).1
      natDegree₁ := by rw [(monic_add_C hXN (by omega) u).2, hdX]
      natDegree₂ := by rw [(monic_add_C hXN (by omega) v).2, hdX]
      window := by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact Finset.mem_range.2 (by omega)
        · rw [Finset.mem_singleton.1 hi]
          exact Finset.mem_range.2 (by omega) }
  · intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hkey : ((X ^ N : A[X]) + C u).coeff 0 = φ.coeff 1 := by
        rw [hco, hφ1, if_neg (by omega), if_pos rfl]; ring
      rw [hkey]
      exact coeff_mem_Vis (by simp) (by omega)
    · have h0 : (if j = 0 then u else 0) = 0 := if_neg (by omega)
      have hkey : ((X ^ N : A[X]) + C u).coeff j = if j = N then 1 else 0 := by
        rw [hco, h0, add_zero]
      rw [hkey]
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
  · intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hkey : ((X ^ N : A[X]) + C v).coeff 0 = φ.coeff 0 := by
        rw [hco, hφ0, if_neg (by omega), if_pos rfl]; ring
      rw [hkey]
      exact coeff_mem_Vis (by simp) (by omega)
    · have h0 : (if j = 0 then v else 0) = 0 := if_neg (by omega)
      have hkey : ((X ^ N : A[X]) + C v).coeff j = if j = N then 1 else 0 := by
        rw [hco, h0, add_zero]
      rw [hkey]
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _

/-- **The block-triangular pair** (paper `lem:compatible-aux-add-left`): for a known monic
`H` of degree `h` and a monic `Q` of degree `q < h`, the pair `(H + Q, H + b)` is compatible
on `{0, …, q}` given `H`. -/
theorem compatiblePair_aux_add_left {H Q : A[X]} {h q : ℕ}
    (hH : H.Monic) (hd : H.natDegree = h) (hK : ∀ j, H.coeff j ∈ K)
    (hQ : Q.Monic) (hdQ : Q.natDegree = q) (hqh : q < h) (b : A) :
    CompatiblePair K (H + Q) (H + C b) h (Finset.range (q + 1)) := by
  have hQlead : Q.coeff q = 1 := by rw [← hdQ]; exact hQ.coeff_natDegree
  have hdegQ : Q.degree < H.degree := by
    rw [degree_eq_natDegree hH.ne_zero, degree_eq_natDegree hQ.ne_zero, hd, hdQ]
    exact_mod_cast hqh
  set φ := combined (H + Q) (H + C b) with hφ
  have hφc : ∀ j, φ.coeff (j + 1) = (H.coeff j + Q.coeff j) + (H.coeff (j + 1)
      + if j + 1 = 0 then b else 0) := by
    intro j
    rw [hφ, coeff_combined, coeff_add, coeff_add, coeff_C]
  have hφ0 : φ.coeff 0 = H.coeff 0 + b := by
    rw [hφ, coeff_combined_zero, coeff_add, coeff_C, if_pos rfl]
  refine
    { mem₁ := ?_
      mem₂ := ?_
      monic₁ := hH.add_of_left hdegQ
      monic₂ := (monic_add_C hH (by omega) b).1
      natDegree₁ := by
        have := degree_add_eq_left_of_degree_lt hdegQ
        exact natDegree_eq_of_degree_eq_some
          (by rw [this, degree_eq_natDegree hH.ne_zero, hd])
      natDegree₂ := by rw [(monic_add_C hH (by omega) b).2, hd]
      window := by
        intro i hi
        exact Finset.mem_range.2 (by have := Finset.mem_range.1 hi; omega) }
  · intro j
    rcases Nat.lt_or_ge j q with hjq | hjq
    · -- fresh coefficient of Q, from φ at j+1 ∈ G
      have hkey : (H + Q).coeff j = φ.coeff (j + 1) - H.coeff (j + 1) := by
        rw [coeff_add, hφc, if_neg (by omega)]; ring
      rw [hkey]
      exact Subalgebra.sub_mem _
        (coeff_mem_Vis (Finset.mem_range.2 (by omega)) (by omega))
        (known_mem_Vis (hK (j + 1)))
    · rcases eq_or_lt_of_le hjq with heq | hlt
      · have hkey : (H + Q).coeff j = H.coeff j + 1 := by
          rw [coeff_add, ← heq, hQlead]
        rw [hkey]
        exact Subalgebra.add_mem _ (known_mem_Vis (hK j)) (Subalgebra.one_mem _)
      · have hz : Q.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hdQ]; exact hlt)
        have hkey : (H + Q).coeff j = H.coeff j := by rw [coeff_add, hz, add_zero]
        rw [hkey]
        exact known_mem_Vis (hK j)
  · intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hkey : (H + C b).coeff 0 = φ.coeff 0 := by
        rw [coeff_add, coeff_C, if_pos rfl, hφ0]
      rw [hkey]
      exact coeff_mem_Vis (Finset.mem_range.2 (by omega)) (by omega)
    · have hkey : (H + C b).coeff j = H.coeff j := by
        rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
      rw [hkey]
      exact known_mem_Vis (hK j)

/-- **Padding a low pair** (paper `lem:compatible-low-padding`): for `N ≥ r ≥ 1` and `Q`
monic of degree `r - 1`, the pair `(Xᴺ + Q, Xᴺ + b)` is compatible on `{0, …, r-1}`. -/
theorem compatiblePair_low_padding {Q : A[X]} {N r : ℕ} (hr : 1 ≤ r) (hNr : r ≤ N)
    (hQ : Q.Monic) (hdQ : Q.natDegree = r - 1) (b : A) :
    CompatiblePair K ((X ^ N : A[X]) + Q) ((X ^ N : A[X]) + C b) N (Finset.range r) := by
  have hXN : (X ^ N : A[X]).Monic := monic_X_pow N
  have hdegQ : Q.degree < (X ^ N : A[X]).degree := by
    rw [degree_eq_natDegree hQ.ne_zero, degree_X_pow, hdQ]
    exact_mod_cast (by omega : r - 1 < N)
  have hdegC : (C b).degree < (X ^ N : A[X]).degree := by
    refine lt_of_le_of_lt degree_C_le ?_
    rw [degree_X_pow]
    exact_mod_cast (by omega : 0 < N)
  have hQlead : Q.coeff (r - 1) = 1 := by rw [← hdQ]; exact hQ.coeff_natDegree
  set φ := combined ((X ^ N : A[X]) + Q) ((X ^ N : A[X]) + C b) with hφ
  have hco₁ : ∀ j, ((X ^ N : A[X]) + Q).coeff j = (if j = N then 1 else 0) + Q.coeff j := by
    intro j
    rw [coeff_add, coeff_X_pow]
  have hco₂ : ∀ j, ((X ^ N : A[X]) + C b).coeff j
      = (if j = N then 1 else 0) + if j = 0 then b else 0 := by
    intro j
    rw [coeff_add, coeff_X_pow, coeff_C]
  have hφc : ∀ j, j + 1 < N → φ.coeff (j + 1) = Q.coeff j := by
    intro j hj
    rw [hφ, coeff_combined, hco₁, hco₂, if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    ring
  have hφ0 : φ.coeff 0 = b := by
    rw [hφ, coeff_combined_zero, hco₂, if_neg (by omega), if_pos rfl]
    ring
  refine
    { mem₁ := ?_
      mem₂ := ?_
      monic₁ := hXN.add_of_left hdegQ
      monic₂ := hXN.add_of_left hdegC
      natDegree₁ := by
        have := degree_add_eq_left_of_degree_lt hdegQ
        exact natDegree_eq_of_degree_eq_some (by rw [this, degree_X_pow])
      natDegree₂ := by
        have := degree_add_eq_left_of_degree_lt hdegC
        exact natDegree_eq_of_degree_eq_some (by rw [this, degree_X_pow])
      window := by
        intro i hi
        exact Finset.mem_range.2 (by have := Finset.mem_range.1 hi; omega) }
  · intro j
    rcases Nat.lt_or_ge j (r - 1) with hjr | hjr
    · -- a fresh coefficient of Q, visible at degree j+1
      have hkey : ((X ^ N : A[X]) + Q).coeff j = φ.coeff (j + 1) := by
        rw [hco₁, if_neg (by omega), hφc j (by omega)]
        ring
      rw [hkey]
      exact coeff_mem_Vis (Finset.mem_range.2 (by omega)) (by omega)
    · -- constants: the leading 1 of Q, zeros, and the leading 1 of X^N
      have hQj : Q.coeff j = if j = r - 1 then 1 else 0 := by
        rcases eq_or_ne j (r - 1) with rfl | hne
        · rw [hQlead, if_pos rfl]
        · rw [if_neg hne, coeff_eq_zero_of_natDegree_lt (by rw [hdQ]; omega)]
      rw [hco₁, hQj]
      refine Subalgebra.add_mem _ ?_ ?_
      · split
        · exact Subalgebra.one_mem _
        · exact Subalgebra.zero_mem _
      · split
        · exact Subalgebra.one_mem _
        · exact Subalgebra.zero_mem _
  · intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hkey : ((X ^ N : A[X]) + C b).coeff 0 = φ.coeff 0 := by
        rw [hco₂, if_neg (by omega), if_pos rfl, hφ0]
        ring
      rw [hkey]
      exact coeff_mem_Vis (Finset.mem_range.2 (by omega)) (by omega)
    · have h0 : (if j = 0 then b else 0) = 0 := if_neg (by omega)
      rw [hco₂, h0, add_zero]
      split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _

end basepairs

end FastPoly
