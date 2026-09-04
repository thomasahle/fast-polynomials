import FastPoly.Section5.Rk2lTri

/-!
# `lem:Rk2l`(3): the odd main branch certificate
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}

omit [Nontrivial A] in
/-- `tLam`, odd main branch (`l ≥ 3`): the five slope bands. -/
theorem tLam_odd_low (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {j : ℕ}
    (hj : j < 2 ^ l) : tLam k l j = 1 := by
  show tLamF k k l j = 1
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_neg hl, if_pos hj]

omit [Nontrivial A] in
theorem tLam_odd_inner (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {j : ℕ}
    (h1 : 2 ^ l ≤ j) (h2 : j < (k - 2) * 2 ^ l) :
    tLam k l j = tLam ((k - 1) / 2) (l + 1) (j - 2 ^ l) := by
  show tLamF k k l j = tLamF ((k - 1) / 2) ((k - 1) / 2) (l + 1) (j - 2 ^ l)
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (Nat.not_lt.mpr h1), if_pos h2]
  exact tLamF_fuel _ _ _ (by omega) (by omega) (l + 1) (j - 2 ^ l)

omit [Nontrivial A] in
theorem tLam_odd_mid1 (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {j : ℕ}
    (h1 : (k - 2) * 2 ^ l ≤ j) (h2 : j < (k - 2) * 2 ^ l + 2 ^ (l - 2)) :
    tLam k l j = (((k - 1) / 2 : ℕ) : ℤ) := by
  show tLamF k k l j = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have h0 : 2 ^ l ≤ (f + 1 - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ f + 1 - 2 from by omega)
    omega
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (Nat.not_lt.mpr (le_trans h0 h1)), if_neg (Nat.not_lt.mpr h1), if_pos h2]

omit [Nontrivial A] in
theorem tLam_odd_mid2 (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {j : ℕ}
    (h1 : (k - 2) * 2 ^ l + 2 ^ (l - 2) ≤ j)
    (h2 : j < (k - 2) * 2 ^ l + 2 ^ (l - 1)) :
    tLam k l j = -(((k - 1 : ℕ)) : ℤ) := by
  show tLamF k k l j = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have h0 : 2 ^ l ≤ (f + 1 - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ f + 1 - 2 from by omega)
    omega
  have hb1 : (f + 1 - 2) * 2 ^ l ≤ j := le_trans (Nat.le_add_right _ _) h1
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (Nat.not_lt.mpr (le_trans h0 hb1)), if_neg (Nat.not_lt.mpr hb1),
    if_neg (Nat.not_lt.mpr h1), if_pos h2]

omit [Nontrivial A] in
theorem tLam_odd_hi (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {j : ℕ}
    (h1 : (k - 2) * 2 ^ l + 2 ^ (l - 1) ≤ j) :
    tLam k l j = -(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ)) := by
  show tLamF k k l j = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have h0 : 2 ^ l ≤ (f + 1 - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ f + 1 - 2 from by omega)
    omega
  have hpow : (2 : ℕ) ^ (l - 2) ≤ 2 ^ (l - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hb2 : (f + 1 - 2) * 2 ^ l + 2 ^ (l - 2) ≤ j :=
    le_trans (Nat.add_le_add_left hpow _) h1
  have hb1 : (f + 1 - 2) * 2 ^ l ≤ j := le_trans (Nat.le_add_right _ _) h1
  rw [tLamF_succ, if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (Nat.not_lt.mpr (le_trans h0 hb1)), if_neg (Nat.not_lt.mpr hb1),
    if_neg (Nat.not_lt.mpr hb2), if_neg (Nat.not_lt.mpr h1)]

omit [Nontrivial A] in
/-- `rSlot`, odd main branch: the row bands. -/
theorem rSlot_odd_zero (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) :
    rSlot (A := A) k l α 0 = α 0 := by
  show rSlotF k k l α 0 = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar, if_neg hl,
    if_pos rfl]

omit [Nontrivial A] in
theorem rSlot_odd_mers (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {r : ℕ}
    (h1 : 1 ≤ r) (h2 : r < 2 ^ l) :
    rSlot (A := A) k l α r = peelSlot l (fun j => α (1 + j)) (r - 1) := by
  show rSlotF k k l α r = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (by omega), if_pos h2]

omit [Nontrivial A] in
theorem rSlot_odd_inner (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {r : ℕ}
    (h1 : 2 ^ l ≤ r) (h2 : r < (k - 2) * 2 ^ l) :
    rSlot (A := A) k l α r
      = rSlot ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)) (r - 2 ^ l) := by
  show rSlotF k k l α r = rSlotF ((k - 1) / 2) ((k - 1) / 2) (l + 1) _ (r - 2 ^ l)
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (by omega), if_neg (Nat.not_lt.mpr h1), if_pos h2]
  exact rSlotF_fuel ((f + 1 - 1) / 2) f ((f + 1 - 1) / 2) (by omega) (by omega)
    (l + 1) _ (r - 2 ^ l)

omit [Nontrivial A] in
theorem rSlot_odd_b0 (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) :
    rSlot (A := A) k l α ((k - 2) * 2 ^ l) = α ((k - 2) * 2 ^ l) := by
  show rSlotF k k l α ((k - 2) * 2 ^ l) = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have h0 : 2 ^ l ≤ (f + 1 - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ f + 1 - 2 from by omega)
    omega
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (by omega), if_neg (Nat.not_lt.mpr h0),
    if_neg (Nat.not_lt.mpr le_rfl), if_pos rfl]

omit [Nontrivial A] in
theorem rSlot_odd_oS3 (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {r : ℕ}
    (h1 : (k - 2) * 2 ^ l < r) (h2 : r < (k - 2) * 2 ^ l + 2 ^ (l - 2)) :
    rSlot (A := A) k l α r
      = peelSlot (l - 2) (fun j => α ((k - 2) * 2 ^ l + 1 + j))
          (r - (k - 2) * 2 ^ l - 1) := by
  show rSlotF k k l α r = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have h0 : 2 ^ l ≤ (f + 1 - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ f + 1 - 2 from by omega)
    omega
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos h2]

omit [Nontrivial A] in
theorem rSlot_odd_eps (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) :
    rSlot (A := A) k l α ((k - 2) * 2 ^ l + 2 ^ (l - 2))
      = α ((k - 2) * 2 ^ l + 2 ^ (l - 2)) := by
  show rSlotF k k l α ((k - 2) * 2 ^ l + 2 ^ (l - 2)) = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hp2 : 1 ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have h0 : 2 ^ l ≤ (f + 1 - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ f + 1 - 2 from by omega)
    omega
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

omit [Nontrivial A] in
theorem rSlot_odd_oS2 (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {r : ℕ}
    (h1 : (k - 2) * 2 ^ l + 2 ^ (l - 2) < r)
    (h2 : r < (k - 2) * 2 ^ l + 2 ^ (l - 1)) :
    rSlot (A := A) k l α r
      = peelSlot (l - 2) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 2) + 1 + j))
          (r - (k - 2) * 2 ^ l - 2 ^ (l - 2) - 1) := by
  show rSlotF k k l α r = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hp2 : 1 ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have h0 : 2 ^ l ≤ (f + 1 - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ f + 1 - 2 from by omega)
    omega
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos h2]

omit [Nontrivial A] in
theorem rSlot_odd_delta (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) :
    rSlot (A := A) k l α ((k - 2) * 2 ^ l + 2 ^ (l - 1))
      = α ((k - 2) * 2 ^ l + 2 ^ (l - 1)) := by
  show rSlotF k k l α ((k - 2) * 2 ^ l + 2 ^ (l - 1)) = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hp2 : 1 ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have hpow : (2 : ℕ) ^ (l - 2) < 2 ^ (l - 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have h0 : 2 ^ l ≤ (f + 1 - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ f + 1 - 2 from by omega)
    omega
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

omit [Nontrivial A] in
theorem rSlot_odd_tS1 (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {r : ℕ}
    (h1 : (k - 2) * 2 ^ l + 2 ^ (l - 1) < r) :
    rSlot (A := A) k l α r
      = peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
          (r - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1) := by
  show rSlotF k k l α r = _
  obtain ⟨f, rfl⟩ : ∃ f, k = f + 1 := ⟨k - 1, by omega⟩
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hp2 : 1 ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have hpow : (2 : ℕ) ^ (l - 2) < 2 ^ (l - 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have h0 : 2 ^ l ≤ (f + 1 - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ f + 1 - 2 from by omega)
    omega
  rw [rSlotF_succ, if_neg (by omega), if_neg (by omega), if_neg hpar, if_neg hl,
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

omit [Nontrivial A] in
/-- The odd correction pair is the `(2, l-1)` base pair under the band shift. -/
theorem oG1_shift :
    oG1 Hp k l α = eE1 Hp 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)) := by
  show oS3 Hp k l α - oS2 Hp k l α ^ 2
    = eS2 Hp 2 (l - 1) _ - tS1 Hp 2 (l - 1) _ ^ 2
  have h1 : oS3 Hp k l α = eS2 Hp 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)) := by
    show peel Hp (l - 2) _ = peel Hp (l - 1 - 1) _
    have hll : l - 1 - 1 = l - 2 := by omega
    rw [hll]
    congr 1
    funext j
    show α ((k - 2) * 2 ^ l + 1 + j)
      = α ((k - 2) * 2 ^ l + ((2 - 2) * 2 ^ (l - 1) + 1 + j))
    congr 1
    omega
  have h2 : oS2 Hp k l α = tS1 Hp 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)) := by
    show Hp (l - 2) + peel Hp (l - 2) _ = Hp (l - 1 - 1) + peel Hp (l - 1 - 1) _
    have hll : l - 1 - 1 = l - 2 := by omega
    rw [hll]
    congr 2
    funext j
    congr 1
    omega
  rw [h1, h2]

omit [Nontrivial A] in
theorem oG2_shift :
    oG2 Hp k l α = eE2 Hp 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)) := by
  show C (α ((k - 2) * 2 ^ l)) - oS2t Hp k l α ^ 2
    = C ((fun j => α ((k - 2) * 2 ^ l + j)) ((2 - 2) * 2 ^ (l - 1)))
      - tS1t Hp 2 (l - 1) _ ^ 2
  have h1 : α ((k - 2) * 2 ^ l)
      = (fun j => α ((k - 2) * 2 ^ l + j)) ((2 - 2) * 2 ^ (l - 1)) := by
    show α ((k - 2) * 2 ^ l) = α ((k - 2) * 2 ^ l + (2 - 2) * 2 ^ (l - 1))
    congr 1
    omega
  have h2 : oS2t Hp k l α = tS1t Hp 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)) := by
    show Hp (l - 2) + C (α ((k - 2) * 2 ^ l + 2 ^ (l - 2)))
      = Hp (l - 1 - 1)
        + C (α ((k - 2) * 2 ^ l + ((2 - 2) * 2 ^ (l - 1) + 2 ^ (l - 1 - 1))))
    have hll : l - 1 - 1 = l - 2 := by omega
    rw [hll]
    congr 2
    congr 1
    omega
  rw [h2, ← h1]

/-- The band certificate of the odd correction pair. -/
theorem oG_cert
    (hHp : ∀ i, 1 ≤ i → i < l - 1 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K)) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R)) :
    CoeffTriangular K (rSlot 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)))
      (fun j => ((tLam 2 (l - 1) j : ℤ) : R)) (2 ^ (l - 1))
      (oG1 Hp k l α) (oG2 Hp k l α) := by
  rw [oG1_shift, oG2_shift]
  exact
    { unit := fun j hj => by
        rcases Nat.lt_or_ge j (2 ^ (l - 1 - 1)) with hlt | hge
        · rw [tLam_two_lo hlt, Int.cast_one]
          exact isUnit_one
        · rw [tLam_two_hi hge,
            show (((-2 : ℤ) : R)) = -2 from by push_cast; ring]
          exact h2.neg
      supp₁ := base_supp₁ hHp (by omega)
      supp₂ := base_supp₂ hHp (by omega)
      pivot := base_pivot hHp (by omega) }


/-- General block certificate for `S⁽¹⁾₁ = H_{2^{l-1}} + Q` at any level's offsets. -/
theorem tS1_block_cert
    (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    CoeffTriangular K
      (peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j)))
      (fun _ => (1 : R)) (2 ^ (l - 1) - 1) 0
      (tS1 Hp k l α - X ^ (2 ^ (l - 1))) := by
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  have hmers := peel_unitriangular Hp (l - 1)
    (fun i h1 h2 => hHp i h1 (by omega)) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
  have h1p : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have := add_block_cert (Hh := Hp (l - 1)) (D := 2 ^ (l - 1)) hK hmers
  exact this

/-- General one-row certificate for `S⁽²⁾₁ = H_{2^{l-1}} + δ` at any level's offsets. -/
theorem tS1t_block_cert
    (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    CoeffTriangular K (fun _ => α ((k - 2) * 2 ^ l + 2 ^ (l - 1)))
      (fun _ => (1 : R)) 1 0 (tS1t Hp k l α - X ^ (2 ^ (l - 1))) := by
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  have h1p : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hco : ∀ j, (tS1t Hp k l α - X ^ (2 ^ (l - 1))).coeff j
      = ((Hp (l - 1)).coeff j - (X ^ (2 ^ (l - 1)) : A[X]).coeff j)
        + (C (α ((k - 2) * 2 ^ l + 2 ^ (l - 1))) : A[X]).coeff j := by
    intro j
    show (Hp (l - 1) + C (α ((k - 2) * 2 ^ l + 2 ^ (l - 1)))
      - X ^ (2 ^ (l - 1))).coeff j = _
    rw [coeff_sub, coeff_add]
    ring
  have hKp : ∀ j, (Hp (l - 1)).coeff j - (X ^ (2 ^ (l - 1)) : A[X]).coeff j ∈ K := by
    intro j
    refine Subalgebra.sub_mem _ (hK j) ?_
    rw [coeff_X_pow]
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
      refine ⟨(Hp (l - 1)).coeff 0 - (X ^ (2 ^ (l - 1)) : A[X]).coeff 0,
        (le_sup_left : K ≤ _) (hKp 0), ?_⟩
      rw [hcomb0, hco, coeff_C_zero, map_one, one_mul]
      ring


omit [Nontrivial A] in
/-- The odd band of `rSlot k l` agrees with the shifted `(2, l-1)` map on the lower
half-band. -/
theorem rSlot_odd_band_eq (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) {t : ℕ}
    (ht : t < 2 ^ (l - 1)) :
    rSlot (A := A) k l α ((k - 2) * 2 ^ l + t)
      = rSlot 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)) t := by
  have hp2 : 1 ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have hpow : (2 : ℕ) ^ (l - 2) < 2 ^ (l - 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hll : l - 1 - 1 = l - 2 := by omega
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rw [Nat.add_zero, rSlot_odd_b0 hpar hk hl, rSlot_two_zero]
    rfl
  · rcases Nat.lt_or_ge t (2 ^ (l - 2)) with h1 | h1
    · rw [rSlot_odd_oS3 hpar hk hl (by omega) (by omega),
        rSlot_two_eS2 (by omega) (by rw [hll]; omega)]
      rw [hll]
      congr 1
      · funext j
        congr 1
        omega
      · omega
    · rcases Nat.eq_or_lt_of_le h1 with heq | h2
      · rw [← heq, rSlot_odd_eps hpar hk hl,
          show (2 : ℕ) ^ (l - 2) = 2 ^ (l - 1 - 1) from by rw [hll],
          rSlot_two_delta]
      · rcases Nat.lt_or_ge t (2 ^ (l - 1)) with h3 | h3
        · rw [rSlot_odd_oS2 hpar hk hl (by omega) (by omega),
            rSlot_two_tS1 (by rw [hll]; omega)]
          rw [hll]
          congr 1
          · funext j
            congr 1
            omega
          · omega
        · omega

/-- Window toolkit for the odd-step certificate. -/
theorem odd_windows
    (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R)) :
    (∀ lo a, lo ≤ (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + a →
      (tS1 Hp k l α).coeff a
        ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico lo ((k - 1) * 2 ^ l)))
    ∧ (∀ lo, lo ≤ (k - 2) * 2 ^ l + 2 ^ (l - 1) →
      ∀ a, (tS1t Hp k l α).coeff a
        ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico lo ((k - 1) * 2 ^ l)))
    ∧ (∀ lo i', lo ≤ 1 + i' →
      (peel Hp l (fun j => α (1 + j))).coeff i'
        ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico lo ((k - 1) * 2 ^ l)))
    ∧ (∀ lo i', lo ≤ (k - 2) * 2 ^ l + i' + 1 →
      (oG1 Hp k l α).coeff i'
        ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico lo ((k - 1) * 2 ^ l)))
    ∧ (∀ lo i', lo ≤ (k - 2) * 2 ^ l + i' →
      (oG2 Hp k l α).coeff i'
        ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico lo ((k - 1) * 2 ^ l))) := by
  obtain ⟨hm1, hd1, hK1⟩ := hHp (l - 1) (by omega) (by omega)
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  set γ := rSlot k l α (A := A) with hγ
  have hslot : ∀ lo t, lo ≤ t → t < (k - 1) * 2 ^ l →
      γ t ∈ K ⊔ adjoin R (γ '' Set.Ico lo ((k - 1) * 2 ^ l)) := fun lo t h1 h2 =>
    (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨h1, h2⟩, rfl⟩)
  have htS1c := tS1_block_cert (Hp := Hp) (α := α) (k := k) hHp (by omega)
  have htS1tc := tS1t_block_cert (Hp := Hp) (α := α) (k := k) hHp (by omega)
  have hmersc := peel_unitriangular Hp l (fun i h1 h2 => hHp i h1 (by omega))
    (by omega) (fun j => α (1 + j))
  have hoGc := oG_cert (Hp := Hp) (α := α) (k := k)
    (fun i h1 h2 => hHp i h1 (by omega)) hl h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro lo a hlo
    have hs : (tS1 Hp k l α).coeff a
        = (tS1 Hp k l α - X ^ (2 ^ (l - 1))).coeff a
          + (X ^ (2 ^ (l - 1)) : A[X]).coeff a := by
      rw [coeff_sub]; ring
    rw [hs]
    refine Subalgebra.add_mem _ ?_ ?_
    · have h1 := htS1c.supp₂ a
      refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) h1
      rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hv : γ ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g)
          = peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j)) g := by
        rw [hγ, rSlot_odd_tS1 hpar hk hl (by omega),
          show (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1
            = g from by omega]
      exact hv ▸ hslot lo ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g) (by omega) (by omega)
    · rw [coeff_X_pow]
      split
      · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro lo hlo a
    have hs : (tS1t Hp k l α).coeff a
        = (tS1t Hp k l α - X ^ (2 ^ (l - 1))).coeff a
          + (X ^ (2 ^ (l - 1)) : A[X]).coeff a := by
      rw [coeff_sub]; ring
    rw [hs]
    refine Subalgebra.add_mem _ ?_ ?_
    · have h1 := htS1tc.supp₂ a
      refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) h1
      rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hv : γ ((k - 2) * 2 ^ l + 2 ^ (l - 1)) = α ((k - 2) * 2 ^ l + 2 ^ (l - 1)) :=
        rSlot_odd_delta hpar hk hl
      exact hv ▸ hslot lo ((k - 2) * 2 ^ l + 2 ^ (l - 1)) (by omega) (by omega)
    · rw [coeff_X_pow]
      split
      · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro lo i' hlo
    have hs : (peel Hp l (fun j => α (1 + j))).coeff i'
        = (peel Hp l (fun j => α (1 + j)) - X ^ (2 ^ l - 1)).coeff i'
          + (X ^ (2 ^ l - 1) : A[X]).coeff i' := by
      rw [coeff_sub]; ring
    rw [hs]
    refine Subalgebra.add_mem _ ?_ ?_
    · have h1 := hmersc.supp₂ i'
      refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) h1
      rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hv : γ (1 + g) = peelSlot l (fun j => α (1 + j)) g := by
        rw [hγ, rSlot_odd_mers hpar hk hl (by omega) (by omega), Nat.add_sub_cancel_left]
      exact hv ▸ hslot lo (1 + g) (by omega) (by omega)
    · rw [coeff_X_pow]
      split
      · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro lo i' hlo
    have h1 := hoGc.supp₁ i'
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) h1
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    rw [← rSlot_odd_band_eq hpar hk hl (by omega)]
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨(k - 2) * 2 ^ l + g, ⟨by omega, by omega⟩, rfl⟩)
  · intro lo i' hlo
    have h1 := hoGc.supp₂ i'
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) h1
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    rw [← rSlot_odd_band_eq hpar hk hl (by omega)]
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨(k - 2) * 2 ^ l + g, ⟨by omega, by omega⟩, rfl⟩)


/-- Degree and membership facts shared by the odd-step support proofs. -/
theorem odd_deg_facts
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hl : ¬ l ≤ 2) :
    (tS1 Hp k l α).Monic ∧ (tS1 Hp k l α).natDegree = 2 ^ (l - 1) ∧
    (tS1t Hp k l α).Monic ∧ (tS1t Hp k l α).natDegree = 2 ^ (l - 1) ∧
    (oG1 Hp k l α).natDegree ≤ 2 ^ (l - 1) ∧
    (oG2 Hp k l α).natDegree ≤ 2 ^ (l - 1) := by
  obtain ⟨hm1, hd1, hK1⟩ := hHp (l - 1) (by omega) (by omega)
  obtain ⟨hm2, hd2, hK2⟩ := hHp (l - 2) (by omega) (by omega)
  have hp2 : 1 ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 2) + 2 ^ (l - 2) = 2 ^ (l - 1) := by
    conv_rhs => rw [show l - 1 = (l - 2) + 1 from by omega, pow_succ]
    ring
  obtain ⟨hmers_m, hmers_d⟩ := peel_monic Hp (l - 1)
    (fun i h1 h2 => ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1⟩) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
  have hdeg1 : (peel Hp (l - 1)
      (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))).degree
      < (Hp (l - 1)).degree := by
    rw [degree_eq_natDegree hmers_m.ne_zero, degree_eq_natDegree hm1.ne_zero, hd1,
      hmers_d]
    exact_mod_cast (by omega : 2 ^ (l - 1) - 1 < 2 ^ (l - 1))
  refine ⟨hm1.add_of_left hdeg1, ?_, ?_, ?_, ?_, ?_⟩
  · show (Hp (l - 1) + peel Hp (l - 1) _).natDegree = 2 ^ (l - 1)
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hdeg1), hd1]
  · obtain ⟨htm, htd⟩ := monic_add_C hm1 (by omega)
      (α ((k - 2) * 2 ^ l + 2 ^ (l - 1)))
    exact htm
  · obtain ⟨htm, htd⟩ := monic_add_C hm1 (by omega)
      (α ((k - 2) * 2 ^ l + 2 ^ (l - 1)))
    show (Hp (l - 1) + C _).natDegree = _
    rw [htd, hd1]
  · -- oG1 = oS3 - oS2²
    obtain ⟨hnegm, hnegd⟩ := eE1_neg_monic (α := fun j => α ((k - 2) * 2 ^ l + j))
      (k := 2) (l := l - 1) (fun i h1 h2 => hHp i h1 (by omega)) (by omega)
    have : oG1 Hp k l α = -(tS1 Hp 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)) ^ 2
        - eS2 Hp 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j))) := by
      rw [oG1_shift]
      unfold eE1
      ring
    rw [this, natDegree_neg, hnegd]
  · obtain ⟨hnegm, hnegd⟩ := eE2_neg_monic (α := fun j => α ((k - 2) * 2 ^ l + j))
      (k := 2) (l := l - 1) (fun i h1 h2 => hHp i h1 (by omega)) (by omega)
    have : oG2 Hp k l α = -(tS1t Hp 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)) ^ 2
        - C ((fun j => α ((k - 2) * 2 ^ l + j)) ((2 - 2) * 2 ^ (l - 1)))) := by
      rw [oG2_shift]
      unfold eE2
      ring
    rw [this, natDegree_neg, hnegd]

/-- Supports of the odd-step remainder pair, first component. -/
theorem odd_supp₁
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R))
    (hin : ∀ j, (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
            Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
        ⊔ adjoin R ((rSlot ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)) (A := A)) ''
          Set.Ico (j + 1) ((k - 3) * 2 ^ l)))
    (hind : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.natDegree ≤ (k - 3) * 2 ^ l)
    (htop : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l) ∈ K) :
    ∀ j, (Rpair Hp Ht k l α).1.coeff j
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)) := by
  obtain ⟨htS1V, htS1tV, hmersV, hoG1V, hoG2V⟩ := odd_windows (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨htS1m, htS1d, htS1tm, htS1td, hoG1d, hoG2d⟩ :=
    odd_deg_facts (k := k) (α := α) hHp hl
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hb3 : (k - 3) * 2 ^ l + 2 ^ l = (k - 2) * 2 ^ l := by
    have h1 : k - 3 + 1 = k - 2 := by omega
    calc (k - 3) * 2 ^ l + 2 ^ l = (k - 3 + 1) * 2 ^ l := by ring
      _ = (k - 2) * 2 ^ l := by rw [h1]
  set γ := rSlot k l α (A := A) with hγ
  set b₀ := (k - 2) * 2 ^ l with hb₀
  intro j
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)) with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  -- S₀-memberships (high-band): W- and U-coefficients
  have hWV : ∀ lo a, lo ≤ b₀ + 2 ^ (l - 1) + 1 →
      (Hp l - (k - 1) • tS1 Hp k l α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo ((k - 1) * 2 ^ l)) := by
    intro lo a hlo
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hMK a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (htS1V lo a (by omega)))
  have hUV : ∀ lo a, lo ≤ b₀ + 2 ^ (l - 1) + 1 →
      (Hp l + tS1 Hp k l α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo ((k - 1) * 2 ^ l)) := by
    intro lo a hlo
    rw [coeff_add]
    exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hMK a))
      (htS1V lo a (by omega))
  -- windowed square coefficients of tS1
  have htS1c := tS1_block_cert (Hp := Hp) (α := α) (k := k) (l := l)
    (fun i h1 h2 => hHp i h1 (by omega)) (by omega)
  have hsqV : ∀ lo m', lo ≤ b₀ + 2 ^ (l - 1) + 1 + (m' - 2 ^ (l - 1)) →
      (tS1 Hp k l α ^ 2).coeff m'
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo ((k - 1) * 2 ^ l)) := by
    intro lo m' hlo
    have hsupp := sq_cert_supp htS1m htS1d htS1c m'
    have hs : (tS1 Hp k l α ^ 2).coeff m'
        = (tS1 Hp k l α ^ 2 - X ^ (2 * 2 ^ (l - 1))).coeff m'
          + (X ^ (2 * 2 ^ (l - 1)) : A[X]).coeff m' := by
      rw [coeff_sub]; ring
    rw [hs]
    refine Subalgebra.add_mem _ ?_ ?_
    · refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hsupp
      rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hv : γ (b₀ + 2 ^ (l - 1) + 1 + g)
          = peelSlot (l - 1) (fun j => α (b₀ + 2 ^ (l - 1) + 1 + j)) g := by
        rw [hγ, hb₀, rSlot_odd_tS1 hpar hk hl (by omega),
          show (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1
            = g from by omega]
      exact hv ▸ (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨b₀ + 2 ^ (l - 1) + 1 + g, ⟨by omega, by omega⟩, rfl⟩)
    · rw [coeff_X_pow]
      split
      · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  -- degree facts for the multipliers
  have htS1dle : (tS1 Hp k l α).natDegree ≤ 2 ^ (l - 1) := le_of_eq htS1d
  have hWdeg : (Hp l - (k - 1) • tS1 Hp k l α).natDegree ≤ 2 ^ l := by
    refine le_trans (natDegree_sub_le _ _) (max_le (le_of_eq hMd) ?_)
    exact le_trans (natDegree_smul_le _ _) (by omega)
  have hUdeg : (Hp l + tS1 Hp k l α).natDegree ≤ 2 ^ l := by
    refine le_trans (natDegree_add_le _ _) (max_le (le_of_eq hMd) ?_)
    omega
  -- the decomposition
  rw [Rpair_odd_fst' hpar (by omega) hl, coeff_add, coeff_add, coeff_add, coeff_add]
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
    (Subalgebra.add_mem _ ?_ ?_) ?_) ?_) ?_
  · -- principal
    have hWU : Hp l - (k - 1) • tS1 Hp k l α
        = Hp l - ((k - 1 : ℕ) : A[X]) * tS1 Hp k l α := by rw [nsmul_eq_mul]
    have hsplit := mul_pow_split (Hp l) (tS1 Hp k l α) (n := k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at hsplit
    have hconst : (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
        = C ((((k - 1).choose 2 : ℕ) : A) - ((k - 1 : ℕ) : A) * ((k - 1 : ℕ) : A)) := by
      rw [map_sub, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast]
    rw [show (Hp l - (k - 1) • tS1 Hp k l α) * (Hp l + tS1 Hp k l α) ^ (k - 1)
          - Hp l ^ k
        = (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
            * (tS1 Hp k l α ^ 2 * Hp l ^ (k - 1 - 1))
          + uTail (Hp l) (tS1 Hp k l α) (k - 1) from by rw [hWU, hsplit]; ring,
      coeff_add, hconst, coeff_C_mul]
    refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hKV _
      (Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _)
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.natCast_mem _ _)))) ?_) ?_
    · -- tS1² · H^{k-2}
      rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
      have hsqdeg : (tS1 Hp k l α ^ 2).natDegree ≤ 2 ^ l := by
        refine le_trans natDegree_pow_le ?_
        omega
      rcases Nat.lt_or_ge (2 ^ l) x.1 with hgt | hle
      · rw [show (tS1 Hp k l α ^ 2).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · rcases Nat.lt_or_ge ((k - 1 - 1) * 2 ^ l) x.2 with hgt2 | hle2
        · rw [show (Hp l ^ (k - 1 - 1)).coeff x.2 = 0 from
            coeff_eq_zero_of_natDegree_lt (by
              rw [hMm.natDegree_pow, hMd]
              exact hgt2), mul_zero]
          exact Subalgebra.zero_mem _
        · have hk2 : (k - 1 - 1) * 2 ^ l = b₀ := by
            rw [hb₀]
            congr 1
          exact Subalgebra.mul_mem _ (hsqV (j + 1) x.1 (by omega))
            (hKV _ (coeff_mem_pow hMK (k - 1 - 1) x.2))
    · -- uTail
      rcases Nat.lt_or_ge (b₀ + 2 ^ (l - 1)) j with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by
          refine lt_of_le_of_lt (natDegree_uTail_le (le_of_eq hMd) htS1dle (by omega)) ?_
          have : 3 * 2 ^ (l - 1) + (k - 1 - 2) * 2 ^ l ≤ b₀ + 2 ^ (l - 1) := by
            have hk3 : (k - 1 - 2) * 2 ^ l = (k - 3) * 2 ^ l := rfl
            rw [hk3]
            omega
          omega)]
        exact Subalgebra.zero_mem _
      · refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono
          (Set.Ico_subset_Ico (show j + 1 ≤ b₀ + 2 ^ (l - 1) + 1 from by omega)
            le_rfl))) K) ?_
        exact coeff_mem_uTail
          (fun i => (le_sup_left : K ≤ _) (hMK i))
          (fun i => htS1V (b₀ + 2 ^ (l - 1) + 1) i (by omega)) (k - 1) j
  · -- oG term
    rw [coeff_smul, nsmul_eq_mul]
    refine Subalgebra.mul_mem _ (hKV _ (Subalgebra.natCast_mem _ _)) ?_
    rcases Nat.lt_or_ge (b₀ + 2 ^ (l - 1)) j with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by
        refine lt_of_le_of_lt (natDegree_mul_le) ?_
        have h1 : (oG1 Hp k l α * (Hp l + tS1 Hp k l α) ^ (k - 3)).natDegree
            ≤ 2 ^ (l - 1) + (k - 3) * 2 ^ l := by
          refine le_trans (natDegree_mul_le) ?_
          have : ((Hp l + tS1 Hp k l α) ^ (k - 3)).natDegree ≤ (k - 3) * 2 ^ l :=
            le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hUdeg)
          omega
        omega)]
      exact Subalgebra.zero_mem _
    · rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge (2 ^ l) x.1 with hgt1 | hle1
      · rw [show (Hp l - (k - 1) • tS1 Hp k l α).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · refine Subalgebra.mul_mem _ (hWV (j + 1) x.1 (by omega)) ?_
        rw [coeff_mul]
        refine Subalgebra.sum_mem _ fun y hy => ?_
        have hya : y.1 + y.2 = x.2 := Finset.mem_antidiagonal.1 hy
        rcases Nat.lt_or_ge (2 ^ (l - 1)) y.1 with hgt2 | hle2
        · rw [show (oG1 Hp k l α).coeff y.1 = 0 from
            coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
          exact Subalgebra.zero_mem _
        · rcases Nat.lt_or_ge ((k - 3) * 2 ^ l) y.2 with hgt3 | hle3
          · rw [show ((Hp l + tS1 Hp k l α) ^ (k - 3)).coeff y.2 = 0 from
              coeff_eq_zero_of_natDegree_lt (by
                refine lt_of_le_of_lt (le_trans natDegree_pow_le
                  (Nat.mul_le_mul_left _ hUdeg)) hgt3), mul_zero]
            exact Subalgebra.zero_mem _
          · refine Subalgebra.mul_mem _ (hoG1V (j + 1) y.1 (by omega)) ?_
            exact coeff_mem_pow (fun i => hUV (j + 1) i (by omega)) (k - 3) y.2
  · -- binTail term
    rcases Nat.lt_or_ge k 5 with hk3 | hk5
    · -- k = 3: the tail is the empty sum
      have hbz : binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α) ((k - 1) / 2)
          = 0 := by
        show (∑ q ∈ Finset.Icc 2 ((k - 1) / 2), _) = 0
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      rw [hbz, mul_zero, coeff_zero]
      exact Subalgebra.zero_mem _
    · have hp21 : (2 : ℕ) ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
      have hU2d : ((Hp l + tS1 Hp k l α) ^ 2).natDegree ≤ 2 ^ (l + 1) := by
        have h := natDegree_pow_le (p := Hp l + tS1 Hp k l α) (n := 2)
        omega
      have hep' : 2 ^ (l - 1) ≤ 2 ^ (l + 1) := by omega
      have hbt : (binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α)
          ((k - 1) / 2)).natDegree
          ≤ 2 * 2 ^ (l - 1) + ((k - 1) / 2 - 2) * 2 ^ (l + 1) :=
        natDegree_binTail_le hU2d hoG1d hep' _
      have hm2 : ((k - 1) / 2 - 2) * 2 ^ (l + 1) = (k - 5) * 2 ^ l := by
        rw [hp21]
        have hc : (k - 1) / 2 - 2 + 2 = (k - 1) / 2 := by omega
        have h2 : ((k - 1) / 2) * (2 * 2 ^ l) = (k - 1) * 2 ^ l := by
          have hh : (k - 1) / 2 * 2 = k - 1 := by omega
          calc ((k - 1) / 2) * (2 * 2 ^ l) = ((k - 1) / 2 * 2) * 2 ^ l := by ring
            _ = (k - 1) * 2 ^ l := by rw [hh]
        have h3 : ((k - 1) / 2 - 2) * (2 * 2 ^ l) + 2 * (2 * 2 ^ l)
            = ((k - 1) / 2) * (2 * 2 ^ l) := by
          rw [← Nat.add_mul, hc]
        have h4 : (k - 5) * 2 ^ l + 4 * 2 ^ l = (k - 1) * 2 ^ l := by
          have hc4 : k - 5 + 4 = k - 1 := by omega
          rw [← Nat.add_mul, hc4]
        omega
      have h7 : (k - 5) * 2 ^ l + 2 * 2 ^ l = (k - 3) * 2 ^ l := by
        have hc7 : k - 5 + 2 = k - 3 := by omega
        rw [← Nat.add_mul, hc7]
      rcases Nat.lt_or_ge ((k - 3) * 2 ^ l) j with hgt | hle
      · have hfin : ((Hp l - (k - 1) • tS1 Hp k l α)
            * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α)
              ((k - 1) / 2)).natDegree < j := by
          have h := natDegree_mul_le
            (p := Hp l - (k - 1) • tS1 Hp k l α)
            (q := binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α) ((k - 1) / 2))
          omega
        rw [coeff_eq_zero_of_natDegree_lt hfin]
        exact Subalgebra.zero_mem _
      · refine coeff_mem_mul (fun a => hWV (j + 1) a (by omega))
          (coeff_mem_binTail
            (coeff_mem_pow (fun i => hUV (j + 1) i (by omega)) 2)
            (fun i => hoG1V (j + 1) i (by omega)) ((k - 1) / 2)) j
  · -- W · inner
    rcases Nat.lt_or_ge b₀ j with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by
        refine lt_of_le_of_lt (natDegree_mul_le) ?_
        have := hind
        omega)]
      exact Subalgebra.zero_mem _
    · rcases eq_or_lt_of_le hle with heqj | hltj
      · -- `j = b₀`: only the inner top coefficient reaches this row
        rw [coeff_mul]
        refine Subalgebra.sum_mem _ fun x hx => ?_
        have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
        rcases Nat.lt_or_ge ((k - 3) * 2 ^ l) x.2 with hgt2 | hle2
        · rw [show (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
              (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
              (fun j => α (2 ^ l + j))).1.coeff x.2 = 0 from
            coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
          exact Subalgebra.zero_mem _
        · rcases eq_or_lt_of_le hle2 with heq2 | hlt2
          · rw [show x.2 = (k - 3) * 2 ^ l from heq2]
            exact Subalgebra.mul_mem _ (hWV (j + 1) x.1 (by omega)) (hKV _ htop)
          · rw [show (Hp l - (k - 1) • tS1 Hp k l α).coeff x.1 = 0 from
              coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
            exact Subalgebra.zero_mem _
      · rw [coeff_mul]
        refine Subalgebra.sum_mem _ fun x hx => ?_
        have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
        rcases Nat.lt_or_ge (2 ^ l) x.1 with hgt1 | hle1
        · rw [show (Hp l - (k - 1) • tS1 Hp k l α).coeff x.1 = 0 from
            coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
          exact Subalgebra.zero_mem _
        · refine Subalgebra.mul_mem _ (hWV (j + 1) x.1 (by omega)) ?_
          refine mem_sup_adjoin_pair ?_ ?_ (hin x.2)
          · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
            exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
          · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
            refine ⟨2 ^ l + g, ⟨by omega, by omega⟩, ?_⟩
            rw [hγ, rSlot_odd_inner hpar hk hl (by omega) (by omega),
              Nat.add_sub_cancel_left]
  · -- the peel block
    exact hmersV (j + 1) j (by omega)

/-- Supports of the odd-step remainder pair, second component. -/
theorem odd_supp₂
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R))
    (hin : ∀ j, (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
            Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
        ⊔ adjoin R ((rSlot ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)) (A := A)) ''
          Set.Ico j ((k - 3) * 2 ^ l)))
    (hind : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).2.natDegree ≤ (k - 3) * 2 ^ l) :
    ∀ j, (Rpair Hp Ht k l α).2.coeff j
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico j ((k - 1) * 2 ^ l)) := by
  obtain ⟨htS1V, htS1tV, hmersV, hoG1V, hoG2V⟩ := odd_windows (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨htS1m, htS1d, htS1tm, htS1td, hoG1d, hoG2d⟩ :=
    odd_deg_facts (k := k) (α := α) hHp hl
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hb3 : (k - 3) * 2 ^ l + 2 ^ l = (k - 2) * 2 ^ l := by
    have h1 : k - 3 + 1 = k - 2 := by omega
    calc (k - 3) * 2 ^ l + 2 ^ l = (k - 3 + 1) * 2 ^ l := by ring
      _ = (k - 2) * 2 ^ l := by rw [h1]
  set γ := rSlot k l α (A := A) with hγ
  set b₀ := (k - 2) * 2 ^ l with hb₀
  intro j
  set V := K ⊔ adjoin R (γ '' Set.Ico j ((k - 1) * 2 ^ l)) with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  have htS1tdle : (tS1t Hp k l α).natDegree ≤ 2 ^ (l - 1) := le_of_eq htS1td
  have hWV : ∀ lo a, lo ≤ b₀ + 2 ^ (l - 1) →
      (Ht - (k - 1) • tS1t Hp k l α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo ((k - 1) * 2 ^ l)) := by
    intro lo a hlo
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (htS1tV lo (by omega) a))
  have hUV : ∀ lo a, lo ≤ b₀ + 2 ^ (l - 1) →
      (Ht + tS1t Hp k l α).coeff a
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo ((k - 1) * 2 ^ l)) := by
    intro lo a hlo
    rw [coeff_add]
    exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hKt a))
      (htS1tV lo (by omega) a)
  have htS1tc := tS1t_block_cert (Hp := Hp) (α := α) (k := k) (l := l)
    (fun i h1 h2 => hHp i h1 (by omega)) (by omega)
  have hsqtV : ∀ lo m', lo ≤ b₀ + 2 ^ (l - 1) →
      (tS1t Hp k l α ^ 2).coeff m'
        ∈ K ⊔ adjoin R (γ '' Set.Ico lo ((k - 1) * 2 ^ l)) := by
    intro lo m' hlo
    rw [sq, coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    exact Subalgebra.mul_mem _ (htS1tV lo (by omega) x.1) (htS1tV lo (by omega) x.2)
  have hWdeg : (Ht - (k - 1) • tS1t Hp k l α).natDegree ≤ 2 ^ l := by
    refine le_trans (natDegree_sub_le _ _) (max_le (le_of_eq hdHt) ?_)
    exact le_trans (natDegree_smul_le _ _) (by omega)
  have hUdeg : (Ht + tS1t Hp k l α).natDegree ≤ 2 ^ l := by
    refine le_trans (natDegree_add_le _ _) (max_le (le_of_eq hdHt) ?_)
    omega
  rw [Rpair_odd_snd' hpar (by omega) hl, coeff_add, coeff_add, coeff_add, coeff_add]
  refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
    (Subalgebra.add_mem _ ?_ ?_) ?_) ?_) ?_
  · -- principal
    have hWU : Ht - (k - 1) • tS1t Hp k l α
        = Ht - ((k - 1 : ℕ) : A[X]) * tS1t Hp k l α := by rw [nsmul_eq_mul]
    have hsplit := mul_pow_split Ht (tS1t Hp k l α) (n := k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at hsplit
    have hconst : (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
        = C ((((k - 1).choose 2 : ℕ) : A) - ((k - 1 : ℕ) : A) * ((k - 1 : ℕ) : A)) := by
      rw [map_sub, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast]
    rw [show (Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
          - Ht ^ k
        = (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
            * (tS1t Hp k l α ^ 2 * Ht ^ (k - 1 - 1))
          + uTail Ht (tS1t Hp k l α) (k - 1) from by rw [hWU, hsplit]; ring,
      coeff_add, hconst, coeff_C_mul]
    refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hKV _
      (Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _)
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
          (Subalgebra.natCast_mem _ _)))) ?_) ?_
    · have htS1tK : ∀ m, 1 ≤ m → (tS1t Hp k l α).coeff m ∈ K := by
        intro m hm
        obtain ⟨hm1, hd1, hK1⟩ := hHp (l - 1) (by omega) (by omega)
        show (Hp (l - 1) + C _).coeff m ∈ K
        rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
        exact hK1 m
      have hsqtK : ∀ m', 2 ^ (l - 1) < m' → (tS1t Hp k l α ^ 2).coeff m' ∈ K := by
        intro m' hgt'
        rw [sq, coeff_mul]
        refine Subalgebra.sum_mem _ fun y hy => ?_
        have hya : y.1 + y.2 = m' := Finset.mem_antidiagonal.1 hy
        rcases Nat.lt_or_ge (2 ^ (l - 1)) y.1 with hg1 | hl1
        · rw [show (tS1t Hp k l α).coeff y.1 = 0 from
            coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
          exact Subalgebra.zero_mem _
        · rcases Nat.lt_or_ge (2 ^ (l - 1)) y.2 with hg2 | hl2
          · rw [show (tS1t Hp k l α).coeff y.2 = 0 from
              coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
            exact Subalgebra.zero_mem _
          · have h1p : 1 ≤ y.1 := by omega
            have h2p : 1 ≤ y.2 := by omega
            exact Subalgebra.mul_mem _ (htS1tK y.1 h1p) (htS1tK y.2 h2p)
      rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge ((k - 1 - 1) * 2 ^ l) x.2 with hg2 | hl2
      · rw [show (Ht ^ (k - 1 - 1)).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by
            rw [hHt.natDegree_pow, hdHt]
            exact hg2), mul_zero]
        exact Subalgebra.zero_mem _
      · have hk2 : (k - 1 - 1) * 2 ^ l = b₀ := by
          rw [hb₀]
          congr 1
        rcases Nat.lt_or_ge (2 ^ (l - 1)) x.1 with hg1 | hl1
        · exact Subalgebra.mul_mem _ (hKV _ (hsqtK x.1 hg1))
            (hKV _ (coeff_mem_pow hKt (k - 1 - 1) x.2))
        · exact Subalgebra.mul_mem _ (hsqtV j x.1 (by omega))
            (hKV _ (coeff_mem_pow hKt (k - 1 - 1) x.2))
    · rcases Nat.lt_or_ge (b₀ + 2 ^ (l - 1)) j with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by
          refine lt_of_le_of_lt (natDegree_uTail_le (le_of_eq hdHt) htS1tdle
            (by omega)) ?_
          have hk3 : (k - 1 - 2) * 2 ^ l = (k - 3) * 2 ^ l := rfl
          omega)]
        exact Subalgebra.zero_mem _
      · refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono
          (Set.Ico_subset_Ico (show j ≤ b₀ + 2 ^ (l - 1) from by omega)
            le_rfl))) K) ?_
        exact coeff_mem_uTail
          (fun i => (le_sup_left : K ≤ _) (hKt i))
          (fun i => htS1tV (b₀ + 2 ^ (l - 1)) le_rfl i) (k - 1) j
  · -- oG term
    rw [coeff_smul, nsmul_eq_mul]
    refine Subalgebra.mul_mem _ (hKV _ (Subalgebra.natCast_mem _ _)) ?_
    rcases Nat.lt_or_ge (b₀ + 2 ^ (l - 1)) j with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by
        refine lt_of_le_of_lt (natDegree_mul_le) ?_
        have h1 : (oG2 Hp k l α * (Ht + tS1t Hp k l α) ^ (k - 3)).natDegree
            ≤ 2 ^ (l - 1) + (k - 3) * 2 ^ l := by
          refine le_trans (natDegree_mul_le) ?_
          have : ((Ht + tS1t Hp k l α) ^ (k - 3)).natDegree ≤ (k - 3) * 2 ^ l :=
            le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hUdeg)
          omega
        omega)]
      exact Subalgebra.zero_mem _
    · rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge (2 ^ l) x.1 with hgt1 | hle1
      · rw [show (Ht - (k - 1) • tS1t Hp k l α).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · refine Subalgebra.mul_mem _ (hWV j x.1 (by omega)) ?_
        rw [coeff_mul]
        refine Subalgebra.sum_mem _ fun y hy => ?_
        have hya : y.1 + y.2 = x.2 := Finset.mem_antidiagonal.1 hy
        rcases Nat.lt_or_ge (2 ^ (l - 1)) y.1 with hgt2 | hle2
        · rw [show (oG2 Hp k l α).coeff y.1 = 0 from
            coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
          exact Subalgebra.zero_mem _
        · rcases Nat.lt_or_ge ((k - 3) * 2 ^ l) y.2 with hgt3 | hle3
          · rw [show ((Ht + tS1t Hp k l α) ^ (k - 3)).coeff y.2 = 0 from
              coeff_eq_zero_of_natDegree_lt (by
                refine lt_of_le_of_lt (le_trans natDegree_pow_le
                  (Nat.mul_le_mul_left _ hUdeg)) hgt3), mul_zero]
            exact Subalgebra.zero_mem _
          · refine Subalgebra.mul_mem _ (hoG2V j y.1 (by omega)) ?_
            exact coeff_mem_pow (fun i => hUV j i (by omega)) (k - 3) y.2
  · -- binTail term
    rcases Nat.lt_or_ge k 5 with hk3 | hk5
    · have hbz : binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α) ((k - 1) / 2)
          = 0 := by
        show (∑ q ∈ Finset.Icc 2 ((k - 1) / 2), _) = 0
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      rw [hbz, mul_zero, coeff_zero]
      exact Subalgebra.zero_mem _
    · have hp21 : (2 : ℕ) ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
      have hU2d : ((Ht + tS1t Hp k l α) ^ 2).natDegree ≤ 2 ^ (l + 1) := by
        have h := natDegree_pow_le (p := Ht + tS1t Hp k l α) (n := 2)
        omega
      have hep' : 2 ^ (l - 1) ≤ 2 ^ (l + 1) := by omega
      have hbt : (binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α)
          ((k - 1) / 2)).natDegree
          ≤ 2 * 2 ^ (l - 1) + ((k - 1) / 2 - 2) * 2 ^ (l + 1) :=
        natDegree_binTail_le hU2d hoG2d hep' _
      have hm2 : ((k - 1) / 2 - 2) * 2 ^ (l + 1) = (k - 5) * 2 ^ l := by
        rw [hp21]
        have hc : (k - 1) / 2 - 2 + 2 = (k - 1) / 2 := by omega
        have h2 : ((k - 1) / 2) * (2 * 2 ^ l) = (k - 1) * 2 ^ l := by
          have hh : (k - 1) / 2 * 2 = k - 1 := by omega
          calc ((k - 1) / 2) * (2 * 2 ^ l) = ((k - 1) / 2 * 2) * 2 ^ l := by ring
            _ = (k - 1) * 2 ^ l := by rw [hh]
        have h3 : ((k - 1) / 2 - 2) * (2 * 2 ^ l) + 2 * (2 * 2 ^ l)
            = ((k - 1) / 2) * (2 * 2 ^ l) := by
          rw [← Nat.add_mul, hc]
        have h4 : (k - 5) * 2 ^ l + 4 * 2 ^ l = (k - 1) * 2 ^ l := by
          have hc4 : k - 5 + 4 = k - 1 := by omega
          rw [← Nat.add_mul, hc4]
        omega
      have h7 : (k - 5) * 2 ^ l + 2 * 2 ^ l = (k - 3) * 2 ^ l := by
        have hc7 : k - 5 + 2 = k - 3 := by omega
        rw [← Nat.add_mul, hc7]
      rcases Nat.lt_or_ge ((k - 3) * 2 ^ l) j with hgt | hle
      · have hfin : ((Ht - (k - 1) • tS1t Hp k l α)
            * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α)
              ((k - 1) / 2)).natDegree < j := by
          have h := natDegree_mul_le
            (p := Ht - (k - 1) • tS1t Hp k l α)
            (q := binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α) ((k - 1) / 2))
          omega
        rw [coeff_eq_zero_of_natDegree_lt hfin]
        exact Subalgebra.zero_mem _
      · refine coeff_mem_mul (fun a => hWV j a (by omega))
          (coeff_mem_binTail
            (coeff_mem_pow (fun i => hUV j i (by omega)) 2)
            (fun i => hoG2V j i (by omega)) ((k - 1) / 2)) j
  · -- W · inner
    rcases Nat.lt_or_ge b₀ j with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by
        refine lt_of_le_of_lt (natDegree_mul_le) ?_
        have := hind
        omega)]
      exact Subalgebra.zero_mem _
    · rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge (2 ^ l) x.1 with hgt1 | hle1
      · rw [show (Ht - (k - 1) • tS1t Hp k l α).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · refine Subalgebra.mul_mem _ (hWV j x.1 (by omega)) ?_
        refine mem_sup_adjoin_pair ?_ ?_ (hin x.2)
        · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
          exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
        · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
          refine ⟨2 ^ l + g, ⟨by omega, by omega⟩, ?_⟩
          rw [hγ, rSlot_odd_inner hpar hk hl (by omega) (by omega),
            Nat.add_sub_cancel_left]
  · -- the constant α₀
    rw [coeff_C]
    split
    · rename_i hj0
      subst hj0
      have hv : γ 0 = α 0 := rSlot_odd_zero hpar hk hl
      exact hv ▸ (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨0, ⟨le_rfl, by omega⟩, rfl⟩)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)


/-- Blanket memberships of the odd remainder components in a window at or below the
low band: every part of `R₁` except the peel block, and of `R₂` except the constant,
has all its parameters at rows `≥ 2^l`. -/
theorem odd_rest_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R))
    (hin₁ : ∀ j, (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
            Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
        ⊔ adjoin R ((rSlot ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)) (A := A)) ''
          Set.Ico (j + 1) ((k - 3) * 2 ^ l)))
    (hin₂ : ∀ j, (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2.coeff j
      ∈ (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
            Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
        ⊔ adjoin R ((rSlot ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)) (A := A)) ''
          Set.Ico j ((k - 3) * 2 ^ l)))
    :
    (∀ m, ((Rpair Hp Ht k l α).1 - peel Hp l (fun j => α (1 + j))).coeff m
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico (2 ^ l) ((k - 1) * 2 ^ l)))
    ∧ (∀ m, ((Rpair Hp Ht k l α).2 - C (α 0)).coeff m
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico (2 ^ l) ((k - 1) * 2 ^ l))) := by
  obtain ⟨htS1V, htS1tV, hmersV, hoG1V, hoG2V⟩ := odd_windows (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hb3 : (k - 3) * 2 ^ l + 2 ^ l = (k - 2) * 2 ^ l := by
    have h1 : k - 3 + 1 = k - 2 := by omega
    calc (k - 3) * 2 ^ l + 2 ^ l = (k - 3 + 1) * 2 ^ l := by ring
      _ = (k - 2) * 2 ^ l := by rw [h1]
  set γ := rSlot k l α (A := A) with hγ
  set S := K ⊔ adjoin R (γ '' Set.Ico (2 ^ l) ((k - 1) * 2 ^ l)) with hS
  have hKS : ∀ x : A, x ∈ K → x ∈ S := fun x hx => (le_sup_left : K ≤ _) hx
  -- every parameter-carrying block sits at rows ≥ 2^l
  have htS1S : ∀ a, (tS1 Hp k l α).coeff a ∈ S := fun a =>
    htS1V (2 ^ l) a (by omega)
  have htS1tS : ∀ a, (tS1t Hp k l α).coeff a ∈ S := fun a =>
    htS1tV (2 ^ l) (by omega) a
  have hoG1S : ∀ a, (oG1 Hp k l α).coeff a ∈ S := fun a =>
    hoG1V (2 ^ l) a (by omega)
  have hoG2S : ∀ a, (oG2 Hp k l α).coeff a ∈ S := fun a =>
    hoG2V (2 ^ l) a (by omega)
  have hW1S : ∀ a, (Hp l - (k - 1) • tS1 Hp k l α).coeff a ∈ S := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ (hKS _ (hMK a))
      (Subalgebra.mul_mem _ (hKS _ (Subalgebra.natCast_mem _ _)) (htS1S a))
  have hU1S : ∀ a, (Hp l + tS1 Hp k l α).coeff a ∈ S := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ (hKS _ (hMK a)) (htS1S a)
  have hW2S : ∀ a, (Ht - (k - 1) • tS1t Hp k l α).coeff a ∈ S := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ (hKS _ (hKt a))
      (Subalgebra.mul_mem _ (hKS _ (Subalgebra.natCast_mem _ _)) (htS1tS a))
  have hU2S : ∀ a, (Ht + tS1t Hp k l α).coeff a ∈ S := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ (hKS _ (hKt a)) (htS1tS a)
  have hI1S : ∀ b, (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
      (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
      (fun j => α (2 ^ l + j))).1.coeff b ∈ S := by
    intro b
    refine mem_sup_adjoin_pair ?_ ?_ (hin₁ b)
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      refine ⟨2 ^ l + g, ⟨by omega, by omega⟩, ?_⟩
      rw [hγ, rSlot_odd_inner hpar hk hl (by omega) (by omega),
        Nat.add_sub_cancel_left]
  have hI2S : ∀ b, (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
      (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
      (fun j => α (2 ^ l + j))).2.coeff b ∈ S := by
    intro b
    refine mem_sup_adjoin_pair ?_ ?_ (hin₂ b)
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      exact ⟨g, ⟨by omega, by omega⟩, rfl⟩
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      refine ⟨2 ^ l + g, ⟨by omega, by omega⟩, ?_⟩
      rw [hγ, rSlot_odd_inner hpar hk hl (by omega) (by omega),
        Nat.add_sub_cancel_left]
  -- constant polynomials with K entries are S-closed
  have hcastS : ∀ (P : A[X]), (∀ a, P.coeff a ∈ S) → ∀ (n' : ℕ) (a : ℕ),
      (P ^ n').coeff a ∈ S := fun P hP n' => coeff_mem_pow hP n'
  constructor
  · intro m
    have hdec : (Rpair Hp Ht k l α).1 - peel Hp l (fun j => α (1 + j))
        = ((Hp l - (k - 1) • tS1 Hp k l α) * (Hp l + tS1 Hp k l α) ^ (k - 1)
            - Hp l ^ k)
          + ((k - 1) / 2) • ((Hp l - (k - 1) • tS1 Hp k l α)
              * (oG1 Hp k l α * (Hp l + tS1 Hp k l α) ^ (k - 3)))
          + (Hp l - (k - 1) • tS1 Hp k l α)
              * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α) ((k - 1) / 2)
          + (Hp l - (k - 1) • tS1 Hp k l α)
              * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                  (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                  (fun j => α (2 ^ l + j))).1 := by
      rw [Rpair_odd_fst' hpar (by omega) hl]
      ring
    rw [hdec, coeff_add, coeff_add, coeff_add]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_) ?_
    · -- principal: W·U^{k-1} - H^k, all factors S-closed, H^k is K
      rw [coeff_sub]
      refine Subalgebra.sub_mem _ ?_ (hKS _ (coeff_mem_pow hMK k m))
      exact coeff_mem_mul hW1S (coeff_mem_pow hU1S (k - 1)) m
    · rw [coeff_smul, nsmul_eq_mul]
      exact Subalgebra.mul_mem _ (hKS _ (Subalgebra.natCast_mem _ _))
        (coeff_mem_mul hW1S
          (coeff_mem_mul hoG1S (coeff_mem_pow hU1S (k - 3))) m)
    · exact coeff_mem_mul hW1S
        (coeff_mem_binTail (coeff_mem_pow hU1S 2) hoG1S ((k - 1) / 2)) m
    · exact coeff_mem_mul hW1S hI1S m
  · intro m
    have hdec : (Rpair Hp Ht k l α).2 - C (α 0)
        = ((Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
            - Ht ^ k)
          + ((k - 1) / 2) • ((Ht - (k - 1) • tS1t Hp k l α)
              * (oG2 Hp k l α * (Ht + tS1t Hp k l α) ^ (k - 3)))
          + (Ht - (k - 1) • tS1t Hp k l α)
              * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α) ((k - 1) / 2)
          + (Ht - (k - 1) • tS1t Hp k l α)
              * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                  (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                  (fun j => α (2 ^ l + j))).2 := by
      rw [Rpair_odd_snd' hpar (by omega) hl]
      ring
    rw [hdec, coeff_add, coeff_add, coeff_add]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_) ?_
    · rw [coeff_sub]
      refine Subalgebra.sub_mem _ ?_ (hKS _ (coeff_mem_pow hKt k m))
      exact coeff_mem_mul hW2S (coeff_mem_pow hU2S (k - 1)) m
    · rw [coeff_smul, nsmul_eq_mul]
      exact Subalgebra.mul_mem _ (hKS _ (Subalgebra.natCast_mem _ _))
        (coeff_mem_mul hW2S
          (coeff_mem_mul hoG2S (coeff_mem_pow hU2S (k - 3))) m)
    · exact coeff_mem_mul hW2S
        (coeff_mem_binTail (coeff_mem_pow hU2S 2) hoG2S ((k - 1) / 2)) m
    · exact coeff_mem_mul hW2S hI2S m

/-- Low rows of the odd-step certificate: the constant pivot at row 0 and the peel
block pivots on `[1, 2^l)`. -/
theorem odd_pivot_low
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2)
    (hrest₁ : ∀ m, ((Rpair Hp Ht k l α).1 - peel Hp l (fun j => α (1 + j))).coeff m
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico (2 ^ l) ((k - 1) * 2 ^ l)))
    (hrest₂ : ∀ m, ((Rpair Hp Ht k l α).2 - C (α 0)).coeff m
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) '' Set.Ico (2 ^ l) ((k - 1) * 2 ^ l))) :
    ∀ j, j < 2 ^ l → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k l α (A := A)) '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)),
      (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff j
        = algebraMap R A (((tLam k l j : ℤ) : R)) * (rSlot k l α (A := A)) j + F := by
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  set γ := rSlot k l α (A := A) with hγ
  have hmersc := peel_unitriangular Hp l (fun i h1 h2 => hHp i h1 (by omega))
    (by omega) (fun j => α (1 + j))
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  intro j hj
  have hsub : ∀ x : A, x ∈ K ⊔ adjoin R (γ '' Set.Ico (2 ^ l) ((k - 1) * 2 ^ l)) →
      x ∈ K ⊔ adjoin R (γ '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)) := by
    intro x hx
    exact SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono
      (Set.Ico_subset_Ico (by omega) le_rfl))) K) hx
  cases j with
  | zero =>
    refine ⟨((Rpair Hp Ht k l α).2 - C (α 0)).coeff 0, hsub _ (hrest₂ 0), ?_⟩
    rw [coeff_combined_zero, tLam_odd_low hpar hk hl (by omega), Int.cast_one,
      map_one, one_mul, hγ, rSlot_odd_zero hpar hk hl]
    have : ((Rpair Hp Ht k l α).2 - C (α 0)).coeff 0
        = (Rpair Hp Ht k l α).2.coeff 0 - α 0 := by
      rw [coeff_sub, coeff_C_zero]
    rw [this]
    ring
  | succ t =>
    obtain ⟨F', hF', hFe⟩ := hmersc.pivot t (by omega)
    rw [hcomb0] at hFe
    have hmt : (peel Hp l (fun j => α (1 + j))).coeff t
        = peelSlot l (fun j => α (1 + j)) t + F' := by
      have hX : ((X : A[X]) ^ (2 ^ l - 1)).coeff t = 0 := by
        rw [coeff_X_pow, if_neg (by omega)]
      have := hFe
      rw [coeff_sub, hX, sub_zero, map_one, one_mul] at this
      exact this
    have hF'V : F' ∈ K ⊔ adjoin R (γ '' Set.Ico (t + 2) ((k - 1) * 2 ^ l)) := by
      refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF'
      rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hv : γ (1 + g) = peelSlot l (fun j => α (1 + j)) g := by
        rw [hγ, rSlot_odd_mers hpar hk hl (by omega) (by omega),
          Nat.add_sub_cancel_left]
      exact hv ▸ (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨1 + g, ⟨by omega, by omega⟩, rfl⟩)
    refine ⟨F' + (((Rpair Hp Ht k l α).1 - peel Hp l (fun j => α (1 + j))).coeff t
      + ((Rpair Hp Ht k l α).2 - C (α 0)).coeff (t + 1)), ?_, ?_⟩
    · refine Subalgebra.add_mem _ ?_ (Subalgebra.add_mem _ ?_ ?_)
      · exact SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono
          (Set.Ico_subset_Ico le_rfl le_rfl))) K) hF'V
      · exact SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono
          (Set.Ico_subset_Ico (by omega) le_rfl))) K) (hrest₁ t)
      · exact SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono
          (Set.Ico_subset_Ico (by omega) le_rfl))) K) (hrest₂ (t + 1))
    · rw [coeff_combined, tLam_odd_low hpar hk hl hj, Int.cast_one, map_one, one_mul,
        hγ, rSlot_odd_mers hpar hk hl (by omega) hj, Nat.add_sub_cancel]
      have h1 : (Rpair Hp Ht k l α).1.coeff t
          = ((Rpair Hp Ht k l α).1 - peel Hp l (fun j => α (1 + j))).coeff t
            + (peelSlot l (fun j => α (1 + j)) t + F') := by
        rw [coeff_sub, ← hmt]
        ring
      have h2 : (Rpair Hp Ht k l α).2.coeff (t + 1)
          = ((Rpair Hp Ht k l α).2 - C (α 0)).coeff (t + 1) := by
        rw [coeff_sub, coeff_C, if_neg (by omega), sub_zero]
      rw [h1, h2]
      ring

/-- The non-inner, non-low parts of the odd remainder live in the band window. -/
theorem odd_high_parts_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R)) :
    (∀ m, (((Hp l - (k - 1) • tS1 Hp k l α) * (Hp l + tS1 Hp k l α) ^ (k - 1)
          - Hp l ^ k)
        + ((k - 1) / 2) • ((Hp l - (k - 1) • tS1 Hp k l α)
            * (oG1 Hp k l α * (Hp l + tS1 Hp k l α) ^ (k - 3)))
        + (Hp l - (k - 1) • tS1 Hp k l α)
            * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α) ((k - 1) / 2)).coeff m
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
          Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
    ∧ (∀ m, (((Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
          - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • tS1t Hp k l α)
            * (oG2 Hp k l α * (Ht + tS1t Hp k l α) ^ (k - 3)))
        + (Ht - (k - 1) • tS1t Hp k l α)
            * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α) ((k - 1) / 2)).coeff m
      ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
          Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l))) := by
  obtain ⟨htS1V, htS1tV, hmersV, hoG1V, hoG2V⟩ := odd_windows (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  set γ := rSlot k l α (A := A) with hγ
  set S := K ⊔ adjoin R (γ '' Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)) with hS
  have hKS : ∀ x : A, x ∈ K → x ∈ S := fun x hx => (le_sup_left : K ≤ _) hx
  have htS1S : ∀ a, (tS1 Hp k l α).coeff a ∈ S := fun a =>
    htS1V ((k - 2) * 2 ^ l) a (by omega)
  have htS1tS : ∀ a, (tS1t Hp k l α).coeff a ∈ S := fun a =>
    htS1tV ((k - 2) * 2 ^ l) (by omega) a
  have hoG1S : ∀ a, (oG1 Hp k l α).coeff a ∈ S := fun a =>
    hoG1V ((k - 2) * 2 ^ l) a (by omega)
  have hoG2S : ∀ a, (oG2 Hp k l α).coeff a ∈ S := fun a =>
    hoG2V ((k - 2) * 2 ^ l) a (by omega)
  have hW1S : ∀ a, (Hp l - (k - 1) • tS1 Hp k l α).coeff a ∈ S := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ (hKS _ (hMK a))
      (Subalgebra.mul_mem _ (hKS _ (Subalgebra.natCast_mem _ _)) (htS1S a))
  have hU1S : ∀ a, (Hp l + tS1 Hp k l α).coeff a ∈ S := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ (hKS _ (hMK a)) (htS1S a)
  have hW2S : ∀ a, (Ht - (k - 1) • tS1t Hp k l α).coeff a ∈ S := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ (hKS _ (hKt a))
      (Subalgebra.mul_mem _ (hKS _ (Subalgebra.natCast_mem _ _)) (htS1tS a))
  have hU2S : ∀ a, (Ht + tS1t Hp k l α).coeff a ∈ S := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ (hKS _ (hKt a)) (htS1tS a)
  constructor
  · intro m
    rw [coeff_add, coeff_add]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_
    · rw [coeff_sub]
      refine Subalgebra.sub_mem _ ?_ (hKS _ (coeff_mem_pow hMK k m))
      exact coeff_mem_mul hW1S (coeff_mem_pow hU1S (k - 1)) m
    · rw [coeff_smul, nsmul_eq_mul]
      exact Subalgebra.mul_mem _ (hKS _ (Subalgebra.natCast_mem _ _))
        (coeff_mem_mul hW1S
          (coeff_mem_mul hoG1S (coeff_mem_pow hU1S (k - 3))) m)
    · exact coeff_mem_mul hW1S
        (coeff_mem_binTail (coeff_mem_pow hU1S 2) hoG1S ((k - 1) / 2)) m
  · intro m
    rw [coeff_add, coeff_add]
    refine Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_
    · rw [coeff_sub]
      refine Subalgebra.sub_mem _ ?_ (hKS _ (coeff_mem_pow hKt k m))
      exact coeff_mem_mul hW2S (coeff_mem_pow hU2S (k - 1)) m
    · rw [coeff_smul, nsmul_eq_mul]
      exact Subalgebra.mul_mem _ (hKS _ (Subalgebra.natCast_mem _ _))
        (coeff_mem_mul hW2S
          (coeff_mem_mul hoG2S (coeff_mem_pow hU2S (k - 3))) m)
    · exact coeff_mem_mul hW2S
        (coeff_mem_binTail (coeff_mem_pow hU2S 2) hoG2S ((k - 1) / 2)) m

/-- Inner-band rows of the odd-step certificate: the W-shifted inner pivots. -/
theorem odd_pivot_inner
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R))
    (hin : CoeffTriangular (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
        Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
      (rSlot ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)))
      (fun j => ((tLam ((k - 1) / 2) (l + 1) j : ℤ) : R)) ((k - 3) * 2 ^ l)
      (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1
      (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2) :
    ∀ j, 2 ^ l ≤ j → j < (k - 2) * 2 ^ l → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k l α (A := A)) '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)),
      (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff j
        = algebraMap R A (((tLam k l j : ℤ) : R)) * (rSlot k l α (A := A)) j + F := by
  obtain ⟨htS1V, htS1tV, hmersV, hoG1V, hoG2V⟩ := odd_windows (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨htS1m, htS1d, htS1tm, htS1td, hoG1d, hoG2d⟩ :=
    odd_deg_facts (k := k) (α := α) hHp hl
  obtain ⟨hhi₁, hhi₂⟩ := odd_high_parts_mem (α := α) hHp hHt hdHt hKt hpar hk hl h2
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hb3 : (k - 3) * 2 ^ l + 2 ^ l = (k - 2) * 2 ^ l := by
    have h1 : k - 3 + 1 = k - 2 := by omega
    calc (k - 3) * 2 ^ l + 2 ^ l = (k - 3 + 1) * 2 ^ l := by ring
      _ = (k - 2) * 2 ^ l := by rw [h1]
  set γ := rSlot k l α (A := A) with hγ
  -- multiplier facts
  have htS1deg : (tS1 Hp k l α).degree < (Hp l).degree := by
    rw [degree_eq_natDegree htS1m.ne_zero, degree_eq_natDegree hMm.ne_zero, hMd,
      htS1d]
    exact_mod_cast (by omega : 2 ^ (l - 1) < 2 ^ l)
  have hsmul₁deg : ((k - 1) • tS1 Hp k l α).degree < (Hp l).degree := by
    refine lt_of_le_of_lt (degree_smul_le _ _) htS1deg
  have hW1m : (Hp l - (k - 1) • tS1 Hp k l α).Monic := by
    have := hMm.add_of_left (q := -((k - 1) • tS1 Hp k l α)) (by
      rw [degree_neg]
      exact hsmul₁deg)
    simpa [sub_eq_add_neg] using this
  have hW1d : (Hp l - (k - 1) • tS1 Hp k l α).natDegree = 2 ^ l := by
    rw [sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        exact hsmul₁deg)), hMd]
  have htS1tdeg : (tS1t Hp k l α).degree < Ht.degree := by
    rw [degree_eq_natDegree htS1tm.ne_zero, degree_eq_natDegree hHt.ne_zero, hdHt,
      htS1td]
    exact_mod_cast (by omega : 2 ^ (l - 1) < 2 ^ l)
  have hsmul₂deg : ((k - 1) • tS1t Hp k l α).degree < Ht.degree := by
    refine lt_of_le_of_lt (degree_smul_le _ _) htS1tdeg
  have hW2m : (Ht - (k - 1) • tS1t Hp k l α).Monic := by
    have := hHt.add_of_left (q := -((k - 1) • tS1t Hp k l α)) (by
      rw [degree_neg]
      exact hsmul₂deg)
    simpa [sub_eq_add_neg] using this
  have hW2d : (Ht - (k - 1) • tS1t Hp k l α).natDegree = 2 ^ l := by
    rw [sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        exact hsmul₂deg)), hdHt]
  -- multipliers live over the enlarged subalgebra
  set K' := K ⊔ adjoin R (γ '' Set.Ico ((k - 2) * 2 ^ l)
    ((k - 1) * 2 ^ l)) with hK'
  have hW1K' : ∀ a, (Hp l - (k - 1) • tS1 Hp k l α).coeff a ∈ K' := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    refine Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hMK a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _)) ?_)
    exact htS1V ((k - 2) * 2 ^ l) a (by omega)
  have hW2K' : ∀ a, (Ht - (k - 1) • tS1t Hp k l α).coeff a ∈ K' := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    refine Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _)) ?_)
    exact htS1tV ((k - 2) * 2 ^ l) (by omega) a
  intro j hj1 hj2
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)) with hV
  have hK'V : ∀ x : A, x ∈ K' → x ∈ V := by
    intro x hx
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hx
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨g, ⟨by omega, hg2⟩, rfl⟩)
  -- the shifted inner pivot over K'
  obtain ⟨F', hF', hFe⟩ := CoeffTriangular.shift_pivot
    hin (by omega) hW1m hW1d hW2m hW2d
    hW1K' hW2K' (j - 2 ^ l) (by omega)
  have hidx : 2 ^ l + (j - 2 ^ l) = j := by omega
  rw [hidx] at hFe
  have hF'V : F' ∈ V := by
    refine SetLike.le_def.1 (sup_le ?_ (adjoin_le ?_)) hF'
    · intro x hx
      exact hK'V x hx
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hv : γ (2 ^ l + g)
          = rSlot ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)) g := by
        rw [hγ, rSlot_odd_inner hpar hk hl (by omega) (by omega),
          Nat.add_sub_cancel_left]
      exact hv ▸ (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨2 ^ l + g, ⟨by omega, by omega⟩, rfl⟩)
  -- assemble: the remaining parts are K-known or high-window at these rows
  have hmersK : ∀ m', 2 ^ l - 1 ≤ m' →
      (peel Hp l (fun j => α (1 + j))).coeff m' ∈ K := by
    intro m' hm'
    obtain ⟨hmm, hmd⟩ := peel_monic Hp l
      (fun i h1 h2 => ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1⟩)
      (by omega) (fun j => α (1 + j))
    rcases Nat.lt_or_ge (2 ^ l - 1) m' with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · rw [show m' = 2 ^ l - 1 from by omega, ← hmd, hmm.coeff_natDegree]
      exact Subalgebra.one_mem _
  have hhiV₁ : ∀ m', (((Hp l - (k - 1) • tS1 Hp k l α)
        * (Hp l + tS1 Hp k l α) ^ (k - 1) - Hp l ^ k)
      + ((k - 1) / 2) • ((Hp l - (k - 1) • tS1 Hp k l α)
          * (oG1 Hp k l α * (Hp l + tS1 Hp k l α) ^ (k - 3)))
      + (Hp l - (k - 1) • tS1 Hp k l α)
          * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α)
            ((k - 1) / 2)).coeff m' ∈ V := by
    intro m'
    refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono
      (Set.Ico_subset_Ico (by omega) le_rfl))) K) (hhi₁ m')
  have hhiV₂ : ∀ m', (((Ht - (k - 1) • tS1t Hp k l α)
        * (Ht + tS1t Hp k l α) ^ (k - 1) - Ht ^ k)
      + ((k - 1) / 2) • ((Ht - (k - 1) • tS1t Hp k l α)
          * (oG2 Hp k l α * (Ht + tS1t Hp k l α) ^ (k - 3)))
      + (Ht - (k - 1) • tS1t Hp k l α)
          * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α)
            ((k - 1) / 2)).coeff m' ∈ V := by
    intro m'
    refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono
      (Set.Ico_subset_Ico (by omega) le_rfl))) K) (hhi₂ m')
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  refine ⟨F' + ((((Hp l - (k - 1) • tS1 Hp k l α)
        * (Hp l + tS1 Hp k l α) ^ (k - 1) - Hp l ^ k)
      + ((k - 1) / 2) • ((Hp l - (k - 1) • tS1 Hp k l α)
          * (oG1 Hp k l α * (Hp l + tS1 Hp k l α) ^ (k - 3)))
      + (Hp l - (k - 1) • tS1 Hp k l α)
          * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α)
            ((k - 1) / 2)).coeff t
      + (peel Hp l (fun j => α (1 + j))).coeff t
      + (((Ht - (k - 1) • tS1t Hp k l α)
          * (Ht + tS1t Hp k l α) ^ (k - 1) - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • tS1t Hp k l α)
            * (oG2 Hp k l α * (Ht + tS1t Hp k l α) ^ (k - 3)))
        + (Ht - (k - 1) • tS1t Hp k l α)
            * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α)
              ((k - 1) / 2)).coeff (t + 1)), ?_, ?_⟩
  · refine Subalgebra.add_mem _ hF'V (Subalgebra.add_mem _ (Subalgebra.add_mem _
      (hhiV₁ t) ((le_sup_left : K ≤ _) (hmersK t (by omega)))) (hhiV₂ (t + 1)))
  · rw [coeff_combined] at hFe ⊢
    have hd₁ : (Rpair Hp Ht k l α).1
        = (((Hp l - (k - 1) • tS1 Hp k l α) * (Hp l + tS1 Hp k l α) ^ (k - 1)
            - Hp l ^ k)
          + ((k - 1) / 2) • ((Hp l - (k - 1) • tS1 Hp k l α)
              * (oG1 Hp k l α * (Hp l + tS1 Hp k l α) ^ (k - 3)))
          + (Hp l - (k - 1) • tS1 Hp k l α)
              * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α) ((k - 1) / 2))
          + (Hp l - (k - 1) • tS1 Hp k l α)
              * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                  (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                  (fun j => α (2 ^ l + j))).1
          + peel Hp l (fun j => α (1 + j)) := by
      rw [Rpair_odd_fst' hpar (by omega) hl]
    have hd₂ : (Rpair Hp Ht k l α).2
        = (((Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
            - Ht ^ k)
          + ((k - 1) / 2) • ((Ht - (k - 1) • tS1t Hp k l α)
              * (oG2 Hp k l α * (Ht + tS1t Hp k l α) ^ (k - 3)))
          + (Ht - (k - 1) • tS1t Hp k l α)
              * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α) ((k - 1) / 2))
          + (Ht - (k - 1) • tS1t Hp k l α)
              * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                  (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                  (fun j => α (2 ^ l + j))).2
          + C (α 0) := by
      rw [Rpair_odd_snd' hpar (by omega) hl]
    have hCz : (C (α 0) : A[X]).coeff (t + 1) = 0 := by
      rw [coeff_C, if_neg (by omega)]
    rw [hd₁, hd₂]
    simp only [coeff_add]
    rw [hCz, tLam_odd_inner hpar hk hl (by omega) (by omega), hγ,
      rSlot_odd_inner hpar hk hl (by omega) (by omega)]
    linear_combination hFe

/-- `W·inner` is fully known at and above row `b₀ - 1`: only the inner pair's top-two
coefficients reach those rows, and those are hypothesised in `K`. -/
theorem odd_winner_high_K
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2)
    (hind₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.natDegree ≤ (k - 3) * 2 ^ l)
    (hind₂ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).2.natDegree ≤ (k - 3) * 2 ^ l)
    (htop₁₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).2.coeff ((k - 3) * 2 ^ l) ∈ K) :
    (∀ m, (k - 2) * 2 ^ l - 1 ≤ m → ((Hp l - (k - 1) • tS1 Hp k l α)
      * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1).coeff m ∈ K)
    ∧ (∀ m, (k - 2) * 2 ^ l ≤ m → ((Ht - (k - 1) • tS1t Hp k l α)
      * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).2).coeff m ∈ K) := by
  obtain ⟨htS1m, htS1d, htS1tm, htS1td, hoG1d, hoG2d⟩ :=
    odd_deg_facts (k := k) (α := α) hHp hl
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hb3 : (k - 3) * 2 ^ l + 2 ^ l = (k - 2) * 2 ^ l := by
    have h1 : k - 3 + 1 = k - 2 := by omega
    calc (k - 3) * 2 ^ l + 2 ^ l = (k - 3 + 1) * 2 ^ l := by ring
      _ = (k - 2) * 2 ^ l := by rw [h1]
  have hp2le : 2 ≤ 2 ^ (l - 1) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 from by omega)
      (show 1 ≤ l - 1 from by omega)
    have h2e : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  have hW₁K : ∀ a, 2 ^ l - 1 ≤ a → (Hp l - (k - 1) • tS1 Hp k l α).coeff a ∈ K := by
    intro a ha
    rw [coeff_sub, coeff_smul,
      show (tS1 Hp k l α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      smul_zero, sub_zero]
    exact hMK a
  have hW₂K : ∀ a, 2 ^ l - 1 ≤ a → (Ht - (k - 1) • tS1t Hp k l α).coeff a ∈ K := by
    intro a ha
    rw [coeff_sub, coeff_smul,
      show (tS1t Hp k l α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      smul_zero, sub_zero]
    exact hKt a
  have hW₁z : ∀ a, 2 ^ l < a → (Hp l - (k - 1) • tS1 Hp k l α).coeff a = 0 := by
    intro a ha
    rw [coeff_sub, coeff_smul,
      show (Hp l).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      show (tS1 Hp k l α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      smul_zero, sub_zero]
  have hW₂z : ∀ a, 2 ^ l < a → (Ht - (k - 1) • tS1t Hp k l α).coeff a = 0 := by
    intro a ha
    rw [coeff_sub, coeff_smul,
      show Ht.coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      show (tS1t Hp k l α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      smul_zero, sub_zero]
  constructor
  · intro m hm
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge ((k - 3) * 2 ^ l) x.2 with hgt | hle
    · rw [show (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge x.2 ((k - 3) * 2 ^ l - 1) with hlo | hhi
      · rw [hW₁z x.1 (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · rcases eq_or_lt_of_le hhi with heq | hlt2
        · rw [show x.2 = (k - 3) * 2 ^ l - 1 from heq.symm]
          exact Subalgebra.mul_mem _ (hW₁K x.1 (by omega)) htop₁₂
        · rw [show x.2 = (k - 3) * 2 ^ l from by omega]
          exact Subalgebra.mul_mem _ (hW₁K x.1 (by omega)) htop₁₁
  · intro m hm
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge ((k - 3) * 2 ^ l) x.2 with hgt | hle
    · rw [show (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).2.coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge x.2 ((k - 3) * 2 ^ l) with hlo | hhi
      · rw [hW₂z x.1 (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · rw [show x.2 = (k - 3) * 2 ^ l from by omega]
        exact Subalgebra.mul_mem _ (hW₂K x.1 (by omega)) htop₂₁


/-- oG-band rows of the odd-step certificate. -/
theorem odd_pivot_band
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R))
    (hind₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.natDegree ≤ (k - 3) * 2 ^ l)
    (hind₂ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).2.natDegree ≤ (k - 3) * 2 ^ l)
    (htop₁₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).2.coeff ((k - 3) * 2 ^ l) ∈ K) :
    ∀ j, (k - 2) * 2 ^ l ≤ j → j < (k - 2) * 2 ^ l + 2 ^ (l - 1) → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k l α (A := A)) '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)),
      (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff j
        = algebraMap R A (((tLam k l j : ℤ) : R)) * (rSlot k l α (A := A)) j + F := by
  obtain ⟨htS1V, htS1tV, hmersV, hoG1V, hoG2V⟩ := odd_windows (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨htS1m, htS1d, htS1tm, htS1tm', hoG1d, hoG2d⟩ :=
    odd_deg_facts (k := k) (α := α) hHp hl
  obtain ⟨hWI₁K, hWI₂K⟩ := odd_winner_high_K (α := α) hHp hdHt hKt hpar hk hl
    hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hp2l : 1 ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
  have hpl2 : 2 ^ (l - 2) + 2 ^ (l - 2) = 2 ^ (l - 1) := by
    conv_rhs => rw [show l - 1 = (l - 2) + 1 from by omega, pow_succ]
    ring
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hb3 : (k - 3) * 2 ^ l + 2 ^ l = (k - 2) * 2 ^ l := by
    have h1 : k - 3 + 1 = k - 2 := by omega
    calc (k - 3) * 2 ^ l + 2 ^ l = (k - 3 + 1) * 2 ^ l := by ring
      _ = (k - 2) * 2 ^ l := by rw [h1]
  set γ := rSlot k l α (A := A) with hγ
  -- monic multipliers
  have htS1deg : (tS1 Hp k l α).degree < (Hp l).degree := by
    rw [degree_eq_natDegree htS1m.ne_zero, degree_eq_natDegree hMm.ne_zero, hMd,
      htS1d]
    exact_mod_cast (by omega : 2 ^ (l - 1) < 2 ^ l)
  have hW1m : (Hp l - (k - 1) • tS1 Hp k l α).Monic := by
    have := hMm.add_of_left (q := -((k - 1) • tS1 Hp k l α)) (by
      rw [degree_neg]
      exact lt_of_le_of_lt (degree_smul_le _ _) htS1deg)
    simpa [sub_eq_add_neg] using this
  have hW1d : (Hp l - (k - 1) • tS1 Hp k l α).natDegree = 2 ^ l := by
    rw [sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        exact lt_of_le_of_lt (degree_smul_le _ _) htS1deg)), hMd]
  have hU1m : (Hp l + tS1 Hp k l α).Monic := hMm.add_of_left htS1deg
  have hU1d : (Hp l + tS1 Hp k l α).natDegree = 2 ^ l := by
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt htS1deg), hMd]
  have htS1tdeg : (tS1t Hp k l α).degree < Ht.degree := by
    rw [degree_eq_natDegree htS1tm.ne_zero, degree_eq_natDegree hHt.ne_zero, hdHt,
      htS1tm']
    exact_mod_cast (by omega : 2 ^ (l - 1) < 2 ^ l)
  have hW2m : (Ht - (k - 1) • tS1t Hp k l α).Monic := by
    have := hHt.add_of_left (q := -((k - 1) • tS1t Hp k l α)) (by
      rw [degree_neg]
      exact lt_of_le_of_lt (degree_smul_le _ _) htS1tdeg)
    simpa [sub_eq_add_neg] using this
  have hW2d : (Ht - (k - 1) • tS1t Hp k l α).natDegree = 2 ^ l := by
    rw [sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        exact lt_of_le_of_lt (degree_smul_le _ _) htS1tdeg)), hdHt]
  have hU2m : (Ht + tS1t Hp k l α).Monic := hHt.add_of_left htS1tdeg
  have hU2d : (Ht + tS1t Hp k l α).natDegree = 2 ^ l := by
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt htS1tdeg), hdHt]
  have hL1m : ((Hp l - (k - 1) • tS1 Hp k l α)
      * (Hp l + tS1 Hp k l α) ^ (k - 3)).Monic := hW1m.mul (hU1m.pow _)
  have hL1d : ((Hp l - (k - 1) • tS1 Hp k l α)
      * (Hp l + tS1 Hp k l α) ^ (k - 3)).natDegree = (k - 2) * 2 ^ l := by
    rw [hW1m.natDegree_mul (hU1m.pow _), hW1d, hU1m.natDegree_pow, hU1d]
    omega
  have hL2m : ((Ht - (k - 1) • tS1t Hp k l α)
      * (Ht + tS1t Hp k l α) ^ (k - 3)).Monic := hW2m.mul (hU2m.pow _)
  have hL2d : ((Ht - (k - 1) • tS1t Hp k l α)
      * (Ht + tS1t Hp k l α) ^ (k - 3)).natDegree = (k - 2) * 2 ^ l := by
    rw [hW2m.natDegree_mul (hU2m.pow _), hW2d, hU2m.natDegree_pow, hU2d]
    omega
  -- multiplier coefficients over the enlarged subalgebra
  set K' := K ⊔ adjoin R (γ '' Set.Ico ((k - 2) * 2 ^ l + 2 ^ (l - 1))
    ((k - 1) * 2 ^ l)) with hK'
  have htS1K' : ∀ a, (tS1 Hp k l α).coeff a ∈ K' :=
    fun a => htS1V ((k - 2) * 2 ^ l + 2 ^ (l - 1)) a (by omega)
  have htS1tK' : ∀ a, (tS1t Hp k l α).coeff a ∈ K' :=
    fun a => htS1tV ((k - 2) * 2 ^ l + 2 ^ (l - 1)) le_rfl a
  have hW1K' : ∀ a, (Hp l - (k - 1) • tS1 Hp k l α).coeff a ∈ K' := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hMK a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (htS1K' a))
  have hU1K' : ∀ a, (Hp l + tS1 Hp k l α).coeff a ∈ K' := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hMK a)) (htS1K' a)
  have hW2K' : ∀ a, (Ht - (k - 1) • tS1t Hp k l α).coeff a ∈ K' := by
    intro a
    rw [coeff_sub, coeff_smul, nsmul_eq_mul]
    exact Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hKt a))
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (Subalgebra.natCast_mem _ _))
        (htS1tK' a))
  have hU2K' : ∀ a, (Ht + tS1t Hp k l α).coeff a ∈ K' := by
    intro a
    rw [coeff_add]
    exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hKt a)) (htS1tK' a)
  have hL1K' : ∀ a, ((Hp l - (k - 1) • tS1 Hp k l α)
      * (Hp l + tS1 Hp k l α) ^ (k - 3)).coeff a ∈ K' :=
    coeff_mem_mul hW1K' (coeff_mem_pow hU1K' (k - 3))
  have hL2K' : ∀ a, ((Ht - (k - 1) • tS1t Hp k l α)
      * (Ht + tS1t Hp k l α) ^ (k - 3)).coeff a ∈ K' :=
    coeff_mem_mul hW2K' (coeff_mem_pow hU2K' (k - 3))
  -- the oG certificate over K'
  have hoGc := (oG_cert (Hp := Hp) (α := α) (k := k)
    (fun i h1 h2 => hHp i h1 (by omega)) hl h2).mono_left
    (le_sup_left : K ≤ K')
  intro j hj1 hj2
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)) with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  have hK'V : ∀ x : A, x ∈ K' → x ∈ V := by
    intro x hx
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hx
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨g, ⟨by omega, hg2⟩, rfl⟩)
  obtain ⟨t, rfl⟩ : ∃ t, j = (k - 2) * 2 ^ l + t := ⟨j - (k - 2) * 2 ^ l, by omega⟩
  have ht : t < 2 ^ (l - 1) := by omega
  obtain ⟨F₀, hF₀, hsheq⟩ := CoeffTriangular.shift_pivot hoGc
    (by omega : 1 ≤ (k - 2) * 2 ^ l) hL1m hL1d hL2m hL2d hL1K' hL2K' t ht
  have hF₀V : F₀ ∈ V := by
    refine SetLike.le_def.1 (sup_le ?_ (adjoin_le ?_)) hF₀
    · intro x hx
      exact hK'V x hx
    · rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      rw [← rSlot_odd_band_eq hpar hk hl (by omega)]
      exact (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨(k - 2) * 2 ^ l + g, ⟨by omega, by omega⟩, rfl⟩)
  -- all corrections are K'-closed (their slots sit at or above the δ-row)
  have hprin₁K' : ∀ m', ((Hp l - (k - 1) • tS1 Hp k l α)
      * (Hp l + tS1 Hp k l α) ^ (k - 1) - Hp l ^ k).coeff m' ∈ K' := by
    intro m'
    rw [coeff_sub]
    exact Subalgebra.sub_mem _
      (coeff_mem_mul hW1K' (coeff_mem_pow hU1K' (k - 1)) m')
      ((le_sup_left : K ≤ _) (coeff_mem_pow hMK k m'))
  have hprin₂K' : ∀ m', ((Ht - (k - 1) • tS1t Hp k l α)
      * (Ht + tS1t Hp k l α) ^ (k - 1) - Ht ^ k).coeff m' ∈ K' := by
    intro m'
    rw [coeff_sub]
    exact Subalgebra.sub_mem _
      (coeff_mem_mul hW2K' (coeff_mem_pow hU2K' (k - 1)) m')
      ((le_sup_left : K ≤ _) (coeff_mem_pow hKt k m'))
  have hbinZ : ∀ (W' U' G' : A[X]), W'.natDegree ≤ 2 ^ l → U'.natDegree ≤ 2 ^ l →
      G'.natDegree ≤ 2 ^ (l - 1) → ∀ m', (k - 3) * 2 ^ l < m' →
      (W' * binTail (U' ^ 2) G' ((k - 1) / 2)).coeff m' = 0 := by
    intro W' U' G' hW' hU' hG' m' hm'
    rcases Nat.lt_or_ge k 5 with hk3 | hk5
    · have hbz : binTail (U' ^ 2) G' ((k - 1) / 2) = 0 := by
        show (∑ q ∈ Finset.Icc 2 ((k - 1) / 2), _) = 0
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      rw [hbz, mul_zero, coeff_zero]
    · have hp21 : (2 : ℕ) ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
      have hUsq : (U' ^ 2).natDegree ≤ 2 ^ (l + 1) := by
        have h := natDegree_pow_le (p := U') (n := 2)
        omega
      have hbt : (binTail (U' ^ 2) G' ((k - 1) / 2)).natDegree
          ≤ 2 * 2 ^ (l - 1) + ((k - 1) / 2 - 2) * 2 ^ (l + 1) :=
        natDegree_binTail_le hUsq hG' (by omega) _
      have hm2 : ((k - 1) / 2 - 2) * 2 ^ (l + 1) = (k - 5) * 2 ^ l := by
        rw [hp21]
        have hc : (k - 1) / 2 - 2 + 2 = (k - 1) / 2 := by omega
        have h2 : ((k - 1) / 2) * (2 * 2 ^ l) = (k - 1) * 2 ^ l := by
          have hh : (k - 1) / 2 * 2 = k - 1 := by omega
          calc ((k - 1) / 2) * (2 * 2 ^ l) = ((k - 1) / 2 * 2) * 2 ^ l := by ring
            _ = (k - 1) * 2 ^ l := by rw [hh]
        have h3 : ((k - 1) / 2 - 2) * (2 * 2 ^ l) + 2 * (2 * 2 ^ l)
            = ((k - 1) / 2) * (2 * 2 ^ l) := by
          rw [← Nat.add_mul, hc]
        have h4 : (k - 5) * 2 ^ l + 4 * 2 ^ l = (k - 1) * 2 ^ l := by
          have hc4 : k - 5 + 4 = k - 1 := by omega
          rw [← Nat.add_mul, hc4]
        omega
      have h7 : (k - 5) * 2 ^ l + 2 * 2 ^ l = (k - 3) * 2 ^ l := by
        have hc7 : k - 5 + 2 = k - 3 := by omega
        rw [← Nat.add_mul, hc7]
      refine coeff_eq_zero_of_natDegree_lt ?_
      have h := natDegree_mul_le (p := W') (q := binTail (U' ^ 2) G' ((k - 1) / 2))
      omega
  have hbin₁Z : ∀ m', (k - 3) * 2 ^ l < m' →
      ((Hp l - (k - 1) • tS1 Hp k l α)
        * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α)
          ((k - 1) / 2)).coeff m' = 0 :=
    hbinZ _ _ _ (le_of_eq hW1d) (le_of_eq hU1d) hoG1d
  have hbin₂Z : ∀ m', (k - 3) * 2 ^ l < m' →
      ((Ht - (k - 1) • tS1t Hp k l α)
        * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α)
          ((k - 1) / 2)).coeff m' = 0 :=
    hbinZ _ _ _ (le_of_eq hW2d) (le_of_eq hU2d) hoG2d
  have hmersK : ∀ m', 2 ^ l - 1 ≤ m' →
      (peel Hp l (fun j => α (1 + j))).coeff m' ∈ K := by
    intro m' hm'
    obtain ⟨hmm, hmd⟩ := peel_monic Hp l
      (fun i h1 h2 => ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1⟩)
      (by omega) (fun j => α (1 + j))
    rcases Nat.lt_or_ge (2 ^ l - 1) m' with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · rw [show m' = 2 ^ l - 1 from by omega, ← hmd, hmm.coeff_natDegree]
      exact Subalgebra.one_mem _
  -- slope bridge
  have hmk : (k - 1) / 2 * 2 = k - 1 := by omega
  have hslope : algebraMap R A (((tLam k l ((k - 2) * 2 ^ l + t) : ℤ) : R))
      = (((k - 1) / 2 : ℕ) : A)
        * algebraMap R A (((tLam 2 (l - 1) t : ℤ) : R)) := by
    have hexp : (2 : ℕ) ^ (l - 1 - 1) = 2 ^ (l - 2) := rfl
    rcases Nat.lt_or_ge t (2 ^ (l - 2)) with hmid | hhi
    · rw [tLam_odd_mid1 hpar hk hl (by omega) (by omega),
        tLam_two_lo (show t < 2 ^ (l - 1 - 1) from by omega),
        Int.cast_natCast, map_natCast, Int.cast_one, map_one, mul_one]
    · rw [tLam_odd_mid2 hpar hk hl (by omega) (by omega),
        tLam_two_hi (show 2 ^ (l - 1 - 1) ≤ t from by omega)]
      have hcast : (((k - 1) / 2 : ℕ) : A) * 2 = ((k - 1 : ℕ) : A) := by
        calc (((k - 1) / 2 : ℕ) : A) * 2 = (((k - 1) / 2 * 2 : ℕ) : A) := by
              push_cast; ring
          _ = _ := by rw [hmk]
      rw [show (((-(k - 1 : ℕ) : ℤ)) : R) = -(((k - 1 : ℕ) : ℤ) : R) from by
          push_cast; ring,
        show (((-2 : ℤ)) : R) = -(((2 : ℕ) : ℤ) : R) from by push_cast; ring,
        map_neg, map_neg, Int.cast_natCast, Int.cast_natCast, map_natCast,
        map_natCast, show ((2 : ℕ) : A) = (2 : A) from by norm_num]
      calc -((k - 1 : ℕ) : A) = -((((k - 1) / 2 : ℕ) : A) * 2) := by rw [hcast]
        _ = (((k - 1) / 2 : ℕ) : A) * -2 := by ring
  have hslot : γ ((k - 2) * 2 ^ l + t)
      = rSlot 2 (l - 1) (fun j => α ((k - 2) * 2 ^ l + j)) t :=
    rSlot_odd_band_eq hpar hk hl ht
  -- decompose the combined coefficient
  have hj1' : 1 ≤ (k - 2) * 2 ^ l + t := by omega
  have hcO : (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff
      ((k - 2) * 2 ^ l + t)
      = (Rpair Hp Ht k l α).1.coeff ((k - 2) * 2 ^ l + t - 1)
        + (Rpair Hp Ht k l α).2.coeff ((k - 2) * 2 ^ l + t) := by
    obtain ⟨s', hs'⟩ : ∃ s', (k - 2) * 2 ^ l + t = s' + 1 :=
      ⟨(k - 2) * 2 ^ l + t - 1, by omega⟩
    rw [hs', coeff_combined, Nat.add_sub_cancel]
  have hcL : (combined ((Hp l - (k - 1) • tS1 Hp k l α)
        * (Hp l + tS1 Hp k l α) ^ (k - 3) * oG1 Hp k l α)
      ((Ht - (k - 1) • tS1t Hp k l α)
        * (Ht + tS1t Hp k l α) ^ (k - 3) * oG2 Hp k l α)).coeff
      ((k - 2) * 2 ^ l + t)
      = ((Hp l - (k - 1) • tS1 Hp k l α)
          * (Hp l + tS1 Hp k l α) ^ (k - 3) * oG1 Hp k l α).coeff
          ((k - 2) * 2 ^ l + t - 1)
        + ((Ht - (k - 1) • tS1t Hp k l α)
            * (Ht + tS1t Hp k l α) ^ (k - 3) * oG2 Hp k l α).coeff
            ((k - 2) * 2 ^ l + t) := by
    obtain ⟨s', hs'⟩ : ∃ s', (k - 2) * 2 ^ l + t = s' + 1 :=
      ⟨(k - 2) * 2 ^ l + t - 1, by omega⟩
    rw [hs', coeff_combined, Nat.add_sub_cancel]
  have hd₁ : (Rpair Hp Ht k l α).1
      = ((Hp l - (k - 1) • tS1 Hp k l α) * (Hp l + tS1 Hp k l α) ^ (k - 1)
          - Hp l ^ k)
        + ((k - 1) / 2) • ((Hp l - (k - 1) • tS1 Hp k l α)
            * (Hp l + tS1 Hp k l α) ^ (k - 3) * oG1 Hp k l α)
        + (Hp l - (k - 1) • tS1 Hp k l α)
            * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α) ((k - 1) / 2)
        + (Hp l - (k - 1) • tS1 Hp k l α)
            * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                (fun j => α (2 ^ l + j))).1
        + peel Hp l (fun j => α (1 + j)) := by
    rw [Rpair_odd_fst' hpar (by omega) hl]
    ring
  have hd₂ : (Rpair Hp Ht k l α).2
      = ((Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
          - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • tS1t Hp k l α)
            * (Ht + tS1t Hp k l α) ^ (k - 3) * oG2 Hp k l α)
        + (Ht - (k - 1) • tS1t Hp k l α)
            * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α) ((k - 1) / 2)
        + (Ht - (k - 1) • tS1t Hp k l α)
            * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                (fun j => α (2 ^ l + j))).2
        + C (α 0) := by
    rw [Rpair_odd_snd' hpar (by omega) hl]
    ring
  have hCz : (C (α 0) : A[X]).coeff ((k - 2) * 2 ^ l + t) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  refine ⟨(((k - 1) / 2 : ℕ) : A) * F₀
    + (((Hp l - (k - 1) • tS1 Hp k l α) * (Hp l + tS1 Hp k l α) ^ (k - 1)
        - Hp l ^ k).coeff ((k - 2) * 2 ^ l + t - 1)
      + ((Hp l - (k - 1) • tS1 Hp k l α)
          * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α)
            ((k - 1) / 2)).coeff ((k - 2) * 2 ^ l + t - 1)
      + ((Hp l - (k - 1) • tS1 Hp k l α)
          * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
              (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
              (fun j => α (2 ^ l + j))).1).coeff ((k - 2) * 2 ^ l + t - 1)
      + (peel Hp l (fun j => α (1 + j))).coeff ((k - 2) * 2 ^ l + t - 1)
      + (((Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
          - Ht ^ k).coeff ((k - 2) * 2 ^ l + t)
        + ((Ht - (k - 1) • tS1t Hp k l α)
            * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α)
              ((k - 1) / 2)).coeff ((k - 2) * 2 ^ l + t)
        + ((Ht - (k - 1) • tS1t Hp k l α)
            * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                (fun j => α (2 ^ l + j))).2).coeff ((k - 2) * 2 ^ l + t))), ?_, ?_⟩
  · refine Subalgebra.add_mem _
      (Subalgebra.mul_mem _ (hKV _ (Subalgebra.natCast_mem _ _)) hF₀V)
      (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (hK'V _ (hprin₁K' _))
          (by rw [hbin₁Z _ (by omega)]; exact Subalgebra.zero_mem _))
        (hKV _ (hWI₁K _ (by omega)))) (hKV _ (hmersK _ (by omega))))
      (Subalgebra.add_mem _ (Subalgebra.add_mem _ (hK'V _ (hprin₂K' _))
        (by rw [hbin₂Z _ (by omega)]; exact Subalgebra.zero_mem _))
        (hKV _ (hWI₂K _ (by omega)))))
  · rw [hcO, hd₁, hd₂]
    simp only [coeff_add, coeff_smul]
    rw [hCz, hslope, hslot]
    rw [hcL] at hsheq
    simp only [nsmul_eq_mul] at hsheq ⊢
    linear_combination (((k - 1) / 2 : ℕ) : A) * hsheq

/-- Principal-band rows of the odd-step certificate: the δ pivot and the tS1 block. -/
theorem odd_pivot_principal
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R))
    (hind₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.natDegree ≤ (k - 3) * 2 ^ l)
    (hind₂ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).2.natDegree ≤ (k - 3) * 2 ^ l)
    (htop₁₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
        (fun j => α (2 ^ l + j))).2.coeff ((k - 3) * 2 ^ l) ∈ K) :
    ∀ j, (k - 2) * 2 ^ l + 2 ^ (l - 1) ≤ j → j < (k - 1) * 2 ^ l → ∃ F ∈ K ⊔ adjoin R
        ((rSlot k l α (A := A)) '' Set.Ico (j + 1) ((k - 1) * 2 ^ l)),
      (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff j
        = algebraMap R A (((tLam k l j : ℤ) : R)) * (rSlot k l α (A := A)) j + F := by
  obtain ⟨htS1V, htS1tV, hmersV, hoG1V, hoG2V⟩ := odd_windows (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨htS1m, htS1d, htS1tm, htS1td, hoG1d, hoG2d⟩ :=
    odd_deg_facts (k := k) (α := α) hHp hl
  obtain ⟨hWI₁K, hWI₂K⟩ := odd_winner_high_K (α := α) hHp hdHt hKt hpar hk hl
    hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  obtain ⟨hm1, hd1, hK1⟩ := hHp (l - 1) (by omega) (by omega)
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
    have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
    omega
  have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.add_mul, one_mul]
  have hb3 : (k - 3) * 2 ^ l + 2 ^ l = (k - 2) * 2 ^ l := by
    have h1 : k - 3 + 1 = k - 2 := by omega
    calc (k - 3) * 2 ^ l + 2 ^ l = (k - 3 + 1) * 2 ^ l := by ring
      _ = (k - 2) * 2 ^ l := by rw [h1]
  have hk2b : (k - 1 - 1) * 2 ^ l = (k - 2) * 2 ^ l := rfl
  set γ := rSlot k l α (A := A) with hγ
  -- block certificates
  have htS1c := tS1_block_cert (Hp := Hp) (α := α) (k := k) (l := l)
    (fun i h1 h2 => hHp i h1 (by omega)) (by omega)
  have htS1tc := tS1t_block_cert (Hp := Hp) (α := α) (k := k) (l := l)
    (fun i h1 h2 => hHp i h1 (by omega)) (by omega)
  -- the two principal exposures
  have hWU₁ : Hp l - (k - 1) • tS1 Hp k l α
      = Hp l - ((k - 1 : ℕ) : A[X]) * tS1 Hp k l α := by rw [nsmul_eq_mul]
  have hWU₂ : Ht - (k - 1) • tS1t Hp k l α
      = Ht - ((k - 1 : ℕ) : A[X]) * tS1t Hp k l α := by rw [nsmul_eq_mul]
  have hp2le : 2 ≤ 2 ^ (l - 1) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 from by omega)
      (show 1 ≤ l - 1 from by omega)
    have h2e : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  -- monic multiplier facts
  have htS1deg : (tS1 Hp k l α).degree < (Hp l).degree := by
    rw [degree_eq_natDegree htS1m.ne_zero, degree_eq_natDegree hMm.ne_zero, hMd,
      htS1d]
    exact_mod_cast (by omega : 2 ^ (l - 1) < 2 ^ l)
  have hW1m : (Hp l - (k - 1) • tS1 Hp k l α).Monic := by
    have := hMm.add_of_left (q := -((k - 1) • tS1 Hp k l α)) (by
      rw [degree_neg]
      exact lt_of_le_of_lt (degree_smul_le _ _) htS1deg)
    simpa [sub_eq_add_neg] using this
  have hW1d : (Hp l - (k - 1) • tS1 Hp k l α).natDegree = 2 ^ l := by
    rw [sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        exact lt_of_le_of_lt (degree_smul_le _ _) htS1deg)), hMd]
  have hU1m : (Hp l + tS1 Hp k l α).Monic := hMm.add_of_left htS1deg
  have hU1d : (Hp l + tS1 Hp k l α).natDegree = 2 ^ l := by
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt htS1deg), hMd]
  have htS1tdeg : (tS1t Hp k l α).degree < Ht.degree := by
    rw [degree_eq_natDegree htS1tm.ne_zero, degree_eq_natDegree hHt.ne_zero, hdHt,
      htS1td]
    exact_mod_cast (by omega : 2 ^ (l - 1) < 2 ^ l)
  have hW2m : (Ht - (k - 1) • tS1t Hp k l α).Monic := by
    have := hHt.add_of_left (q := -((k - 1) • tS1t Hp k l α)) (by
      rw [degree_neg]
      exact lt_of_le_of_lt (degree_smul_le _ _) htS1tdeg)
    simpa [sub_eq_add_neg] using this
  have hW2d : (Ht - (k - 1) • tS1t Hp k l α).natDegree = 2 ^ l := by
    rw [sub_eq_add_neg,
      natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt (by
        rw [degree_neg]
        exact lt_of_le_of_lt (degree_smul_le _ _) htS1tdeg)), hdHt]
  have hU2m : (Ht + tS1t Hp k l α).Monic := hHt.add_of_left htS1tdeg
  have hU2d : (Ht + tS1t Hp k l α).natDegree = 2 ^ l := by
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt htS1tdeg), hdHt]
  have hL1d : ((Hp l - (k - 1) • tS1 Hp k l α)
      * (Hp l + tS1 Hp k l α) ^ (k - 3)).natDegree = (k - 2) * 2 ^ l := by
    rw [hW1m.natDegree_mul (hU1m.pow _), hW1d, hU1m.natDegree_pow, hU1d]
    omega
  have hL2d : ((Ht - (k - 1) • tS1t Hp k l α)
      * (Ht + tS1t Hp k l α) ^ (k - 3)).natDegree = (k - 2) * 2 ^ l := by
    rw [hW2m.natDegree_mul (hU2m.pow _), hW2d, hU2m.natDegree_pow, hU2d]
    omega
  -- top-K facts
  have hoGc := oG_cert (Hp := Hp) (α := α) (k := k)
    (fun i h1 h2 => hHp i h1 (by omega)) hl h2
  have hoG1Ktop : ∀ i, 2 ^ (l - 1) - 1 ≤ i → (oG1 Hp k l α).coeff i ∈ K := by
    intro i hi
    refine mem_of_sup_adjoin_empty ?_ (hoGc.supp₁ i)
    rw [Set.image_eq_empty]
    exact Set.Ico_eq_empty (by omega)
  have hoG2Ktop : ∀ i, 2 ^ (l - 1) ≤ i → (oG2 Hp k l α).coeff i ∈ K := by
    intro i hi
    refine mem_of_sup_adjoin_empty ?_ (hoGc.supp₂ i)
    rw [Set.image_eq_empty]
    exact Set.Ico_eq_empty (by omega)
  have hW₁Ktop : ∀ a, 2 ^ l - 1 ≤ a → (Hp l - (k - 1) • tS1 Hp k l α).coeff a ∈ K := by
    intro a ha
    rw [coeff_sub, coeff_smul, nsmul_eq_mul,
      show (tS1 Hp k l α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      mul_zero, sub_zero]
    exact hMK a
  have hU₁Ktop : ∀ a, 2 ^ l - 1 ≤ a → (Hp l + tS1 Hp k l α).coeff a ∈ K := by
    intro a ha
    rw [coeff_add,
      show (tS1 Hp k l α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      add_zero]
    exact hMK a
  have hW₂Ktop : ∀ a, 2 ^ l - 1 ≤ a → (Ht - (k - 1) • tS1t Hp k l α).coeff a ∈ K := by
    intro a ha
    rw [coeff_sub, coeff_smul, nsmul_eq_mul,
      show (tS1t Hp k l α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      mul_zero, sub_zero]
    exact hKt a
  have hU₂Ktop : ∀ a, 2 ^ l - 1 ≤ a → (Ht + tS1t Hp k l α).coeff a ∈ K := by
    intro a ha
    rw [coeff_add,
      show (tS1t Hp k l α).coeff a = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      add_zero]
    exact hKt a
  have hUpow₁K : ∀ b, (k - 3) * 2 ^ l - 1 ≤ b →
      ((Hp l + tS1 Hp k l α) ^ (k - 3)).coeff b ∈ K :=
    fun b hb => coeff_pow_high_K (le_of_eq hU1d) hU₁Ktop (k - 3) b hb
  have hUpow₂K : ∀ b, (k - 3) * 2 ^ l - 1 ≤ b →
      ((Ht + tS1t Hp k l α) ^ (k - 3)).coeff b ∈ K :=
    fun b hb => coeff_pow_high_K (le_of_eq hU2d) hU₂Ktop (k - 3) b hb
  have hL₁Ktop : ∀ a, (k - 2) * 2 ^ l - 1 ≤ a →
      ((Hp l - (k - 1) • tS1 Hp k l α)
        * (Hp l + tS1 Hp k l α) ^ (k - 3)).coeff a ∈ K := by
    intro a ha
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = a := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (2 ^ l) x.1 with hgt | hle
    · rw [show (Hp l - (k - 1) • tS1 Hp k l α).coeff x.1 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge ((k - 3) * 2 ^ l) x.2 with hgt2 | hle2
      · rw [show ((Hp l + tS1 Hp k l α) ^ (k - 3)).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by
            have : ((Hp l + tS1 Hp k l α) ^ (k - 3)).natDegree ≤ (k - 3) * 2 ^ l := by
              refine le_trans natDegree_pow_le ?_
              exact Nat.mul_le_mul_left _ (le_of_eq hU1d)
            omega), mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hW₁Ktop x.1 (by omega)) (hUpow₁K x.2 (by omega))
  have hL₂Ktop : ∀ a, (k - 2) * 2 ^ l - 1 ≤ a →
      ((Ht - (k - 1) • tS1t Hp k l α)
        * (Ht + tS1t Hp k l α) ^ (k - 3)).coeff a ∈ K := by
    intro a ha
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = a := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (2 ^ l) x.1 with hgt | hle
    · rw [show (Ht - (k - 1) • tS1t Hp k l α).coeff x.1 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge ((k - 3) * 2 ^ l) x.2 with hgt2 | hle2
      · rw [show ((Ht + tS1t Hp k l α) ^ (k - 3)).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by
            have : ((Ht + tS1t Hp k l α) ^ (k - 3)).natDegree ≤ (k - 3) * 2 ^ l := by
              refine le_trans natDegree_pow_le ?_
              exact Nat.mul_le_mul_left _ (le_of_eq hU2d)
            omega), mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hW₂Ktop x.1 (by omega)) (hUpow₂K x.2 (by omega))
  have hoGt₁K : ∀ m', (k - 2) * 2 ^ l + 2 ^ (l - 1) - 1 ≤ m' →
      ((Hp l - (k - 1) • tS1 Hp k l α)
        * (Hp l + tS1 Hp k l α) ^ (k - 3) * oG1 Hp k l α).coeff m' ∈ K := by
    intro m' hm'
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m' := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (2 ^ (l - 1)) x.2 with hgt | hle
    · rw [show (oG1 Hp k l α).coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge ((k - 2) * 2 ^ l) x.1 with hgt1 | hle1
      · rw [show ((Hp l - (k - 1) • tS1 Hp k l α)
            * (Hp l + tS1 Hp k l α) ^ (k - 3)).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hL₁Ktop x.1 (by omega)) (hoG1Ktop x.2 (by omega))
  have hoGt₂K : ∀ m', (k - 2) * 2 ^ l + 2 ^ (l - 1) ≤ m' →
      ((Ht - (k - 1) • tS1t Hp k l α)
        * (Ht + tS1t Hp k l α) ^ (k - 3) * oG2 Hp k l α).coeff m' ∈ K := by
    intro m' hm'
    rw [coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m' := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (2 ^ (l - 1)) x.2 with hgt | hle
    · rw [show (oG2 Hp k l α).coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge ((k - 2) * 2 ^ l) x.1 with hgt1 | hle1
      · rw [show ((Ht - (k - 1) • tS1t Hp k l α)
            * (Ht + tS1t Hp k l α) ^ (k - 3)).coeff x.1 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hL₂Ktop x.1 (by omega)) (hoG2Ktop x.2 (by omega))
  -- binTail terms vanish here
  have hbinZ : ∀ (W' U' G' : A[X]), W'.natDegree ≤ 2 ^ l → U'.natDegree ≤ 2 ^ l →
      G'.natDegree ≤ 2 ^ (l - 1) → ∀ m', (k - 3) * 2 ^ l < m' →
      (W' * binTail (U' ^ 2) G' ((k - 1) / 2)).coeff m' = 0 := by
    intro W' U' G' hW' hU' hG' m' hm'
    rcases Nat.lt_or_ge k 5 with hk3 | hk5
    · have hbz : binTail (U' ^ 2) G' ((k - 1) / 2) = 0 := by
        show (∑ q ∈ Finset.Icc 2 ((k - 1) / 2), _) = 0
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      rw [hbz, mul_zero, coeff_zero]
    · have hp21 : (2 : ℕ) ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
      have hUsq : (U' ^ 2).natDegree ≤ 2 ^ (l + 1) := by
        have h := natDegree_pow_le (p := U') (n := 2)
        omega
      have hbt : (binTail (U' ^ 2) G' ((k - 1) / 2)).natDegree
          ≤ 2 * 2 ^ (l - 1) + ((k - 1) / 2 - 2) * 2 ^ (l + 1) :=
        natDegree_binTail_le hUsq hG' (by omega) _
      have hm2 : ((k - 1) / 2 - 2) * 2 ^ (l + 1) = (k - 5) * 2 ^ l := by
        rw [hp21]
        have hc : (k - 1) / 2 - 2 + 2 = (k - 1) / 2 := by omega
        have h2 : ((k - 1) / 2) * (2 * 2 ^ l) = (k - 1) * 2 ^ l := by
          have hh : (k - 1) / 2 * 2 = k - 1 := by omega
          calc ((k - 1) / 2) * (2 * 2 ^ l) = ((k - 1) / 2 * 2) * 2 ^ l := by ring
            _ = (k - 1) * 2 ^ l := by rw [hh]
        have h3 : ((k - 1) / 2 - 2) * (2 * 2 ^ l) + 2 * (2 * 2 ^ l)
            = ((k - 1) / 2) * (2 * 2 ^ l) := by
          rw [← Nat.add_mul, hc]
        have h4 : (k - 5) * 2 ^ l + 4 * 2 ^ l = (k - 1) * 2 ^ l := by
          have hc4 : k - 5 + 4 = k - 1 := by omega
          rw [← Nat.add_mul, hc4]
        omega
      have h7 : (k - 5) * 2 ^ l + 2 * 2 ^ l = (k - 3) * 2 ^ l := by
        have hc7 : k - 5 + 2 = k - 3 := by omega
        rw [← Nat.add_mul, hc7]
      refine coeff_eq_zero_of_natDegree_lt ?_
      have h := natDegree_mul_le (p := W') (q := binTail (U' ^ 2) G' ((k - 1) / 2))
      omega
  have hbin₁Z := hbinZ _ _ _ (le_of_eq hW1d) (le_of_eq hU1d) hoG1d
  have hbin₂Z := hbinZ _ _ _ (le_of_eq hW2d) (le_of_eq hU2d) hoG2d
  have hmersK : ∀ m', 2 ^ l - 1 ≤ m' →
      (peel Hp l (fun j => α (1 + j))).coeff m' ∈ K := by
    intro m' hm'
    obtain ⟨hmm, hmd⟩ := peel_monic Hp l
      (fun i h1 h2 => ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1⟩)
      (by omega) (fun j => α (1 + j))
    rcases Nat.lt_or_ge (2 ^ l - 1) m' with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · rw [show m' = 2 ^ l - 1 from by omega, ← hmd, hmm.coeff_natDegree]
      exact Subalgebra.one_mem _
  -- principal₂ is K above the δ-row
  have htS1tK1 : ∀ m, 1 ≤ m → (tS1t Hp k l α).coeff m ∈ K := by
    intro m hm
    show (Hp (l - 1) + C _).coeff m ∈ K
    rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
    exact hK1 m
  have hsqtK : ∀ m', 2 ^ (l - 1) < m' → (tS1t Hp k l α ^ 2).coeff m' ∈ K := by
    intro m' hgt'
    rw [sq, coeff_mul]
    refine Subalgebra.sum_mem _ fun y hy => ?_
    have hya : y.1 + y.2 = m' := Finset.mem_antidiagonal.1 hy
    rcases Nat.lt_or_ge (2 ^ (l - 1)) y.1 with hg1 | hl1
    · rw [show (tS1t Hp k l α).coeff y.1 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge (2 ^ (l - 1)) y.2 with hg2 | hl2
      · rw [show (tS1t Hp k l α).coeff y.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (htS1tK1 y.1 (by omega)) (htS1tK1 y.2 (by omega))
  have hprinsplit₂ : (Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
      - Ht ^ k
      = (((k - 1).choose 2 : A[X]) - ((k - 1 : ℕ) : A[X]) * ((k - 1 : ℕ) : A[X]))
          * (tS1t Hp k l α ^ 2 * Ht ^ (k - 1 - 1))
        + uTail Ht (tS1t Hp k l α) (k - 1) := by
    have hsplit := mul_pow_split Ht (tS1t Hp k l α) (n := k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at hsplit
    rw [hWU₂, hsplit]
    ring
  have hprin₂K : ∀ m', (k - 2) * 2 ^ l + 2 ^ (l - 1) < m' →
      ((Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
        - Ht ^ k).coeff m' ∈ K := by
    intro m' hm'
    rw [hprinsplit₂, coeff_add,
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
      have hxa : x.1 + x.2 = m' := Finset.mem_antidiagonal.1 hx
      rcases Nat.lt_or_ge ((k - 1 - 1) * 2 ^ l) x.2 with hg2 | hl2
      · rw [show (Ht ^ (k - 1 - 1)).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by
            rw [hHt.natDegree_pow, hdHt]
            exact hg2), mul_zero]
        exact Subalgebra.zero_mem _
      · have hx1 : 2 ^ (l - 1) < x.1 := by omega
        exact Subalgebra.mul_mem _ (hsqtK x.1 hx1)
          (coeff_mem_pow hKt (k - 1 - 1) x.2)
    · rw [show (uTail Ht (tS1t Hp k l α) (k - 1)).coeff m' = 0 from
        coeff_eq_zero_of_natDegree_lt (by
          refine lt_of_le_of_lt (natDegree_uTail_le (le_of_eq hdHt)
            (le_of_eq htS1td) (by omega)) ?_
          have hk3 : (k - 1 - 2) * 2 ^ l = (k - 3) * 2 ^ l := rfl
          omega)]
      exact Subalgebra.zero_mem _
  -- expanded decompositions
  have hd₁ : (Rpair Hp Ht k l α).1
      = ((Hp l - (k - 1) • tS1 Hp k l α) * (Hp l + tS1 Hp k l α) ^ (k - 1)
          - Hp l ^ k)
        + ((k - 1) / 2) • ((Hp l - (k - 1) • tS1 Hp k l α)
            * (Hp l + tS1 Hp k l α) ^ (k - 3) * oG1 Hp k l α)
        + (Hp l - (k - 1) • tS1 Hp k l α)
            * binTail ((Hp l + tS1 Hp k l α) ^ 2) (oG1 Hp k l α) ((k - 1) / 2)
        + (Hp l - (k - 1) • tS1 Hp k l α)
            * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                (fun j => α (2 ^ l + j))).1
        + peel Hp l (fun j => α (1 + j)) := by
    rw [Rpair_odd_fst' hpar (by omega) hl]
    ring
  have hd₂ : (Rpair Hp Ht k l α).2
      = ((Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
          - Ht ^ k)
        + ((k - 1) / 2) • ((Ht - (k - 1) • tS1t Hp k l α)
            * (Ht + tS1t Hp k l α) ^ (k - 3) * oG2 Hp k l α)
        + (Ht - (k - 1) • tS1t Hp k l α)
            * binTail ((Ht + tS1t Hp k l α) ^ 2) (oG2 Hp k l α) ((k - 1) / 2)
        + (Ht - (k - 1) • tS1t Hp k l α)
            * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                (fun j => α (2 ^ l + j))).2
        + C (α 0) := by
    rw [Rpair_odd_snd' hpar (by omega) hl]
    ring
  -- slope bridge
  have hslope : ∀ j', (k - 2) * 2 ^ l + 2 ^ (l - 1) ≤ j' →
      algebraMap R A (((tLam k l j' : ℤ) : R)) = -((k * (k - 1) : ℕ) : A) := by
    intro j' hj'
    rw [tLam_odd_hi hpar hk hl hj',
      show (((-(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ))) : ℤ) : R)
        = -(((k * (k - 1) : ℕ) : ℤ) : R) from by push_cast; ring,
      map_neg, Int.cast_natCast, map_natCast]
  intro j hj1 hj2
  rcases eq_or_lt_of_le hj1 with heq | hlt
  · -- the δ row: pivot from the second-component principal term
    subst heq
    obtain ⟨F₂, hF₂, hFe₂⟩ := principal_expose (K := K) hHt hdHt hKt htS1tm htS1td
      htS1tc (by omega) hp1 (by omega) (by omega : 2 ≤ k - 1) 0 (by omega)
    have hF₂K : F₂ ∈ K := by
      refine mem_of_sup_adjoin_empty ?_ hF₂
      rw [Set.image_eq_empty]
      exact Set.Ico_eq_empty (by omega)
    rw [show k - 1 + 1 = k from by omega] at hFe₂
    rw [show (k - 1 - 1) * 2 ^ l + 2 ^ (l - 1) + 0
      = (k - 2) * 2 ^ l + 2 ^ (l - 1) from by omega] at hFe₂
    -- first-component window closure for the principal term
    have htS1V' : ∀ a, (tS1 Hp k l α).coeff a ∈ K ⊔ adjoin R
        (γ '' Set.Ico ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1) ((k - 1) * 2 ^ l)) :=
      fun a => htS1V _ a (by omega)
    have hW1V : ∀ a, (Hp l - (k - 1) • tS1 Hp k l α).coeff a ∈ K ⊔ adjoin R
        (γ '' Set.Ico ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1) ((k - 1) * 2 ^ l)) := by
      intro a
      rw [coeff_sub, coeff_smul, nsmul_eq_mul]
      exact Subalgebra.sub_mem _ ((le_sup_left : K ≤ _) (hMK a))
        (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (htS1V' a))
    have hU1V : ∀ a, (Hp l + tS1 Hp k l α).coeff a ∈ K ⊔ adjoin R
        (γ '' Set.Ico ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1) ((k - 1) * 2 ^ l)) := by
      intro a
      rw [coeff_add]
      exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hMK a)) (htS1V' a)
    have hprin₁V : ∀ m', ((Hp l - (k - 1) • tS1 Hp k l α)
        * (Hp l + tS1 Hp k l α) ^ (k - 1) - Hp l ^ k).coeff m' ∈ K ⊔ adjoin R
        (γ '' Set.Ico ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1) ((k - 1) * 2 ^ l)) := by
      intro m'
      rw [coeff_sub]
      exact Subalgebra.sub_mem _
        (coeff_mem_mul hW1V (coeff_mem_pow hU1V (k - 1)) m')
        ((le_sup_left : K ≤ _) (coeff_mem_pow hMK k m'))
    have hslotδ : γ ((k - 2) * 2 ^ l + 2 ^ (l - 1))
        = α ((k - 2) * 2 ^ l + 2 ^ (l - 1)) := by
      rw [hγ]
      exact rSlot_odd_delta hpar hk hl
    have hcO : (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff
        ((k - 2) * 2 ^ l + 2 ^ (l - 1))
        = (Rpair Hp Ht k l α).1.coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1) - 1)
          + (Rpair Hp Ht k l α).2.coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1)) := by
      obtain ⟨s', hs'⟩ : ∃ s', (k - 2) * 2 ^ l + 2 ^ (l - 1) = s' + 1 :=
        ⟨(k - 2) * 2 ^ l + 2 ^ (l - 1) - 1, by omega⟩
      rw [hs', coeff_combined, Nat.add_sub_cancel]
    have hCz : (C (α 0) : A[X]).coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1)) = 0 := by
      rw [coeff_C, if_neg (by omega)]
    refine ⟨((Hp l - (k - 1) • tS1 Hp k l α) * (Hp l + tS1 Hp k l α) ^ (k - 1)
        - Hp l ^ k).coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1) - 1)
      + (((k - 1) / 2 : ℕ) : A) * ((Hp l - (k - 1) • tS1 Hp k l α)
          * (Hp l + tS1 Hp k l α) ^ (k - 3) * oG1 Hp k l α).coeff
          ((k - 2) * 2 ^ l + 2 ^ (l - 1) - 1)
      + ((Hp l - (k - 1) • tS1 Hp k l α)
          * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
              (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
              (fun j => α (2 ^ l + j))).1).coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1) - 1)
      + (peel Hp l (fun j => α (1 + j))).coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1) - 1)
      + ((((k - 1) / 2 : ℕ) : A) * ((Ht - (k - 1) • tS1t Hp k l α)
            * (Ht + tS1t Hp k l α) ^ (k - 3) * oG2 Hp k l α).coeff
            ((k - 2) * 2 ^ l + 2 ^ (l - 1))
        + ((Ht - (k - 1) • tS1t Hp k l α)
            * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                (fun j => α (2 ^ l + j))).2).coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1)))
      + F₂, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
          (hprin₁V _)
          ((le_sup_left : K ≤ _) (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
            (hoGt₁K _ (by omega)))))
          ((le_sup_left : K ≤ _) (hWI₁K _ (by omega))))
        ((le_sup_left : K ≤ _) (hmersK _ (by omega))))
        (Subalgebra.add_mem _
          ((le_sup_left : K ≤ _) (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
            (hoGt₂K _ (by omega))))
          ((le_sup_left : K ≤ _) (hWI₂K _ (by omega)))))
        ((le_sup_left : K ≤ _) hF₂K)
    · rw [hcO, hd₁, hd₂]
      simp only [coeff_add, coeff_smul]
      rw [hCz, hslope _ (by omega), hslotδ,
        hbin₁Z _ (by omega), hbin₂Z _ (by omega)]
      simp only [nsmul_eq_mul] at hFe₂ ⊢
      linear_combination hFe₂
  · -- the tS1 block rows: pivot from the first-component principal term
    obtain ⟨g, rfl⟩ : ∃ g, j = (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g :=
      ⟨j - ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1), by omega⟩
    have hg : g < 2 ^ (l - 1) - 1 := by omega
    obtain ⟨F₁, hF₁, hFe₁⟩ := principal_expose (K := K) hMm hMd hMK htS1m htS1d
      htS1c (by omega) hp1 (by omega) (by omega : 2 ≤ k - 1) g hg
    rw [show k - 1 + 1 = k from by omega] at hFe₁
    rw [show (k - 1 - 1) * 2 ^ l + 2 ^ (l - 1) + g
      = (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g - 1 from by omega] at hFe₁
    have hβγ : ∀ g', peelSlot (l - 1)
        (fun j' => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j')) g'
        = γ ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g') := by
      intro g'
      rw [hγ, rSlot_odd_tS1 hpar hk hl (by omega)]
      congr 1
      omega
    have hF₁V : F₁ ∈ K ⊔ adjoin R (γ '' Set.Ico
        ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g + 1) ((k - 1) * 2 ^ l)) := by
      refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF₁
      rintro _ ⟨g', ⟨hg1, hg2⟩, rfl⟩
      rw [hβγ g']
      exact (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨(k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g',
          ⟨by omega, by omega⟩, rfl⟩)
    have hslotT : γ ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g)
        = peelSlot (l - 1)
          (fun j' => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j')) g := by
      rw [hβγ g]
    have hcO : (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff
        ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g)
        = (Rpair Hp Ht k l α).1.coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g - 1)
          + (Rpair Hp Ht k l α).2.coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g) := by
      obtain ⟨s', hs'⟩ : ∃ s', (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g = s' + 1 :=
        ⟨(k - 2) * 2 ^ l + 2 ^ (l - 1) + g, by omega⟩
      rw [hs', coeff_combined]
      congr 2
    have hCz : (C (α 0) : A[X]).coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g) = 0 := by
      rw [coeff_C, if_neg (by omega)]
    refine ⟨(((k - 1) / 2 : ℕ) : A) * ((Hp l - (k - 1) • tS1 Hp k l α)
          * (Hp l + tS1 Hp k l α) ^ (k - 3) * oG1 Hp k l α).coeff
          ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g - 1)
      + ((Hp l - (k - 1) • tS1 Hp k l α)
          * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
              (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
              (fun j => α (2 ^ l + j))).1).coeff
          ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g - 1)
      + (peel Hp l (fun j => α (1 + j))).coeff
          ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g - 1)
      + (((Ht - (k - 1) • tS1t Hp k l α) * (Ht + tS1t Hp k l α) ^ (k - 1)
            - Ht ^ k).coeff ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g)
        + (((k - 1) / 2 : ℕ) : A) * ((Ht - (k - 1) • tS1t Hp k l α)
            * (Ht + tS1t Hp k l α) ^ (k - 3) * oG2 Hp k l α).coeff
            ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g)
        + ((Ht - (k - 1) • tS1t Hp k l α)
            * (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                (fun j => α (2 ^ l + j))).2).coeff
            ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g))
      + F₁, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (Subalgebra.add_mem _
          ((le_sup_left : K ≤ _) (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
            (hoGt₁K _ (by omega))))
          ((le_sup_left : K ≤ _) (hWI₁K _ (by omega))))
        ((le_sup_left : K ≤ _) (hmersK _ (by omega))))
        (Subalgebra.add_mem _ (Subalgebra.add_mem _
          ((le_sup_left : K ≤ _) (hprin₂K _ (by omega)))
          ((le_sup_left : K ≤ _) (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
            (hoGt₂K _ (by omega)))))
          ((le_sup_left : K ≤ _) (hWI₂K _ (by omega)))))
        hF₁V
    · rw [hcO, hd₁, hd₂]
      simp only [coeff_add, coeff_smul]
      rw [hCz, hslope _ (by omega), hslotT,
        hbin₁Z _ (by omega), hbin₂Z _ (by omega)]
      simp only [nsmul_eq_mul] at hFe₁ ⊢
      linear_combination hFe₁

/-- **Odd branch step**: the full triangular certificate for the level-`(k, l)` odd
remainder pair, assembled from the inner `((k-1)/2, l+1)` certificate. -/
theorem Rk2l_tri_odd_step
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2)
    (h2 : IsUnit (2 : R)) (hum : IsUnit ((((k - 1) / 2 : ℕ) : ℤ) : R))
    (huk : IsUnit (((k : ℕ) : ℤ) : R)) (huk1 : IsUnit (((k - 1 : ℕ) : ℤ) : R))
    (hin : CoeffTriangular (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
        Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
      (rSlot ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)))
      (fun j => ((tLam ((k - 1) / 2) (l + 1) j : ℤ) : R)) ((k - 3) * 2 ^ l)
      (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1
      (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2)
    (hind₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1.natDegree ≤ (k - 3) * 2 ^ l)
    (hind₂ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2.natDegree ≤ (k - 3) * 2 ^ l)
    (htop₁₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l) ∈ K)
    (htop₁₂ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l - 1) ∈ K)
    (htop₂₁ : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
        (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2.coeff ((k - 3) * 2 ^ l) ∈ K) :
    CoeffTriangular K (rSlot k l α) (fun j => ((tLam k l j : ℤ) : R))
      ((k - 1) * 2 ^ l) (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2 where
  unit j hj := by
    rcases Nat.lt_or_ge j (2 ^ l) with hlow | h1
    · rw [tLam_odd_low hpar hk hl hlow, Int.cast_one]
      exact isUnit_one
    · rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l) with hinn | hb
      · rw [tLam_odd_inner hpar hk hl h1 hinn]
        refine hin.unit _ ?_
        have hb3 : (k - 3) * 2 ^ l + 2 ^ l = (k - 2) * 2 ^ l := by
          have h1' : k - 3 + 1 = k - 2 := by omega
          calc (k - 3) * 2 ^ l + 2 ^ l = (k - 3 + 1) * 2 ^ l := by ring
            _ = (k - 2) * 2 ^ l := by rw [h1']
        omega
      · rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l + 2 ^ (l - 2)) with hm1 | hm
        · rw [tLam_odd_mid1 hpar hk hl hb hm1]
          exact hum
        · rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l + 2 ^ (l - 1)) with hm2 | hhi
          · rw [tLam_odd_mid2 hpar hk hl hm hm2,
              show (((-(k - 1 : ℕ) : ℤ)) : R) = -(((k - 1 : ℕ) : ℤ) : R) from by
                push_cast; ring]
            exact huk1.neg
          · rw [tLam_odd_hi hpar hk hl hhi,
              show (((-(((k : ℕ) : ℤ) * ((k - 1 : ℕ) : ℤ))) : ℤ) : R)
                = -((((k : ℕ) : ℤ) : R) * (((k - 1 : ℕ) : ℤ) : R)) from by
                push_cast; ring]
            exact (huk.mul huk1).neg
  supp₁ := odd_supp₁ hHp hpar hk hl h2 (fun j => hin.supp₁ j) hind₁ htop₁₁
  supp₂ := odd_supp₂ hHp hHt hdHt hKt hpar hk hl h2 (fun j => hin.supp₂ j) hind₂
  pivot j hj := by
    rcases Nat.lt_or_ge j (2 ^ l) with hlow | h1
    · obtain ⟨hrest₁, hrest₂⟩ := odd_rest_mem hHp hKt hpar hk hl h2
        (fun j => hin.supp₁ j) (fun j => hin.supp₂ j)
      exact odd_pivot_low hHp hpar hk hl hrest₁ hrest₂ j hlow
    · rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l) with hinn | hb
      · exact odd_pivot_inner hHp hHt hdHt hKt hpar hk hl h2 hin j h1 hinn
      · rcases Nat.lt_or_ge j ((k - 2) * 2 ^ l + 2 ^ (l - 1)) with hband | hpr
        · exact odd_pivot_band hHp hHt hdHt hKt hpar hk hl h2
            hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁ j hb hband
        · exact odd_pivot_principal hHp hHt hdHt hKt hpar hk hl h2
            hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁ j hpr hj
end FastPoly
