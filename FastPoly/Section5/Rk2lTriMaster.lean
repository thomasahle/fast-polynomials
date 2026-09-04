import FastPoly.Section5.Rk2lTriOddBase
import FastPoly.Section5.Rk2lTriEven
import FastPoly.Section5.Rk2l

/-!
# `lem:Rk2l`(3): the master triangular certificate

Strong induction on `k` through the three branch certificates
(`Rk2l_tri_base`, `Rk2l_tri_even_step`, `Rk2l_tri_odd_step`,
`Rk2l_tri_oddbase_step`).  The recursive call runs over the band-augmented context
`K ⊔ adjoin (rSlot k l α '' band)`; the inner pair's boundary coefficients are
recovered in plain `K` through the sharpened `Rk2l_top_two`.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}

omit [Nontrivial A] in
/-- Boundary coefficient of a square: only the top-two coefficients of the base
enter. -/
theorem sq_sublead_mem {P : A[X]} {D : ℕ} (hPd : P.natDegree ≤ D)
    (htop : P.coeff D ∈ K) (hsub : P.coeff (D - 1) ∈ K) (h1 : 1 ≤ D) :
    (P ^ 2).coeff (2 * D - 1) ∈ K := by
  rw [sq, coeff_mul]
  refine Subalgebra.sum_mem _ fun x hx => ?_
  have hxa : x.1 + x.2 = 2 * D - 1 := Finset.mem_antidiagonal.1 hx
  rcases Nat.lt_or_ge D x.1 with hg1 | hl1
  · rw [show P.coeff x.1 = 0 from coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    exact Subalgebra.zero_mem _
  · rcases Nat.lt_or_ge D x.2 with hg2 | hl2
    · rw [show P.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
        mul_zero]
      exact Subalgebra.zero_mem _
    · have hx1 : x.1 = D - 1 ∨ x.1 = D := by omega
      have hx2 : x.2 = D - 1 ∨ x.2 = D := by omega
      rcases hx1 with h | h <;> rcases hx2 with h' | h' <;>
        rw [h, h'] <;> exact Subalgebra.mul_mem _ (by assumption) (by assumption)

/-- Subleading coefficient of the square of a monic base plus a low perturbation:
only the base's subleading coefficient enters. -/
theorem add_low_sq_sublead_mem {B s : A[X]} {D : ℕ} (hBm : B.Monic)
    (hBd : B.natDegree = D) (hs : s = 0 ∨ s.natDegree < D - 1) (h1 : 1 ≤ D)
    (hKsub : B.coeff (D - 1) ∈ K) :
    ((B + s) ^ 2).coeff (2 * D - 1) ∈ K := by
  obtain ⟨hm, hd⟩ := monic_add_low (e := s) hBm (by
    rcases hs with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr (by omega))
  rw [hBd] at hd
  have hsz : s.coeff (D - 1) = 0 := by
    rcases hs with rfl | hlt
    · exact coeff_zero _
    · exact coeff_eq_zero_of_natDegree_lt hlt
  refine sq_sublead_mem (le_of_eq hd) ?_ ?_ h1
  · rw [← hd, hm.coeff_natDegree]
    exact Subalgebra.one_mem _
  · rw [coeff_add, hsz, add_zero]
    exact hKsub

/-- Subleading coefficient of the odd tower update is known. -/
theorem oddH_sublead_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l)
    (hK2 : (Hp l).coeff (2 ^ l - 1) ∈ K) :
    (oddH Hp k l α).coeff (2 ^ (l + 1) - 1) ∈ K := by
  obtain ⟨-, hs1d⟩ := tS1_good (k := k) (α := α) hHp (by omega)
  obtain ⟨hLm, hLd⟩ := hHp l (by omega) le_rfl
  obtain ⟨hG1d, -, -⟩ := oG1_top (k := k) (α := α) hHp hl
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hp21 : 2 ^ l + 2 ^ l = 2 ^ (l + 1) := by
    rw [pow_succ]
    ring
  have hp2le : 2 ≤ 2 ^ (l - 1) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 from by omega)
      (show 1 ≤ l - 1 from by omega)
    have h2e : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  have hG1z : (oG1 Hp k l α).coeff (2 ^ (l + 1) - 1) = 0 := by
    refine coeff_eq_zero_of_natDegree_lt ?_
    have h := hG1d
    omega
  rw [oddH_eq_sq_add, coeff_add, hG1z]
  refine Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _)
  have h := add_low_sq_sublead_mem (K := K) (s := tS1 Hp k l α) hLm hLd
    (Or.inr (by rw [hs1d]; omega)) (by omega) hK2
  rw [show 2 * 2 ^ l - 1 = 2 ^ (l + 1) - 1 from by omega] at h
  exact h

/-- Subleading coefficient of the odd companion update is known. -/
theorem oddHt_sublead_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 3 ≤ l) (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l)
    (hKt2 : Ht.coeff (2 ^ l - 1) ∈ K) :
    (oddHt Hp Ht k l α).coeff (2 ^ (l + 1) - 1) ∈ K := by
  obtain ⟨-, hs1td⟩ := tS1t_good (k := k) (α := α) hHp (by omega)
  obtain ⟨hG2d, -, -⟩ := oG2_top (k := k) (α := α) hHp hl
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hp21 : 2 ^ l + 2 ^ l = 2 ^ (l + 1) := by
    rw [pow_succ]
    ring
  have hp2le : 2 ≤ 2 ^ (l - 1) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 from by omega)
      (show 1 ≤ l - 1 from by omega)
    have h2e : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  have hG2z : (oG2 Hp k l α).coeff (2 ^ (l + 1) - 1) = 0 := by
    refine coeff_eq_zero_of_natDegree_lt ?_
    have h := hG2d
    omega
  rw [oddHt_eq_sq_add, coeff_add, hG2z]
  refine Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _)
  have h := add_low_sq_sublead_mem (K := K) (s := tS1t Hp k l α) hHt hdHt
    (Or.inr (by rw [hs1td]; omega)) (by omega) hKt2
  rw [show 2 * 2 ^ l - 1 = 2 ^ (l + 1) - 1 from by omega] at h
  exact h


/-- Subleading coefficient of the even tower update is known. -/
theorem evenH_sublead_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l)
    (hK2 : (Hp l).coeff (2 ^ l - 1) ∈ K) :
    (evenH Hp k l α).coeff (2 ^ (l + 1) - 1) ∈ K := by
  obtain ⟨hLm, hLd⟩ := hHp l (by omega) le_rfl
  obtain ⟨hE1d, -, -⟩ := eE1_top (k := k) (α := α) hHp hl
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hp2le : 2 ≤ 2 ^ l := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 from by omega)
      (show 1 ≤ l from by omega)
    have h2e : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  have hp21 : 2 ^ l + 2 ^ l = 2 ^ (l + 1) := by
    rw [pow_succ]
    ring
  have hE1z : (eE1 Hp k l α).coeff (2 ^ (l + 1) - 1) = 0 := by
    refine coeff_eq_zero_of_natDegree_lt ?_
    have h := hE1d
    omega
  rw [evenH_eq_sq_add, coeff_add, hE1z]
  refine Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _)
  have htop : (Hp l).coeff (2 ^ l) ∈ K := by
    rw [← hLd, hLm.coeff_natDegree]
    exact Subalgebra.one_mem _
  have h := sq_sublead_mem (K := K) (le_of_eq hLd) htop hK2 (by omega)
  rw [show 2 * 2 ^ l - 1 = 2 ^ (l + 1) - 1 from by omega] at h
  exact h

/-- Subleading coefficient of the even companion update is known. -/
theorem evenHt_sublead_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l) (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l)
    (hKt2 : Ht.coeff (2 ^ l - 1) ∈ K) :
    (evenHt Hp Ht k l α).coeff (2 ^ (l + 1) - 1) ∈ K := by
  obtain ⟨hE2d, -, -⟩ := eE2_top (k := k) (α := α) hHp hl
  have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
  have hp2le : 2 ≤ 2 ^ l := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 from by omega)
      (show 1 ≤ l from by omega)
    have h2e : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  have hp21 : 2 ^ l + 2 ^ l = 2 ^ (l + 1) := by
    rw [pow_succ]
    ring
  have hE2z : (eE2 Hp k l α).coeff (2 ^ (l + 1) - 1) = 0 := by
    refine coeff_eq_zero_of_natDegree_lt ?_
    have h := hE2d
    omega
  rw [evenHt_eq_sq_add, coeff_add, hE2z]
  refine Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _)
  have htop : Ht.coeff (2 ^ l) ∈ K := by
    rw [← hdHt, hHt.coeff_natDegree]
    exact Subalgebra.one_mem _
  have h := sq_sublead_mem (K := K) (le_of_eq hdHt) htop hKt2 (by omega)
  rw [show 2 * 2 ^ l - 1 = 2 ^ (l + 1) - 1 from by omega] at h
  exact h

/-- Subleading coefficient of the base octic core is known. -/
theorem obH8_sublead_mem
    (h1 : (Hp 1).Monic ∧ (Hp 1).natDegree = 2 ^ 1)
    (h2 : (Hp 2).Monic ∧ (Hp 2).natDegree = 2 ^ 2)
    (hK2 : (Hp 2).coeff 3 ∈ K) :
    (obH8 Hp k α).coeff 7 ∈ K := by
  obtain ⟨h1m, h1d⟩ := h1
  obtain ⟨h2m, h2d⟩ := h2
  obtain ⟨-, hbd⟩ := obS1_good (Hp := Hp) (k := k) (α := α) ⟨h1m, h1d⟩
  have h2d' : (Hp 2).natDegree = 4 := by rw [h2d]; norm_num
  have hGz : (obG k α).coeff 7 = 0 := obG_coeff_high (by omega)
  rw [obH8_eq_sq_add, coeff_add, hGz]
  refine Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _)
  have h := add_low_sq_sublead_mem (K := K) (s := obS1 Hp k α) h2m h2d'
    (Or.inr (by rw [hbd]; omega)) (by omega) hK2
  norm_num at h
  exact h

/-- **`lem:Rk2l-top-boundary`** (sharpened form): **Sharpened boundary**: the four boundary coefficients are known from only the
top-two data of the tower — composable with updated towers. -/
theorem Rk2l_top_two (hk : 2 ≤ k) (hl : 2 ≤ l)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l)
    (hsd : l = 2 → ¬ k % 2 = 0 → 3 ≤ k → ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hK1 : (Hp (l - 1)).coeff (2 ^ (l - 1) - 1) ∈ K)
    (hK2 : (Hp l).coeff (2 ^ l - 1) ∈ K)
    (hKt2 : Ht.coeff (2 ^ l - 1) ∈ K) :
    (Rpair Hp Ht k l α).1.coeff ((k - 1) * 2 ^ l) ∈ K ∧
    (Rpair Hp Ht k l α).1.coeff ((k - 1) * 2 ^ l - 1) ∈ K ∧
    (Rpair Hp Ht k l α).2.coeff ((k - 1) * 2 ^ l) ∈ K ∧
    (Rpair Hp Ht k l α).2.coeff ((k - 1) * 2 ^ l - 1) ∈ K := by
  have hγ : ∀ m : ℕ, -((m : ℕ) : A) ∈ K := fun m =>
    Subalgebra.neg_mem _ (Subalgebra.natCast_mem _ _)
  have hval : ∀ m u : ℕ, ∀ s h : A, s ∈ K → h ∈ K →
      -((m : ℕ) : A) * (2 • s + u • h) ∈ K := by
    intro m u s h hs hh
    refine Subalgebra.mul_mem _ (hγ m) (Subalgebra.add_mem _ ?_ ?_)
    · exact nsmul_mem hs 2
    · exact nsmul_mem hh u
  have hval' : ∀ m u : ℕ, ∀ s h : A, s ∈ K → h ∈ K →
      -((m : ℕ) : A) * (2 • s + ((u : ℕ) : A) * h) ∈ K := by
    intro m u s h hs hh
    exact Subalgebra.mul_mem _ (hγ m) (Subalgebra.add_mem _ (nsmul_mem hs 2)
      (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) hh))
  obtain ⟨hlead1, hlead2⟩ := Rk2l_lead k hk l Hp Ht α hl hHp hHt hdHt hsd
  rcases eq_or_ne (k % 2) 0 with hpar | hpar
  · -- even
    obtain ⟨hi1, hi2⟩ := Rk2l_deg_even (α := α) hk hpar hl hHp hHt hdHt
    obtain ⟨⟨-, -, hs1⟩, ⟨-, -, hs2⟩⟩ := Rpair_even_top (k := k) (α := α) hHp hl hpar
      hk hHt hdHt hi1 hi2
    rw [tS1_coeff_top (k := k) (α := α) hHp hl] at hs1
    rw [tS1t_coeff_top (k := k) (α := α) hl] at hs2
    have hm1 : (Hp (l - 1)).coeff (2 ^ (l - 1) - 1) + 1 ∈ K :=
      Subalgebra.add_mem _ hK1 (Subalgebra.one_mem _)
    exact ⟨by rw [hlead1]; exact hγ _,
      by rw [hs1]; exact hval' _ _ _ _ hm1 hK2,
      by rw [hlead2]; exact hγ _,
      by rw [hs2]; exact hval' _ _ _ _ hK1 hKt2⟩
  · have hk3 : 3 ≤ k := by omega
    rcases Nat.lt_or_ge l 3 with hlb | hl3
    · -- shared odd base, l = 2
      have hleq : l = 2 := by omega
      subst hleq
      obtain ⟨ρ, hρ⟩ := hsd rfl hpar hk3
      obtain ⟨hi1, hi2⟩ := Rk2l_deg_oddbase (α := α) hk3 hpar hHp
      obtain ⟨⟨-, -, hs1⟩, ⟨-, -, hs2⟩⟩ := Rpair_oddbase_top (k := k) (α := α) hHp
        hpar hk3 hHt hdHt ⟨ρ, hρ⟩ hi1 hi2
      rw [show (2:ℕ) - 1 = 1 from rfl, obS1_coeff_one (k := k) (α := α)] at hs1
      rw [show (2:ℕ) - 1 = 1 from rfl, hρ, obS1_sub_coeff_one (k := k) (α := α) ρ,
        obS1_coeff_one (k := k) (α := α)] at hs2
      have hK1' : (Hp 1).coeff 1 ∈ K := by
        have h := hK1
        norm_num at h
        exact h
      have hm1 : (Hp 1).coeff 1 + 1 ∈ K :=
        Subalgebra.add_mem _ hK1' (Subalgebra.one_mem _)
      exact ⟨by rw [hlead1]; exact hγ _,
        by rw [hs1]; exact hval _ _ _ _ hm1 hK2,
        by rw [hlead2]; exact hγ _,
        by rw [hs2]; exact hval _ _ _ _ hm1 hKt2⟩
    · -- odd main, l ≥ 3
      obtain ⟨hi1, hi2⟩ := Rk2l_deg_odd (α := α) hk3 hpar hl3 hHp hHt hdHt
      obtain ⟨⟨-, -, hs1⟩, ⟨-, -, hs2⟩⟩ := Rpair_odd_top (k := k) (α := α) hHp hl3
        hpar hk3 hHt hdHt hi1 hi2
      rw [tS1_coeff_top (k := k) (α := α) hHp (by omega)] at hs1
      rw [tS1t_coeff_top (k := k) (α := α) (by omega)] at hs2
      have hm1 : (Hp (l - 1)).coeff (2 ^ (l - 1) - 1) + 1 ∈ K :=
        Subalgebra.add_mem _ hK1 (Subalgebra.one_mem _)
      exact ⟨by rw [hlead1]; exact hγ _,
        by rw [hs1]; exact hval _ _ _ _ hm1 hK2,
        by rw [hlead2]; exact hγ _,
        by rw [hs2]; exact hval _ _ _ _ hK1 hKt2⟩


/-- `Rk2l_top_two`, extended to `k ≥ 1`: at `k = 1` the remainder pair vanishes and
all four boundary coefficients are trivially known. -/
theorem Rk2l_top_two' (hk : 1 ≤ k) (hl : 2 ≤ l)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l)
    (hsd : l = 2 → ¬ k % 2 = 0 → 3 ≤ k → ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hK1 : (Hp (l - 1)).coeff (2 ^ (l - 1) - 1) ∈ K)
    (hK2 : (Hp l).coeff (2 ^ l - 1) ∈ K)
    (hKt2 : Ht.coeff (2 ^ l - 1) ∈ K) :
    (Rpair Hp Ht k l α).1.coeff ((k - 1) * 2 ^ l) ∈ K ∧
    (Rpair Hp Ht k l α).1.coeff ((k - 1) * 2 ^ l - 1) ∈ K ∧
    (Rpair Hp Ht k l α).2.coeff ((k - 1) * 2 ^ l) ∈ K ∧
    (Rpair Hp Ht k l α).2.coeff ((k - 1) * 2 ^ l - 1) ∈ K := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hkeq : k = 1 := by omega
    subst hkeq
    rw [Rpair_one]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      first
      | (rw [show ((0, 0) : A[X] × A[X]).1 = 0 from rfl, coeff_zero]
         exact Subalgebra.zero_mem _)
      | (rw [show ((0, 0) : A[X] × A[X]).2 = 0 from rfl, coeff_zero]
         exact Subalgebra.zero_mem _)
  · exact Rk2l_top_two hk2 hl hHp hHt hdHt hsd hK1 hK2 hKt2


section updateMem

/-- The odd tower update's coefficients lie in the band-augmented context. -/
theorem oddH_coeff_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R)) :
    ∀ j, (oddH Hp k l α).coeff j ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
      Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)) := by
  obtain ⟨htS1V, htS1tV, hmersV, hoG1V, hoG2V⟩ := odd_windows (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  intro j
  rw [oddH_eq_sq_add, coeff_add]
  refine Subalgebra.add_mem _ ?_ (hoG1V ((k - 2) * 2 ^ l) j (by omega))
  refine coeff_mem_pow ?_ 2 j
  intro a
  have hlo : (k - 2) * 2 ^ l ≤ (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + a :=
    (Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  rw [coeff_add]
  exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hMK a))
    (htS1V ((k - 2) * 2 ^ l) a hlo)

/-- The odd companion update's coefficients lie in the band-augmented context. -/
theorem oddHt_coeff_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) (hl : ¬ l ≤ 2) (h2 : IsUnit (2 : R)) :
    ∀ j, (oddHt Hp Ht k l α).coeff j ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
      Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)) := by
  obtain ⟨htS1V, htS1tV, hmersV, hoG1V, hoG2V⟩ := odd_windows (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  intro j
  rw [oddHt_eq_sq_add, coeff_add]
  refine Subalgebra.add_mem _ ?_ (hoG2V ((k - 2) * 2 ^ l) j (by omega))
  refine coeff_mem_pow ?_ 2 j
  intro a
  have hlo : (k - 2) * 2 ^ l ≤ (k - 2) * 2 ^ l + 2 ^ (l - 1) :=
    Nat.le_add_right _ _
  rw [coeff_add]
  exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hKt a))
    (htS1tV ((k - 2) * 2 ^ l) hlo a)

/-- The even tower update's coefficients lie in the band-augmented context. -/
theorem evenH_coeff_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : k % 2 = 0) (hk : 4 ≤ k) (hl : 2 ≤ l) (h2 : IsUnit (2 : R)) :
    ∀ j, (evenH Hp k l α).coeff j ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
      Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)) := by
  obtain ⟨heE1V, heE2V⟩ := eE_window (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  obtain ⟨hMm, hMd, hMK⟩ := hHp l (by omega) le_rfl
  intro j
  rw [evenH_eq_sq_add, coeff_add]
  refine Subalgebra.add_mem _ ?_ (heE1V ((k - 2) * 2 ^ l) j (by omega))
  exact coeff_mem_pow (fun a => (le_sup_left : K ≤ _) (hMK a)) 2 j

/-- The even companion update's coefficients lie in the band-augmented context. -/
theorem evenHt_coeff_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hKt : ∀ j, Ht.coeff j ∈ K)
    (hpar : k % 2 = 0) (hk : 4 ≤ k) (hl : 2 ≤ l) (h2 : IsUnit (2 : R)) :
    ∀ j, (evenHt Hp Ht k l α).coeff j ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
      Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)) := by
  obtain ⟨heE1V, heE2V⟩ := eE_window (α := α)
    (fun i h1 h2 => hHp i h1 (by omega)) hpar hk hl h2
  intro j
  rw [evenHt_eq_sq_add, coeff_add]
  refine Subalgebra.add_mem _ ?_ (heE2V ((k - 2) * 2 ^ l) j (by omega))
  exact coeff_mem_pow (fun a => (le_sup_left : K ≤ _) (hKt a)) 2 j

/-- The base octic core's coefficients lie in the band-augmented context. -/
theorem obH8_coeff_mem
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hpar : ¬ k % 2 = 0) (hk : 3 ≤ k) :
    ∀ j, (obH8 Hp k α).coeff j ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
      Set.Ico (4 * (k - 2)) (4 * (k - 1))) := by
  obtain ⟨hobS1V, hobGVi, hQ₃V⟩ := ob_windows (α := α) hHp hpar hk
  obtain ⟨h2m, h2d, h2K⟩ := hHp 2 (by omega) (by omega)
  intro j
  rw [obH8_eq_sq_add, coeff_add]
  refine Subalgebra.add_mem _ ?_ (hobGVi (4 * (k - 2)) j (by omega))
  refine coeff_mem_pow ?_ 2 j
  intro a
  rw [coeff_add]
  exact Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (h2K a))
    (hobS1V (4 * (k - 2)) a (by omega))

end updateMem

/-- Membership-aware form of `good_update`: the updated tower is good and all its
coefficients lie in `V`, given the base tower's coefficients in `K ≤ V` and the new
top element's coefficients in `V`. -/
theorem good_update_mem {V : Subalgebra R A} {m : ℕ} {H' : A[X]}
    (hHp : ∀ i, 1 ≤ i → i ≤ m → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hH' : H'.Monic) (hd' : H'.natDegree = 2 ^ (m + 1))
    (hKV : K ≤ V) (hnew : ∀ j, H'.coeff j ∈ V) :
    ∀ i, 1 ≤ i → i ≤ m + 1 →
      ((Function.update Hp (m + 1) H') i).Monic ∧
      ((Function.update Hp (m + 1) H') i).natDegree = 2 ^ i ∧
      (∀ j, ((Function.update Hp (m + 1) H') i).coeff j ∈ V) := by
  intro i h1 hi
  rcases eq_or_ne i (m + 1) with rfl | hne
  · have hupd : Function.update Hp (m + 1) H' (m + 1) = H' := by
      rw [update_last]
    rw [hupd]
    exact ⟨hH', hd', hnew⟩
  · have hupd : Function.update Hp (m + 1) H' i = Hp i := by
      rw [update_ne _ hne]
    rw [hupd]
    obtain ⟨hm', hd'', hK'⟩ := hHp i h1 (by omega)
    exact ⟨hm', hd'', fun j => hKV (hK' j)⟩


/-- **`lem:Rk2l`(3), master form**: the remainder pair of `T_{k,2^l}` is
unit-slope triangular over the slot map `rSlot k l`, relative to any known context
containing the tower coefficients.  Strong induction on `k` through the three branch
certificates. -/
theorem Rk2l_triangular : ∀ k, 1 ≤ k →
    ∀ (l : ℕ) (Hp : ℕ → A[X]) (Ht : A[X]) (α : ℕ → A) (K : Subalgebra R A), 2 ≤ l →
    (∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K)) →
    Ht.Monic → Ht.natDegree = 2 ^ l → (∀ j, Ht.coeff j ∈ K) →
    (l = 2 → ¬ k % 2 = 0 → 3 ≤ k → ∃ ρ : A, Ht - Hp 2 = C ρ) →
    (∀ n : ℕ, 1 ≤ n → n ≤ k → IsUnit (((n : ℕ) : ℤ) : R)) →
    CoeffTriangular K (rSlot k l α) (fun j => ((tLam k l j : ℤ) : R))
      ((k - 1) * 2 ^ l) (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk l Hp Ht α K hl htower hHt hdHt hKt hsd hadm
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · -- `k = 1`: the remainder pair vanishes
      have hkeq : k = 1 := by omega
      subst hkeq
      have hT : Tpair Hp Ht 1 l α = (Hp l, Ht) := by
        show TF 1 1 l Hp Ht α = _
        exact TF_succ_le_one (by omega)
      have hR1 : (Rpair Hp Ht 1 l α).1 = 0 := by
        show (Tpair Hp Ht 1 l α).1 - Hp l ^ 1 = 0
        rw [hT, pow_one]
        simp
      have hR2 : (Rpair Hp Ht 1 l α).2 = 0 := by
        show (Tpair Hp Ht 1 l α).2 - Ht ^ 1 = 0
        rw [hT, pow_one]
        simp
      exact
        { unit := fun j hj => absurd hj (by omega)
          supp₁ := fun j => by
            rw [hR1, coeff_zero]
            exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
          supp₂ := fun j => by
            rw [hR2, coeff_zero]
            exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
          pivot := fun j hj => absurd hj (by omega) }
    · have h2 : IsUnit (2 : R) := isUnit_two_of_cast hadm hk2
      have htower2 : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i :=
        fun i h1 h2' => ⟨(htower i h1 h2').1, (htower i h1 h2').2.1⟩
      rcases eq_or_lt_of_le hk2 with hk2eq | hk3
      · -- `k = 2`: the explicit base certificate
        subst hk2eq
        rw [show (2 - 1) * 2 ^ l = 2 ^ l from by norm_num]
        exact Rk2l_tri_base (Ht := Ht) (α := α)
          (fun i h1 h2' => htower i h1 (by omega)) hl h2
      · rcases eq_or_ne (k % 2) 0 with hpar | hpar
        · -- even branch, `k ≥ 4`
          have hk4 : 4 ≤ k := by omega
          obtain ⟨hHm', hHd'⟩ := evenH_good (k := k) (α := α) htower2 hl
          obtain ⟨hTm', hTd'⟩ := evenHt_good (k := k) (α := α) htower2 hl hHt hdHt
          have hgood' := good_update (m := l) (H' := evenH Hp k l α) htower2 hHm' hHd'
          have htower' : ∀ i, 1 ≤ i → i ≤ l + 1 →
              ((Function.update Hp (l + 1) (evenH Hp k l α)) i).Monic ∧
              ((Function.update Hp (l + 1) (evenH Hp k l α)) i).natDegree = 2 ^ i ∧
              (∀ j, ((Function.update Hp (l + 1) (evenH Hp k l α)) i).coeff j
                ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
                    Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l))) :=
            good_update_mem (m := l) (H' := evenH Hp k l α) htower hHm' hHd'
              le_sup_left (evenH_coeff_mem (α := α) htower hpar hk4 hl h2)
          have hKt' : ∀ j, (evenHt Hp Ht k l α).coeff j
              ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
                  Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)) :=
            evenHt_coeff_mem (α := α) htower hKt hpar hk4 hl h2
          have hin0 := ih (k / 2) (by omega) (by omega) (l + 1)
            (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α) α
            (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
              Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
            (by omega) htower' hTm' hTd' hKt'
            (fun h32 => absurd h32 (by omega))
            (fun n h1 h2' => hadm n h1 (by omega))
          have hconv : (k / 2 - 1) * 2 ^ (l + 1) = (k - 2) * 2 ^ l :=
            even_band_conv hpar (by omega)
          rw [hconv] at hin0
          obtain ⟨hind₁, hind₂⟩ := Rk2l_deg (k / 2) (by omega) (l + 1)
            (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α) α
            (by omega) hgood' hTm' hTd' (fun h32 => absurd h32 (by omega))
          rw [hconv] at hind₁ hind₂
          -- boundary coefficients of the inner pair are fully known
          have hupdl : Function.update Hp (l + 1) (evenH Hp k l α) (l + 1 - 1)
              = Hp l := by
            have hne : l + 1 - 1 ≠ l + 1 := by omega
            have h : Function.update Hp (l + 1) (evenH Hp k l α) (l + 1 - 1)
                = Hp (l + 1 - 1) := by
              rw [update_ne _ hne]
            rw [h, show l + 1 - 1 = l from by omega]
          have hupdt : Function.update Hp (l + 1) (evenH Hp k l α) (l + 1)
              = evenH Hp k l α := by
            rw [update_last]
          obtain ⟨htop₁₁, htop₁₂, htop₂₁, -⟩ := Rk2l_top_two (K := K)
            (α := α) (by omega : 2 ≤ k / 2) (by omega : 2 ≤ l + 1) hgood' hTm' hTd'
            (fun h32 => absurd h32 (by omega))
            (by
              rw [hupdl, show 2 ^ (l + 1 - 1) - 1 = 2 ^ l - 1 from by
                rw [show l + 1 - 1 = l from by omega]]
              exact (htower l (by omega) le_rfl).2.2 _)
            (by
              rw [hupdt]
              exact evenH_sublead_mem (α := α) htower2 hl
                ((htower l (by omega) le_rfl).2.2 _))
            (evenHt_sublead_mem (α := α) htower2 hl hHt hdHt (hKt _))
          rw [hconv] at htop₁₁ htop₁₂ htop₂₁
          have hu2 : IsUnit (((k / 2 : ℕ) : ℤ) : R) := hadm (k / 2) (by omega) (by omega)
          have huk : IsUnit (((k : ℕ) : ℤ) : R) := hadm k (by omega) le_rfl
          exact Rk2l_tri_even_step htower hHt hdHt hKt hpar hk4 hl h2 hu2 huk
            hin0 hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁
        · have hk3' : 3 ≤ k := by omega
          have hum : IsUnit ((((k - 1) / 2 : ℕ) : ℤ) : R) :=
            hadm ((k - 1) / 2) (by omega) (by omega)
          have huk : IsUnit (((k : ℕ) : ℤ) : R) := hadm k (by omega) le_rfl
          have huk1 : IsUnit (((k - 1 : ℕ) : ℤ) : R) := hadm (k - 1) (by omega) (by omega)
          rcases Nat.lt_or_ge l 3 with hlb | hl3
          · -- shared odd base, `l = 2`
            have hleq : l = 2 := by omega
            subst hleq
            obtain ⟨h8m, h8d⟩ := obH8_good (k := k) (α := α)
              (htower2 1 (by omega) (by omega)) (htower2 2 (by omega) le_rfl)
            have hgood3 := good_update (m := 2) (H' := obH8 Hp k α) htower2 h8m h8d
            obtain ⟨ht8m, ht8d⟩ := monic_add_low (e := C (α (4 * (k - 2)))) h8m
              (Or.inr (by rw [natDegree_C, h8d]; norm_num))
            have hobtK : ∀ j, (obH8 Hp k α + C (α (4 * (k - 2)))).coeff j
                ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
                    Set.Ico (4 * (k - 2)) (4 * (k - 1))) := by
              intro j
              rw [coeff_add]
              refine Subalgebra.add_mem _
                (obH8_coeff_mem (α := α) htower hpar hk3' j) ?_
              rw [coeff_C]
              split
              · exact (le_sup_right : adjoin R _ ≤ _)
                  (subset_adjoin ⟨4 * (k - 2), ⟨le_rfl, by omega⟩,
                    rSlot_ob_band hpar hk3' le_rfl⟩)
              · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
            have htower' : ∀ i, 1 ≤ i → i ≤ 3 →
                ((Function.update Hp 3 (obH8 Hp k α)) i).Monic ∧
                ((Function.update Hp 3 (obH8 Hp k α)) i).natDegree = 2 ^ i ∧
                (∀ j, ((Function.update Hp 3 (obH8 Hp k α)) i).coeff j
                  ∈ K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
                      Set.Ico (4 * (k - 2)) (4 * (k - 1)))) :=
              good_update_mem (m := 2) (H' := obH8 Hp k α) htower h8m h8d
                le_sup_left (obH8_coeff_mem (α := α) htower hpar hk3')
            have hin0 := ih ((k - 1) / 2) (by omega) (by omega) 3
              (Function.update Hp 3 (obH8 Hp k α))
              (obH8 Hp k α + C (α (4 * (k - 2)))) (fun j => α (4 + j))
              (K ⊔ adjoin R ((rSlot k 2 α (A := A)) ''
                Set.Ico (4 * (k - 2)) (4 * (k - 1))))
              (by omega) htower' ht8m (ht8d.trans h8d) hobtK
              (fun h32 => absurd h32 (by omega))
              (fun n h1 h2' => hadm n h1 (by omega))
            have hconv : ((k - 1) / 2 - 1) * 2 ^ 3 = 4 * (k - 3) :=
              odd_band_conv_base' hpar (by omega)
            rw [hconv] at hin0
            obtain ⟨hind₁, hind₂⟩ := Rk2l_deg ((k - 1) / 2) (by omega) 3
              (Function.update Hp 3 (obH8 Hp k α))
              (obH8 Hp k α + C (α (4 * (k - 2)))) (fun j => α (4 + j))
              (by omega) hgood3 ht8m (ht8d.trans h8d)
              (fun h32 => absurd h32 (by omega))
            rw [hconv] at hind₁ hind₂
            have hupdl : Function.update Hp 3 (obH8 Hp k α) (3 - 1) = Hp 2 := by
              have hne : (3 : ℕ) - 1 ≠ 3 := by omega
              have h : Function.update Hp 3 (obH8 Hp k α) (3 - 1) = Hp (3 - 1) := by
                rw [update_ne _ hne]
              rw [h, show (3 : ℕ) - 1 = 2 from by omega]
            have hupdt : Function.update Hp 3 (obH8 Hp k α) 3 = obH8 Hp k α := by
              rw [update_last]
            have htopP : (Rpair (Function.update Hp 3 (obH8 Hp k α))
                  (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
                  (fun j => α (4 + j))).1.coeff (4 * (k - 3)) ∈ K
                ∧ (Rpair (Function.update Hp 3 (obH8 Hp k α))
                  (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
                  (fun j => α (4 + j))).1.coeff (4 * (k - 3) - 1) ∈ K
                ∧ (Rpair (Function.update Hp 3 (obH8 Hp k α))
                  (obH8 Hp k α + C (α (4 * (k - 2)))) ((k - 1) / 2) 3
                  (fun j => α (4 + j))).2.coeff (4 * (k - 3)) ∈ K := by
              obtain ⟨h1', h2'', h3', -⟩ := Rk2l_top_two' (K := K)
                (α := fun j => α (4 + j)) (by omega : 1 ≤ (k - 1) / 2)
                (by omega : 2 ≤ 3) hgood3 ht8m (ht8d.trans h8d)
                (fun h32 => absurd h32 (by omega))
                (by
                  rw [hupdl]
                  exact (htower 2 (by omega) le_rfl).2.2 _)
                (by
                  rw [hupdt, show 2 ^ 3 - 1 = 7 from by norm_num]
                  exact obH8_sublead_mem (α := α) (htower2 1 (by omega) (by omega))
                    (htower2 2 (by omega) le_rfl)
                    ((htower 2 (by omega) le_rfl).2.2 3))
                (by
                  rw [show 2 ^ 3 - 1 = 7 from by norm_num, coeff_add,
                    show (C (α (4 * (k - 2))) : A[X]).coeff 7 = 0 from by
                      rw [coeff_C, if_neg (by omega)]]
                  refine Subalgebra.add_mem _ ?_ (Subalgebra.zero_mem _)
                  exact obH8_sublead_mem (α := α) (htower2 1 (by omega) (by omega))
                    (htower2 2 (by omega) le_rfl)
                    ((htower 2 (by omega) le_rfl).2.2 3))
              rw [hconv] at h1' h2'' h3'
              exact ⟨h1', h2'', h3'⟩
            obtain ⟨htop₁₁, htop₁₂, htop₂₁⟩ := htopP
            obtain ⟨ρ, hρ⟩ := hsd rfl hpar hk3'
            rw [show (k - 1) * 2 ^ 2 = 4 * (k - 1) from by ring]
            exact Rk2l_tri_oddbase_step htower hHt
              (by rw [hdHt]; norm_num) hKt ⟨ρ, hρ⟩ hpar hk3' h2 hum huk huk1
              hin0 hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁
          · -- odd main branch, `l ≥ 3`
            have hlne : ¬ l ≤ 2 := by omega
            obtain ⟨hHm', hHd'⟩ := oddH_good (k := k) (α := α) htower2 hl3
            obtain ⟨hTm', hTd'⟩ := oddHt_good (k := k) (α := α) htower2 hl3 hHt hdHt
            have hgood' := good_update (m := l) (H' := oddH Hp k l α) htower2 hHm' hHd'
            have htower' : ∀ i, 1 ≤ i → i ≤ l + 1 →
                ((Function.update Hp (l + 1) (oddH Hp k l α)) i).Monic ∧
                ((Function.update Hp (l + 1) (oddH Hp k l α)) i).natDegree = 2 ^ i ∧
                (∀ j, ((Function.update Hp (l + 1) (oddH Hp k l α)) i).coeff j
                  ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
                      Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l))) :=
              good_update_mem (m := l) (H' := oddH Hp k l α) htower hHm' hHd'
                le_sup_left (oddH_coeff_mem (α := α) htower hpar hk3' hlne h2)
            have hKt' : ∀ j, (oddHt Hp Ht k l α).coeff j
                ∈ K ⊔ adjoin R ((rSlot k l α (A := A)) ''
                    Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)) :=
              oddHt_coeff_mem (α := α) htower hKt hpar hk3' hlne h2
            have hin0 := ih ((k - 1) / 2) (by omega) (by omega) (l + 1)
              (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
              (fun j => α (2 ^ l + j))
              (K ⊔ adjoin R ((rSlot k l α (A := A)) ''
                Set.Ico ((k - 2) * 2 ^ l) ((k - 1) * 2 ^ l)))
              (by omega) htower' hTm' hTd' hKt'
              (fun h32 => absurd h32 (by omega))
              (fun n h1 h2' => hadm n h1 (by omega))
            have hconv : ((k - 1) / 2 - 1) * 2 ^ (l + 1) = (k - 3) * 2 ^ l :=
              odd_band_conv hpar (by omega)
            rw [hconv] at hin0
            obtain ⟨hind₁, hind₂⟩ := Rk2l_deg ((k - 1) / 2) (by omega) (l + 1)
              (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
              (fun j => α (2 ^ l + j)) (by omega) hgood' hTm' hTd'
              (fun h32 => absurd h32 (by omega))
            rw [hconv] at hind₁ hind₂
            have hupdl : Function.update Hp (l + 1) (oddH Hp k l α) (l + 1 - 1)
                = Hp l := by
              have hne : l + 1 - 1 ≠ l + 1 := by omega
              have h : Function.update Hp (l + 1) (oddH Hp k l α) (l + 1 - 1)
                  = Hp (l + 1 - 1) := by
                rw [update_ne _ hne]
              rw [h, show l + 1 - 1 = l from by omega]
            have hupdt : Function.update Hp (l + 1) (oddH Hp k l α) (l + 1)
                = oddH Hp k l α := by
              rw [update_last]
            have htopP : (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                  (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                  (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l) ∈ K
                ∧ (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                  (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                  (fun j => α (2 ^ l + j))).1.coeff ((k - 3) * 2 ^ l - 1) ∈ K
                ∧ (Rpair (Function.update Hp (l + 1) (oddH Hp k l α))
                  (oddHt Hp Ht k l α) ((k - 1) / 2) (l + 1)
                  (fun j => α (2 ^ l + j))).2.coeff ((k - 3) * 2 ^ l) ∈ K := by
              obtain ⟨h1', h2'', h3', -⟩ := Rk2l_top_two' (K := K)
                (α := fun j => α (2 ^ l + j)) (by omega : 1 ≤ (k - 1) / 2)
                (by omega : 2 ≤ l + 1) hgood' hTm' hTd'
                (fun h32 => absurd h32 (by omega))
                (by
                  rw [hupdl, show 2 ^ (l + 1 - 1) - 1 = 2 ^ l - 1 from by
                    rw [show l + 1 - 1 = l from by omega]]
                  exact (htower l (by omega) le_rfl).2.2 _)
                (by
                  rw [hupdt]
                  exact oddH_sublead_mem (α := α) htower2 hl3
                    ((htower l (by omega) le_rfl).2.2 _))
                (oddHt_sublead_mem (α := α) htower2 hl3 hHt hdHt (hKt _))
              rw [hconv] at h1' h2'' h3'
              exact ⟨h1', h2'', h3'⟩
            obtain ⟨htop₁₁, htop₁₂, htop₂₁⟩ := htopP
            exact Rk2l_tri_odd_step htower hHt hdHt hKt hpar hk3' hlne h2 hum
              huk huk1 hin0 hind₁ hind₂ htop₁₁ htop₁₂ htop₂₁

end FastPoly
