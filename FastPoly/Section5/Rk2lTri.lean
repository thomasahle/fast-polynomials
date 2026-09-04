import FastPoly.Section5.CertEngines
import FastPoly.Section5.RSlots
import FastPoly.Section5.Slopes
import FastPoly.Section5.Rk2lEven
import FastPoly.Section5.Rk2lOdd

/-!
# `lem:Rk2l`(3): the stage-table certificates

Per-branch `CoeffTriangular` certificates for `Rpair` over `rSlot` with slopes `tLam`.
This file: the `k = 2` base.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {Hp : ℕ → A[X]} {Ht : A[X]} {l : ℕ} {α : ℕ → A}

omit [Nontrivial A] in
/-- The `k = 2` remainder pair is exactly the first-order correction pair. -/
theorem Rpair_two (hl : ¬ l ≤ 1) :
    Rpair Hp Ht 2 l α = (eE1 Hp 2 l α, eE2 Hp 2 l α) := by
  have hT : Tpair Hp Ht 2 l α = (evenH Hp 2 l α, evenHt Hp Ht 2 l α) := by
    show TF 2 2 l Hp Ht α = _
    rw [TF_succ, if_neg (by omega), if_pos (by omega), if_neg hl,
      TF_succ, if_pos (by omega)]
    have hupd : Function.update Hp (l + 1) (evenH Hp 2 l α) (l + 1)
        = evenH Hp 2 l α := by
      rw [update_last]
    rw [hupd]
  show ((Tpair Hp Ht 2 l α).1 - Hp l ^ 2, (Tpair Hp Ht 2 l α).2 - Ht ^ 2) = _
  rw [hT]
  refine Prod.ext ?_ ?_
  · show evenH Hp 2 l α - Hp l ^ 2 = eE1 Hp 2 l α
    rw [evenH_eq_sq_add]
    ring
  · show evenHt Hp Ht 2 l α - Ht ^ 2 = eE2 Hp 2 l α
    rw [evenHt_eq_sq_add]
    ring

section values

omit [Nontrivial A] in
/-- `tLam` at `k = 2`: slope 1 on the lower half, `-2` above. -/
theorem tLam_two_lo {j : ℕ} (hj : j < 2 ^ (l - 1)) : tLam 2 l j = 1 := by
  show tLamF 2 2 l j = 1
  rw [tLamF_succ, if_neg (by omega), if_pos (by omega), if_neg (by omega),
    if_pos (by omega)]
  norm_num

omit [Nontrivial A] in
theorem tLam_two_hi {j : ℕ} (hj : 2 ^ (l - 1) ≤ j) : tLam 2 l j = -2 := by
  show tLamF 2 2 l j = -2
  rw [tLamF_succ, if_neg (by omega), if_pos (by omega), if_neg (by omega),
    if_neg (by omega)]
  norm_num

omit [Nontrivial A] in
/-- `rSlot` at `k = 2`: the four bands. -/
theorem rSlot_two_zero : rSlot (A := A) 2 l α 0 = α 0 := by
  show rSlotF 2 2 l α 0 = α 0
  unfold rSlotF
  rw [if_neg (by omega), if_pos rfl, if_pos rfl]

omit [Nontrivial A] in
theorem rSlot_two_eS2 {r : ℕ} (h1 : 1 ≤ r) (h2 : r < 2 ^ (l - 1)) :
    rSlot (A := A) 2 l α r = peelSlot (l - 1) (fun j => α (1 + j)) (r - 1) := by
  show rSlotF 2 2 l α r = _
  unfold rSlotF
  rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos h2]

omit [Nontrivial A] in
theorem rSlot_two_delta : rSlot (A := A) 2 l α (2 ^ (l - 1)) = α (2 ^ (l - 1)) := by
  show rSlotF 2 2 l α (2 ^ (l - 1)) = _
  unfold rSlotF
  have h1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega), if_pos rfl]

omit [Nontrivial A] in
theorem rSlot_two_tS1 {r : ℕ} (h1 : 2 ^ (l - 1) < r) :
    rSlot (A := A) 2 l α r
      = peelSlot (l - 1) (fun j => α (2 ^ (l - 1) + 1 + j)) (r - 2 ^ (l - 1) - 1) := by
  show rSlotF 2 2 l α r = _
  unfold rSlotF
  have hp : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

end values

section blocks

variable (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
    (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l)

omit [Nontrivial A] in
/-- The scalar companion `S⁽²⁾₁ = H_{2^{l-1}} + δ` as a one-row certificate. -/
theorem tS1t_cert (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧
    (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    CoeffTriangular K (fun _ => α (2 ^ (l - 1))) (fun _ => (1 : R)) 1 0
      (tS1t Hp 2 l α - X ^ (2 ^ (l - 1))) := by
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  have hco : ∀ j, (tS1t Hp 2 l α - X ^ (2 ^ (l - 1))).coeff j
      = ((Hp (l - 1)).coeff j - (X ^ (2 ^ (l - 1)) : A[X]).coeff j)
        + (C (α ((2 - 2) * 2 ^ l + 2 ^ (l - 1))) : A[X]).coeff j := by
    intro j
    show (Hp (l - 1) + C (α ((2 - 2) * 2 ^ l + 2 ^ (l - 1))) - X ^ (2 ^ (l - 1))).coeff j = _
    rw [coeff_sub, coeff_add]
    ring
  have hKp : ∀ j, (Hp (l - 1)).coeff j - (X ^ (2 ^ (l - 1)) : A[X]).coeff j ∈ K := by
    intro j
    refine Subalgebra.sub_mem _ (hK j) ?_
    rw [coeff_X_pow]
    split
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  have hidx : (2 - 2) * 2 ^ l + 2 ^ (l - 1) = 2 ^ (l - 1) := by omega
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
      rw [hidx]
      exact (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨0, ⟨le_rfl, by omega⟩, rfl⟩)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro j hj
    match j, hj with
    | 0, _ =>
      refine ⟨(Hp (l - 1)).coeff 0 - (X ^ (2 ^ (l - 1)) : A[X]).coeff 0,
        (le_sup_left : K ≤ _) (hKp 0), ?_⟩
      rw [hcomb0, hco, coeff_C_zero, hidx, map_one, one_mul]
      ring

/-- `S⁽¹⁾₁ = H_{2^{l-1}} + Q`-block certificate over the shifted peel slots. -/
theorem tS1_cert (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧
    (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    CoeffTriangular K
      (peelSlot (l - 1) (fun j => α (2 ^ (l - 1) + 1 + j)))
      (fun _ => (1 : R)) (2 ^ (l - 1) - 1) 0
      (tS1 Hp 2 l α - X ^ (2 ^ (l - 1))) := by
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  have hmers := peel_unitriangular Hp (l - 1)
    (fun i h1 h2 => hHp i h1 (by omega)) (by omega)
    (fun j => α ((2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
  have hidx : ∀ j, (2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j = 2 ^ (l - 1) + 1 + j := by
    intro j; omega
  have hsl : (fun j => α ((2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
      = (fun j => α (2 ^ (l - 1) + 1 + j)) := funext fun j => by rw [hidx]
  rw [hsl] at hmers
  have := add_block_cert (Hh := Hp (l - 1)) (D := 2 ^ (l - 1)) hK hmers
  show CoeffTriangular K _ _ _ 0
    ((Hp (l - 1) + peel Hp (l - 1) (fun j => α ((2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j)))
      - X ^ (2 ^ (l - 1)))
  rw [hsl]
  exact this

/-- `S⁽¹⁾₂ = Q`-block certificate over the shifted peel slots. -/
theorem eS2_cert (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧
    (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    CoeffTriangular K (peelSlot (l - 1) (fun j => α (1 + j)))
      (fun _ => (1 : R)) (2 ^ (l - 1) - 1) 0
      (eS2 Hp 2 l α - X ^ (2 ^ (l - 1) - 1)) := by
  have hmers := peel_unitriangular Hp (l - 1)
    (fun i h1 h2 => hHp i h1 (by omega)) (by omega)
    (fun j => α ((2 - 2) * 2 ^ l + 1 + j))
  have hsl : (fun j => α ((2 - 2) * 2 ^ l + 1 + j)) = (fun j => α (1 + j)) :=
    funext fun j => by
      have : (2 - 2) * 2 ^ l + 1 + j = 1 + j := by omega
      rw [this]
  rw [hsl] at hmers
  show CoeffTriangular K (peelSlot (l - 1) (fun j => α (1 + j))) (fun _ => (1 : R))
    (2 ^ (l - 1) - 1) 0
    (peel Hp (l - 1) (fun j => α ((2 - 2) * 2 ^ l + 1 + j)) - X ^ (2 ^ (l - 1) - 1))
  rw [hsl]
  exact hmers

end blocks

section baseSupports

variable (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
    (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l)

/-- Window toolkit for the `k = 2` base certificate. -/
theorem base_windows (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧
    (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    (∀ lo m, lo ≤ m + 1 →
      (eS2 Hp 2 l α).coeff m ∈ K ⊔ adjoin R ((rSlot 2 l α (A := A)) '' Set.Ico lo (2 ^ l)))
    ∧ (∀ lo m, lo ≤ 2 ^ (l - 1) + 1 + m →
      (tS1 Hp 2 l α).coeff m ∈ K ⊔ adjoin R ((rSlot 2 l α (A := A)) '' Set.Ico lo (2 ^ l)))
    ∧ (∀ lo, lo ≤ 2 ^ (l - 1) →
      (tS1t Hp 2 l α).coeff 0 ∈ K ⊔ adjoin R ((rSlot 2 l α (A := A)) '' Set.Ico lo (2 ^ l)))
    ∧ (∀ m, 1 ≤ m → (tS1t Hp 2 l α).coeff m ∈ K) := by
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp2 : 2 ^ (l - 1) + 2 ^ (l - 1) ≤ 2 ^ l := by
    have : 2 ^ l = 2 ^ (l - 1) * 2 := by
      conv_lhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    omega
  set γ := rSlot 2 l α (A := A) with hγ
  have hslot : ∀ lo t, lo ≤ t → t < 2 ^ l →
      γ t ∈ K ⊔ adjoin R (γ '' Set.Ico lo (2 ^ l)) := fun lo t h1 h2 =>
    (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨h1, h2⟩, rfl⟩)
  have heS2c := eS2_cert (Hp := Hp) (α := α) hHp hl
  have htS1c := tS1_cert (Hp := Hp) (α := α) hHp hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lo m hlo
    have hs : (eS2 Hp 2 l α).coeff m
        = (eS2 Hp 2 l α - X ^ (2 ^ (l - 1) - 1)).coeff m
          + (X ^ (2 ^ (l - 1) - 1) : A[X]).coeff m := by
      rw [coeff_sub]; ring
    rw [hs]
    refine Subalgebra.add_mem _ ?_ ?_
    · have h1 := heS2c.supp₂ m
      refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) h1
      rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hv : γ (g + 1) = peelSlot (l - 1) (fun j => α (1 + j)) g := by
        rw [hγ, rSlot_two_eS2 (by omega) (by omega), Nat.add_sub_cancel]
      exact hv ▸ hslot lo (g + 1) (by omega) (by omega)
    · rw [coeff_X_pow]
      split
      · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro lo m hlo
    have hs : (tS1 Hp 2 l α).coeff m
        = (tS1 Hp 2 l α - X ^ (2 ^ (l - 1))).coeff m
          + (X ^ (2 ^ (l - 1)) : A[X]).coeff m := by
      rw [coeff_sub]; ring
    rw [hs]
    refine Subalgebra.add_mem _ ?_ ?_
    · have h1 := htS1c.supp₂ m
      refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) h1
      rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
      have hv : γ (2 ^ (l - 1) + 1 + g)
          = peelSlot (l - 1) (fun j => α (2 ^ (l - 1) + 1 + j)) g := by
        rw [hγ, rSlot_two_tS1 (by omega),
          show 2 ^ (l - 1) + 1 + g - 2 ^ (l - 1) - 1 = g from by omega]
      exact hv ▸ hslot lo (2 ^ (l - 1) + 1 + g) (by omega) (by omega)
    · rw [coeff_X_pow]
      split
      · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · intro lo hlo
    show (Hp (l - 1) + C (α ((2 - 2) * 2 ^ l + 2 ^ (l - 1)))).coeff 0 ∈ _
    rw [coeff_add, coeff_C_zero, show (2 - 2) * 2 ^ l + 2 ^ (l - 1) = 2 ^ (l - 1) from
      by omega]
    refine Subalgebra.add_mem _ ((le_sup_left : K ≤ _) (hK 0)) ?_
    have hv : γ (2 ^ (l - 1)) = α (2 ^ (l - 1)) := rSlot_two_delta
    exact hv ▸ hslot lo (2 ^ (l - 1)) (by omega) (by omega)
  · intro m hm
    show (Hp (l - 1) + C (α ((2 - 2) * 2 ^ l + 2 ^ (l - 1)))).coeff m ∈ K
    rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
    exact hK m

/-- Supports, first component: `eE1 = eS2 - tS1²`. -/
theorem base_supp₁ (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧
    (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    ∀ j, (eE1 Hp 2 l α).coeff j
      ∈ K ⊔ adjoin R ((rSlot 2 l α (A := A)) '' Set.Ico (j + 1) (2 ^ l)) := by
  obtain ⟨heS2V, htS1V, _, _⟩ := base_windows (Hp := Hp) (α := α) hHp hl
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  obtain ⟨hmers_m, hmers_d⟩ := peel_monic Hp (l - 1)
    (fun i h1 h2 => ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1⟩) (by omega)
    (fun j => α ((2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
  have htS1d : (tS1 Hp 2 l α).natDegree = 2 ^ (l - 1) := by
    show (Hp (l - 1) + peel Hp (l - 1) _).natDegree = 2 ^ (l - 1)
    have hdeg : (peel Hp (l - 1) (fun j => α ((2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))).degree
        < (Hp (l - 1)).degree := by
      rw [degree_eq_natDegree hmers_m.ne_zero, degree_eq_natDegree hm.ne_zero, hd,
        hmers_d]
      exact_mod_cast (by
        have h1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
        omega : 2 ^ (l - 1) - 1 < 2 ^ (l - 1))
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hdeg), hd]
  intro j
  show (eS2 Hp 2 l α - tS1 Hp 2 l α ^ 2).coeff j ∈ _
  rw [coeff_sub, sq, coeff_mul]
  refine Subalgebra.sub_mem _ (heS2V (j + 1) j (by omega))
    (Subalgebra.sum_mem _ fun x hx => ?_)
  have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
  rcases Nat.lt_or_ge (2 ^ (l - 1)) x.1 with hgt1 | hle1
  · rw [show (tS1 Hp 2 l α).coeff x.1 = 0 from
      coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    exact Subalgebra.zero_mem _
  · rcases Nat.lt_or_ge (2 ^ (l - 1)) x.2 with hgt | hle
    · rw [show (tS1 Hp 2 l α).coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact Subalgebra.zero_mem _
    · exact Subalgebra.mul_mem _ (htS1V (j + 1) x.1 (by omega))
        (htS1V (j + 1) x.2 (by omega))
/-- Supports, second component: `eE2 = C σ - tS1t²`. -/
theorem base_supp₂ (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧
    (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    ∀ j, (eE2 Hp 2 l α).coeff j
      ∈ K ⊔ adjoin R ((rSlot 2 l α (A := A)) '' Set.Ico j (2 ^ l)) := by
  obtain ⟨_, _, htS1t0, htS1tK⟩ := base_windows (Hp := Hp) (α := α) hHp hl
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  obtain ⟨htm, htd⟩ := monic_add_C hm (by
    rw [hd]; exact Nat.one_le_pow _ _ (by omega)) (α ((2 - 2) * 2 ^ l + 2 ^ (l - 1)))
  have htS1td : (tS1t Hp 2 l α).natDegree = 2 ^ (l - 1) := by
    show (Hp (l - 1) + C (α ((2 - 2) * 2 ^ l + 2 ^ (l - 1)))).natDegree = _
    rw [htd, hd]
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp2 : 2 ^ (l - 1) + 2 ^ (l - 1) ≤ 2 ^ l := by
    have : 2 ^ l = 2 ^ (l - 1) * 2 := by
      conv_lhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    omega
  intro j
  show (C (α ((2 - 2) * 2 ^ l)) - tS1t Hp 2 l α ^ 2).coeff j ∈ _
  rw [coeff_sub, sq, coeff_mul]
  refine Subalgebra.sub_mem _ ?_ (Subalgebra.sum_mem _ fun x hx => ?_)
  · rw [coeff_C]
    split
    · rename_i hj0
      subst hj0
      rw [show (2 - 2) * 2 ^ l = 0 from by omega]
      have hv : rSlot (A := A) 2 l α 0 = α 0 := rSlot_two_zero
      exact hv ▸ (le_sup_right : adjoin R _ ≤ _)
        (subset_adjoin ⟨0, ⟨le_rfl, by positivity⟩, rfl⟩)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (2 ^ (l - 1)) x.1 with hgt1 | hle1
    · rw [show (tS1t Hp 2 l α).coeff x.1 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge (2 ^ (l - 1)) x.2 with hgt2 | hle2
      · rw [show (tS1t Hp 2 l α).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
        exact Subalgebra.zero_mem _
      · rcases Nat.eq_zero_or_pos x.1 with h10 | h1p
        · rcases Nat.eq_zero_or_pos x.2 with h20 | h2p
          · rw [h10, h20]
            exact Subalgebra.mul_mem _ (htS1t0 j (by omega)) (htS1t0 j (by omega))
          · rw [h10]
            exact Subalgebra.mul_mem _ (htS1t0 j (by omega))
              ((le_sup_left : K ≤ _) (htS1tK x.2 h2p))
        · rcases Nat.eq_zero_or_pos x.2 with h20 | h2p
          · rw [h20]
            exact Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (htS1tK x.1 h1p))
              (htS1t0 j (by omega))
          · exact Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (htS1tK x.1 h1p))
              ((le_sup_left : K ≤ _) (htS1tK x.2 h2p))

/-- Pivots of the `k = 2` base certificate. -/
theorem base_pivot (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧
    (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    ∀ j, j < 2 ^ l → ∃ F ∈ K ⊔ adjoin R
        ((rSlot 2 l α (A := A)) '' Set.Ico (j + 1) (2 ^ l)),
      (combined (eE1 Hp 2 l α) (eE2 Hp 2 l α)).coeff j
        = algebraMap R A (((tLam 2 l j : ℤ) : R)) * (rSlot 2 l α (A := A)) j + F := by
  obtain ⟨heS2V, htS1V, htS1t0, htS1tK⟩ := base_windows (Hp := Hp) (α := α) hHp hl
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp2 : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  have hp2le : 2 ≤ 2 ^ (l - 1) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ 2 from by omega)
      (show 1 ≤ l - 1 from by omega)
    have h2 : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  set γ := rSlot 2 l α (A := A) with hγ
  have hslot : ∀ lo t, lo ≤ t → t < 2 ^ l →
      γ t ∈ K ⊔ adjoin R (γ '' Set.Ico lo (2 ^ l)) := fun lo t h1 h2 =>
    (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨h1, h2⟩, rfl⟩)
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  have heS2c := eS2_cert (Hp := Hp) (α := α) hHp hl
  have htS1c := tS1_cert (Hp := Hp) (α := α) hHp hl
  have htS1tc := tS1t_cert (Hp := Hp) (α := α) hHp hl
  -- monic/degree facts
  obtain ⟨hmers_m, hmers_d⟩ := peel_monic Hp (l - 1)
    (fun i h1 h2 => ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1⟩) (by omega)
    (fun j => α ((2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
  obtain ⟨heS2_m, heS2_d⟩ := peel_monic Hp (l - 1)
    (fun i h1 h2 => ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1⟩) (by omega)
    (fun j => α ((2 - 2) * 2 ^ l + 1 + j))
  have heS2d : (eS2 Hp 2 l α).natDegree = 2 ^ (l - 1) - 1 := heS2_d
  have htS1m : (tS1 Hp 2 l α).Monic := by
    show (Hp (l - 1) + peel Hp (l - 1) _).Monic
    have hdeg : (peel Hp (l - 1)
        (fun j => α ((2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))).degree
        < (Hp (l - 1)).degree := by
      rw [degree_eq_natDegree hmers_m.ne_zero, degree_eq_natDegree hm.ne_zero, hd,
        hmers_d]
      exact_mod_cast (by omega : 2 ^ (l - 1) - 1 < 2 ^ (l - 1))
    exact hm.add_of_left hdeg
  have htS1d : (tS1 Hp 2 l α).natDegree = 2 ^ (l - 1) := by
    show (Hp (l - 1) + peel Hp (l - 1) _).natDegree = 2 ^ (l - 1)
    have hdeg : (peel Hp (l - 1)
        (fun j => α ((2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))).degree
        < (Hp (l - 1)).degree := by
      rw [degree_eq_natDegree hmers_m.ne_zero, degree_eq_natDegree hm.ne_zero, hd,
        hmers_d]
      exact_mod_cast (by omega : 2 ^ (l - 1) - 1 < 2 ^ (l - 1))
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hdeg), hd]
  obtain ⟨htm, htd'⟩ := monic_add_C hm (by rw [hd]; omega)
    (α ((2 - 2) * 2 ^ l + 2 ^ (l - 1)))
  have htS1tm : (tS1t Hp 2 l α).Monic := htm
  have htS1td : (tS1t Hp 2 l α).natDegree = 2 ^ (l - 1) := by
    show (Hp (l - 1) + C _).natDegree = _
    rw [htd', hd]
  -- square-sum memberships
  have hsq₁V : ∀ lo m, lo ≤ m + 2 → m < 2 ^ (l - 1) →
      (tS1 Hp 2 l α ^ 2).coeff m ∈ K ⊔ adjoin R (γ '' Set.Ico lo (2 ^ l)) := by
    intro lo m hlo hmlt
    rw [sq, coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (2 ^ (l - 1)) x.1 with hgt1 | hle1
    · rw [show (tS1 Hp 2 l α).coeff x.1 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge (2 ^ (l - 1)) x.2 with hgt2 | hle2
      · rw [show (tS1 Hp 2 l α).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (htS1V lo x.1 (by omega))
          (htS1V lo x.2 (by omega))
  have hsqtK : ∀ m, 2 ^ (l - 1) < m → (tS1t Hp 2 l α ^ 2).coeff m ∈ K := by
    intro m hgt
    rw [sq, coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (2 ^ (l - 1)) x.1 with hgt1 | hle1
    · rw [show (tS1t Hp 2 l α).coeff x.1 = 0 from
        coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge (2 ^ (l - 1)) x.2 with hgt2 | hle2
      · rw [show (tS1t Hp 2 l α).coeff x.2 = 0 from
          coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
        exact Subalgebra.zero_mem _
      · have h11 : 1 ≤ x.1 := by omega
        have h21 : 1 ≤ x.2 := by omega
        exact Subalgebra.mul_mem _ (htS1tK x.1 h11) (htS1tK x.2 h21)
  have hsqt2V : ∀ lo m, lo ≤ 2 ^ (l - 1) →
      (tS1t Hp 2 l α ^ 2).coeff m ∈ K ⊔ adjoin R (γ '' Set.Ico lo (2 ^ l)) := by
    intro lo m hlo
    rw [sq, coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.eq_zero_or_pos x.1 with h10 | h1p
    · rcases Nat.eq_zero_or_pos x.2 with h20 | h2p
      · rw [h10, h20]
        exact Subalgebra.mul_mem _ (htS1t0 lo hlo) (htS1t0 lo hlo)
      · rw [h10]
        exact Subalgebra.mul_mem _ (htS1t0 lo hlo)
          ((le_sup_left : K ≤ _) (htS1tK x.2 h2p))
    · rcases Nat.eq_zero_or_pos x.2 with h20 | h2p
      · rw [h20]
        exact Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (htS1tK x.1 h1p))
          (htS1t0 lo hlo)
      · exact Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (htS1tK x.1 h1p))
          ((le_sup_left : K ≤ _) (htS1tK x.2 h2p))
  have hcast1 : algebraMap R A (((1 : ℤ) : R)) = 1 := by
    rw [Int.cast_one, map_one]
  have hcast2 : algebraMap R A (((-2 : ℤ) : R)) = -2 := by
    rw [show (((-2 : ℤ) : R)) = -(2 : R) from by push_cast; ring, map_neg, map_ofNat]
  intro j hj
  cases j with
  | zero =>
    rw [tLam_two_lo (by omega)]
    refine ⟨-(tS1t Hp 2 l α ^ 2).coeff 0, ?_, ?_⟩
    · exact Subalgebra.neg_mem _ (hsqt2V 1 0 (by omega))
    · rw [coeff_combined_zero, hcast1, one_mul, hγ, rSlot_two_zero]
      show (C (α ((2 - 2) * 2 ^ l)) - tS1t Hp 2 l α ^ 2).coeff 0 = _
      rw [coeff_sub, coeff_C_zero, show (2 - 2) * 2 ^ l = 0 from by omega]
      ring
  | succ t =>
    have hcO : (combined (eE1 Hp 2 l α) (eE2 Hp 2 l α)).coeff (t + 1)
        = (eE1 Hp 2 l α).coeff t + (eE2 Hp 2 l α).coeff (t + 1) := coeff_combined _ _ t
    have heE1 : (eE1 Hp 2 l α).coeff t
        = (eS2 Hp 2 l α).coeff t - (tS1 Hp 2 l α ^ 2).coeff t := by
      show (eS2 Hp 2 l α - tS1 Hp 2 l α ^ 2).coeff t = _
      rw [coeff_sub]
    have heE2 : (eE2 Hp 2 l α).coeff (t + 1)
        = - (tS1t Hp 2 l α ^ 2).coeff (t + 1) := by
      show (C (α ((2 - 2) * 2 ^ l)) - tS1t Hp 2 l α ^ 2).coeff (t + 1) = _
      rw [coeff_sub, coeff_C, if_neg (by omega)]
      ring
    rcases Nat.lt_or_ge (t + 1) (2 ^ (l - 1)) with hband | hband
    · -- eS2 band, slope 1
      obtain ⟨F', hF', hFe⟩ := heS2c.pivot t (by omega)
      rw [hcomb0] at hFe
      have heS2t : (eS2 Hp 2 l α).coeff t
          = peelSlot (l - 1) (fun j => α (1 + j)) t + F' := by
        have hX : ((X : A[X]) ^ (2 ^ (l - 1) - 1)).coeff t = 0 := by
          rw [coeff_X_pow, if_neg (by omega)]
        have := hFe
        rw [coeff_sub, hX, sub_zero, map_one, one_mul] at this
        exact this
      have hF'V : F' ∈ K ⊔ adjoin R (γ '' Set.Ico (t + 2) (2 ^ l)) := by
        refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF'
        rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
        have hv : γ (g + 1) = peelSlot (l - 1) (fun j => α (1 + j)) g := by
          rw [hγ, rSlot_two_eS2 (by omega) (by omega), Nat.add_sub_cancel]
        exact hv ▸ hslot (t + 2) (g + 1) (by omega) (by omega)
      refine ⟨F' - (tS1 Hp 2 l α ^ 2).coeff t - (tS1t Hp 2 l α ^ 2).coeff (t + 1),
        ?_, ?_⟩
      · exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hF'V
          (hsq₁V (t + 2) t (by omega) (by omega))) (hsqt2V (t + 2) (t + 1) (by omega))
      · rw [hcO, heE1, heE2, heS2t, tLam_two_lo (by omega), hcast1, one_mul, hγ,
          rSlot_two_eS2 (by omega) (by omega), Nat.add_sub_cancel]
        ring
    · rcases Nat.eq_or_lt_of_le hband with heq | hlt
      · -- δ row, slope -2
        obtain ⟨F₂, hF₂, hFe₂⟩ := sq_cert_pivot htS1tm htS1td htS1tc (by omega)
          (show 0 < 1 from by omega)
        have hF₂K : F₂ ∈ K := by
          refine mem_of_sup_adjoin_empty ?_ hF₂
          rw [Set.image_eq_empty]
          exact Set.Ico_eq_empty (by omega)
        have heS2K : (eS2 Hp 2 l α).coeff t ∈ K := by
          have h1 := cert_high_mem₂ heS2c (show 2 ^ (l - 1) - 1 ≤ t from by omega)
          have hs : (eS2 Hp 2 l α).coeff t
              = (eS2 Hp 2 l α - X ^ (2 ^ (l - 1) - 1)).coeff t
                + (X ^ (2 ^ (l - 1) - 1) : A[X]).coeff t := by
            rw [coeff_sub]; ring
          rw [hs]
          refine Subalgebra.add_mem _ h1 ?_
          rw [coeff_X_pow]
          split
          · exact Subalgebra.one_mem _
          · exact Subalgebra.zero_mem _
        refine ⟨(eS2 Hp 2 l α).coeff t - (tS1 Hp 2 l α ^ 2).coeff t - F₂, ?_, ?_⟩
        · exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _
            ((le_sup_left : K ≤ _) heS2K) (hsq₁V (t + 2) t (by omega) (by omega)))
            ((le_sup_left : K ≤ _) hF₂K)
        · have hidx : 2 ^ (l - 1) + 0 = t + 1 := by omega
          rw [hidx] at hFe₂
          rw [hcO, heE1, heE2, hFe₂, tLam_two_hi (by omega), hcast2, hγ,
            show t + 1 = 2 ^ (l - 1) from by omega, rSlot_two_delta]
          ring
      · -- tS1 band, slope -2
        have hr3 : t - 2 ^ (l - 1) < 2 ^ (l - 1) - 1 := by omega
        have heD3 : (2 ^ (l - 1) - 1) + 1 ≤ 2 ^ (l - 1) := by omega
        obtain ⟨F₃, hF₃, hFe₃⟩ := sq_cert_pivot htS1m htS1d htS1c heD3 hr3
        have hF₃V : F₃ ∈ K ⊔ adjoin R (γ '' Set.Ico (t + 2) (2 ^ l)) := by
          refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF₃
          rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
          have hv : γ (2 ^ (l - 1) + 1 + g)
              = peelSlot (l - 1) (fun j => α (2 ^ (l - 1) + 1 + j)) g := by
            rw [hγ, rSlot_two_tS1 (by omega),
              show 2 ^ (l - 1) + 1 + g - 2 ^ (l - 1) - 1 = g from by omega]
          exact hv ▸ hslot (t + 2) (2 ^ (l - 1) + 1 + g) (by omega) (by omega)
        have heS2z : (eS2 Hp 2 l α).coeff t = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        have hidx : 2 ^ (l - 1) + (t - 2 ^ (l - 1)) = t := by omega
        rw [hidx] at hFe₃
        refine ⟨- F₃ - (tS1t Hp 2 l α ^ 2).coeff (t + 1), ?_, ?_⟩
        · refine Subalgebra.sub_mem _ (Subalgebra.neg_mem _ hF₃V) ?_
          exact (le_sup_left : K ≤ _) (hsqtK (t + 1) (by omega))
        · rw [hcO, heE1, heE2, heS2z, hFe₃, tLam_two_hi (by omega), hcast2, hγ,
            rSlot_two_tS1 (by omega),
            show t + 1 - 2 ^ (l - 1) - 1 = t - 2 ^ (l - 1) from by omega]
          ring

/-- **`lem:Rk2l`(3), `k = 2` base**: the remainder pair carries the full stage-table
certificate over `rSlot 2 l` with slopes `tLam 2 l`. -/
theorem Rk2l_tri_base (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧
    (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l)
    (h2 : IsUnit (2 : R)) :
    CoeffTriangular K (rSlot 2 l α) (fun j => ((tLam 2 l j : ℤ) : R)) (2 ^ l)
      (Rpair Hp Ht 2 l α).1 (Rpair Hp Ht 2 l α).2 := by
  rw [Rpair_two (by omega : ¬ l ≤ 1)]
  exact
    { unit := fun j hj => by
        rcases Nat.lt_or_ge j (2 ^ (l - 1)) with hlt | hge
        · rw [tLam_two_lo hlt, Int.cast_one]
          exact isUnit_one
        · rw [tLam_two_hi hge,
            show (((-2 : ℤ) : R)) = -2 from by push_cast; ring]
          exact h2.neg
      supp₁ := base_supp₁ hHp hl
      supp₂ := base_supp₂ hHp hl
      pivot := base_pivot hHp hl }

end baseSupports


omit [Nontrivial A] in
/-- The first-order correction at level `(k, l)` is the `k = 2` correction under an
`α`-shift by the band offset. -/
theorem eE1_shift :
    eE1 Hp k l α = eE1 Hp 2 l (fun j => α ((k - 2) * 2 ^ l + j)) := by
  show eS2 Hp k l α - tS1 Hp k l α ^ 2 = eS2 Hp 2 l _ - tS1 Hp 2 l _ ^ 2
  have h1 : eS2 Hp k l α = eS2 Hp 2 l (fun j => α ((k - 2) * 2 ^ l + j)) := by
    show peel Hp (l - 1) _ = peel Hp (l - 1) _
    congr 1
    funext j
    show α ((k - 2) * 2 ^ l + 1 + j) = α ((k - 2) * 2 ^ l + ((2 - 2) * 2 ^ l + 1 + j))
    congr 1
    omega
  have h2 : tS1 Hp k l α = tS1 Hp 2 l (fun j => α ((k - 2) * 2 ^ l + j)) := by
    show Hp (l - 1) + peel Hp (l - 1) _ = Hp (l - 1) + peel Hp (l - 1) _
    congr 2
    funext j
    show α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j)
      = α ((k - 2) * 2 ^ l + ((2 - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
    congr 1
    omega
  rw [h1, h2]

omit [Nontrivial A] in
theorem eE2_shift :
    eE2 Hp k l α = eE2 Hp 2 l (fun j => α ((k - 2) * 2 ^ l + j)) := by
  show C (α ((k - 2) * 2 ^ l)) - tS1t Hp k l α ^ 2 = _ - tS1t Hp 2 l _ ^ 2
  have h1 : α ((k - 2) * 2 ^ l)
      = (fun j => α ((k - 2) * 2 ^ l + j)) ((2 - 2) * 2 ^ l) := by
    show α ((k - 2) * 2 ^ l) = α ((k - 2) * 2 ^ l + (2 - 2) * 2 ^ l)
    congr 1
    omega
  have h2 : tS1t Hp k l α = tS1t Hp 2 l (fun j => α ((k - 2) * 2 ^ l + j)) := by
    show Hp (l - 1) + C (α ((k - 2) * 2 ^ l + 2 ^ (l - 1)))
      = Hp (l - 1) + C (α ((k - 2) * 2 ^ l + ((2 - 2) * 2 ^ l + 2 ^ (l - 1))))
    congr 3
    omega
  rw [h2, ← h1]

/-- The band certificate of the first-order correction pair at any level, via the
`α`-shift to the `k = 2` base. -/
theorem eE_cert {K : Subalgebra R A}
    (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) (h2 : IsUnit (2 : R)) :
    CoeffTriangular K (rSlot 2 l (fun j => α ((k - 2) * 2 ^ l + j)))
      (fun j => ((tLam 2 l j : ℤ) : R)) (2 ^ l)
      (eE1 Hp k l α) (eE2 Hp k l α) := by
  rw [eE1_shift, eE2_shift]
  exact
    { unit := fun j hj => by
        rcases Nat.lt_or_ge j (2 ^ (l - 1)) with hlt | hge
        · rw [tLam_two_lo hlt, Int.cast_one]
          exact isUnit_one
        · rw [tLam_two_hi hge,
            show (((-2 : ℤ) : R)) = -2 from by push_cast; ring]
          exact h2.neg
      supp₁ := base_supp₁ hHp hl
      supp₂ := base_supp₂ hHp hl
      pivot := base_pivot hHp hl }


/-- `-eE1` is monic of degree `2^l` (so `eE1` has degree `2^l` with leading `-1`). -/
theorem eE1_neg_monic
    (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    (tS1 Hp k l α ^ 2 - eS2 Hp k l α).Monic ∧
    (tS1 Hp k l α ^ 2 - eS2 Hp k l α).natDegree = 2 ^ l := by
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp2 : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  obtain ⟨hmers_m, hmers_d⟩ := peel_monic Hp (l - 1)
    (fun i h1 h2 => ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1⟩) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
  obtain ⟨heS2_m, heS2_d⟩ := peel_monic Hp (l - 1)
    (fun i h1 h2 => ⟨(hHp i h1 (by omega)).1, (hHp i h1 (by omega)).2.1⟩) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 1 + j))
  have htS1m : (tS1 Hp k l α).Monic := by
    show (Hp (l - 1) + peel Hp (l - 1) _).Monic
    have hdeg : (peel Hp (l - 1)
        (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))).degree
        < (Hp (l - 1)).degree := by
      rw [degree_eq_natDegree hmers_m.ne_zero, degree_eq_natDegree hm.ne_zero, hd,
        hmers_d]
      exact_mod_cast (by omega : 2 ^ (l - 1) - 1 < 2 ^ (l - 1))
    exact hm.add_of_left hdeg
  have htS1d : (tS1 Hp k l α).natDegree = 2 ^ (l - 1) := by
    show (Hp (l - 1) + peel Hp (l - 1) _).natDegree = 2 ^ (l - 1)
    have hdeg : (peel Hp (l - 1)
        (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))).degree
        < (Hp (l - 1)).degree := by
      rw [degree_eq_natDegree hmers_m.ne_zero, degree_eq_natDegree hm.ne_zero, hd,
        hmers_d]
      exact_mod_cast (by omega : 2 ^ (l - 1) - 1 < 2 ^ (l - 1))
    rw [natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hdeg), hd]
  have hsqm : (tS1 Hp k l α ^ 2).Monic := htS1m.pow 2
  have hsqd : (tS1 Hp k l α ^ 2).natDegree = 2 ^ l := by
    rw [htS1m.natDegree_pow, htS1d]
    omega
  have hlow : eS2 Hp k l α = 0 ∨
      (eS2 Hp k l α).natDegree < (tS1 Hp k l α ^ 2).natDegree := by
    right
    rw [hsqd]
    show (peel Hp (l - 1) _).natDegree < 2 ^ l
    rw [heS2_d]
    omega
  obtain ⟨h1, h2⟩ := monic_sub_low hsqm hlow
  exact ⟨h1, h2.trans hsqd⟩

/-- `-eE2` is monic of degree `2^l`. -/
theorem eE2_neg_monic
    (hHp : ∀ i, 1 ≤ i → i < l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K)) (hl : 2 ≤ l) :
    (tS1t Hp k l α ^ 2 - C (α ((k - 2) * 2 ^ l))).Monic ∧
    (tS1t Hp k l α ^ 2 - C (α ((k - 2) * 2 ^ l))).natDegree = 2 ^ l := by
  obtain ⟨hm, hd, hK⟩ := hHp (l - 1) (by omega) (by omega)
  have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
  have hp2 : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
    conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
    ring
  obtain ⟨htm, htd⟩ := monic_add_C hm (by omega) (α ((k - 2) * 2 ^ l + 2 ^ (l - 1)))
  have htS1tm : (tS1t Hp k l α).Monic := htm
  have htS1td : (tS1t Hp k l α).natDegree = 2 ^ (l - 1) := by
    show (Hp (l - 1) + C _).natDegree = _
    rw [htd, hd]
  have hsqm : (tS1t Hp k l α ^ 2).Monic := htS1tm.pow 2
  have hsqd : (tS1t Hp k l α ^ 2).natDegree = 2 ^ l := by
    rw [htS1tm.natDegree_pow, htS1td]
    omega
  have hlow : C (α ((k - 2) * 2 ^ l)) = 0 ∨
      (C (α ((k - 2) * 2 ^ l)) : A[X]).natDegree < (tS1t Hp k l α ^ 2).natDegree := by
    right
    rw [hsqd, natDegree_C]
    positivity
  obtain ⟨h1, h2⟩ := monic_sub_low hsqm hlow
  exact ⟨h1, h2.trans hsqd⟩

end FastPoly
