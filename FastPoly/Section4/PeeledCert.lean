import FastPoly.Section4.Peeled
import FastPoly.Section4.Unitriangular
import FastPoly.Section4.MersCert

/-!
# Unitriangular certificate for the peeled gadget

`peel_unitriangular`: the peeled known-powers gadget is coefficient-triangular with
unit slopes, in the exact `CoeffTriangular` shape of `mers_unitriangular`, so every
Section-5 consumer of the certificate can swap gadget families by name.

The slot map `peelSlot` mirrors the peel layout: the `B` child occupies rows
`0 … 2^{k-1}-2`, the glue key `γ` pivots at row `2^{k-1}-1` (the remainder's top
row, with unit slope since both children are monic), and the `W` child occupies
rows `2^{k-1} … 2^k-2`.  The step certificate follows from the decomposition

  `peel - X^d = (H + Cγ)·(W - X^{d'}) + (B - X^{d'}) + (H - X^h)·X^{d'} + (γ+1)·X^{d'}`

with `h = 2^{k-1}`, `d' = h - 1`, `d = h + d'`, using the shift calculus of
`Recover/Triangular.lean` on the two child certificates.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Row-to-parameter slot map of the peeled certificate.  `B`-child rows
`0 … 2^{k-1}-2`, glue row `2^{k-1}-1`, `W`-child rows `2^{k-1} … 2^k-2`. -/
noncomputable def peelSlot : ℕ → (ℕ → A) → ℕ → A
  | 0, α, r => α r
  | 1, α, r => α r
  | 2, α, r => α r
  | (kk + 3), α, r =>
      if r < 2 ^ (kk + 2) - 1 then peelSlot (kk + 2) (fun j => α (2 ^ (kk + 2) + j)) r
      else if r = 2 ^ (kk + 2) - 1 then α 0
      else peelSlot (kk + 2) (fun j => α (1 + j)) (r - 2 ^ (kk + 2))

theorem peelSlot_B (kk : ℕ) (α : ℕ → A) {r : ℕ} (hr : r < 2 ^ (kk + 2) - 1) :
    peelSlot (kk + 3) α r = peelSlot (kk + 2) (fun j => α (2 ^ (kk + 2) + j)) r := by
  simp only [peelSlot, if_pos hr]

theorem peelSlot_gamma (kk : ℕ) (α : ℕ → A) :
    peelSlot (kk + 3) α (2 ^ (kk + 2) - 1) = α 0 := by
  simp only [peelSlot, if_neg (lt_irrefl _), if_pos rfl, if_true]

theorem peelSlot_W (kk : ℕ) (α : ℕ → A) (i : ℕ) :
    peelSlot (kk + 3) α (2 ^ (kk + 2) + i) = peelSlot (kk + 2) (fun j => α (1 + j)) i := by
  have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
  simp only [peelSlot, if_neg (by omega : ¬ 2 ^ (kk + 2) + i < 2 ^ (kk + 2) - 1),
    if_neg (by omega : ¬ 2 ^ (kk + 2) + i = 2 ^ (kk + 2) - 1)]
  congr 1
  omega

/-- Transport a `B`-child slot window into the parent window. -/
theorem peelSlot_B_image (kk : ℕ) (α : ℕ → A) {a b : ℕ} (hb : b ≤ 2 ^ (kk + 2) - 1) :
    (peelSlot (kk + 2) (fun j => α (2 ^ (kk + 2) + j))) '' Set.Ico a b
      ⊆ (peelSlot (kk + 3) α) '' Set.Ico a b := by
  rintro _ ⟨r, ⟨hr1, hr2⟩, rfl⟩
  exact ⟨r, ⟨hr1, hr2⟩, peelSlot_B kk α (by omega)⟩

/-- Transport a `W`-child slot window into the parent window. -/
theorem peelSlot_W_image (kk : ℕ) (α : ℕ → A) (a b : ℕ) :
    (peelSlot (kk + 2) (fun j => α (1 + j))) '' Set.Ico a b
      ⊆ (peelSlot (kk + 3) α) '' Set.Ico (2 ^ (kk + 2) + a) (2 ^ (kk + 2) + b) := by
  rintro _ ⟨r, ⟨hr1, hr2⟩, rfl⟩
  exact ⟨2 ^ (kk + 2) + r, ⟨by omega, by omega⟩, peelSlot_W kk α r⟩

section main

variable [Nontrivial A]

/-- **Unitriangular certificate for the peeled gadget** (`lem:peeled-Q-decodable`,
certificate form): same `CoeffTriangular` shape as `mers_unitriangular`. -/
theorem peel_unitriangular {K : Subalgebra R A} (Hp : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
        (∀ j, (Hp i).coeff j ∈ K)) →
      1 ≤ k → ∀ α : ℕ → A,
      CoeffTriangular K (peelSlot k α) (fun _ => (1 : R)) (2 ^ k - 1)
        0 (peel Hp k α - X ^ (2 ^ k - 1)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α
    match k with
    | 1 =>
      have h1 : peel Hp 1 α - X ^ (2 ^ 1 - 1) = C (α 0) := by
        show (X + C (α 0)) - X ^ (2 ^ 1 - 1) = C (α 0)
        norm_num
      rw [h1, show peelSlot (A := A) 1 α = α from funext fun r => rfl]
      refine
        { unit := fun j hj => isUnit_one
          supp₁ := fun j => by rw [coeff_zero]; exact Subalgebra.zero_mem _
          supp₂ := ?_
          pivot := ?_ }
      · intro j
        rw [coeff_C]
        split
        · rename_i hj0
          subst hj0
          exact (le_sup_right : adjoin R _ ≤ _)
            (subset_adjoin ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩)
        · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
      · intro j hj
        match j, hj with
        | 0, _ =>
          refine ⟨0, (le_sup_left : K ≤ _) (Subalgebra.zero_mem _), ?_⟩
          rw [coeff_combined_zero, coeff_C_zero, map_one, one_mul, add_zero]
    | 2 =>
      obtain ⟨h1m, h1d, h1K⟩ := hHp 1 (by omega) (by omega)
      have hs2 : peelSlot (A := A) 2 α = α := funext fun r => rfl
      rw [show (2 : ℕ) ^ 2 - 1 = 3 from by norm_num, hs2]
      exact mers_two_unitriangular Hp h1m h1d h1K α
    | (kk + 3) =>
      have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
      have hdd : 2 ^ (kk + 3) - 1 = 2 ^ (kk + 2) + (2 ^ (kk + 2) - 1) := by
        have : (2:ℕ) ^ (kk + 3) = 2 ^ (kk + 2) + 2 ^ (kk + 2) := by ring
        omega
      obtain ⟨hHm, hHd, hHK⟩ := hHp (kk + 2) (by omega) (by omega)
      set h : ℕ := 2 ^ (kk + 2) with hh
      set d' : ℕ := 2 ^ (kk + 2) - 1 with hd'
      set d : ℕ := 2 ^ (kk + 3) - 1 with hd
      set W : A[X] := peel Hp (kk + 2) (fun j => α (1 + j)) with hWdef
      set B : A[X] := peel Hp (kk + 2) (fun j => α (2 ^ (kk + 2) + j)) with hBdef
      obtain ⟨hWm, hWd⟩ := peel_monic Hp (kk + 2)
        (fun i' hi1 hik => ⟨(hHp i' hi1 (by omega)).1, (hHp i' hi1 (by omega)).2.1⟩)
        (by omega) (fun j => α (1 + j))
      obtain ⟨hBm, hBd⟩ := peel_monic Hp (kk + 2)
        (fun i' hi1 hik => ⟨(hHp i' hi1 (by omega)).1, (hHp i' hi1 (by omega)).2.1⟩)
        (by omega) (fun j => α (2 ^ (kk + 2) + j))
      rw [← hWdef] at hWm hWd
      rw [← hBdef] at hBm hBd
      have hcW := ih (kk + 2) (by omega) (fun i' hi1 hik => hHp i' hi1 (by omega))
        (by omega) (fun j => α (1 + j))
      have hcB := ih (kk + 2) (by omega) (fun i' hi1 hik => hHp i' hi1 (by omega))
        (by omega) (fun j => α (2 ^ (kk + 2) + j))
      rw [← hWdef] at hcW
      rw [← hBdef] at hcB
      -- remainder degrees
      have hsubdeg : ∀ P : A[X], P.Monic → P.natDegree = d' →
          ∀ m, d' ≤ m → (P - X ^ d').coeff m = 0 := by
        intro P hm hdeg m hmge
        rw [coeff_sub, coeff_X_pow]
        rcases eq_or_lt_of_le hmge with hEq | hlt
        · rw [← hEq, if_pos rfl, ← hdeg, hm.coeff_natDegree]
          ring
        · rw [if_neg (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
          ring
      have hHlow : ∀ m, d' < m → (Hp (kk + 2) - X ^ h).coeff m = 0 := by
        intro m hmgt
        rw [coeff_sub, coeff_X_pow]
        rcases eq_or_lt_of_le (show h ≤ m from by omega) with hEq | hlt
        · rw [← hEq, if_pos rfl, ← hHd, hHm.coeff_natDegree]
          ring
        · rw [if_neg (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
          ring
      have hHlowd : (Hp (kk + 2) - X ^ h).natDegree ≤ d' :=
        natDegree_le_iff_coeff_eq_zero.mpr fun m hm => hHlow m hm
      have hHlowK : ∀ m, (Hp (kk + 2) - X ^ h).coeff m ∈ K := by
        intro m
        rw [coeff_sub]
        refine Subalgebra.sub_mem _ (hHK m) ?_
        rw [coeff_X_pow]
        split
        · exact Subalgebra.one_mem _
        · exact Subalgebra.zero_mem _
      -- the six-term decomposition
      have hsplit : peel Hp (kk + 3) α - X ^ d
          = (W - X ^ d') * X ^ h
            + (Hp (kk + 2) - X ^ h) * (W - X ^ d')
            + C (α 0) * (W - X ^ d')
            + (B - X ^ d')
            + (Hp (kk + 2) - X ^ h) * X ^ d'
            + C (α 0 + 1) * X ^ d' := by
        rw [peel_unfold, ← hWdef, ← hBdef, show d = h + d' from by omega, pow_add,
          map_add, C_1]
        ring
      -- per-row membership of the six summands, relative to the row context
      have hctx : ∀ j : ℕ,
          (peel Hp (kk + 3) α - X ^ d).coeff j
            ∈ K ⊔ adjoin R ((peelSlot (kk + 3) α) '' Set.Ico j d) := by
        intro j
        set V := K ⊔ adjoin R ((peelSlot (kk + 3) α) '' Set.Ico j d) with hV
        have hKV : K ≤ V := le_sup_left
        -- transports into V
        have htrW : ∀ a, j ≤ h + a →
            (W - X ^ d').coeff a ∈ V := by
          intro a hja
          have := hcW.supp₂ a
          refine SetLike.le_def.1 (sup_le hKV (adjoin_le ?_)) this
          intro y hy
          have hy2 := peelSlot_W_image kk α a d' hy
          refine (le_sup_right : adjoin R _ ≤ V) (subset_adjoin ?_)
          obtain ⟨r, ⟨hr1, hr2⟩, rfl⟩ := hy2
          exact ⟨r, ⟨by omega, by omega⟩, rfl⟩
        have htrB : ∀ a, j ≤ a →
            (B - X ^ d').coeff a ∈ V := by
          intro a hja
          rcases Nat.lt_or_ge a d' with ha | ha
          · have := hcB.supp₂ a
            refine SetLike.le_def.1 (sup_le hKV (adjoin_le ?_)) this
            intro y hy
            have hy2 := peelSlot_B_image kk α (le_rfl) hy
            refine (le_sup_right : adjoin R _ ≤ V) (subset_adjoin ?_)
            obtain ⟨r, ⟨hr1, hr2⟩, rfl⟩ := hy2
            exact ⟨r, ⟨by omega, by omega⟩, rfl⟩
          · rw [hsubdeg B hBm hBd a ha]
            exact Subalgebra.zero_mem _
        have hγV : j ≤ d' → (α 0 : A) ∈ V := by
          intro hjd
          have : peelSlot (kk + 3) α d' ∈ V :=
            slot_mem_sup_adjoin_Ico _ (by omega) (by omega)
          rw [hd'] at this
          rwa [peelSlot_gamma kk α] at this
        rw [hsplit]
        iterate 5 rw [coeff_add]
        refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
          (Subalgebra.add_mem _ (Subalgebra.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_
        -- 1. (W - X^d') * X^h
        · rcases Nat.lt_or_ge j h with hjh | hjh
          · rw [coeff_mul_X_pow', if_neg (by omega)]
            exact Subalgebra.zero_mem _
          · rw [coeff_mul_X_pow', if_pos (by omega)]
            exact htrW _ (by omega)
        -- 2. (Hp - X^h) * (W - X^d')
        · rw [coeff_mul]
          refine Subalgebra.sum_mem _ fun x hx => ?_
          have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
          rcases Nat.lt_or_ge d' x.1 with hx1 | hx1
          · rw [hHlow x.1 hx1, zero_mul]
            exact Subalgebra.zero_mem _
          · refine Subalgebra.mul_mem _ (hKV (hHlowK x.1)) ?_
            exact htrW x.2 (by omega)
        -- 3. C (α 0) * (W - X^d')
        · rw [coeff_C_mul]
          rcases Nat.lt_or_ge j h with hj | hj
          · exact Subalgebra.mul_mem _ (hγV (by omega)) (htrW j (by omega))
          · rw [hsubdeg W hWm hWd j (by omega), mul_zero]
            exact Subalgebra.zero_mem _
        -- 4. B - X^d'
        · exact htrB j le_rfl
        -- 5. (Hp - X^h) * X^d'
        · rcases Nat.lt_or_ge j d' with hjd5 | hjd5
          · rw [coeff_mul_X_pow', if_neg (by omega)]
            exact Subalgebra.zero_mem _
          · rw [coeff_mul_X_pow', if_pos (by omega)]
            exact hKV (hHlowK _)
        -- 6. C (α 0 + 1) * X^d'
        · rcases Nat.lt_or_ge j d' with hjd6 | hjd6
          · rw [coeff_mul_X_pow', if_neg (by omega)]
            exact Subalgebra.zero_mem _
          · rcases eq_or_lt_of_le hjd6 with hEq | hlt
            · rw [coeff_mul_X_pow', if_pos (by omega), coeff_C, if_pos (by omega)]
              exact Subalgebra.add_mem _ (hγV (by omega)) (Subalgebra.one_mem _)
            · rw [coeff_mul_X_pow', if_pos (by omega), coeff_C, if_neg (by omega)]
              exact Subalgebra.zero_mem _
      refine
        { unit := fun j hj => isUnit_one
          supp₁ := fun j => by rw [coeff_zero]; exact Subalgebra.zero_mem _
          supp₂ := fun j => hctx j
          pivot := ?_ }
      intro j hj
      rw [coeff_combined_zero_left]
      -- the row context above the pivot
      set V := K ⊔ adjoin R ((peelSlot (kk + 3) α) '' Set.Ico (j + 1) d) with hV
      have hKV : K ≤ V := le_sup_left
      have htrW : ∀ a, j + 1 ≤ h + a → (W - X ^ d').coeff a ∈ V := by
        intro a hja
        have := hcW.supp₂ a
        refine SetLike.le_def.1 (sup_le hKV (adjoin_le ?_)) this
        intro y hy
        obtain ⟨r, ⟨hr1, hr2⟩, rfl⟩ := peelSlot_W_image kk α a d' hy
        exact (le_sup_right : adjoin R _ ≤ V)
          (subset_adjoin ⟨r, ⟨by omega, by omega⟩, rfl⟩)
      have hγV : j + 1 ≤ d' → (α 0 : A) ∈ V := by
        intro hjd
        have : peelSlot (kk + 3) α d' ∈ V :=
          slot_mem_sup_adjoin_Ico _ (by omega) (by omega)
        rw [hd'] at this
        rwa [peelSlot_gamma kk α] at this
      -- band split
      rcases Nat.lt_or_ge j d' with hjB | hjge
      -- B band: j < d'
      · obtain ⟨F, hF, hpiv⟩ := hcB.pivot j (by omega)
        have hFV : F ∈ V := by
          refine SetLike.le_def.1 (sup_le hKV (adjoin_le ?_)) hF
          intro y hy
          obtain ⟨r, ⟨hr1, hr2⟩, rfl⟩ := peelSlot_B_image kk α (le_rfl) hy
          exact (le_sup_right : adjoin R _ ≤ V)
            (subset_adjoin ⟨r, ⟨by omega, by omega⟩, rfl⟩)
        rw [coeff_combined_zero_left] at hpiv
        refine ⟨F + ((W - X ^ d') * X ^ h).coeff j
            + ((Hp (kk + 2) - X ^ h) * (W - X ^ d')).coeff j
            + (C (α 0) * (W - X ^ d')).coeff j
            + ((Hp (kk + 2) - X ^ h) * X ^ d').coeff j
            + (C (α 0 + 1) * X ^ d').coeff j, ?_, ?_⟩
        · refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
            (Subalgebra.add_mem _ (Subalgebra.add_mem _ hFV ?_) ?_) ?_) ?_) ?_
          · rcases Nat.lt_or_ge j h with hjh | hjh
            · rw [coeff_mul_X_pow', if_neg (by omega)]
              exact Subalgebra.zero_mem _
            · rw [coeff_mul_X_pow', if_pos (by omega)]
              exact htrW _ (by omega)
          · rw [coeff_mul]
            refine Subalgebra.sum_mem _ fun x hx => ?_
            have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
            rcases Nat.lt_or_ge d' x.1 with hx1 | hx1
            · rw [hHlow x.1 hx1, zero_mul]
              exact Subalgebra.zero_mem _
            · exact Subalgebra.mul_mem _ (hKV (hHlowK x.1)) (htrW x.2 (by omega))
          · rw [coeff_C_mul]
            exact Subalgebra.mul_mem _ (hγV (by omega)) (htrW j (by omega))
          · rcases Nat.lt_or_ge j d' with hjd5 | hjd5
            · rw [coeff_mul_X_pow', if_neg (by omega)]
              exact Subalgebra.zero_mem _
            · rw [coeff_mul_X_pow', if_pos (by omega)]
              exact hKV (hHlowK _)
          · rw [coeff_mul_X_pow', if_neg (by omega)]
            exact Subalgebra.zero_mem _
        · have hslot : peelSlot (kk + 3) α j
              = peelSlot (kk + 2) (fun t => α (2 ^ (kk + 2) + t)) j :=
            peelSlot_B kk α (by omega)
          rw [hsplit]
          iterate 5 rw [coeff_add]
          rw [hslot, hpiv]
          ring
      rcases eq_or_lt_of_le hjge with hjγ | hjW
      -- γ row: j = d'
      · refine ⟨1 + ((W - X ^ d') * X ^ h).coeff j
            + ((Hp (kk + 2) - X ^ h) * (W - X ^ d')).coeff j
            + ((Hp (kk + 2) - X ^ h) * X ^ d').coeff j, ?_, ?_⟩
        · refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
            (hKV (Subalgebra.one_mem _)) ?_) ?_) ?_
          · rcases Nat.lt_or_ge j h with hjh | hjh
            · rw [coeff_mul_X_pow', if_neg (by omega)]
              exact Subalgebra.zero_mem _
            · rw [coeff_mul_X_pow', if_pos (by omega)]
              exact htrW _ (by omega)
          · rw [coeff_mul]
            refine Subalgebra.sum_mem _ fun x hx => ?_
            have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
            rcases Nat.lt_or_ge x.2 d' with hx2 | hx2
            · refine Subalgebra.mul_mem _ (hKV (hHlowK x.1)) ?_
              exact htrW x.2 (by omega)
            · rw [hsubdeg W hWm hWd x.2 hx2, mul_zero]
              exact Subalgebra.zero_mem _
          · rcases Nat.lt_or_ge j d' with hjd5 | hjd5
            · rw [coeff_mul_X_pow', if_neg (by omega)]
              exact Subalgebra.zero_mem _
            · rw [coeff_mul_X_pow', if_pos (by omega)]
              exact hKV (hHlowK _)
        · rw [hsplit]
          iterate 5 rw [coeff_add]
          have hz3 : (C (α 0) * (W - X ^ d')).coeff j = 0 := by
            rw [coeff_C_mul, hsubdeg W hWm hWd j (by omega), mul_zero]
          have hz4 : (B - X ^ d').coeff j = 0 := hsubdeg B hBm hBd j (by omega)
          have h6 : (C (α 0 + 1) * X ^ d').coeff j = α 0 + 1 := by
            rw [coeff_mul_X_pow', if_pos (by omega),
              show j - d' = 0 from by omega, coeff_C_zero]
          have hslot : peelSlot (kk + 3) α j = α 0 := by
            rw [show j = 2 ^ (kk + 2) - 1 from by omega]
            exact peelSlot_gamma kk α
          rw [hz3, hz4, h6, hslot, map_one, one_mul]
          ring
      -- W band: d' < j < d
      · have hji : j = h + (j - h) := by omega
        have hiW : j - h < d' := by omega
        obtain ⟨F, hF, hpiv⟩ := hcW.pivot (j - h) hiW
        have hFV : F ∈ V := by
          refine SetLike.le_def.1 (sup_le hKV (adjoin_le ?_)) hF
          intro y hy
          obtain ⟨r, ⟨hr1, hr2⟩, rfl⟩ := peelSlot_W_image kk α (j - h + 1) d' hy
          exact (le_sup_right : adjoin R _ ≤ V)
            (subset_adjoin ⟨r, ⟨by omega, by omega⟩, rfl⟩)
        rw [coeff_combined_zero_left] at hpiv
        refine ⟨F + ((Hp (kk + 2) - X ^ h) * (W - X ^ d')).coeff j
            + ((Hp (kk + 2) - X ^ h) * X ^ d').coeff j, ?_, ?_⟩
        · refine Subalgebra.add_mem _ (Subalgebra.add_mem _ hFV ?_) ?_
          · rw [coeff_mul]
            refine Subalgebra.sum_mem _ fun x hx => ?_
            have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
            rcases Nat.lt_or_ge d' x.1 with hx1 | hx1
            · rw [hHlow x.1 hx1, zero_mul]
              exact Subalgebra.zero_mem _
            · exact Subalgebra.mul_mem _ (hKV (hHlowK x.1)) (htrW x.2 (by omega))
          · rcases Nat.lt_or_ge j d' with hjd5 | hjd5
            · rw [coeff_mul_X_pow', if_neg (by omega)]
              exact Subalgebra.zero_mem _
            · rw [coeff_mul_X_pow', if_pos (by omega)]
              exact hKV (hHlowK _)
        · have h1 : ((W - X ^ d') * X ^ h).coeff j = (W - X ^ d').coeff (j - h) := by
            rw [coeff_mul_X_pow', if_pos (by omega)]
          have hz3 : (C (α 0) * (W - X ^ d')).coeff j = 0 := by
            rw [coeff_C_mul, hsubdeg W hWm hWd j (by omega), mul_zero]
          have hz4 : (B - X ^ d').coeff j = 0 := hsubdeg B hBm hBd j (by omega)
          have hz6 : (C (α 0 + 1) * X ^ d').coeff j = 0 := by
            rw [coeff_mul_X_pow', if_pos (by omega), coeff_C, if_neg (by omega)]
          have hslot : peelSlot (kk + 3) α j
              = peelSlot (kk + 2) (fun t => α (1 + t)) (j - h) := by
            have hW := peelSlot_W kk α (j - h)
            rwa [show 2 ^ (kk + 2) + (j - h) = j from by omega] at hW
          rw [hsplit]
          iterate 5 rw [coeff_add]
          rw [h1, hz3, hz4, hz6, hslot, hpiv]
          ring

end main

end FastPoly
