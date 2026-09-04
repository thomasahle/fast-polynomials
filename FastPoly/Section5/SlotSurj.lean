import FastPoly.Section5.QFourKOne
import FastPoly.Section4.PeeledCert

/-!
# Slot-map inversion

The deferred surjectivity half of parameter recovery: a subalgebra containing the
tower data and all slot values contains every raw parameter.  For the Mersenne gadget
this goes through the coefficient detour (`peel_coeff_mem_slots` + `peel_correct`);
for the `Rk2l` slot map it is a branch recursion mirroring `rSlotF`
(`rSlot_param_mem`), with the updated tower elements re-entering through the
band values.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {Hp : ℕ → A[X]}

/-- The coefficients of the Mersenne gadget lie in the closure of its slot values. -/
theorem mers_coeff_mem_slots (k : ℕ)
    (hHp : ∀ i, 1 ≤ i → i < k → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hk : 1 ≤ k) (α : ℕ → A) :
    ∀ j, (mers Hp k α).coeff j
      ∈ K ⊔ adjoin R ((mersSlot k α (A := A)) '' Set.Ico 0 (2 ^ k - 1)) := by
  intro j
  have hcert := mers_unitriangular (K := K) Hp k hHp hk α
  have hsupp := hcert.supp₂ j
  have hkey : (mers Hp k α).coeff j
      = (mers Hp k α - X ^ (2 ^ k - 1)).coeff j + (X ^ (2 ^ k - 1) : A[X]).coeff j := by
    rw [coeff_sub]
    ring
  rw [hkey]
  refine Subalgebra.add_mem _ ?_ ?_
  · refine SetLike.le_def.1 (sup_le le_sup_left (adjoin_le ?_)) hsupp
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨g, ⟨by omega, by omega⟩, rfl⟩)
  · rw [coeff_X_pow]
    split
    · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)

/-- **Slot inversion for the Mersenne gadget**: a subalgebra containing the tower data
and all slot values contains every raw parameter. -/
theorem mers_param_from_slots (k : ℕ) {V : Subalgebra R A}
    (hHp : ∀ i, 1 ≤ i → i < k → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ V))
    (hk : 1 ≤ k) (α : ℕ → A)
    (hslots : ∀ g, g < 2 ^ k - 1 → mersSlot k α (A := A) g ∈ V) :
    ∀ t, t < 2 ^ k - 1 → α t ∈ V := by
  have hcoeffs : ∀ j, (mers Hp k α).coeff j ∈ V := by
    intro j
    have h := mers_coeff_mem_slots (K := V) k hHp hk α j
    refine SetLike.le_def.1 (sup_le le_rfl (adjoin_le ?_)) h
    rintro _ ⟨g, ⟨-, hg2⟩, rfl⟩
    exact hslots g hg2
  exact mers_correct (K := V) Hp k hHp hk α V le_rfl hcoeffs


/-- The coefficients of the peeled gadget lie in the closure of its slot values. -/
theorem peel_coeff_mem_slots (k : ℕ)
    (hHp : ∀ i, 1 ≤ i → i < k → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hk : 1 ≤ k) (α : ℕ → A) :
    ∀ j, (peel Hp k α).coeff j
      ∈ K ⊔ adjoin R ((peelSlot k α (A := A)) '' Set.Ico 0 (2 ^ k - 1)) := by
  intro j
  have hcert := peel_unitriangular (K := K) Hp k hHp hk α
  have hsupp := hcert.supp₂ j
  have hkey : (peel Hp k α).coeff j
      = (peel Hp k α - X ^ (2 ^ k - 1)).coeff j + (X ^ (2 ^ k - 1) : A[X]).coeff j := by
    rw [coeff_sub]
    ring
  rw [hkey]
  refine Subalgebra.add_mem _ ?_ ?_
  · refine SetLike.le_def.1 (sup_le le_sup_left (adjoin_le ?_)) hsupp
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨g, ⟨by omega, by omega⟩, rfl⟩)
  · rw [coeff_X_pow]
    split
    · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)

/-- **Slot inversion for the peeled gadget**: a subalgebra containing the tower data
and all slot values contains every raw parameter. -/
theorem peel_param_from_slots (k : ℕ) {V : Subalgebra R A}
    (hHp : ∀ i, 1 ≤ i → i < k → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ V))
    (hk : 1 ≤ k) (α : ℕ → A)
    (hslots : ∀ g, g < 2 ^ k - 1 → peelSlot k α (A := A) g ∈ V) :
    ∀ t, t < 2 ^ k - 1 → α t ∈ V := by
  have hcoeffs : ∀ j, (peel Hp k α).coeff j ∈ V := by
    intro j
    have h := peel_coeff_mem_slots (K := V) k hHp hk α j
    refine SetLike.le_def.1 (sup_le le_rfl (adjoin_le ?_)) h
    rintro _ ⟨g, ⟨-, hg2⟩, rfl⟩
    exact hslots g hg2
  exact peel_correct (K := V) Hp k hHp hk α V le_rfl hcoeffs


/-- **Slot inversion for the `Rk2l` slot map** (`rSlot` surjectivity onto its
parameter block): a subalgebra containing the tower data and all slot values of
`rSlot k l α` contains every raw parameter of the block. -/
theorem rSlot_param_mem {V : Subalgebra R A} (h2 : IsUnit (2 : R)) :
    ∀ k, 1 ≤ k → ∀ (l : ℕ) (Hp : ℕ → A[X]) (α : ℕ → A), 2 ≤ l →
    (∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ V)) →
    (∀ r, r < (k - 1) * 2 ^ l → rSlot k l α (A := A) r ∈ V) →
    ∀ t, t < (k - 1) * 2 ^ l → α t ∈ V := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk l Hp α hl htower hvals t ht
    have hp1 : 1 ≤ 2 ^ (l - 1) := Nat.one_le_pow _ _ (by omega)
    have hp0 : 1 ≤ 2 ^ l := Nat.one_le_pow _ _ (by omega)
    have hple : 2 ^ (l - 1) + 2 ^ (l - 1) = 2 ^ l := by
      conv_rhs => rw [show l = (l - 1) + 1 from by omega, pow_succ]
      ring
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · have hk1' : k = 1 := by omega
      subst hk1'
      exact absurd ht (by norm_num)
    rcases eq_or_lt_of_le hk2 with hk2e | hk3
    · -- `k = 2`
      subst hk2e
      have ht' : t < 2 ^ l := by
        have hone : (2 - 1) * 2 ^ l = 2 ^ l := by norm_num
        omega
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · subst ht0
        have h := hvals 0 (by
          have hone : (2 - 1) * 2 ^ l = 2 ^ l := by norm_num
          omega)
        rwa [rSlot_two_zero] at h
      · rcases Nat.lt_or_ge t (2 ^ (l - 1)) with htlo | hthi
        · have hdec := peel_param_from_slots (Hp := Hp) (l - 1) (V := V)
            (fun i h1 h2' => htower i h1 (by omega)) (by omega)
            (fun j => α (1 + j))
            (by
              intro g hg
              have h := hvals (1 + g) (by
                have hone : (2 - 1) * 2 ^ l = 2 ^ l := by norm_num
                omega)
              rw [rSlot_two_eS2 (by omega) (by omega),
                show 1 + g - 1 = g from by omega] at h
              exact h)
          have h := hdec (t - 1) (by omega)
          have h' : α (1 + (t - 1)) ∈ V := h
          rwa [show 1 + (t - 1) = t from by omega] at h'
        · rcases eq_or_lt_of_le hthi with hteq | htgt
          · have h := hvals (2 ^ (l - 1)) (by
              have hone : (2 - 1) * 2 ^ l = 2 ^ l := by norm_num
              omega)
            rw [rSlot_two_delta] at h
            rwa [← hteq]
          · have hdec := peel_param_from_slots (Hp := Hp) (l - 1) (V := V)
              (fun i h1 h2' => htower i h1 (by omega)) (by omega)
              (fun j => α (2 ^ (l - 1) + 1 + j))
              (by
                intro g hg
                have h := hvals (2 ^ (l - 1) + 1 + g) (by
                  have hone : (2 - 1) * 2 ^ l = 2 ^ l := by norm_num
                  omega)
                rw [rSlot_two_tS1 (by omega),
                  show 2 ^ (l - 1) + 1 + g - 2 ^ (l - 1) - 1 = g from by omega]
                  at h
                exact h)
            have h := hdec (t - 2 ^ (l - 1) - 1) (by omega)
            have h' : α (2 ^ (l - 1) + 1 + (t - 2 ^ (l - 1) - 1)) ∈ V := h
            rwa [show 2 ^ (l - 1) + 1 + (t - 2 ^ (l - 1) - 1) = t from by omega]
              at h'
    · rcases eq_or_ne (k % 2) 0 with hpar | hpar
      · -- even branch
        have hk4 : 4 ≤ k := by omega
        have hb3 : (k - 2) * 2 ^ l + 2 ^ l = (k - 1) * 2 ^ l := by
          have h1 : k - 2 + 1 = k - 1 := by omega
          calc (k - 2) * 2 ^ l + 2 ^ l = (k - 2 + 1) * 2 ^ l := by ring
            _ = (k - 1) * 2 ^ l := by rw [h1]
        rcases Nat.lt_or_ge t ((k - 2) * 2 ^ l) with htin | htband
        · -- inner recursion
          have htower2 : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧
              (Hp i).natDegree = 2 ^ i :=
            fun i h1 hi => ⟨(htower i h1 hi).1, (htower i h1 hi).2.1⟩
          obtain ⟨hHm', hHd'⟩ := evenH_good (k := k) (α := α) htower2 hl
          have hbandV : ∀ g, (k - 2) * 2 ^ l ≤ g → g < (k - 1) * 2 ^ l →
              rSlot k l α (A := A) g ∈ V := fun g h1' h2' => hvals g h2'
          have hupdV : ∀ i, 1 ≤ i → i ≤ l + 1 →
              ((Function.update Hp (l + 1) (evenH Hp k l α)) i).Monic ∧
              ((Function.update Hp (l + 1) (evenH Hp k l α)) i).natDegree = 2 ^ i ∧
              (∀ j, ((Function.update Hp (l + 1) (evenH Hp k l α)) i).coeff j ∈ V) :=
            good_update_mem (m := l) (H' := evenH Hp k l α) htower hHm' hHd'
              le_rfl (by
                intro j
                have h := evenH_coeff_mem (K := V) (α := α) htower hpar hk4 hl h2 j
                refine SetLike.le_def.1 (sup_le le_rfl (adjoin_le ?_)) h
                rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
                exact hbandV g hg1 hg2)
          have hconv : (k / 2 - 1) * 2 ^ (l + 1) = (k - 2) * 2 ^ l :=
            even_band_conv hpar (by omega)
          refine ih (k / 2) (by omega) (by omega) (l + 1)
            (Function.update Hp (l + 1) (evenH Hp k l α)) α (by omega) hupdV
            ?_ t (by omega)
          intro r hr
          rw [hconv] at hr
          have h := hvals r (by omega)
          rwa [rSlot_even_inner hpar hk4 hr] at h
        · -- even band
          rcases eq_or_lt_of_le htband with hteq | htgt
          · have h := hvals ((k - 2) * 2 ^ l) (by omega)
            rw [rSlot_even_b0 hpar hk4] at h
            rwa [← hteq]
          · rcases Nat.lt_or_ge t ((k - 2) * 2 ^ l + 2 ^ (l - 1)) with htmid | hthi
            · have hdec := peel_param_from_slots (Hp := Hp) (l - 1) (V := V)
                (fun i h1 h2' => htower i h1 (by omega)) (by omega)
                (fun j => α ((k - 2) * 2 ^ l + 1 + j))
                (by
                  intro g hg
                  have h := hvals ((k - 2) * 2 ^ l + 1 + g) (by omega)
                  rw [rSlot_even_eS2 hpar hk4 (by omega) (by omega),
                    show (k - 2) * 2 ^ l + 1 + g - (k - 2) * 2 ^ l - 1 = g from
                      by omega] at h
                  exact h)
              have h := hdec (t - (k - 2) * 2 ^ l - 1) (by omega)
              have h' : α ((k - 2) * 2 ^ l + 1 + (t - (k - 2) * 2 ^ l - 1)) ∈ V := h
              rwa [show (k - 2) * 2 ^ l + 1 + (t - (k - 2) * 2 ^ l - 1) = t from
                by omega] at h'
            · rcases eq_or_lt_of_le hthi with hteq2 | htgt2
              · have h := hvals ((k - 2) * 2 ^ l + 2 ^ (l - 1)) (by omega)
                rw [rSlot_even_delta hpar hk4] at h
                rwa [← hteq2]
              · have hdec := peel_param_from_slots (Hp := Hp) (l - 1) (V := V)
                  (fun i h1 h2' => htower i h1 (by omega)) (by omega)
                  (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
                  (by
                    intro g hg
                    have h := hvals ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g)
                      (by omega)
                    rw [rSlot_even_tS1 hpar hk4 (by omega),
                      show (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g
                          - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1 = g from by omega]
                      at h
                    exact h)
                have h := hdec (t - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1) (by omega)
                have h' : α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1
                    + (t - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1)) ∈ V := h
                rwa [show (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1
                    + (t - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1) = t from by omega]
                  at h'
      · -- odd branches
        have hk3' : 3 ≤ k := by omega
        rcases Nat.lt_or_ge l 3 with hlb | hl3
        · -- shared odd base, `l = 2`
          have hleq : l = 2 := by omega
          subst hleq
          have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
          rcases Nat.lt_or_ge t 4 with htlo | ht4
          · have h := hvals t (by omega)
            rwa [rSlot_ob_low hpar hk3' htlo] at h
          · rcases Nat.lt_or_ge t (4 * (k - 2)) with htin | htband
            · -- inner recursion
              have htower2 : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧
                  (Hp i).natDegree = 2 ^ i :=
                fun i h1 hi => ⟨(htower i h1 hi).1, (htower i h1 hi).2.1⟩
              obtain ⟨h8m, h8d⟩ := obH8_good (k := k) (α := α)
                (htower2 1 (by omega) (by omega)) (htower2 2 (by omega) le_rfl)
              have hupdV : ∀ i, 1 ≤ i → i ≤ 3 →
                  ((Function.update Hp 3 (obH8 Hp k α)) i).Monic ∧
                  ((Function.update Hp 3 (obH8 Hp k α)) i).natDegree = 2 ^ i ∧
                  (∀ j, ((Function.update Hp 3 (obH8 Hp k α)) i).coeff j ∈ V) :=
                good_update_mem (m := 2) (H' := obH8 Hp k α) htower h8m h8d
                  le_rfl (by
                    intro j
                    have h := obH8_coeff_mem (K := V) (α := α) htower hpar hk3' j
                    refine SetLike.le_def.1 (sup_le le_rfl (adjoin_le ?_)) h
                    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
                    exact hvals g (by omega))
              have hconv3 : ((k - 1) / 2 - 1) * 2 ^ 3 = 4 * (k - 3) :=
                odd_band_conv_base' hpar (by omega)
              have hdec := ih ((k - 1) / 2) (by omega) (by omega) 3
                (Function.update Hp 3 (obH8 Hp k α)) (fun j => α (4 + j))
                (by omega) hupdV
                (by
                  intro r hr
                  rw [hconv3] at hr
                  have h := hvals (4 + r) (by omega)
                  rw [rSlot_ob_inner hpar hk3' (by omega) (by omega),
                    Nat.add_sub_cancel_left] at h
                  exact h)
                (t - 4) (by rw [hconv3]; omega)
              have h' : α (4 + (t - 4)) ∈ V := hdec
              rwa [show 4 + (t - 4) = t from by omega] at h'
            · have h := hvals t (by omega)
              rwa [rSlot_ob_band hpar hk3' htband] at h
        · -- odd main, `l ≥ 3`
          have hlne : ¬ l ≤ 2 := by omega
          have hp2 : 1 ≤ 2 ^ (l - 2) := Nat.one_le_pow _ _ (by omega)
          have hpl2 : 2 ^ (l - 2) + 2 ^ (l - 2) = 2 ^ (l - 1) := by
            conv_rhs => rw [show l - 1 = (l - 2) + 1 from by omega, pow_succ]
            ring
          have hb0lb : 2 ^ l ≤ (k - 2) * 2 ^ l := by
            have := Nat.mul_le_mul_right (2 ^ l) (show 1 ≤ k - 2 from by omega)
            omega
          have hd : (k - 1) * 2 ^ l = (k - 2) * 2 ^ l + 2 ^ l := by
            have h1 : k - 2 + 1 = k - 1 := by omega
            calc (k - 1) * 2 ^ l = (k - 2 + 1) * 2 ^ l := by rw [h1]
              _ = (k - 2) * 2 ^ l + 2 ^ l := by ring
          rcases Nat.eq_zero_or_pos t with ht0 | htpos
          · subst ht0
            have h := hvals 0 (by omega)
            rwa [rSlot_odd_zero hpar hk3' hlne] at h
          · rcases Nat.lt_or_ge t (2 ^ l) with htlo | htmid
            · -- the low peel slice at height `l`
              have hdec := peel_param_from_slots (Hp := Hp) l (V := V)
                (fun i h1 h2' => htower i h1 (by omega)) (by omega)
                (fun j => α (1 + j))
                (by
                  intro g hg
                  have h := hvals (1 + g) (by omega)
                  rw [rSlot_odd_mers hpar hk3' hlne (by omega) (by omega),
                    Nat.add_sub_cancel_left] at h
                  exact h)
              have h := hdec (t - 1) (by omega)
              have h' : α (1 + (t - 1)) ∈ V := h
              rwa [show 1 + (t - 1) = t from by omega] at h'
            · rcases Nat.lt_or_ge t ((k - 2) * 2 ^ l) with htin | htband
              · -- inner recursion
                have htower2 : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧
                    (Hp i).natDegree = 2 ^ i :=
                  fun i h1 hi => ⟨(htower i h1 hi).1, (htower i h1 hi).2.1⟩
                obtain ⟨hHm', hHd'⟩ := oddH_good (k := k) (α := α) htower2 hl3
                have hupdV : ∀ i, 1 ≤ i → i ≤ l + 1 →
                    ((Function.update Hp (l + 1) (oddH Hp k l α)) i).Monic ∧
                    ((Function.update Hp (l + 1) (oddH Hp k l α)) i).natDegree
                      = 2 ^ i ∧
                    (∀ j, ((Function.update Hp (l + 1) (oddH Hp k l α)) i).coeff j
                      ∈ V) :=
                  good_update_mem (m := l) (H' := oddH Hp k l α) htower hHm' hHd'
                    le_rfl (by
                      intro j
                      have h := oddH_coeff_mem (K := V) (α := α) htower hpar hk3'
                        hlne h2 j
                      refine SetLike.le_def.1 (sup_le le_rfl (adjoin_le ?_)) h
                      rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
                      exact hvals g (by omega))
                have hconv : ((k - 1) / 2 - 1) * 2 ^ (l + 1) = (k - 3) * 2 ^ l :=
                  odd_band_conv hpar (by omega)
                have hb3 : (k - 3) * 2 ^ l + 2 ^ l = (k - 2) * 2 ^ l := by
                  have h1 : k - 3 + 1 = k - 2 := by omega
                  calc (k - 3) * 2 ^ l + 2 ^ l = (k - 3 + 1) * 2 ^ l := by ring
                    _ = (k - 2) * 2 ^ l := by rw [h1]
                have hdec := ih ((k - 1) / 2) (by omega) (by omega) (l + 1)
                  (Function.update Hp (l + 1) (oddH Hp k l α))
                  (fun j => α (2 ^ l + j)) (by omega) hupdV
                  (by
                    intro r hr
                    rw [hconv] at hr
                    have h := hvals (2 ^ l + r) (by omega)
                    rw [rSlot_odd_inner hpar hk3' hlne (by omega) (by omega),
                      Nat.add_sub_cancel_left] at h
                    exact h)
                  (t - 2 ^ l) (by rw [hconv]; omega)
                have h' : α (2 ^ l + (t - 2 ^ l)) ∈ V := hdec
                rwa [show 2 ^ l + (t - 2 ^ l) = t from by omega] at h'
              · -- the odd band
                rcases eq_or_lt_of_le htband with hteq | htgt
                · have h := hvals ((k - 2) * 2 ^ l) (by omega)
                  rw [rSlot_odd_b0 hpar hk3' hlne] at h
                  rwa [← hteq]
                · rcases Nat.lt_or_ge t ((k - 2) * 2 ^ l + 2 ^ (l - 2)) with
                    hto3 | hto3'
                  · -- the oS3 slice at height `l - 2`
                    have hdec := peel_param_from_slots (Hp := Hp) (l - 2) (V := V)
                      (fun i h1 h2' => htower i h1 (by omega)) (by omega)
                      (fun j => α ((k - 2) * 2 ^ l + 1 + j))
                      (by
                        intro g hg
                        have h := hvals ((k - 2) * 2 ^ l + 1 + g) (by omega)
                        rw [rSlot_odd_oS3 hpar hk3' hlne (by omega) (by omega),
                          show (k - 2) * 2 ^ l + 1 + g - (k - 2) * 2 ^ l - 1 = g
                            from by omega] at h
                        exact h)
                    have h := hdec (t - (k - 2) * 2 ^ l - 1) (by omega)
                    have h' : α ((k - 2) * 2 ^ l + 1
                        + (t - (k - 2) * 2 ^ l - 1)) ∈ V := h
                    rwa [show (k - 2) * 2 ^ l + 1 + (t - (k - 2) * 2 ^ l - 1) = t
                      from by omega] at h'
                  · rcases eq_or_lt_of_le hto3' with hteq2 | htgt2
                    · have h := hvals ((k - 2) * 2 ^ l + 2 ^ (l - 2)) (by omega)
                      rw [rSlot_odd_eps hpar hk3' hlne] at h
                      rwa [← hteq2]
                    · rcases Nat.lt_or_ge t ((k - 2) * 2 ^ l + 2 ^ (l - 1)) with
                        hto2 | hto2'
                      · -- the oS2 slice at height `l - 2`
                        have hdec := peel_param_from_slots (Hp := Hp) (l - 2)
                          (V := V)
                          (fun i h1 h2' => htower i h1 (by omega)) (by omega)
                          (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 2) + 1 + j))
                          (by
                            intro g hg
                            have h := hvals ((k - 2) * 2 ^ l + 2 ^ (l - 2) + 1 + g)
                              (by omega)
                            rw [rSlot_odd_oS2 hpar hk3' hlne (by omega) (by omega),
                              show (k - 2) * 2 ^ l + 2 ^ (l - 2) + 1 + g
                                  - (k - 2) * 2 ^ l - 2 ^ (l - 2) - 1 = g from
                                by omega] at h
                            exact h)
                        have h := hdec (t - (k - 2) * 2 ^ l - 2 ^ (l - 2) - 1)
                          (by omega)
                        have h' : α ((k - 2) * 2 ^ l + 2 ^ (l - 2) + 1
                            + (t - (k - 2) * 2 ^ l - 2 ^ (l - 2) - 1)) ∈ V := h
                        rwa [show (k - 2) * 2 ^ l + 2 ^ (l - 2) + 1
                            + (t - (k - 2) * 2 ^ l - 2 ^ (l - 2) - 1) = t from
                          by omega] at h'
                      · rcases eq_or_lt_of_le hto2' with hteq3 | htgt3
                        · have h := hvals ((k - 2) * 2 ^ l + 2 ^ (l - 1)) (by omega)
                          rw [rSlot_odd_delta hpar hk3' hlne] at h
                          rwa [← hteq3]
                        · -- the tS1 slice at height `l - 1`
                          have hdec := peel_param_from_slots (Hp := Hp) (l - 1)
                            (V := V)
                            (fun i h1 h2' => htower i h1 (by omega)) (by omega)
                            (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
                            (by
                              intro g hg
                              have h := hvals
                                ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g) (by omega)
                              rw [rSlot_odd_tS1 hpar hk3' hlne (by omega),
                                show (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + g
                                    - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1 = g from
                                  by omega] at h
                              exact h)
                          have h := hdec
                            (t - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1) (by omega)
                          have h' : α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1
                              + (t - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1)) ∈ V := h
                          rwa [show (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1
                              + (t - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1) = t from
                            by omega] at h'


/-- Combined coefficients of the remainder pair, from the `T`-pair and the two top
powers: `R⁽ⁱ⁾ = T⁽ⁱ⁾ - (power)ᵏ` termwise. -/
theorem Rpair_combined_coeff_mem {V : Subalgebra R A} {Hp : ℕ → A[X]} {Ht : A[X]}
    {k l : ℕ} {α : ℕ → A}
    (hT₁ : ∀ j, (Tpair Hp Ht k l α).1.coeff j ∈ V)
    (hT₂ : ∀ j, (Tpair Hp Ht k l α).2.coeff j ∈ V)
    (hHl : ∀ j, (Hp l).coeff j ∈ V) (hHt : ∀ j, Ht.coeff j ∈ V) :
    ∀ i, (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff i ∈ V := by
  obtain ⟨hsp₁, hsp₂⟩ := Tpair_eq_pow_add_R (Hp := Hp) (Ht := Ht) (k := k)
    (l := l) (α := α)
  have hR₁ : ∀ j, (Rpair Hp Ht k l α).1.coeff j ∈ V := by
    intro j
    have hkey : (Rpair Hp Ht k l α).1.coeff j
        = (Tpair Hp Ht k l α).1.coeff j - (Hp l ^ k).coeff j := by
      rw [hsp₁, coeff_add]
      ring
    rw [hkey]
    exact sub_mem (hT₁ j) (coeff_mem_pow hHl k j)
  have hR₂ : ∀ j, (Rpair Hp Ht k l α).2.coeff j ∈ V := by
    intro j
    have hkey : (Rpair Hp Ht k l α).2.coeff j
        = (Tpair Hp Ht k l α).2.coeff j - (Ht ^ k).coeff j := by
      rw [hsp₂, coeff_add]
      ring
    rw [hkey]
    exact sub_mem (hT₂ j) (coeff_mem_pow hHt k j)
  intro i
  cases i with
  | zero => rw [coeff_combined_zero]; exact hR₂ 0
  | succ m => rw [coeff_combined]; exact add_mem (hR₁ m) (hR₂ (m + 1))

/-- **Full `Rk2l` parameter extraction**: from the combined remainder coefficients and
the tower data, every raw parameter of the block is recovered. -/
theorem Rk2l_extract {K V : Subalgebra R A} {Hp : ℕ → A[X]} {Ht : A[X]}
    (k : ℕ) (hk : 1 ≤ k) (l : ℕ) (α : ℕ → A) (hl : 2 ≤ l)
    (htower : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) (hKt : ∀ j, Ht.coeff j ∈ K)
    (hsd : l = 2 → ¬ k % 2 = 0 → 3 ≤ k → ∃ ρ : A, Ht - Hp 2 = C ρ)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ k → IsUnit (((n : ℕ) : ℤ) : R))
    (h2 : IsUnit (2 : R))
    (hKV : K ≤ V)
    (hcomb : ∀ i, (combined (Rpair Hp Ht k l α).1 (Rpair Hp Ht k l α).2).coeff i
      ∈ V) :
    ∀ t, t < (k - 1) * 2 ^ l → α t ∈ V := by
  have hcert := Rk2l_triangular k hk l Hp Ht α K hl htower hHt hdHt hKt hsd hadm
  have hvals : ∀ r, r < (k - 1) * 2 ^ l → rSlot k l α (A := A) r ∈ V := by
    intro r hr
    have h := hcert.param_mem r hr
    refine SetLike.le_def.1 (sup_le hKV (adjoin_le ?_)) h
    rintro _ ⟨i, ⟨-, -⟩, rfl⟩
    exact hcomb i
  exact rSlot_param_mem h2 k hk l Hp α hl
    (fun i h1 hi => ⟨(htower i h1 hi).1, (htower i h1 hi).2.1,
      fun j => hKV ((htower i h1 hi).2.2 j)⟩) hvals

end FastPoly
