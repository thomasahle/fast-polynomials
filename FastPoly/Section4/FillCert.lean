import FastPoly.Recover.Triangular
import FastPoly.Section4.FillRec
import FastPoly.Recover.Multiplication
import Mathlib.Tactic.LinearCombination

/-!
# Generic fill-chain certificates

The fill-step invariant used by the auxiliary odd-degree gadgets (validated in
`tools/fill_stage_cert.py`): pair-form `CoeffTriangular` certificates over the
`fillSlot` slot layout, with the dead tail consumed by the `b`/`q` bands.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The fill-step local slot function (local fill-chain invariant):
row `0` is the second-component additive constant, rows `[1, D)` read the
`qh`-certificate slots, rows `[D, m)` the shifted input slots, row `m` the
multiplier scalar `b`, rows `[m+1, m+D/2)` the `q`-certificate slots, and the
new dead tail `[m+D/2, m+D-2)` is zero. -/
def fillSlot (D m : ℕ) (βin βq βqh : ℕ → A) (b ah : A) : ℕ → A := fun r =>
  if r = 0 then ah
  else if r < D then βqh (r - 1)
  else if r < m then βin (r - D)
  else if r = m then b
  else if r < m + D / 2 then βq (r - m - 1)
  else 0

/-- Band evaluation of `fillSlot`: row `0`. -/
theorem fillSlot_zero (D m : ℕ) (βin βq βqh : ℕ → A) (b ah : A) :
    fillSlot D m βin βq βqh b ah 0 = ah := rfl

/-- Band evaluation of `fillSlot`: the `qh`-band `[1, D)`. -/
theorem fillSlot_qh (D m : ℕ) (βin βq βqh : ℕ → A) (b ah : A) (r : ℕ)
    (h1 : 1 ≤ r) (h2 : r < D) :
    fillSlot D m βin βq βqh b ah r = βqh (r - 1) := by
  unfold fillSlot
  rw [if_neg (by omega), if_pos h2]

/-- Band evaluation of `fillSlot`: the shifted input band `[D, m)`. -/
theorem fillSlot_in (D m : ℕ) (βin βq βqh : ℕ → A) (b ah : A) (r : ℕ)
    (h1 : D ≤ r) (h2 : r < m) (hD : 0 < D) :
    fillSlot D m βin βq βqh b ah r = βin (r - D) := by
  unfold fillSlot
  rw [if_neg (by omega), if_neg (by omega), if_pos h2]

/-- Band evaluation of `fillSlot`: the multiplier row `m`. -/
theorem fillSlot_b (D m : ℕ) (βin βq βqh : ℕ → A) (b ah : A)
    (h1 : 0 < m) (h2 : D ≤ m) :
    fillSlot D m βin βq βqh b ah m = b := by
  unfold fillSlot
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- Band evaluation of `fillSlot`: the `q`-band `(m, m + D/2)`. -/
theorem fillSlot_q (D m : ℕ) (βin βq βqh : ℕ → A) (b ah : A) (r : ℕ)
    (h1 : m < r) (h2 : r < m + D / 2) (h3 : D ≤ m) :
    fillSlot D m βin βq βqh b ah r = βq (r - m - 1) := by
  unfold fillSlot
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos h2]

/-- Band evaluation of `fillSlot`: the dead tail `[m + D/2, ∞)`. -/
theorem fillSlot_tail (D m : ℕ) (βin βq βqh : ℕ → A) (b ah : A) (r : ℕ)
    (h1 : m + D / 2 ≤ r) (h2 : 2 ≤ D) (h3 : D ≤ m) :
    fillSlot D m βin βq βqh b ah r = 0 := by
  unfold fillSlot
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

section fillStepCert

variable {K : Subalgebra R A} {βin βq βqh : ℕ → A} {D m : ℕ}
  {H q qh S₁ S₂ : A[X]} {b ah : A}

/-- Window membership toolkit for the fill-step slot function. -/
theorem fillSlot_windows
    (hdead : ∀ r, m - D ≤ r → r < m - 2 → βin r = 0)
    (h4 : 4 ≤ D) (hm : D + 2 ≤ m) :
    (∀ lo t, 1 ≤ lo → lo ≤ t + 1 → t < D - 1 →
        βqh t ∈ K ⊔ adjoin R ((fillSlot D m βin βq βqh b ah (A := A)) '' Set.Ico lo (m + D - 2)))
    ∧ (∀ lo g, g < m - 2 → lo ≤ g + D →
        βin g ∈ K ⊔ adjoin R ((fillSlot D m βin βq βqh b ah (A := A)) '' Set.Ico lo (m + D - 2)))
    ∧ (∀ lo t, lo ≤ m + 1 + t → t < D / 2 - 1 →
        βq t ∈ K ⊔ adjoin R ((fillSlot D m βin βq βqh b ah (A := A)) '' Set.Ico lo (m + D - 2))) := by
  set γ := fillSlot D m βin βq βqh b ah (A := A) with hγ
  have hD2 : 2 ≤ D / 2 := by omega
  have hD2' : D / 2 ≤ D - 2 := by omega
  have hslot : ∀ lo t, lo ≤ t → t < m + D - 2 →
      γ t ∈ K ⊔ adjoin R (γ '' Set.Ico lo (m + D - 2)) := fun lo t h1 h2 =>
    (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨h1, h2⟩, rfl⟩)
  refine ⟨fun lo t hlo1 hlo ht => ?_, fun lo g hg hlo => ?_, fun lo t hlo ht => ?_⟩
  · have hv : γ (t + 1) = βqh t := by
      show fillSlot D m βin βq βqh b ah (t + 1) = βqh t
      rw [fillSlot_qh D m βin βq βqh b ah (t + 1) (by omega) (by omega),
        Nat.add_sub_cancel]
    exact hv ▸ hslot lo (t + 1) (by omega) (by omega)
  · rcases Nat.lt_or_ge g (m - D) with hlow | hhigh
    · have hv : γ (g + D) = βin g := by
        show fillSlot D m βin βq βqh b ah (g + D) = βin g
        rw [fillSlot_in D m βin βq βqh b ah (g + D) (by omega) (by omega) (by omega),
          Nat.add_sub_cancel]
      exact hv ▸ hslot lo (g + D) (by omega) (by omega)
    · rw [hdead g hhigh hg]
      exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  · have hv : γ (m + 1 + t) = βq t := by
      show fillSlot D m βin βq βqh b ah (m + 1 + t) = βq t
      rw [fillSlot_q D m βin βq βqh b ah (m + 1 + t) (by omega) (by omega) (by omega),
        show m + 1 + t - m - 1 = t from by omega]
    exact hv ▸ hslot lo (m + 1 + t) (by omega) (by omega)

/-- Supports half of the fill-step certificate, first component. -/
theorem fillStep_supp₁
    (hHd : H.natDegree = D) (hHK : ∀ j, H.coeff j ∈ K)
    (hd₁ : S₁.natDegree = m)
    (hin : CoeffTriangular K βin (fun _ => (1 : R)) (m - 2) (S₁ - X ^ m) (S₂ - X ^ m))
    (hdead : ∀ r, m - D ≤ r → r < m - 2 → βin r = 0)
    (hq : CoeffTriangular K βq (fun _ => (1 : R)) (D / 2 - 1) 0 (q - X ^ (D / 2 - 1)))
    (hqd : q.natDegree = D / 2 - 1)
    (hqh : CoeffTriangular K βqh (fun _ => (1 : R)) (D - 1) 0 (qh - X ^ (D - 1)))
    (h4 : 4 ≤ D) (hm : D + 2 ≤ m) :
    ∀ j, ((H + q) * S₁ + qh - X ^ (m + D)).coeff j
      ∈ K ⊔ adjoin R ((fillSlot D m βin βq βqh b ah (A := A)) '' Set.Ico (j + 1) (m + D - 2)) := by
  obtain ⟨hqhW, hinW, hqW⟩ := fillSlot_windows (K := K) (βq := βq) (βqh := βqh) (b := b) (ah := ah) hdead h4 hm
  intro j
  set V := K ⊔ adjoin R ((fillSlot D m βin βq βqh b ah (A := A)) '' Set.Ico (j + 1) (m + D - 2)) with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  -- windowed coefficient memberships
  have hS₁V : ∀ c, j ≤ c + D → S₁.coeff c ∈ V := by
    intro c hc
    refine coeff_mem_of_sub_pow m c ?_
    refine mem_of_sup_adjoin_le (le_sup_left : K ≤ _) ?_ (hin.supp₁ c)
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hinW (j + 1) g hg2 (by omega)
  have hqV : ∀ a, j ≤ m + a → q.coeff a ∈ V := by
    intro a ha
    refine coeff_mem_of_sub_pow (D / 2 - 1) a ?_
    refine mem_of_sup_adjoin_le (le_sup_left : K ≤ _) ?_ (hq.supp₂ a)
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hqW (j + 1) g (by omega) hg2
  have hqhV : qh.coeff j ∈ V := by
    refine coeff_mem_of_sub_pow (D - 1) j ?_
    refine mem_of_sup_adjoin_le (le_sup_left : K ≤ _) ?_ (hqh.supp₂ j)
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hqhW (j + 1) g (by omega) (by omega) hg2
  rw [coeff_sub, coeff_add, coeff_mul]
  refine Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.sum_mem _ fun x hx => ?_) hqhV) ?_
  · have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rw [coeff_add, add_mul]
    refine Subalgebra.add_mem _ ?_ ?_
    · rcases Nat.lt_or_ge D x.1 with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1)) (hS₁V x.2 (by omega))
    · rcases Nat.lt_or_ge (D / 2 - 1) x.1 with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
        · rw [show S₁.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
            mul_zero]
          exact Subalgebra.zero_mem _
        · exact Subalgebra.mul_mem _ (hqV x.1 (by omega)) (hS₁V x.2 (by omega))
  · exact coeff_X_pow_mem V _ _

/-- Supports half of the fill-step certificate, second component. -/
theorem fillStep_supp₂
    (hHd : H.natDegree = D) (hHK : ∀ j, H.coeff j ∈ K)
    (hd₂ : S₂.natDegree = m)
    (hin : CoeffTriangular K βin (fun _ => (1 : R)) (m - 2) (S₁ - X ^ m) (S₂ - X ^ m))
    (hdead : ∀ r, m - D ≤ r → r < m - 2 → βin r = 0)
    (h4 : 4 ≤ D) (hm : D + 2 ≤ m) :
    ∀ j, ((H + C b) * S₂ + C ah - X ^ (m + D)).coeff j
      ∈ K ⊔ adjoin R ((fillSlot D m βin βq βqh b ah (A := A)) '' Set.Ico j (m + D - 2)) := by
  obtain ⟨hqhW, hinW, hqW⟩ := fillSlot_windows (K := K) (βq := βq) (βqh := βqh) (b := b) (ah := ah) hdead h4 hm
  intro j
  set γ := fillSlot D m βin βq βqh b ah (A := A) with hγdef
  set V := K ⊔ adjoin R (γ '' Set.Ico j (m + D - 2)) with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  have hslot : ∀ t, j ≤ t → t < m + D - 2 → γ t ∈ V := fun t h1 h2 =>
    (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨h1, h2⟩, rfl⟩)
  have hγ0 : γ 0 = ah := rfl
  have hγm : γ m = b := fillSlot_b D m βin βq βqh b ah (by omega) (by omega)
  have hS₂V : ∀ c, j ≤ c + D → S₂.coeff c ∈ V := by
    intro c hc
    refine coeff_mem_of_sub_pow m c ?_
    refine mem_of_sup_adjoin_le (le_sup_left : K ≤ _) ?_ (hin.supp₂ c)
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hinW j g hg2 (by omega)
  rw [coeff_sub, coeff_add, coeff_mul]
  refine Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.sum_mem _ fun x hx => ?_) ?_) ?_
  · have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
    rw [coeff_add, add_mul]
    refine Subalgebra.add_mem _ ?_ ?_
    · rcases Nat.lt_or_ge D x.1 with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1)) (hS₂V x.2 (by omega))
    · rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
      · rw [h0, coeff_C_zero]
        rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
        · rw [show S₂.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
            mul_zero]
          exact Subalgebra.zero_mem _
        · refine Subalgebra.mul_mem _ ?_ (hS₂V x.2 (by omega))
          exact hγm ▸ hslot m (by omega) (by omega)
      · rw [coeff_C, if_neg (by omega), zero_mul]
        exact Subalgebra.zero_mem _
  · rw [coeff_C]
    split
    · exact hγ0 ▸ hslot 0 (by omega) (by omega)
    · exact Subalgebra.zero_mem _
  · exact coeff_X_pow_mem V _ _

/-- Pivot rows below the multiplier band: row 0 (`ah`), the `qh`-band `[1, D)`, and the
shifted input band `[D, m)` (the input certificate's pivots, dead rows included). -/
theorem fillStep_pivot_low (hHm : H.Monic) (hHd : H.natDegree = D)
    (hHK : ∀ j, H.coeff j ∈ K)
    (hd₁ : S₁.natDegree = m) (hd₂ : S₂.natDegree = m)
    (hin : CoeffTriangular K βin (fun _ => (1 : R)) (m - 2) (S₁ - X ^ m) (S₂ - X ^ m))
    (hdead : ∀ r, m - D ≤ r → r < m - 2 → βin r = 0)
    (hq : CoeffTriangular K βq (fun _ => (1 : R)) (D / 2 - 1) 0 (q - X ^ (D / 2 - 1)))
    (hqd : q.natDegree = D / 2 - 1)
    (hqh : CoeffTriangular K βqh (fun _ => (1 : R)) (D - 1) 0 (qh - X ^ (D - 1)))
    (hqhm : qh.Monic) (hqhd : qh.natDegree = D - 1)
    (h4 : 4 ≤ D) (hm : D + 2 ≤ m) :
    ∀ j, j < m → ∃ F ∈ K ⊔ adjoin R
        ((fillSlot D m βin βq βqh b ah (A := A)) '' Set.Ico (j + 1) (m + D - 2)),
      (combined ((H + q) * S₁ + qh - X ^ (m + D))
          ((H + C b) * S₂ + C ah - X ^ (m + D))).coeff j
        = algebraMap R A 1 * (fillSlot D m βin βq βqh b ah (A := A)) j + F := by
  obtain ⟨hqhW, hinW, hqW⟩ := fillSlot_windows (K := K) (βq := βq) (βqh := βqh) (b := b) (ah := ah) hdead h4 hm
  intro j hj
  set γ := fillSlot D m βin βq βqh b ah (A := A) with hγdef
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) (m + D - 2)) with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  have hslot : ∀ t, j + 1 ≤ t → t < m + D - 2 → γ t ∈ V := fun t h1 h2 =>
    (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨h1, h2⟩, rfl⟩)
  -- generic combined-with-zero collapse (for the q/qh certificates)
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  have hγm : γ m = b := fillSlot_b D m βin βq βqh b ah (by omega) (by omega)
  -- strict-window coefficient memberships
  have hS₁V : ∀ c, j + 1 ≤ c + 1 + D → S₁.coeff c ∈ V := by
    intro c hc
    refine coeff_mem_of_sub_pow m c ?_
    refine mem_of_sup_adjoin_le (le_sup_left : K ≤ _) ?_ (hin.supp₁ c)
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hinW (j + 1) g hg2 (by omega)
  have hS₂V : ∀ c, j + 1 ≤ c + D → S₂.coeff c ∈ V := by
    intro c hc
    refine coeff_mem_of_sub_pow m c ?_
    refine mem_of_sup_adjoin_le (le_sup_left : K ≤ _) ?_ (hin.supp₂ c)
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hinW (j + 1) g hg2 (by omega)
  have hqV : ∀ a, j + 1 ≤ m + 1 + a → q.coeff a ∈ V := by
    intro a ha
    refine coeff_mem_of_sub_pow (D / 2 - 1) a ?_
    refine mem_of_sup_adjoin_le (le_sup_left : K ≤ _) ?_ (hq.supp₂ a)
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hqW (j + 1) g (by omega) hg2
  have hqhK : ∀ t, D - 1 ≤ t → qh.coeff t ∈ K := by
    intro t ht
    rcases Nat.lt_or_ge (D - 1) t with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · have ht' : t = D - 1 := by omega
      rw [ht', ← hqhd, hqhm.coeff_natDegree]
      exact Subalgebra.one_mem _
  -- γ values on the low bands
  have hγ0 : γ 0 = ah := rfl
  have hγqh : ∀ r, 1 ≤ r → r < D → γ r = βqh (r - 1) :=
    fun r h1 h2 => fillSlot_qh D m βin βq βqh b ah r h1 h2
  have hγin : ∀ r, D ≤ r → r < m → γ r = βin (r - D) :=
    fun r h1 h2 => fillSlot_in D m βin βq βqh b ah r h1 h2 (by omega)
  -- boundary coefficients of the multipliers
  have hHqD : (H + q).coeff D = 1 := by
    rw [coeff_add, show q.coeff D = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
      add_zero, ← hHd]
    exact hHm.coeff_natDegree
  have hHbD : (H + C b).coeff D = 1 := by
    rw [coeff_add, coeff_C, if_neg (by omega), add_zero, ← hHd]
    exact hHm.coeff_natDegree
  -- filtered-rest memberships for the two products at boundary x.1 = D
  have hrest₁ : (∀ x ∈ (Finset.antidiagonal (j - 1)).filter (fun x : ℕ × ℕ => x.1 ≠ D),
      (H + q).coeff x.1 * S₁.coeff x.2 ∈ V) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    have hxa : x.1 + x.2 = j - 1 := Finset.mem_antidiagonal.1 hx1
    rw [coeff_add, add_mul]
    refine Subalgebra.add_mem _ ?_ ?_
    · rcases Nat.lt_or_ge D x.1 with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1)) (hS₁V x.2 (by omega))
    · rcases Nat.lt_or_ge (D / 2 - 1) x.1 with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
        · rw [show S₁.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
            mul_zero]
          exact Subalgebra.zero_mem _
        · exact Subalgebra.mul_mem _ (hqV x.1 (by omega)) (hS₁V x.2 (by omega))
  have hrest₂ : (∀ x ∈ (Finset.antidiagonal j).filter (fun x : ℕ × ℕ => x.1 ≠ D),
      (H + C b).coeff x.1 * S₂.coeff x.2 ∈ V) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx1
    rw [coeff_add, add_mul]
    refine Subalgebra.add_mem _ ?_ ?_
    · rcases Nat.lt_or_ge D x.1 with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1)) (hS₂V x.2 (by omega))
    · rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
      · rw [h0, coeff_C_zero]
        rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
        · rw [show S₂.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
            mul_zero]
          exact Subalgebra.zero_mem _
        · refine Subalgebra.mul_mem _ ?_ (hS₂V x.2 (by omega))
          exact hγm ▸ hslot m (by omega) (by omega)
      · rw [coeff_C, if_neg (by omega), zero_mul]
        exact Subalgebra.zero_mem _
  -- X-power kills at active rows
  have hXk₁ : ((X : A[X]) ^ (m + D)).coeff (j - 1) = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  have hXk₂ : ((X : A[X]) ^ (m + D)).coeff j = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  cases j with
  | zero =>
    -- row 0: pivot ah
    refine ⟨(H.coeff 0 + b) * S₂.coeff 0, ?_, ?_⟩
    · refine Subalgebra.mul_mem _ (Subalgebra.add_mem _ (hKV _ (hHK 0)) ?_)
        (hS₂V 0 (by omega))
      exact hγm ▸ hslot m (by omega) (by omega)
    · rw [coeff_combined_zero, coeff_sub, coeff_X_pow, if_neg (by omega), sub_zero,
        coeff_add, coeff_C_zero, mul_coeff_zero, coeff_add, coeff_C_zero, hγ0,
        map_one, one_mul]
      ring
  | succ t =>
    have hcO : (combined ((H + q) * S₁ + qh - X ^ (m + D))
        ((H + C b) * S₂ + C ah - X ^ (m + D))).coeff (t + 1)
        = ((H + q) * S₁).coeff t + qh.coeff t
          + (((H + C b) * S₂).coeff (t + 1) + (C ah : A[X]).coeff (t + 1)) := by
      rw [coeff_combined, coeff_sub, coeff_sub, coeff_X_pow, coeff_X_pow,
        if_neg (by omega), if_neg (by omega), sub_zero, sub_zero, coeff_add, coeff_add]
    have hCah : (C ah : A[X]).coeff (t + 1) = 0 := by
      rw [coeff_C, if_neg (by omega)]
    rcases Nat.lt_or_ge (t + 1) D with hband | hband
    · -- qh band: pivot βqh t
      obtain ⟨F', hF', hFe⟩ := hqh.pivot t (by omega)
      rw [hcomb0] at hFe
      have hqht : qh.coeff t = βqh t + F' := by
        have hXq : ((X : A[X]) ^ (D - 1)).coeff t = 0 := by
          rw [coeff_X_pow, if_neg (by omega)]
        have := hFe
        rw [coeff_sub, hXq, sub_zero, map_one, one_mul] at this
        exact this
      have hmul₁ : ((H + q) * S₁).coeff t ∈ V := by
        rw [coeff_mul]
        refine Subalgebra.sum_mem _ fun x hx => ?_
        have hxa : x.1 + x.2 = t := Finset.mem_antidiagonal.1 hx
        rw [coeff_add, add_mul]
        refine Subalgebra.add_mem _ ?_ ?_
        · rcases Nat.lt_or_ge D x.1 with hgt | hle
          · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
            exact Subalgebra.zero_mem _
          · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1))
              (hS₁V x.2 (by omega))
        · rcases Nat.lt_or_ge (D / 2 - 1) x.1 with hgt | hle
          · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
            exact Subalgebra.zero_mem _
          · exact Subalgebra.mul_mem _ (hqV x.1 (by omega))
              (hS₁V x.2 (by omega))
      have hmul₂ : ((H + C b) * S₂).coeff (t + 1) ∈ V := by
        rw [coeff_mul]
        refine Subalgebra.sum_mem _ fun x hx => ?_
        have hxa : x.1 + x.2 = t + 1 := Finset.mem_antidiagonal.1 hx
        rw [coeff_add, add_mul]
        refine Subalgebra.add_mem _ ?_ ?_
        · rcases Nat.lt_or_ge D x.1 with hgt | hle
          · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
            exact Subalgebra.zero_mem _
          · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1)) (hS₂V x.2 (by omega))
        · rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
          · rw [h0, coeff_C_zero]
            refine Subalgebra.mul_mem _ ?_ (hS₂V x.2 (by omega))
            exact hγm ▸ hslot m (by omega) (by omega)
          · rw [coeff_C, if_neg (by omega), zero_mul]
            exact Subalgebra.zero_mem _
      have hF'V : F' ∈ V := by
        refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF'
        rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
        exact hqhW (t + 2) g (by omega) (by omega) hg2
      refine ⟨F' + (((H + q) * S₁).coeff t + ((H + C b) * S₂).coeff (t + 1)), ?_, ?_⟩
      · exact Subalgebra.add_mem _ hF'V (Subalgebra.add_mem _ hmul₁ hmul₂)
      · rw [hcO, hCah, add_zero, hqht, hγqh (t + 1) (by omega) hband,
          Nat.add_sub_cancel, map_one, one_mul]
        ring
    · -- shifted input band: pivot βin (t + 1 - D)
      obtain ⟨F', hF', hFe⟩ := hin.pivot (t + 1 - D) (by omega)
      have hsplit₁ := coeff_mul_split_fst (H + q) S₁ t D
      have hsplit₂ := coeff_mul_split_fst (H + C b) S₂ (t + 1) D
      have hbnd : (if D ≤ t then (H + q).coeff D * S₁.coeff (t - D) else 0)
          + (if D ≤ t + 1 then (H + C b).coeff D * S₂.coeff (t + 1 - D) else 0)
          = (combined (S₁ - X ^ m) (S₂ - X ^ m)).coeff (t + 1 - D) := by
        rcases Nat.lt_or_ge t D with h0 | h1
        · -- g = 0 (t + 1 = D): no first-component boundary
          rw [if_neg (by omega), if_pos (by omega), hHbD, one_mul, zero_add,
            show t + 1 - D = 0 from by omega, coeff_combined_zero, coeff_sub,
            coeff_X_pow, if_neg (by omega), sub_zero]
        · rw [if_pos h1, if_pos (by omega), hHqD, hHbD, one_mul, one_mul,
            show t + 1 - D = (t - D) + 1 from by omega, coeff_combined,
            coeff_sub, coeff_sub, coeff_X_pow, coeff_X_pow, if_neg (by omega),
            if_neg (by omega), sub_zero, sub_zero]
      have hqhKt : qh.coeff t ∈ K := hqhK t (by omega)
      have hF'V : F' ∈ V := by
        refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF'
        rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
        exact hinW (t + 2) g hg2 (by omega)
      refine ⟨F' + (∑ x ∈ (Finset.antidiagonal t).filter (fun x : ℕ × ℕ => x.1 ≠ D),
          (H + q).coeff x.1 * S₁.coeff x.2
        + qh.coeff t
        + ∑ x ∈ (Finset.antidiagonal (t + 1)).filter (fun x : ℕ × ℕ => x.1 ≠ D),
          (H + C b).coeff x.1 * S₂.coeff x.2), ?_, ?_⟩
      · refine Subalgebra.add_mem _ hF'V (Subalgebra.add_mem _ (Subalgebra.add_mem _
          (Subalgebra.sum_mem _ fun x hx => ?_) (hKV _ hqhKt))
          (Subalgebra.sum_mem _ fun x hx => ?_))
        · obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
          have hxa : x.1 + x.2 = t := Finset.mem_antidiagonal.1 hx1
          rw [coeff_add, add_mul]
          refine Subalgebra.add_mem _ ?_ ?_
          · rcases Nat.lt_or_ge D x.1 with hgt | hle
            · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
              exact Subalgebra.zero_mem _
            · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1)) (hS₁V x.2 (by omega))
          · rcases Nat.lt_or_ge (D / 2 - 1) x.1 with hgt | hle
            · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
              exact Subalgebra.zero_mem _
            · exact Subalgebra.mul_mem _ (hqV x.1 (by omega)) (hS₁V x.2 (by omega))
        · obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
          have hxa : x.1 + x.2 = t + 1 := Finset.mem_antidiagonal.1 hx1
          rw [coeff_add, add_mul]
          refine Subalgebra.add_mem _ ?_ ?_
          · rcases Nat.lt_or_ge D x.1 with hgt | hle
            · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
              exact Subalgebra.zero_mem _
            · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1)) (hS₂V x.2 (by omega))
          · rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
            · rw [h0, coeff_C_zero]
              rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
              · rw [show S₂.coeff x.2 = 0 from
                  coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
                exact Subalgebra.zero_mem _
              · refine Subalgebra.mul_mem _ ?_ (hS₂V x.2 (by omega))
                exact hγm ▸ hslot m (by omega) (by omega)
            · rw [coeff_C, if_neg (by omega), zero_mul]
              exact Subalgebra.zero_mem _
      · have hFe' : (if D ≤ t then (H + q).coeff D * S₁.coeff (t - D) else 0)
            + (if D ≤ t + 1 then (H + C b).coeff D * S₂.coeff (t + 1 - D) else 0)
            = βin (t + 1 - D) + F' := by
          rw [hbnd, hFe, map_one, one_mul]
        rw [hcO, hCah, add_zero, hsplit₁, hsplit₂, hγin (t + 1) hband (by omega),
          map_one, one_mul]
        linear_combination hFe'

/-- Pivot rows of the multiplier band and above: the `b`-pivot at row `m` (read against
`S₂`'s leading coefficient), the `q`-band `[m+1, m+D/2)` (read against `S₁`'s leading
coefficient), and the all-known dead tail `[m+D/2, m+D-2)`. -/
theorem fillStep_pivot_top (hHd : H.natDegree = D)
    (hHK : ∀ j, H.coeff j ∈ K)
    (hs₁m : S₁.Monic) (hd₁ : S₁.natDegree = m)
    (hs₂m : S₂.Monic) (hd₂ : S₂.natDegree = m)
    (hin : CoeffTriangular K βin (fun _ => (1 : R)) (m - 2) (S₁ - X ^ m) (S₂ - X ^ m))
    (hdead : ∀ r, m - D ≤ r → r < m - 2 → βin r = 0)
    (hq : CoeffTriangular K βq (fun _ => (1 : R)) (D / 2 - 1) 0 (q - X ^ (D / 2 - 1)))
    (hqm : q.Monic) (hqd : q.natDegree = D / 2 - 1)
    (hqhm : qh.Monic) (hqhd : qh.natDegree = D - 1)
    (h4 : 4 ≤ D) (hm : D + 2 ≤ m) :
    ∀ j, m ≤ j → j < m + D - 2 → ∃ F ∈ K ⊔ adjoin R
        ((fillSlot D m βin βq βqh b ah (A := A)) '' Set.Ico (j + 1) (m + D - 2)),
      (combined ((H + q) * S₁ + qh - X ^ (m + D))
          ((H + C b) * S₂ + C ah - X ^ (m + D))).coeff j
        = algebraMap R A 1 * (fillSlot D m βin βq βqh b ah (A := A)) j + F := by
  obtain ⟨hqhW, hinW, hqW⟩ := fillSlot_windows (K := K) (βq := βq) (βqh := βqh) (b := b) (ah := ah) hdead h4 hm
  intro j hj1 hj2
  set γ := fillSlot D m βin βq βqh b ah (A := A) with hγdef
  set V := K ⊔ adjoin R (γ '' Set.Ico (j + 1) (m + D - 2)) with hV
  have hKV : ∀ x : A, x ∈ K → x ∈ V := fun x hx => (le_sup_left : K ≤ _) hx
  have hslot : ∀ t, j + 1 ≤ t → t < m + D - 2 → γ t ∈ V := fun t h1 h2 =>
    (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨t, ⟨h1, h2⟩, rfl⟩)
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  -- K-membership of high input rows (windows land entirely in the dead range)
  have hdeadK : ∀ lo, m - D ≤ lo →
      (∀ x ∈ (βin '' Set.Ico lo (m - 2) : Set A), x ∈ K) := by
    intro lo hlo x hx
    obtain ⟨g, ⟨hg1, hg2⟩, rfl⟩ := hx
    rw [hdead g (by omega) hg2]
    exact Subalgebra.zero_mem _
  have hS₁K : ∀ c, m - D - 1 ≤ c → S₁.coeff c ∈ K := by
    intro c hc
    refine coeff_mem_of_sub_pow m c ?_
    exact mem_of_sup_adjoin_le le_rfl (hdeadK (c + 1) (by omega)) (hin.supp₁ c)
  have hS₂K : ∀ c, m - D ≤ c → S₂.coeff c ∈ K := by
    intro c hc
    refine coeff_mem_of_sub_pow m c ?_
    exact mem_of_sup_adjoin_le le_rfl (hdeadK c (by omega)) (hin.supp₂ c)
  have hqV : ∀ a, j + 1 ≤ m + 1 + a → q.coeff a ∈ V := by
    intro a ha
    refine coeff_mem_of_sub_pow (D / 2 - 1) a ?_
    refine mem_of_sup_adjoin_le (le_sup_left : K ≤ _) ?_ (hq.supp₂ a)
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact hqW (j + 1) g (by omega) hg2
  have hqhK : ∀ t, D - 1 ≤ t → qh.coeff t ∈ K := by
    intro t ht
    rcases Nat.lt_or_ge (D - 1) t with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · have ht' : t = D - 1 := by omega
      rw [ht', ← hqhd, hqhm.coeff_natDegree]
      exact Subalgebra.one_mem _
  have hγm : γ m = b := fillSlot_b D m βin βq βqh b ah (by omega) (by omega)
  have hγq : ∀ r, m + 1 ≤ r → r < m + D / 2 → γ r = βq (r - m - 1) :=
    fun r h1 h2 => fillSlot_q D m βin βq βqh b ah r (by omega) h2 (by omega)
  have hγz : ∀ r, m + D / 2 ≤ r → γ r = 0 :=
    fun r h1 => fillSlot_tail D m βin βq βqh b ah r h1 (by omega) (by omega)
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  have hcO : (combined ((H + q) * S₁ + qh - X ^ (m + D))
      ((H + C b) * S₂ + C ah - X ^ (m + D))).coeff (t + 1)
      = ((H + q) * S₁).coeff t + qh.coeff t
        + (((H + C b) * S₂).coeff (t + 1) + (C ah : A[X]).coeff (t + 1)) := by
    rw [coeff_combined, coeff_sub, coeff_sub, coeff_X_pow, coeff_X_pow,
      if_neg (by omega), if_neg (by omega), sub_zero, sub_zero, coeff_add, coeff_add]
  have hCah : (C ah : A[X]).coeff (t + 1) = 0 := by
    rw [coeff_C, if_neg (by omega)]
  have hqhKt : qh.coeff t ∈ K := hqhK t (by omega)
  -- membership of the second product minus its constant-row boundary is handled per band
  rcases Nat.lt_or_ge (t + 1) (m + 1) with hband | hband
  · -- row m: pivot b
    have hc : t + 1 = m := by omega
    -- membership of the full first product against mixed K/window data
    have hprod₁V : ((H + q) * S₁).coeff t ∈ V := by
      rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = t := Finset.mem_antidiagonal.1 hx
      rw [coeff_add, add_mul]
      refine Subalgebra.add_mem _ ?_ ?_
      · rcases Nat.lt_or_ge D x.1 with hgt | hle
        · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
          exact Subalgebra.zero_mem _
        · rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
          · rw [show S₁.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
              mul_zero]
            exact Subalgebra.zero_mem _
          · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1))
              (hKV _ (hS₁K x.2 (by omega)))
      · rcases Nat.lt_or_ge (D / 2 - 1) x.1 with hgt | hle
        · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
          exact Subalgebra.zero_mem _
        · rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
          · rw [show S₁.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
              mul_zero]
            exact Subalgebra.zero_mem _
          · exact Subalgebra.mul_mem _ (hqV x.1 (by omega))
              (hKV _ (hS₁K x.2 (by omega)))
    have hsplit₂ := coeff_mul_split_fst (H + C b) S₂ (t + 1) 0
    have hb0 : (H + C b).coeff 0 = H.coeff 0 + b := by
      rw [coeff_add, coeff_C_zero]
    have hS₂top : S₂.coeff (t + 1) = 1 := by
      rw [hc, ← hd₂]
      exact hs₂m.coeff_natDegree
    have hrest₂V : (∑ x ∈ (Finset.antidiagonal (t + 1)).filter
        (fun x : ℕ × ℕ => x.1 ≠ 0), (H + C b).coeff x.1 * S₂.coeff x.2) ∈ V := by
      refine Subalgebra.sum_mem _ fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      have hxa : x.1 + x.2 = t + 1 := Finset.mem_antidiagonal.1 hx1
      rw [coeff_add, coeff_C, if_neg (by omega), add_zero]
      rcases Nat.lt_or_ge D x.1 with hgt | hle
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1)) (hKV _ (hS₂K x.2 (by omega)))
    refine ⟨((H + q) * S₁).coeff t + qh.coeff t + (H.coeff 0
      + ∑ x ∈ (Finset.antidiagonal (t + 1)).filter (fun x : ℕ × ℕ => x.1 ≠ 0),
        (H + C b).coeff x.1 * S₂.coeff x.2), ?_, ?_⟩
    · exact Subalgebra.add_mem _ (Subalgebra.add_mem _ hprod₁V (hKV _ hqhKt))
        (Subalgebra.add_mem _ (hKV _ (hHK 0)) hrest₂V)
    · rw [hcO, hCah, add_zero, hsplit₂, if_pos (by omega), hb0, Nat.sub_zero,
        hS₂top, mul_one, hc, hγm, map_one, one_mul]
      ring
  · have hmul₂K : ((H + C b) * S₂).coeff (t + 1) ∈ K := by
      rw [coeff_mul]
      refine Subalgebra.sum_mem _ fun x hx => ?_
      have hxa : x.1 + x.2 = t + 1 := Finset.mem_antidiagonal.1 hx
      rw [coeff_add, add_mul]
      refine Subalgebra.add_mem _ ?_ ?_
      · rcases Nat.lt_or_ge D x.1 with hgt | hle
        · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
          exact Subalgebra.zero_mem _
        · rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
          · rw [show S₂.coeff x.2 = 0 from
              coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
            exact Subalgebra.zero_mem _
          · exact Subalgebra.mul_mem _ (hHK x.1) (hS₂K x.2 (by omega))
      · rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
        · rw [h0, coeff_C_zero,
            show S₂.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
            mul_zero]
          exact Subalgebra.zero_mem _
        · rw [coeff_C, if_neg (by omega), zero_mul]
          exact Subalgebra.zero_mem _
    rcases Nat.lt_or_ge (t + 1) (m + D / 2) with hband2 | hband2
    · -- q band: pivot βq (t - m)
      obtain ⟨F', hF', hFe⟩ := hq.pivot (t - m) (by omega)
      rw [hcomb0] at hFe
      have hqt : q.coeff (t - m) = βq (t - m) + F' := by
        have hXq : ((X : A[X]) ^ (D / 2 - 1)).coeff (t - m) = 0 := by
          rw [coeff_X_pow, if_neg (by omega)]
        have := hFe
        rw [coeff_sub, hXq, sub_zero, map_one, one_mul] at this
        exact this
      have hsplit₁ := coeff_mul_split_snd (H + q) S₁ t m
      have hS₁top : S₁.coeff m = 1 := by
        rw [← hd₁]
        exact hs₁m.coeff_natDegree
      have hrest₁V : (∑ x ∈ (Finset.antidiagonal t).filter
          (fun x : ℕ × ℕ => x.2 ≠ m), (H + q).coeff x.1 * S₁.coeff x.2) ∈ V := by
        refine Subalgebra.sum_mem _ fun x hx => ?_
        obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
        have hxa : x.1 + x.2 = t := Finset.mem_antidiagonal.1 hx1
        rw [coeff_add, add_mul]
        refine Subalgebra.add_mem _ ?_ ?_
        · rcases Nat.lt_or_ge D x.1 with hgt | hle
          · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
            exact Subalgebra.zero_mem _
          · rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
            · rw [show S₁.coeff x.2 = 0 from
                coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
              exact Subalgebra.zero_mem _
            · exact Subalgebra.mul_mem _ (hKV _ (hHK x.1))
                (hKV _ (hS₁K x.2 (by omega)))
        · rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
          · rw [show S₁.coeff x.2 = 0 from
              coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
            exact Subalgebra.zero_mem _
          · rcases Nat.lt_or_ge (D / 2 - 1) x.1 with hgt | hle
            · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
              exact Subalgebra.zero_mem _
            · exact Subalgebra.mul_mem _ (hqV x.1 (by omega))
                (hKV _ (hS₁K x.2 (by omega)))
      have hF'V : F' ∈ V := by
        refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF'
        rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
        exact hqW (t + 2) g (by omega) hg2
      refine ⟨H.coeff (t - m) + F'
        + ∑ x ∈ (Finset.antidiagonal t).filter (fun x : ℕ × ℕ => x.2 ≠ m),
            (H + q).coeff x.1 * S₁.coeff x.2
        + qh.coeff t + ((H + C b) * S₂).coeff (t + 1), ?_, ?_⟩
      · exact Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
          (Subalgebra.add_mem _ (hKV _ (hHK (t - m))) hF'V) hrest₁V)
          (hKV _ hqhKt)) (hKV _ hmul₂K)
      · rw [hcO, hCah, add_zero, hsplit₁, if_pos (by omega), hS₁top, mul_one,
          coeff_add, hγq (t + 1) (by omega) hband2,
          show t + 1 - m - 1 = t - m from by omega, map_one, one_mul]
        linear_combination hqt
    · -- dead tail: slot 0, everything known
      have hmul₁K : ((H + q) * S₁).coeff t ∈ K := by
        rw [coeff_mul]
        refine Subalgebra.sum_mem _ fun x hx => ?_
        have hxa : x.1 + x.2 = t := Finset.mem_antidiagonal.1 hx
        rw [coeff_add, add_mul]
        refine Subalgebra.add_mem _ ?_ ?_
        · rcases Nat.lt_or_ge D x.1 with hgt | hle
          · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
            exact Subalgebra.zero_mem _
          · rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
            · rw [show S₁.coeff x.2 = 0 from
                coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
              exact Subalgebra.zero_mem _
            · exact Subalgebra.mul_mem _ (hHK x.1) (hS₁K x.2 (by omega))
        · rcases Nat.lt_or_ge m x.2 with hgt2 | hle2
          · rw [show S₁.coeff x.2 = 0 from
              coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
            exact Subalgebra.zero_mem _
          · rcases Nat.lt_or_ge (D / 2 - 1) x.1 with hgt | hle
            · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
              exact Subalgebra.zero_mem _
            · rw [show q.coeff x.1 = 1 from by
                rw [show x.1 = D / 2 - 1 from by omega, ← hqd]
                exact hqm.coeff_natDegree, one_mul]
              exact hS₁K x.2 (by omega)
      refine ⟨((H + q) * S₁).coeff t + qh.coeff t + ((H + C b) * S₂).coeff (t + 1),
        ?_, ?_⟩
      · exact hKV _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ hmul₁K hqhKt) hmul₂K)
      · rw [hcO, hCah, add_zero, hγz (t + 1) (by omega)]
        simp only [map_one, one_mul, zero_add]

/-- **The fill-step certificate** (chain invariant step of `lem:Q-unitriangular`):
one `fillStep` on a certified pair with dead tail `2^i - 2` reproduces the pair-form
certificate at degree `m + D` over the `fillSlot` layout. -/
theorem fillStep_cert (hHm : H.Monic) (hHd : H.natDegree = D)
    (hHK : ∀ j, H.coeff j ∈ K)
    (hs₁m : S₁.Monic) (hd₁ : S₁.natDegree = m)
    (hs₂m : S₂.Monic) (hd₂ : S₂.natDegree = m)
    (hin : CoeffTriangular K βin (fun _ => (1 : R)) (m - 2) (S₁ - X ^ m) (S₂ - X ^ m))
    (hdead : ∀ r, m - D ≤ r → r < m - 2 → βin r = 0)
    (hq : CoeffTriangular K βq (fun _ => (1 : R)) (D / 2 - 1) 0 (q - X ^ (D / 2 - 1)))
    (hqm : q.Monic) (hqd : q.natDegree = D / 2 - 1)
    (hqh : CoeffTriangular K βqh (fun _ => (1 : R)) (D - 1) 0 (qh - X ^ (D - 1)))
    (hqhm : qh.Monic) (hqhd : qh.natDegree = D - 1)
    (h4 : 4 ≤ D) (hm : D + 2 ≤ m) :
    CoeffTriangular K (fillSlot D m βin βq βqh b ah) (fun _ => (1 : R)) (m + D - 2)
      ((H + q) * S₁ + qh - X ^ (m + D))
      ((H + C b) * S₂ + C ah - X ^ (m + D)) :=
  { unit := fun j hj => isUnit_one
    supp₁ := fillStep_supp₁ hHd hHK hd₁ hin hdead hq hqd hqh h4 hm
    supp₂ := fillStep_supp₂ hHd hHK hd₂ hin hdead h4 hm
    pivot := fun j hj => by
      rcases Nat.lt_or_ge j m with hjm | hjm
      · exact fillStep_pivot_low hHm hHd hHK hd₁ hd₂ hin hdead hq hqd hqh hqhm hqhd
          h4 hm j hjm
      · exact fillStep_pivot_top hHd hHK hs₁m hd₁ hs₂m hd₂ hin hdead hq hqm hqd
          hqhm hqhd h4 hm j hjm hj }

end fillStepCert


/-- Slot function of the `SP` base pair: row `0` is the tilde constant `δ`, rows
`[1, e)` read the inner block, the rest is dead. -/
def spSlot (e : ℕ) (δ : A) (β : ℕ → A) : ℕ → A := fun r =>
  if r = 0 then δ else if r < e then β (r - 1) else 0

/-- Band evaluation of `spSlot`: row `0`. -/
theorem spSlot_zero (e : ℕ) (δ : A) (β : ℕ → A) : spSlot e δ β 0 = δ := rfl

/-- Band evaluation of `spSlot`: the inner block `[1, e)`. -/
theorem spSlot_in (e : ℕ) (δ : A) (β : ℕ → A) (r : ℕ) (h1 : 1 ≤ r) (h2 : r < e) :
    spSlot e δ β r = β (r - 1) := by
  unfold spSlot
  rw [if_neg (by omega), if_pos h2]

/-- Band evaluation of `spSlot`: the dead tail `[e, ∞)`. -/
theorem spSlot_tail (e : ℕ) (δ : A) (β : ℕ → A) (r : ℕ) (h1 : e ≤ r) (h2 : 1 ≤ e) :
    spSlot e δ β r = 0 := by
  unfold spSlot
  rw [if_neg (by omega), if_neg (by omega)]

/-- **Base certificate of the fill chain** (the `SP` pair): adding a certified inner
block of degree `e - 1` to a known monic of degree `m ≥ e + 2` gives a pair-form
certificate with dead tail `[e, m - 2)`. -/
theorem sp_cert {K : Subalgebra R A} {β : ℕ → A} {P Hh : A[X]} {δ : A} {e m : ℕ}
    (hHK : ∀ j, Hh.coeff j ∈ K)
    (hPd : P.natDegree = e - 1)
    (hP : CoeffTriangular K β (fun _ => (1 : R)) (e - 1) 0 (P - X ^ (e - 1)))
    (hPm : P.Monic)
    (he : 2 ≤ e) (hm : e + 2 ≤ m) :
    CoeffTriangular K (spSlot e δ β) (fun _ => (1 : R)) (m - 2)
      (Hh + P - X ^ m) (Hh + C δ - X ^ m) := by
  set γ := spSlot e δ β with hγdef
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  have hγ0 : γ 0 = δ := rfl
  have hγin : ∀ r, 1 ≤ r → r < e → γ r = β (r - 1) :=
    fun r h1 h2 => spSlot_in e δ β r h1 h2
  have hγz : ∀ r, e ≤ r → γ r = 0 :=
    fun r h1 => spSlot_tail e δ β r h1 (by omega)
  -- inner coefficients: K-known at high rows, windowed below
  have hPK : ∀ t, e - 1 ≤ t → P.coeff t ∈ K := by
    intro t ht
    rcases Nat.lt_or_ge (e - 1) t with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · rw [show t = e - 1 from by omega, ← hPd, hPm.coeff_natDegree]
      exact Subalgebra.one_mem _
  have hPW : ∀ lo t, lo ≤ t + 1 →
      P.coeff t ∈ K ⊔ adjoin R (γ '' Set.Ico lo (m - 2)) := by
    intro lo t hlo
    refine coeff_mem_of_sub_pow (e - 1) t ?_
    refine mem_of_sup_adjoin_le (le_sup_left : K ≤ _) ?_ (hP.supp₂ t)
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    have hv : γ (g + 1) = β g := by
      rw [hγin (g + 1) (by omega) (by omega), Nat.add_sub_cancel]
    exact hv ▸ (le_sup_right : adjoin R _ ≤ _)
      (subset_adjoin ⟨g + 1, ⟨by omega, by omega⟩, rfl⟩)
  refine
    { unit := fun j hj => isUnit_one
      supp₁ := ?_
      supp₂ := ?_
      pivot := ?_ }
  · intro j
    rw [coeff_sub, coeff_add]
    refine Subalgebra.sub_mem _ (Subalgebra.add_mem _
      ((le_sup_left : K ≤ _) (hHK j)) (hPW (j + 1) j (by omega))) ?_
    exact coeff_X_pow_mem _ _ _
  · intro j
    rw [coeff_sub, coeff_add, coeff_C]
    refine Subalgebra.sub_mem _ (Subalgebra.add_mem _
      ((le_sup_left : K ≤ _) (hHK j)) ?_) ?_
    · split
      · rename_i hj0
        subst hj0
        rcases Nat.lt_or_ge 0 (m - 2) with hpos | hneg
        · exact hγ0 ▸ (le_sup_right : adjoin R _ ≤ _)
            (subset_adjoin ⟨0, ⟨le_rfl, by omega⟩, rfl⟩)
        · omega
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
    · exact coeff_X_pow_mem _ _ _
  · intro j hj
    have hXk₂ : ((X : A[X]) ^ m).coeff j = 0 := by
      rw [coeff_X_pow, if_neg (by omega)]
    cases j with
    | zero =>
      refine ⟨Hh.coeff 0, (le_sup_left : K ≤ _) (hHK 0), ?_⟩
      rw [coeff_combined_zero, coeff_sub, hXk₂, sub_zero, coeff_add, coeff_C_zero,
        hγ0, map_one, one_mul]
      ring
    | succ t =>
      have hXk₁ : ((X : A[X]) ^ m).coeff t = 0 := by
        rw [coeff_X_pow, if_neg (by omega)]
      have hCz : (C δ : A[X]).coeff (t + 1) = 0 := by
        rw [coeff_C, if_neg (by omega)]
      have hcO : (combined (Hh + P - X ^ m) (Hh + C δ - X ^ m)).coeff (t + 1)
          = (Hh.coeff t + P.coeff t) + Hh.coeff (t + 1) := by
        rw [coeff_combined, coeff_sub, coeff_sub, hXk₁, hXk₂, sub_zero, sub_zero,
          coeff_add, coeff_add, hCz, add_zero]
      rcases Nat.lt_or_ge (t + 1) e with hband | hband
      · -- live inner rows
        obtain ⟨F', hF', hFe⟩ := hP.pivot t (by omega)
        rw [hcomb0] at hFe
        have hPt : P.coeff t = β t + F' := by
          have hXq : ((X : A[X]) ^ (e - 1)).coeff t = 0 := by
            rw [coeff_X_pow, if_neg (by omega)]
          have := hFe
          rw [coeff_sub, hXq, sub_zero, map_one, one_mul] at this
          exact this
        have hF'V : F' ∈ K ⊔ adjoin R (γ '' Set.Ico (t + 2) (m - 2)) := by
          refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF'
          rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
          have hv : γ (g + 1) = β g := by
            rw [hγin (g + 1) (by omega) (by omega), Nat.add_sub_cancel]
          exact hv ▸ (le_sup_right : adjoin R _ ≤ _)
            (subset_adjoin ⟨g + 1, ⟨by omega, by omega⟩, rfl⟩)
        refine ⟨F' + (Hh.coeff t + Hh.coeff (t + 1)), ?_, ?_⟩
        · exact Subalgebra.add_mem _ hF'V ((le_sup_left : K ≤ _)
            (Subalgebra.add_mem _ (hHK t) (hHK (t + 1))))
        · rw [hcO, hPt, hγin (t + 1) (by omega) hband, Nat.add_sub_cancel,
            map_one, one_mul]
          ring
      · -- dead rows: inner coefficient is K-known
        refine ⟨(Hh.coeff t + P.coeff t) + Hh.coeff (t + 1),
          (le_sup_left : K ≤ _) (Subalgebra.add_mem _ (Subalgebra.add_mem _
            (hHK t) (hPK t (by omega))) (hHK (t + 1))), ?_⟩
        rw [hcO, hγz (t + 1) (by omega)]
        simp only [map_one, one_mul, zero_add]

section chain

variable [Nontrivial A]

/-- The composed slot function of a fill chain: level `l` is applied first (on input
degree `n`), then the chain continues at level `l - 1` on the grown pair. -/
noncomputable def chainSlot (Bq Bqh : ℕ → ℕ → A) (bs ahs : ℕ → A) :
    ℕ → ℕ → (ℕ → A) → (ℕ → A)
  | 0, _, β => β
  | 1, _, β => β
  | (i + 2), n, β =>
    chainSlot Bq Bqh bs ahs (i + 1) (n + 2 ^ (i + 2))
      (fillSlot (2 ^ (i + 2)) n β (Bq (i + 2)) (Bqh (i + 2)) (bs (i + 2)) (ahs (i + 2)))

/-- **The fill-chain certificate**: iterating `fillStep_cert` down the chain.  The dead
tail `2^l - 2` of the input certificate is consumed exactly, level by level. -/
theorem fillChain_cert {K : Subalgebra R A} (Hf : ℕ → A[X]) (Dd : ℕ → FillData A)
    (Bq Bqh : ℕ → ℕ → A) :
    ∀ l (S : A[X] × A[X]) (n : ℕ) (β : ℕ → A),
      S.1.Monic → S.1.natDegree = n → S.2.Monic → S.2.natDegree = n →
      CoeffTriangular K β (fun _ => (1 : R)) (n - 2) (S.1 - X ^ n) (S.2 - X ^ n) →
      (∀ r, n - 2 ^ l ≤ r → r < n - 2 → β r = 0) →
      2 ^ l + 2 ≤ n →
      (∀ i, 2 ≤ i → i ≤ l →
        (Hf i).Monic ∧ (Hf i).natDegree = 2 ^ i ∧ (∀ j, (Hf i).coeff j ∈ K) ∧
        (Dd i).q.Monic ∧ (Dd i).q.natDegree = 2 ^ (i - 1) - 1 ∧
        (Dd i).qh.Monic ∧ (Dd i).qh.natDegree = 2 ^ i - 1 ∧
        CoeffTriangular K (Bq i) (fun _ => (1 : R)) (2 ^ (i - 1) - 1) 0
          ((Dd i).q - X ^ (2 ^ (i - 1) - 1)) ∧
        CoeffTriangular K (Bqh i) (fun _ => (1 : R)) (2 ^ i - 1) 0
          ((Dd i).qh - X ^ (2 ^ i - 1))) →
      CoeffTriangular K
        (chainSlot Bq Bqh (fun i => (Dd i).b) (fun i => (Dd i).ah) l n β)
        (fun _ => (1 : R)) (n + (2 ^ (l + 1) - 4) - 2)
        ((fillChain Hf Dd l S).1 - X ^ (n + (2 ^ (l + 1) - 4)))
        ((fillChain Hf Dd l S).2 - X ^ (n + (2 ^ (l + 1) - 4))) := by
  intro l
  induction l with
  | zero =>
    intro S n β hm₁ hd₁ hm₂ hd₂ hin hdead hn hdata
    rw [show n + (2 ^ (0 + 1) - 4) = n from by norm_num]
    exact hin
  | succ i ih =>
    match i with
    | 0 =>
      intro S n β hm₁ hd₁ hm₂ hd₂ hin hdead hn hdata
      rw [show n + (2 ^ (1 + 1) - 4) = n from by norm_num]
      exact hin
    | i + 1 =>
      intro S n β hm₁ hd₁ hm₂ hd₂ hin hdead hn hdata
      -- power bridges
      have hp1 : 2 ^ (i + 2) = 2 * 2 ^ (i + 1) := by rw [pow_succ]; ring
      have hp2 : 2 ^ (i + 2 + 1) = 2 * 2 ^ (i + 2) := by rw [pow_succ]; ring
      have hge : 1 ≤ 2 ^ (i + 1) := Nat.one_le_pow _ _ (by omega)
      have hD2 : 2 ^ (i + 2) / 2 = 2 ^ (i + 1) := by omega
      obtain ⟨hHm, hHd, hHK, hqm, hqd, hqhm, hqhd, hqcert, hqhcert⟩ :=
        hdata (i + 2) (by omega) le_rfl
      have hqd' : (Dd (i + 2)).q.natDegree = 2 ^ (i + 1) - 1 := hqd
      have hqcert' : CoeffTriangular K (Bq (i + 2)) (fun _ => (1 : R))
          (2 ^ (i + 1) - 1) 0 ((Dd (i + 2)).q - X ^ (2 ^ (i + 1) - 1)) := hqcert
      -- one fill step
      obtain ⟨⟨hm₁', hd₁'⟩, ⟨hm₂', hd₂'⟩⟩ := fillStep_monic (b := (Dd (i + 2)).b)
        (ah := (Dd (i + 2)).ah) (q := (Dd (i + 2)).q) (qh := (Dd (i + 2)).qh)
        hHm hHd (by omega) (by omega) (by omega) hm₁ hd₁ hm₂ hd₂
      have hstep := fillStep_cert (b := (Dd (i + 2)).b) (ah := (Dd (i + 2)).ah)
        hHm hHd hHK hm₁ hd₁ hm₂ hd₂ hin
        (fun r h1 h2 => hdead r (by omega) h2)
        (by rw [hD2]; exact hqcert') hqm (by rw [hD2]; exact hqd')
        hqhcert hqhm hqhd
        (by
          have h44 : (2 : ℕ) ^ 2 ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
          have h4e : (2 : ℕ) ^ 2 = 4 := by norm_num
          omega)
        hn
      -- dead tail for the next level
      have hdead' : ∀ r, n + 2 ^ (i + 2) - 2 ^ (i + 1) ≤ r →
          r < n + 2 ^ (i + 2) - 2 →
          fillSlot (2 ^ (i + 2)) n β (Bq (i + 2)) (Bqh (i + 2)) ((Dd (i + 2)).b)
            ((Dd (i + 2)).ah) r = 0 := by
        intro r h1 h2
        exact fillSlot_tail _ _ _ _ _ _ _ r (by omega) (by omega) (by omega)
      -- recursive call on the grown pair
      have hrec := ih (fillStep (Hf (i + 2)) (Dd (i + 2)) S) (n + 2 ^ (i + 2))
        (fillSlot (2 ^ (i + 2)) n β (Bq (i + 2)) (Bqh (i + 2)) ((Dd (i + 2)).b)
          ((Dd (i + 2)).ah))
        hm₁' hd₁' hm₂' hd₂'
        (by
          have : n + 2 ^ (i + 2) - 2 = n + (2 ^ (i + 2) - 2) := by omega
          exact hstep)
        hdead'
        (by omega)
        (fun i' h2 hle => hdata i' h2 (by omega))
      rw [show n + (2 ^ (i + 2 + 1) - 4)
          = n + 2 ^ (i + 2) + (2 ^ (i + 1 + 1) - 4) from by omega]
      exact hrec

end chain

end FastPoly
