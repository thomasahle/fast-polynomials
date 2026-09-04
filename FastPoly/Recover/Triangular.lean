import FastPoly.Recover.Multiplication
import FastPoly.Recover.Combination

/-!
# Coefficient-triangular remainder pairs

Paper `def:coefficient-triangular` and `lem:triangular-shift`: the scalar-triangular
invariant carried by the `T_{k,2^l}` remainder recursion, and its stability under
multiplication by known monic factors of equal degree — the repair for the overlapping
residual `x·L₁R⁽¹⁾ + L₂R⁽²⁾` in `lem:Rk2l`.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Transport a coefficient membership across subtraction of a monomial: the
coefficients of `X ^ d` are `0` or `1`, hence in every subalgebra. -/
theorem coeff_mem_of_sub_pow {V : Subalgebra R A} {P : A[X]} (d c : ℕ)
    (h : (P - X ^ d).coeff c ∈ V) : P.coeff c ∈ V := by
  have hs : P.coeff c = (P - X ^ d).coeff c + (X ^ d : A[X]).coeff c := by
    rw [coeff_sub]; ring
  rw [hs]
  exact Subalgebra.add_mem _ h (coeff_X_pow_mem V d c)

/-- Collapse a `K ⊔ adjoin R s` membership into any subalgebra containing `K` and `s`. -/
theorem mem_of_sup_adjoin_le {K V : Subalgebra R A} {s : Set A} {x : A}
    (hKV : K ≤ V) (hsV : ∀ y ∈ s, y ∈ V) (hx : x ∈ K ⊔ adjoin R s) : x ∈ V :=
  SetLike.le_def.1 (sup_le hKV (adjoin_le hsV)) hx

/-- **Coefficient-triangular remainder pair** (paper `def:coefficient-triangular`):
parameters `α j` (`j < d`) with pivot slopes `lam j`; the two support conditions and the
pivot equation for the combined remainder `D = X·R₁ + R₂`.  Coefficients at or above `d`
are automatically `K`-recoverable (their windows are empty). -/
structure CoeffTriangular (K : Subalgebra R A) (α : ℕ → A) (lam : ℕ → R) (d : ℕ)
    (R₁ R₂ : A[X]) : Prop where
  unit : ∀ j, j < d → IsUnit (lam j)
  supp₁ : ∀ j, R₁.coeff j ∈ K ⊔ adjoin R (α '' Set.Ico (j + 1) d)
  supp₂ : ∀ j, R₂.coeff j ∈ K ⊔ adjoin R (α '' Set.Ico j d)
  pivot : ∀ j, j < d → ∃ F ∈ K ⊔ adjoin R (α '' Set.Ico (j + 1) d),
    (combined R₁ R₂).coeff j = algebraMap R A (lam j) * α j + F

namespace CoeffTriangular

variable {K : Subalgebra R A} {α : ℕ → A} {lam : ℕ → R} {d : ℕ} {R₁ R₂ : A[X]}

/-- The parameters are recoverable, causally, from the combined remainder polynomial. -/
theorem param_mem (h : CoeffTriangular K α lam d R₁ R₂) :
    ∀ j, j < d →
      α j ∈ K ⊔ adjoin R ((fun i => (combined R₁ R₂).coeff i) '' Set.Ico j d) := by
  have main : ∀ fuel j, j < d → d - j ≤ fuel →
      α j ∈ K ⊔ adjoin R ((fun i => (combined R₁ R₂).coeff i) '' Set.Ico j d) := by
    intro fuel
    induction fuel with
    | zero => intro j hj hf; omega
    | succ fuel ih =>
      intro j hj hf
      obtain ⟨F, hF, hDj⟩ := h.pivot j hj
      set V := K ⊔ adjoin R ((fun i => (combined R₁ R₂).coeff i) '' Set.Ico j d) with hV
      have hFV : F ∈ V := by
        refine SetLike.le_def.1 (sup_le le_sup_left (adjoin_le ?_)) hF
        rintro _ ⟨i, hi, rfl⟩
        obtain ⟨hi1, hi2⟩ := hi
        have hmem := ih i hi2 (by omega)
        refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono ?_)) K) hmem
        exact Set.Ico_subset_Ico (by omega) le_rfl
      have hDV : (combined R₁ R₂).coeff j ∈ V :=
        (le_sup_right : adjoin R _ ≤ V) (subset_adjoin ⟨j, ⟨le_rfl, hj⟩, rfl⟩)
      exact mem_of_unit_slope (h.unit j hj) (Subalgebra.sub_mem _ hDV hFV)
        (by rw [hDj]; ring)
  exact fun j hj => main (d - j) j hj le_rfl

/-- **Shifting a triangular remainder block** (paper `lem:triangular-shift`), support part
for the first component: a parameter `α i` occurs in `[x^j](L₁·R₁)` only when
`j ≤ h + i - 1`. -/
theorem shift_supp₁ (h : CoeffTriangular K α lam d R₁ R₂)
    {L₁ : A[X]} {hd : ℕ} (hL₁ : L₁.natDegree ≤ hd) (hKL₁ : ∀ j, L₁.coeff j ∈ K) (j : ℕ) :
    (L₁ * R₁).coeff j ∈ K ⊔ adjoin R (α '' Set.Ico (j + 1 - hd) d) := by
  rw [coeff_mul]
  refine Subalgebra.sum_mem _ fun x hx => ?_
  have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
  rcases Nat.lt_or_ge hd x.1 with hgt | hle
  · have hz : L₁.coeff x.1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, zero_mul]
    exact Subalgebra.zero_mem _
  · refine Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (hKL₁ x.1)) ?_
    have hs := h.supp₁ x.2
    refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono ?_)) K) hs
    exact Set.Ico_subset_Ico (by omega) le_rfl

/-- Support part for the second component: `α i` occurs in `[x^j](L₂·R₂)` only when
`j ≤ h + i`. -/
theorem shift_supp₂ (h : CoeffTriangular K α lam d R₁ R₂)
    {L₂ : A[X]} {hd : ℕ} (hL₂ : L₂.natDegree ≤ hd) (hKL₂ : ∀ j, L₂.coeff j ∈ K) (j : ℕ) :
    (L₂ * R₂).coeff j ∈ K ⊔ adjoin R (α '' Set.Ico (j - hd) d) := by
  rw [coeff_mul]
  refine Subalgebra.sum_mem _ fun x hx => ?_
  have hxa : x.1 + x.2 = j := Finset.mem_antidiagonal.1 hx
  rcases Nat.lt_or_ge hd x.1 with hgt | hle
  · have hz : L₂.coeff x.1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, zero_mul]
    exact Subalgebra.zero_mem _
  · refine Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (hKL₂ x.1)) ?_
    have hs := h.supp₂ x.2
    refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono ?_)) K) hs
    exact Set.Ico_subset_Ico (by omega) le_rfl

/-- **Shifting a triangular remainder block** (paper `lem:triangular-shift`), pivot part:
for monic known `L₁, L₂` of the same degree `h ≥ 1`, the combined polynomial of
`(L₁R₁, L₂R₂)` has, at degree `h + j`, the same pivot `lam j · α j` as the inner pair at
`j`, with an error known given `K` and the later parameters. -/
theorem shift_pivot (h : CoeffTriangular K α lam d R₁ R₂)
    {L₁ L₂ : A[X]} {hd : ℕ} (hd1 : 1 ≤ hd)
    (hL₁ : L₁.Monic) (hdL₁ : L₁.natDegree = hd)
    (hL₂ : L₂.Monic) (hdL₂ : L₂.natDegree = hd)
    (hKL₁ : ∀ j, L₁.coeff j ∈ K) (hKL₂ : ∀ j, L₂.coeff j ∈ K) :
    ∀ j, j < d → ∃ F ∈ K ⊔ adjoin R (α '' Set.Ico (j + 1) d),
      (combined (L₁ * R₁) (L₂ * R₂)).coeff (hd + j)
        = algebraMap R A (lam j) * α j + F := by
  intro j hj
  obtain ⟨F, hF, hDj⟩ := h.pivot j hj
  have hl₁ : L₁.coeff hd = 1 := by rw [← hdL₁]; exact hL₁.coeff_natDegree
  have hl₂ : L₂.coeff hd = 1 := by rw [← hdL₂]; exact hL₂.coeff_natDegree
  set W := K ⊔ adjoin R (α '' Set.Ico (j + 1) d) with hW
  -- rest sums of the two splits
  set S₁ := ∑ x ∈ (Finset.antidiagonal (hd + j - 1)).filter (fun x : ℕ × ℕ => x.1 ≠ hd),
      L₁.coeff x.1 * R₁.coeff x.2 with hS₁
  set S₂ := ∑ x ∈ (Finset.antidiagonal (hd + j)).filter (fun x : ℕ × ℕ => x.1 ≠ hd),
      L₂.coeff x.1 * R₂.coeff x.2 with hS₂
  have hS₁mem : S₁ ∈ W := by
    rw [hS₁]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hm := Finset.mem_filter.1 hx
    have hxa : x.1 + x.2 = hd + j - 1 := Finset.mem_antidiagonal.1 hm.1
    have hx1 : x.1 ≠ hd := hm.2
    rcases Nat.lt_or_ge hd x.1 with hgt | hle
    · have hz : L₁.coeff x.1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, zero_mul]
      exact Subalgebra.zero_mem _
    · refine Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (hKL₁ x.1)) ?_
      have hs := h.supp₁ x.2
      refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono ?_)) K) hs
      exact Set.Ico_subset_Ico (by omega) le_rfl
  have hS₂mem : S₂ ∈ W := by
    rw [hS₂]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hm := Finset.mem_filter.1 hx
    have hxa : x.1 + x.2 = hd + j := Finset.mem_antidiagonal.1 hm.1
    have hx1 : x.1 ≠ hd := hm.2
    rcases Nat.lt_or_ge hd x.1 with hgt | hle
    · have hz : L₂.coeff x.1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, zero_mul]
      exact Subalgebra.zero_mem _
    · refine Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) (hKL₂ x.1)) ?_
      have hs := h.supp₂ x.2
      refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono ?_)) K) hs
      exact Set.Ico_subset_Ico (by omega) le_rfl
  -- expand the target coefficient
  obtain ⟨e, he⟩ : ∃ e, hd + j = e + 1 := ⟨hd + j - 1, by omega⟩
  have hcomb : (combined (L₁ * R₁) (L₂ * R₂)).coeff (hd + j)
      = (L₁ * R₁).coeff (hd + j - 1) + (L₂ * R₂).coeff (hd + j) := by
    rw [he, coeff_combined, show e + 1 - 1 = e from by omega]
  have hsplit₁ : (L₁ * R₁).coeff (hd + j - 1)
      = (if hd ≤ hd + j - 1 then R₁.coeff (hd + j - 1 - hd) else 0) + S₁ := by
    rw [coeff_mul_split_fst L₁ R₁ (hd + j - 1) hd, hl₁, hS₁]
    congr 1
    split
    · rw [one_mul]
    · rfl
  have hsplit₂ : (L₂ * R₂).coeff (hd + j)
      = R₂.coeff j + S₂ := by
    rw [coeff_mul_split_fst L₂ R₂ (hd + j) hd, hl₂, if_pos (by omega),
      show hd + j - hd = j from by omega, one_mul, hS₂]
  refine ⟨F + S₁ + S₂, Subalgebra.add_mem _ (Subalgebra.add_mem _ hF hS₁mem) hS₂mem, ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · -- j = 0: no first-component boundary
    have hno : ¬ hd ≤ hd + 0 - 1 := by omega
    have hD0 : (combined R₁ R₂).coeff 0 = R₂.coeff 0 := coeff_combined_zero R₁ R₂
    rw [hcomb, hsplit₁, hsplit₂, if_neg hno]
    rw [hD0] at hDj
    rw [hDj]
    ring
  · -- j ≥ 1: the two boundaries assemble the inner combined coefficient at j
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hyes : hd ≤ hd + (j' + 1) - 1 := by omega
    have hidx : hd + (j' + 1) - 1 - hd = j' := by omega
    have hDj' : (combined R₁ R₂).coeff (j' + 1) = R₁.coeff j' + R₂.coeff (j' + 1) :=
      coeff_combined R₁ R₂ j'
    rw [hcomb, hsplit₁, hsplit₂, if_pos hyes, hidx]
    rw [hDj'] at hDj
    rw [show R₁.coeff j' + S₁ + (R₂.coeff (j' + 1) + S₂)
        = (R₁.coeff j' + R₂.coeff (j' + 1)) + S₁ + S₂ from by ring, hDj]
    ring

/-- **A triangular remainder pair is causal** (paper `lem:triangular-implies-compatible`,
compatibility half).  If `(T₁, T₂)` differ from `(R₁, R₂)` by polynomials with known
coefficients (e.g. `T₁ = H^k + R₁`, `T₂ = H̃^k + R₂` with known monic powers), are monic
of degree `N ≥ d`, and `(R₁, R₂)` is coefficient-triangular for the `d` parameters, then
`(T₁, T₂)` is a compatible pair on the window `range d`. -/
theorem toCompatiblePair (h : CoeffTriangular K α lam d R₁ R₂)
    {T₁ T₂ : A[X]} {N : ℕ}
    (hk₁ : ∀ j, T₁.coeff j - R₁.coeff j ∈ K) (hk₂ : ∀ j, T₂.coeff j - R₂.coeff j ∈ K)
    (hm₁ : T₁.Monic) (hd₁ : T₁.natDegree = N)
    (hm₂ : T₂.Monic) (hd₂ : T₂.natDegree = N)
    (hdN : d ≤ N) :
    CompatiblePair K T₁ T₂ N (Finset.range d) := by
  have hcomb : ∀ i, (combined T₁ T₂).coeff i - (combined R₁ R₂).coeff i ∈ K := by
    intro i
    cases i with
    | zero =>
      rw [coeff_combined_zero, coeff_combined_zero]
      exact hk₂ 0
    | succ m =>
      rw [coeff_combined, coeff_combined]
      have hkey : T₁.coeff m + T₂.coeff (m + 1) - (R₁.coeff m + R₂.coeff (m + 1))
          = (T₁.coeff m - R₁.coeff m) + (T₂.coeff (m + 1) - R₂.coeff (m + 1)) := by ring
      rw [hkey]
      exact Subalgebra.add_mem _ (hk₁ m) (hk₂ (m + 1))
  have hα : ∀ i, i < d → ∀ t, t ≤ i →
      α i ∈ Vis R K (combined R₁ R₂) (Finset.range d) t := by
    intro i hi t ht
    have hp := h.param_mem i hi
    refine SetLike.le_def.1
      (sup_le (fun x hx => known_mem_Vis hx) (adjoin_le ?_)) hp
    rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    exact coeff_mem_Vis (Finset.mem_range.2 hm2) (by omega)
  have hlift : ∀ t, K ⊔ adjoin R (α '' Set.Ico t d)
      ≤ Vis R K (combined R₁ R₂) (Finset.range d) t := by
    intro t
    refine sup_le (fun x hx => known_mem_Vis hx) (adjoin_le ?_)
    rintro _ ⟨i, ⟨hi1, hi2⟩, rfl⟩
    exact hα i hi2 t hi1
  have hVis : ∀ t, Vis R K (combined T₁ T₂) (Finset.range d) t
      = Vis R K (combined R₁ R₂) (Finset.range d) t :=
    fun t => Vis_congr_of_diff_known hcomb t
  refine
    { mem₁ := ?_
      mem₂ := ?_
      monic₁ := hm₁
      monic₂ := hm₂
      natDegree₁ := hd₁
      natDegree₂ := hd₂
      window := ?_ }
  · intro j
    rw [hVis]
    have hR : R₁.coeff j ∈ Vis R K (combined R₁ R₂) (Finset.range d) (j + 1) :=
      hlift (j + 1) (h.supp₁ j)
    have hkey : T₁.coeff j = (T₁.coeff j - R₁.coeff j) + R₁.coeff j := by ring
    rw [hkey]
    exact Subalgebra.add_mem _ (known_mem_Vis (hk₁ j)) hR
  · intro j
    rw [hVis]
    have hR : R₂.coeff j ∈ Vis R K (combined R₁ R₂) (Finset.range d) j :=
      hlift j (h.supp₂ j)
    have hkey : T₂.coeff j = (T₂.coeff j - R₂.coeff j) + R₂.coeff j := by ring
    rw [hkey]
    exact Subalgebra.add_mem _ (known_mem_Vis (hk₂ j)) hR
  · intro i hi
    exact Finset.mem_range.2 (by have := Finset.mem_range.1 hi; omega)

end CoeffTriangular

section certHelpers

variable {K : Subalgebra R A} {β : ℕ → A} {lam : ℕ → R} {e : ℕ} {R₁ R₂ : A[X]}

/-- Empty-window collapse: membership in `K ⊔ adjoin ∅` is membership in `K`. -/
theorem mem_of_sup_adjoin_empty {x : A} {s : Set A} (hs : s = ∅)
    (hx : x ∈ K ⊔ adjoin R s) : x ∈ K := by
  rw [hs, Algebra.adjoin_empty, sup_bot_eq] at hx
  exact hx

/-- High rows of a certified pair are `K`-known (first component, rows `≥ e - 1`). -/
theorem cert_high_mem₁ (h : CoeffTriangular K β lam e R₁ R₂) {j : ℕ} (hj : e ≤ j + 1) :
    R₁.coeff j ∈ K :=
  mem_of_sup_adjoin_empty (by
    rw [Set.image_eq_empty]
    exact Set.Ico_eq_empty (by omega)) (h.supp₁ j)

/-- High rows of a certified pair are `K`-known (second component, rows `≥ e`). -/
theorem cert_high_mem₂ (h : CoeffTriangular K β lam e R₁ R₂) {j : ℕ} (hj : e ≤ j) :
    R₂.coeff j ∈ K :=
  mem_of_sup_adjoin_empty (by
    rw [Set.image_eq_empty]
    exact Set.Ico_eq_empty (by omega)) (h.supp₂ j)

end certHelpers

/-- Transport a certificate along a parameter function agreeing below `d`. -/
theorem CoeffTriangular.congr_param {K : Subalgebra R A} {α α' : ℕ → A} {lam : ℕ → R}
    {d : ℕ} {R₁ R₂ : A[X]} (hab : ∀ j, j < d → α j = α' j)
    (h : CoeffTriangular K α lam d R₁ R₂) : CoeffTriangular K α' lam d R₁ R₂ := by
  have himg : ∀ lo, α' '' Set.Ico lo d = α '' Set.Ico lo d := by
    intro lo
    apply Set.image_congr
    intro x hx
    exact (hab x hx.2).symm
  exact
    { unit := h.unit
      supp₁ := fun j => by rw [himg]; exact h.supp₁ j
      supp₂ := fun j => by rw [himg]; exact h.supp₂ j
      pivot := fun j hj => by
        obtain ⟨F, hF, hE⟩ := h.pivot j hj
        exact ⟨F, by rw [himg]; exact hF, by rw [← hab j hj]; exact hE⟩ }

section concatenation

variable {K : Subalgebra R A}

/-- Window glue for block concatenation (`lem:triangular-block-concatenation`, index
part): the window `[a, c)` splits as the higher block `[b, c)` joined with `[a, b)`. -/
theorem adjoin_Ico_glue (K : Subalgebra R A) (α : ℕ → A) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    K ⊔ adjoin R (α '' Set.Ico a c)
      = (K ⊔ adjoin R (α '' Set.Ico b c)) ⊔ adjoin R (α '' Set.Ico a b) := by
  rw [← Set.Ico_union_Ico_eq_Ico hab hbc, Set.image_union, Algebra.adjoin_union]
  rw [sup_comm (adjoin R (α '' Set.Ico a b)) (adjoin R (α '' Set.Ico b c)), ← sup_assoc]

/-- Side-data absorption (`lem:triangular-block-concatenation`, substitution part):
membership relative to an enlarged context `B` collapses to `K` once every element of `B`
is recoverable from `K` and the higher parameters `t`. -/
theorem side_data_absorb {B : Subalgebra R A} {s t : Set A}
    (hB : B ≤ K ⊔ adjoin R t) : B ⊔ adjoin R s ≤ K ⊔ adjoin R (s ∪ t) := by
  refine sup_le (le_trans hB ?_) ?_
  · exact sup_le le_sup_left
      (le_trans (adjoin_mono Set.subset_union_right) le_sup_right)
  · exact le_trans (adjoin_mono Set.subset_union_left) le_sup_right

end concatenation

/-- A slot value inside the adjoined band. -/
theorem slot_mem_sup_adjoin_Ico {K : Subalgebra R A} (γ : ℕ → A) {lo t hi : ℕ}
    (hlo : lo ≤ t) (hhi : t < hi) :
    γ t ∈ K ⊔ Algebra.adjoin R (γ '' Set.Ico lo hi) :=
  (le_sup_right : Algebra.adjoin R _ ≤ _)
    (Algebra.subset_adjoin ⟨t, ⟨hlo, hhi⟩, rfl⟩)

/-- A known element inside a band-augmented context. -/
theorem known_mem_sup_adjoin {K : Subalgebra R A} {s : Set A} {x : A}
    (hx : x ∈ K) : x ∈ K ⊔ Algebra.adjoin R s :=
  (le_sup_left : K ≤ _) hx

end FastPoly
