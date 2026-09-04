import FastPoly.Section4.FillCert
import FastPoly.Recover.Multiplication
import FastPoly.Section5.UBinomial

/-!
# Certificate engines for the `lem:Rk2l`(3) stage tables

Generic `CoeffTriangular` engines: adding a known monic to a certified block, and the
slope-2 pivot structure of the square of a certified monic.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {K : Subalgebra R A} {β : ℕ → A} {e D : ℕ} {P Hh : A[X]}

/-- Adding a fully known polynomial to a certified block preserves the certificate
(any leading normalization `X^D` with `e ≤ D`). -/
theorem add_block_cert (hHK : ∀ j, Hh.coeff j ∈ K)
    (hP : CoeffTriangular K β (fun _ => (1 : R)) e 0 (P - X ^ e)) :
    CoeffTriangular K β (fun _ => (1 : R)) e 0 (Hh + P - X ^ D) := by
  have hsplit : ∀ j, (Hh + P - X ^ D).coeff j
      = (P - X ^ e).coeff j + ((Hh.coeff j + (X ^ e : A[X]).coeff j)
        - (X ^ D : A[X]).coeff j) := by
    intro j
    rw [coeff_sub, coeff_sub, coeff_add]
    ring
  have hKpart : ∀ j, (Hh.coeff j + (X ^ e : A[X]).coeff j)
      - (X ^ D : A[X]).coeff j ∈ K := by
    intro j
    refine Subalgebra.sub_mem _ (Subalgebra.add_mem _ (hHK j) ?_) ?_ <;>
      (rw [coeff_X_pow]; split)
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  refine
    { unit := fun j hj => isUnit_one
      supp₁ := fun j => by rw [coeff_zero]; exact Subalgebra.zero_mem _
      supp₂ := ?_
      pivot := ?_ }
  · intro j
    rw [hsplit]
    exact Subalgebra.add_mem _ (hP.supp₂ j) ((le_sup_left : K ≤ _) (hKpart j))
  · intro j hj
    obtain ⟨F, hF, hFe⟩ := hP.pivot j hj
    rw [hcomb0] at hFe
    refine ⟨F + ((Hh.coeff j + (X ^ e : A[X]).coeff j) - (X ^ D : A[X]).coeff j),
      Subalgebra.add_mem _ hF ((le_sup_left : K ≤ _) (hKpart j)), ?_⟩
    rw [hcomb0, hsplit, hFe]
    ring

/-- Symmetric boundary split of a square's upper-window coefficient. -/
theorem sq_coeff_split (hPd : P.natDegree = D) (hPm : P.Monic) {r : ℕ} (hr : r < D) :
    (P ^ 2).coeff (D + r) = 2 * P.coeff r
      + ∑ x ∈ (Finset.antidiagonal (D + r)).filter
          (fun x : ℕ × ℕ => x.1 ≠ D ∧ x.2 ≠ D),
        P.coeff x.1 * P.coeff x.2 := by
  classical
  have hsq : (P ^ 2).coeff (D + r) = ∑ x ∈ Finset.antidiagonal (D + r),
      P.coeff x.1 * P.coeff x.2 := by
    rw [sq, coeff_mul]
  have hmem₁ : ((D, r) : ℕ × ℕ) ∈ (Finset.antidiagonal (D + r)).filter
      (fun x : ℕ × ℕ => x.1 = D) := by
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    exact ⟨rfl, rfl⟩
  have h1 : ∑ x ∈ (Finset.antidiagonal (D + r)).filter (fun x : ℕ × ℕ => x.1 = D),
      P.coeff x.1 * P.coeff x.2 = P.coeff r := by
    rw [Finset.sum_eq_single_of_mem ((D, r) : ℕ × ℕ) hmem₁]
    · rw [← hPd, hPm.coeff_natDegree, one_mul]
    · intro y hy hne
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
      have hya : y.1 + y.2 = D + r := Finset.mem_antidiagonal.1 hy1
      exact absurd (Prod.ext hy2 (by omega)) hne
  have hmem₂ : ((r, D) : ℕ × ℕ) ∈ ((Finset.antidiagonal (D + r)).filter
      (fun x : ℕ × ℕ => ¬ x.1 = D)).filter (fun x : ℕ × ℕ => x.2 = D) := by
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_antidiagonal]
    exact ⟨⟨by omega, by omega⟩, rfl⟩
  have h2 : ∑ x ∈ ((Finset.antidiagonal (D + r)).filter
      (fun x : ℕ × ℕ => ¬ x.1 = D)).filter (fun x : ℕ × ℕ => x.2 = D),
      P.coeff x.1 * P.coeff x.2 = P.coeff r := by
    rw [Finset.sum_eq_single_of_mem ((r, D) : ℕ × ℕ) hmem₂]
    · rw [← hPd, hPm.coeff_natDegree, mul_one]
    · intro y hy hne
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
      obtain ⟨hy3, _⟩ := Finset.mem_filter.1 hy1
      have hya : y.1 + y.2 = D + r := Finset.mem_antidiagonal.1 hy3
      exact absurd (Prod.ext (by omega) hy2) hne
  have hsplit1 := Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal (D + r))
    (fun x : ℕ × ℕ => x.1 = D) (fun x : ℕ × ℕ => P.coeff x.1 * P.coeff x.2)
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.antidiagonal (D + r)).filter (fun x : ℕ × ℕ => ¬ x.1 = D))
    (fun x : ℕ × ℕ => x.2 = D) (fun x : ℕ × ℕ => P.coeff x.1 * P.coeff x.2)
  have hff : ((Finset.antidiagonal (D + r)).filter
      (fun x : ℕ × ℕ => ¬ x.1 = D)).filter (fun x : ℕ × ℕ => ¬ x.2 = D)
      = (Finset.antidiagonal (D + r)).filter
        (fun x : ℕ × ℕ => x.1 ≠ D ∧ x.2 ≠ D) := by
    rw [Finset.filter_filter]
  rw [hsq, ← hsplit1, h1, ← hsplit2, h2, hff]
  ring

/-- **Square certificate engine**: the upper window of `P²` pivots the block of `P`
with slope 2; every coefficient of `P² - x^{2D}` is supported on the block window
shifted by `D`. -/
theorem sq_cert_pivot (hPm : P.Monic) (hPd : P.natDegree = D)
    (hP : CoeffTriangular K β (fun _ => (1 : R)) e 0 (P - X ^ D))
    (heD : e + 1 ≤ D) {r : ℕ} (hr : r < e) :
    ∃ F ∈ K ⊔ adjoin R (β '' Set.Ico (r + 1) e),
      (P ^ 2).coeff (D + r) = 2 * β r + F := by
  have hcomb0 : ∀ (W : A[X]) (i : ℕ), (combined (0 : A[X]) W).coeff i = W.coeff i :=
    fun W i => coeff_combined_zero_left W i
  set V := K ⊔ adjoin R (β '' Set.Ico (r + 1) e) with hV
  have hPW : ∀ m, r + 1 ≤ m → P.coeff m ∈ V := by
    intro m hm
    have hs : P.coeff m = (P - X ^ D).coeff m + (X ^ D : A[X]).coeff m := by
      rw [coeff_sub]; ring
    rw [hs]
    refine Subalgebra.add_mem _ ?_ ?_
    · have h1 := hP.supp₂ m
      exact SetLike.le_def.1 (sup_le_sup_left
        (adjoin_mono (Set.image_mono (Set.Ico_subset_Ico (by omega) le_rfl))) K) h1
    · rw [coeff_X_pow]
      split
      · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  obtain ⟨F', hF', hFe⟩ := hP.pivot r hr
  rw [hcomb0] at hFe
  have hPr : P.coeff r = β r + F' := by
    have hX : ((X : A[X]) ^ D).coeff r = 0 := by
      rw [coeff_X_pow, if_neg (by omega)]
    have := hFe
    rw [coeff_sub, hX, sub_zero, map_one, one_mul] at this
    exact this
  have hF'V : F' ∈ V := by
    refine SetLike.le_def.1 (sup_le (le_sup_left : K ≤ _) (adjoin_le ?_)) hF'
    rintro _ ⟨g, ⟨hg1, hg2⟩, rfl⟩
    exact (le_sup_right : adjoin R _ ≤ _) (subset_adjoin ⟨g, ⟨hg1, hg2⟩, rfl⟩)
  have hrest : (∑ x ∈ (Finset.antidiagonal (D + r)).filter
      (fun x : ℕ × ℕ => x.1 ≠ D ∧ x.2 ≠ D),
        P.coeff x.1 * P.coeff x.2) ∈ V := by
    refine Subalgebra.sum_mem _ fun x hx => ?_
    obtain ⟨hxf, hne1, hne2⟩ : x ∈ Finset.antidiagonal (D + r) ∧ x.1 ≠ D ∧ x.2 ≠ D := by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact ⟨h1, h2.1, h2.2⟩
    have hxa : x.1 + x.2 = D + r := Finset.mem_antidiagonal.1 hxf
    rcases Nat.lt_or_ge D x.1 with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge D x.2 with hgt2 | hle2
      · rw [show P.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
          mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hPW x.1 (by omega)) (hPW x.2 (by omega))
  refine ⟨2 * F' + (∑ x ∈ (Finset.antidiagonal (D + r)).filter
      (fun x : ℕ × ℕ => x.1 ≠ D ∧ x.2 ≠ D), P.coeff x.1 * P.coeff x.2), ?_, ?_⟩
  · refine Subalgebra.add_mem _ ?_ hrest
    have h2 : (2 : A) ∈ K := by
      have := Subalgebra.one_mem K
      have h2' : (2 : A) = 1 + 1 := by norm_num
      rw [h2']
      exact Subalgebra.add_mem _ this this
    exact Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) h2) hF'V
  · rw [sq_coeff_split hPd hPm (by omega), hPr]
    ring

/-- Support half of the square engine: every coefficient of `P² - x^{2D}` lies in the
`D`-shifted block window. -/
theorem sq_cert_supp (hPm : P.Monic) (hPd : P.natDegree = D)
    (hP : CoeffTriangular K β (fun _ => (1 : R)) e 0 (P - X ^ D)) :
    ∀ m, (P ^ 2 - X ^ (2 * D)).coeff m ∈ K ⊔ adjoin R (β '' Set.Ico (m - D) e) := by
  intro m
  set V := K ⊔ adjoin R (β '' Set.Ico (m - D) e) with hV
  have hPW : ∀ c, m - D ≤ c → P.coeff c ∈ V := by
    intro c hc
    have hs : P.coeff c = (P - X ^ D).coeff c + (X ^ D : A[X]).coeff c := by
      rw [coeff_sub]; ring
    rw [hs]
    refine Subalgebra.add_mem _ ?_ ?_
    · have h1 := hP.supp₂ c
      exact SetLike.le_def.1 (sup_le_sup_left
        (adjoin_mono (Set.image_mono (Set.Ico_subset_Ico (by omega) le_rfl))) K) h1
    · rw [coeff_X_pow]
      split
      · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
      · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  rw [coeff_sub, sq, coeff_mul]
  refine Subalgebra.sub_mem _ (Subalgebra.sum_mem _ fun x hx => ?_) ?_
  · have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge D x.1 with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge D x.2 with hgt2 | hle2
      · rw [show P.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
          mul_zero]
        exact Subalgebra.zero_mem _
      · exact Subalgebra.mul_mem _ (hPW x.1 (by omega)) (hPW x.2 (by omega))
  · rw [coeff_X_pow]
    split
    · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
    · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)


section windowedShift

variable {K K' : Subalgebra R A} {α : ℕ → A} {lam : ℕ → R} {d : ℕ} {R₁ R₂ : A[X]}

/-- Certificates are monotone in the known subalgebra. -/
theorem CoeffTriangular.mono_left (hKK : K ≤ K')
    (h : CoeffTriangular K α lam d R₁ R₂) : CoeffTriangular K' α lam d R₁ R₂ where
  unit := h.unit
  supp₁ j := SetLike.le_def.1 (sup_le_sup_right hKK _) (h.supp₁ j)
  supp₂ j := SetLike.le_def.1 (sup_le_sup_right hKK _) (h.supp₂ j)
  pivot j hj := by
    obtain ⟨F, hF, hFe⟩ := h.pivot j hj
    exact ⟨F, SetLike.le_def.1 (sup_le_sup_right hKK _) hF, hFe⟩

end windowedShift


section coeffClosure

variable {S : Subalgebra R A} {P E : A[X]}

/-- Coefficients of a product stay in a subalgebra containing both factors'. -/
theorem coeff_mem_mul (hP : ∀ j, P.coeff j ∈ S) (hE : ∀ j, E.coeff j ∈ S) :
    ∀ j, (P * E).coeff j ∈ S := by
  intro j
  rw [coeff_mul]
  exact Subalgebra.sum_mem _ fun x hx =>
    Subalgebra.mul_mem _ (hP x.1) (hE x.2)

/-- Coefficients of a constant shift stay in a subalgebra containing the
polynomial's coefficients and the shift. -/
theorem coeff_add_C_mem {c : A} (hP : ∀ j, P.coeff j ∈ S) (hc : c ∈ S) :
    ∀ j, (P + C c).coeff j ∈ S := by
  intro j
  rw [coeff_add, coeff_C]
  refine Subalgebra.add_mem _ (hP j) ?_
  split
  · exact hc
  · exact Subalgebra.zero_mem _

theorem coeff_mem_pow (hP : ∀ j, P.coeff j ∈ S) :
    ∀ (n : ℕ) (j : ℕ), (P ^ n).coeff j ∈ S := by
  intro n
  induction n with
  | zero =>
    intro j
    rw [pow_zero, coeff_one]
    split
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | succ n ih =>
    intro j
    rw [pow_succ]
    exact coeff_mem_mul ih hP j

theorem coeff_mem_binTail (hP : ∀ j, P.coeff j ∈ S) (hE : ∀ j, E.coeff j ∈ S)
    (m : ℕ) : ∀ j, (binTail P E m).coeff j ∈ S := by
  intro j
  show (∑ q ∈ Finset.Icc 2 m, E ^ q * P ^ (m - q) * ((m.choose q : ℕ) : A[X])).coeff j
    ∈ S
  rw [Polynomial.finset_sum_coeff]
  refine Subalgebra.sum_mem _ fun q hq => ?_
  refine coeff_mem_mul (coeff_mem_mul (coeff_mem_pow hE q) (coeff_mem_pow hP (m - q)))
    (fun i => ?_) j
  rw [← Polynomial.C_eq_natCast, coeff_C]
  split
  · exact Subalgebra.natCast_mem _ _
  · exact Subalgebra.zero_mem _

end coeffClosure

/-- Closure engine for `uTail`. -/
theorem coeff_mem_uTail {S : Subalgebra R A} {H U : A[X]}
    (hH : ∀ j, H.coeff j ∈ S) (hU : ∀ j, U.coeff j ∈ S) (n : ℕ) :
    ∀ j, (uTail H U n).coeff j ∈ S := by
  intro j
  show (∑ t ∈ Finset.Icc 3 (n + 1),
    ((n.choose t : A[X]) - (n : A[X]) * (n.choose (t - 1) : A[X]))
      * (U ^ t * H ^ (n + 1 - t))).coeff j ∈ S
  rw [Polynomial.finset_sum_coeff]
  refine Subalgebra.sum_mem _ fun t ht => ?_
  refine coeff_mem_mul (fun i => ?_)
    (coeff_mem_mul (coeff_mem_pow hU t) (coeff_mem_pow hH (n + 1 - t))) j
  rw [show ((n.choose t : A[X]) - (n : A[X]) * (n.choose (t - 1) : A[X]))
      = C (((n.choose t : ℕ) : A) - ((n : ℕ) : A) * ((n.choose (t - 1) : ℕ) : A))
    from by rw [map_sub, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast,
      Polynomial.C_eq_natCast], coeff_C]
  split
  · exact Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _))
  · exact Subalgebra.zero_mem _

section principal

variable {H U : A[X]} {D r n : ℕ}

/-- Boundary extraction for a product against a monic factor of known degree. -/
theorem mul_coeff_boundary {P L : A[X]} {D : ℕ} (hL : L.Monic) (hLd : L.natDegree = D)
    (m : ℕ) :
    (P * L).coeff (D + m) = P.coeff m
      + ∑ x ∈ (Finset.antidiagonal (D + m)).filter (fun x : ℕ × ℕ => x.2 ≠ D),
        P.coeff x.1 * L.coeff x.2 := by
  have h := coeff_mul_split_snd P L (D + m) D
  rw [h, if_pos (by omega), show D + m - D = m from by omega, ← hLd,
    hL.coeff_natDegree, mul_one]

/-- At its degree bound, `uTail`'s coefficient is a known constant (the `t = 3` term's
monic leading coefficient). -/
theorem uTail_coeff_bound {K : Subalgebra R A} {H U : A[X]} {D r n : ℕ}
    (hHm : H.Monic) (hHd : H.natDegree = D)
    (hUm : U.Monic) (hUd : U.natDegree = r) (hrD : r < D) :
    ∀ m, 3 * r + (n - 2) * D ≤ m → (uTail H U n).coeff m ∈ K := by
  intro m hm
  show (∑ t ∈ Finset.Icc 3 (n + 1),
    ((n.choose t : A[X]) - (n : A[X]) * (n.choose (t - 1) : A[X]))
      * (U ^ t * H ^ (n + 1 - t))).coeff m ∈ K
  rw [Polynomial.finset_sum_coeff]
  refine Subalgebra.sum_mem _ fun t ht => ?_
  obtain ⟨ht3, htn⟩ := Finset.mem_Icc.1 ht
  have hconst : ((n.choose t : A[X]) - (n : A[X]) * (n.choose (t - 1) : A[X]))
      = C (((n.choose t : ℕ) : A) - ((n : ℕ) : A) * ((n.choose (t - 1) : ℕ) : A)) := by
    rw [map_sub, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast,
      Polynomial.C_eq_natCast]
  rw [hconst, coeff_C_mul]
  refine Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _)
    (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _)
      (Subalgebra.natCast_mem _ _))) ?_
  have hptm : (U ^ t * H ^ (n + 1 - t)).Monic := (hUm.pow t).mul (hHm.pow _)
  have hptd : (U ^ t * H ^ (n + 1 - t)).natDegree = t * r + (n + 1 - t) * D := by
    rw [(hUm.pow t).natDegree_mul (hHm.pow _), hUm.natDegree_pow, hHm.natDegree_pow,
      hUd, hHd]
  -- degree comparison: t·r + (n+1-t)·D ≤ 3r + (n-2)·D, strict for t > 3
  rcases Nat.eq_or_lt_of_le ht3 with heq3 | ht4
  · -- t = 3: at the bound, 0 or the monic leading 1
    subst heq3
    have hnn : (n + 1 - 3) * D = (n - 2) * D := rfl
    rcases Nat.lt_or_ge (3 * r + (n + 1 - 3) * D) m with hgt | hle
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _
    · have hm' : m = (U ^ 3 * H ^ (n + 1 - 3)).natDegree := by omega
      rw [hm', hptm.coeff_natDegree]
      exact Subalgebra.one_mem _
  · -- t ≥ 4: strictly below the bound
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 4 := ⟨t - 4, by omega⟩
    have hb1 : (u + 4) * r = (u + 1) * r + 3 * r := by ring
    have hb2 : (n - 2) * D = (n + 1 - (u + 4)) * D + (u + 1) * D := by
      have hmd : n - 2 = (n + 1 - (u + 4)) + (u + 1) := by omega
      rw [hmd, Nat.add_mul]
    have hur : (u + 1) * r < (u + 1) * D := mul_lt_mul_of_pos_left hrD (by omega)
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Subalgebra.zero_mem _

/-- **Generic principal exposure**: for a certified sub-block `U` of a monic `H` with
`D = 2r`, the odd principal `-(n•U)`-perturbed power exposes the block's slots in its
top window with constant slope `-(n+1)·n`. -/
theorem principal_expose {K : Subalgebra R A} {β : ℕ → A} {H U : A[X]} {D r e n : ℕ}
    (hHm : H.Monic) (hHd : H.natDegree = D) (hHK : ∀ i, H.coeff i ∈ K)
    (hUm : U.Monic) (hUd : U.natDegree = r)
    (hUc : CoeffTriangular K β (fun _ => (1 : R)) e 0 (U - X ^ r))
    (h2r : 2 * r = D) (hr2 : 1 ≤ r) (her : e + 1 ≤ r) (hn : 2 ≤ n) :
    ∀ g, g < e → ∃ F ∈ K ⊔ adjoin R (β '' Set.Ico (g + 1) e),
      ((H - n • U) * (H + U) ^ n - H ^ (n + 1)).coeff ((n - 1) * D + r + g)
        = -(((n + 1) * n : ℕ) : A) * β g + F := by
  intro g hg
  have hDpos : 1 ≤ D := by omega
  -- the split
  have hW : H - n • U = H - (n : A[X]) * U := by
    rw [nsmul_eq_mul]
  have hsplit := mul_pow_split H U (n := n) hn
  -- constant normalization
  have hconst : ((n.choose 2 : A[X]) - (n : A[X]) * (n : A[X]))
      = C (((n.choose 2 : ℕ) : A) - ((n : ℕ) : A) * ((n : ℕ) : A)) := by
    rw [map_sub, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_natCast]
  -- coefficient at the exposure row
  set m := (n - 1) * D + r + g with hm
  have hprin : ((H - n • U) * (H + U) ^ n - H ^ (n + 1)).coeff m
      = (((n.choose 2 : ℕ) : A) - ((n : ℕ) : A) * ((n : ℕ) : A))
          * (U ^ 2 * H ^ (n - 1)).coeff m
        + (uTail H U n).coeff m := by
    rw [hW, show (H - (n : A[X]) * U) * (H + U) ^ n - H ^ (n + 1)
        = ((n.choose 2 : A[X]) - (n : A[X]) * (n : A[X])) * (U ^ 2 * H ^ (n - 1))
          + uTail H U n from by rw [hsplit]; ring,
      coeff_add, hconst, coeff_C_mul]
  -- the square-shift boundary
  have hLm : (H ^ (n - 1)).Monic := hHm.pow _
  have hLd : (H ^ (n - 1)).natDegree = (n - 1) * D := by
    rw [hHm.natDegree_pow, hHd]
  have hbord := mul_coeff_boundary (P := U ^ 2) (L := H ^ (n - 1)) hLm hLd (r + g)
  have hmidx : (n - 1) * D + (r + g) = m := by omega
  rw [hmidx] at hbord
  -- the square pivot
  obtain ⟨F', hF', hFe⟩ := sq_cert_pivot hUm hUd hUc (by omega) hg
  rw [hFe] at hbord
  -- uTail membership
  have huT : (uTail H U n).coeff m ∈ K := by
    refine uTail_coeff_bound hHm hHd hUm hUd (by omega) m ?_
    have : 3 * r + (n - 2) * D + g = m := by
      have hD2 : D = r + r := by omega
      have hnd : (n - 1) * D = (n - 2) * D + D := by
        have : n - 1 = (n - 2) + 1 := by omega
        rw [this, Nat.add_mul, one_mul]
      omega
    omega
  -- rest-sum membership (strict window)
  have hrest : (∑ x ∈ (Finset.antidiagonal m).filter
      (fun x : ℕ × ℕ => x.2 ≠ (n - 1) * D),
        (U ^ 2).coeff x.1 * (H ^ (n - 1)).coeff x.2)
      ∈ K ⊔ adjoin R (β '' Set.Ico (g + 1) e) := by
    refine Subalgebra.sum_mem _ fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
    have hxa : x.1 + x.2 = m := Finset.mem_antidiagonal.1 hx1
    rcases Nat.lt_or_ge ((n - 1) * D) x.2 with hgt | hle
    · rw [show (H ^ (n - 1)).coeff x.2 = 0 from
        coeff_eq_zero_of_natDegree_lt (by rw [hLd]; exact hgt), mul_zero]
      exact Subalgebra.zero_mem _
    · have hx1lb : r + g < x.1 := by omega
      have hsupp := sq_cert_supp hUm hUd hUc x.1
      refine Subalgebra.mul_mem _ ?_
        ((le_sup_left : K ≤ _) (coeff_mem_pow hHK (n - 1) x.2))
      have hsub : Set.Ico (x.1 - r) e ⊆ Set.Ico (g + 1) e :=
        Set.Ico_subset_Ico (by omega) le_rfl
      have hXz : (U ^ 2).coeff x.1 = (U ^ 2 - X ^ (2 * r)).coeff x.1
          + (X ^ (2 * r) : A[X]).coeff x.1 := by
        rw [coeff_sub]
        ring
      rw [hXz]
      refine Subalgebra.add_mem _ ?_ ?_
      · exact SetLike.le_def.1 (sup_le_sup_left
          (adjoin_mono (Set.image_mono hsub)) K) hsupp
      · rw [coeff_X_pow]
        split
        · exact (le_sup_left : K ≤ _) (Subalgebra.one_mem _)
        · exact (le_sup_left : K ≤ _) (Subalgebra.zero_mem _)
  -- constant algebra
  have hcK : (((n.choose 2 : ℕ) : A) - ((n : ℕ) : A) * ((n : ℕ) : A)) ∈ K :=
    Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _))
  have hF'W : F' ∈ K ⊔ adjoin R (β '' Set.Ico (g + 1) e) := hF'
  refine ⟨(((n.choose 2 : ℕ) : A) - ((n : ℕ) : A) * ((n : ℕ) : A)) * (F' +
      (∑ x ∈ (Finset.antidiagonal m).filter
        (fun x : ℕ × ℕ => x.2 ≠ (n - 1) * D),
          (U ^ 2).coeff x.1 * (H ^ (n - 1)).coeff x.2))
    + (uTail H U n).coeff m, ?_, ?_⟩
  · exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) hcK)
      (Subalgebra.add_mem _ hF'W hrest)) ((le_sup_left : K ≤ _) huT)
  · have hslope : (((n.choose 2 : ℕ) : A) - ((n : ℕ) : A) * ((n : ℕ) : A)) * 2
        = -(((n + 1) * n : ℕ) : A) := by
      have h2dvd : 2 ∣ n * (n - 1) := by
        rcases Nat.even_or_odd n with he | ho
        · exact Dvd.dvd.mul_right he.two_dvd _
        · exact Dvd.dvd.mul_left (Nat.Odd.sub_odd ho odd_one).two_dvd _
      have hch : n.choose 2 * 2 = n * (n - 1) := by
        rw [Nat.choose_two_right, Nat.div_mul_cancel h2dvd]
      have hnsub : n * (n - 1) + n * 1 = n * n := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have h1 : (((n + 1) * n : ℕ) : A)
          = ((n : ℕ) : A) * ((n : ℕ) : A) + ((n : ℕ) : A) := by
        push_cast
        ring
      have hc2 : ((n.choose 2 * 2 : ℕ) : A) = ((n * (n - 1) : ℕ) : A) := by rw [hch]
      have hc3 : ((n * (n - 1) + n * 1 : ℕ) : A) = ((n * n : ℕ) : A) := by rw [hnsub]
      push_cast at hc2 hc3
      have h2 : ((n.choose 2 : ℕ) : A) * 2
          = ((n : ℕ) : A) * ((n : ℕ) : A) - ((n : ℕ) : A) := by
        linear_combination hc2 + hc3
      linear_combination h2 + h1
    rw [hprin, hbord]
    linear_combination β g * hslope

end principal

/-- High coefficients of a power are known when the base's are. -/
theorem coeff_pow_high_K {K : Subalgebra R A} {U : A[X]} {D : ℕ}
    (hUd : U.natDegree ≤ D) (hUK : ∀ a, D - 1 ≤ a → U.coeff a ∈ K) :
    ∀ (n : ℕ) (b : ℕ), n * D - 1 ≤ b → (U ^ n).coeff b ∈ K := by
  intro n
  induction n with
  | zero =>
    intro b hb
    rw [pow_zero, coeff_one]
    split
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | succ n ih =>
    intro b hb
    rw [pow_succ, coeff_mul]
    refine Subalgebra.sum_mem _ fun x hx => ?_
    have hxa : x.1 + x.2 = b := Finset.mem_antidiagonal.1 hx
    rcases Nat.lt_or_ge (n * D) x.1 with hgt | hle
    · rw [show (U ^ n).coeff x.1 = 0 from coeff_eq_zero_of_natDegree_lt (by
        have : (U ^ n).natDegree ≤ n * D :=
          le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hUd)
        omega), zero_mul]
      exact Subalgebra.zero_mem _
    · rcases Nat.lt_or_ge D x.2 with hgt2 | hle2
      · rw [show U.coeff x.2 = 0 from coeff_eq_zero_of_natDegree_lt (by omega),
          mul_zero]
        exact Subalgebra.zero_mem _
      · have hb1 : (n + 1) * D = n * D + D := by ring
        exact Subalgebra.mul_mem _ (ih x.1 (by omega)) (hUK x.2 (by omega))

/-- Absorb a two-layer adjoin context into a single window: if both generator sets
land in `T`, then `(K ⊔ adjoin S₁) ⊔ adjoin S₂ ≤ K ⊔ adjoin T`. -/
theorem mem_sup_adjoin_pair {K : Subalgebra R A} {S₁ S₂ T : Set A} {x : A}
    (h₁ : S₁ ⊆ T) (h₂ : S₂ ⊆ T)
    (hx : x ∈ (K ⊔ adjoin R S₁) ⊔ adjoin R S₂) : x ∈ K ⊔ adjoin R T :=
  SetLike.le_def.1 (sup_le (sup_le le_sup_left
    (le_trans (adjoin_mono h₁) le_sup_right))
    (le_trans (adjoin_mono h₂) le_sup_right)) hx

/-- Extract `IsUnit (2 : R)` from a `ℤ`-cast admissibility hypothesis. -/
theorem isUnit_two_of_cast {R : Type*} [CommRing R] {n : ℕ}
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R)) (hn : 2 ≤ n) :
    IsUnit (2 : R) := by
  have h := hadm 2 (by omega) hn
  rwa [show (((2 : ℕ) : ℤ) : R) = (2 : R) from by push_cast; ring] at h

end FastPoly
