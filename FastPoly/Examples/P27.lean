import FastPoly.Polynomial.CausalShell
import FastPoly.Section4.FillRec

/-!
# The degree-27 special construction

The proof treats the three inner gadgets as opaque monic polynomials of degrees `13`, `3`,
and `7`.  Its mathematical content is the outer descending decoder: three applications of
the relative square-shell theorem, with seam coefficients `+1`, `-1`, and `+1`, followed by
four scalar pivots.  Conditional decoders for `Q₁₃`, `Q₇`, and `Q₃` can therefore be
composed afterwards, in that order, without circular side information.
-/

namespace FastPoly.P27

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

noncomputable def H2 (a : ℕ → A) : A[X] :=
  (X + C (a 3)) * X + C (a 2)

noncomputable def T1 (a : ℕ → A) (A13 B3 : A[X]) : A[X] :=
  A13 ^ 2 - B3 ^ 2 + C (a 1)

noncomputable def T2 (a : ℕ → A) (A13 B3 C7 : A[X]) : A[X] :=
  T1 a A13 B3 + C7 ^ 2 - H2 a ^ 2 + C (a 0)

noncomputable def Phi (a : ℕ → A) (A13 B3 C7 : A[X]) : A[X] :=
  combined (T1 a A13 B3) (T2 a A13 B3 C7)

noncomputable def V (K : Subalgebra R A) (a : ℕ → A)
    (A13 B3 C7 : A[X]) (t : ℕ) : Subalgebra R A :=
  Vis R K (Phi a A13 B3 C7) (range 27) t

/-! The three successive residuals of the decoder. -/

noncomputable def EA (a : ℕ → A) (B3 C7 : A[X]) : A[X] :=
  -((X + 1) * B3 ^ 2) + (X + 1) * C (a 1) + C7 ^ 2 - H2 a ^ 2 + C (a 0)

noncomputable def EC (a : ℕ → A) (B3 : A[X]) : A[X] :=
  -((X + 1) * B3 ^ 2) + (X + 1) * C (a 1) - H2 a ^ 2 + C (a 0)

noncomputable def EB (a : ℕ → A) : A[X] :=
  -((X + 1) * C (a 1)) + H2 a ^ 2 - C (a 0)

noncomputable def L (a : ℕ → A) : A[X] :=
  (X + 1) * C (a 1) - H2 a ^ 2 + C (a 0)

theorem H2_eq (a : ℕ → A) :
    H2 a = X ^ 2 + C (a 3) * X + C (a 2) := by
  simp only [H2]
  ring

theorem Phi_eq (a : ℕ → A) (A13 B3 C7 : A[X]) :
    Phi a A13 B3 C7 = (X + 1) * A13 ^ 2 + EA a B3 C7 := by
  simp only [Phi, T1, T2, EA, combined]
  ring

theorem EA_eq (a : ℕ → A) (B3 C7 : A[X]) :
    EA a B3 C7 = C7 ^ 2 + EC a B3 := by
  simp only [EA, EC]
  ring

theorem EC_eq (a : ℕ → A) (B3 : A[X]) :
    EC a B3 = -((X + 1) * B3 ^ 2) - EB a := by
  simp only [EC, EB]
  ring

theorem L_eq (a : ℕ → A) (B3 : A[X]) :
    L a = EC a B3 + (X + 1) * B3 ^ 2 := by
  simp only [L, EC]
  ring

theorem L_expanded (a : ℕ → A) :
    L a = -X ^ 4 + C (-2 * a 3) * X ^ 3 + C (-(a 3 ^ 2 + 2 * a 2)) * X ^ 2 +
      C (a 1 - 2 * a 3 * a 2) * X + C (a 1 - a 2 ^ 2 + a 0) := by
  simp only [L, H2_eq, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]
  ring

section structural

variable [Nontrivial A]

theorem H2_good (a : ℕ → A) : (H2 a).Monic ∧ (H2 a).natDegree = 2 := by
  have hm : ((X + C (a 3)) * X : A[X]).Monic := (monic_X_add_C (a 3)).mul monic_X
  have hd : ((X + C (a 3)) * X : A[X]).natDegree = 2 := by
    rw [(monic_X_add_C (a 3)).natDegree_mul monic_X, natDegree_X_add_C, natDegree_X]
  obtain ⟨hm', hd'⟩ := monic_add_low (e := C (a 2)) hm
    (Or.inr (by rw [natDegree_C, hd]; omega))
  exact ⟨hm', hd'.trans hd⟩

theorem X_add_one_good : ((X + 1 : A[X]).Monic ∧ (X + 1 : A[X]).natDegree = 1) := by
  constructor
  · simpa only [C_1] using monic_X_add_C (1 : A)
  · simpa only [C_1] using natDegree_X_add_C (1 : A)

theorem EB_natDegree_le (a : ℕ → A) : (EB a).natDegree ≤ 4 := by
  obtain ⟨h2m, h2d⟩ := H2_good a
  have h2sq : (H2 a ^ 2).natDegree = 4 := by rw [h2m.natDegree_pow, h2d]
  have hlin : ((X + 1) * C (a 1) : A[X]).natDegree ≤ 1 := by
    refine le_trans natDegree_mul_le ?_
    rw [X_add_one_good.2, natDegree_C]
  rw [EB]
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans (natDegree_add_le _ _)
      (max_le (by rw [natDegree_neg]; omega) (by omega))
  · rw [natDegree_C]
    omega

theorem EC_natDegree_le (a : ℕ → A) (B3 : A[X])
    (hBm : B3.Monic) (hBd : B3.natDegree = 3) : (EC a B3).natDegree ≤ 7 := by
  have hBsq : (B3 ^ 2).natDegree = 6 := by rw [hBm.natDegree_pow, hBd]
  have hprod : ((X + 1) * B3 ^ 2).natDegree = 7 := by
    rw [X_add_one_good.1.natDegree_mul (hBm.pow 2), X_add_one_good.2, hBsq]
  rw [EC_eq]
  exact le_trans (natDegree_sub_le _ _)
    (max_le (by rw [natDegree_neg, hprod]) (by have := EB_natDegree_le a; omega))

theorem EA_natDegree_le (a : ℕ → A) (B3 C7 : A[X])
    (hBm : B3.Monic) (hBd : B3.natDegree = 3)
    (hCm : C7.Monic) (hCd : C7.natDegree = 7) : (EA a B3 C7).natDegree ≤ 14 := by
  have hCsq : (C7 ^ 2).natDegree = 14 := by rw [hCm.natDegree_pow, hCd]
  rw [EA_eq]
  exact le_trans (natDegree_add_le _ _)
    (max_le (by omega) (by have := EC_natDegree_le a B3 hBm hBd; omega))

theorem EA_coeff_14 (a : ℕ → A) (B3 C7 : A[X])
    (hBm : B3.Monic) (hBd : B3.natDegree = 3)
    (hCm : C7.Monic) (hCd : C7.natDegree = 7) : (EA a B3 C7).coeff 14 = 1 := by
  have hCsqm : (C7 ^ 2).Monic := hCm.pow 2
  have hCsqd : (C7 ^ 2).natDegree = 14 := by rw [hCm.natDegree_pow, hCd]
  have hECz : (EC a B3).coeff 14 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by have := EC_natDegree_le a B3 hBm hBd; omega)
  rw [EA_eq, coeff_add, hECz, add_zero, ← hCsqd, hCsqm.coeff_natDegree]

theorem EC_coeff_7 (a : ℕ → A) (B3 : A[X])
    (hBm : B3.Monic) (hBd : B3.natDegree = 3) : (EC a B3).coeff 7 = -1 := by
  have hPm : ((X + 1) * B3 ^ 2 : A[X]).Monic := X_add_one_good.1.mul (hBm.pow 2)
  have hPd : ((X + 1) * B3 ^ 2 : A[X]).natDegree = 7 := by
    rw [X_add_one_good.1.natDegree_mul (hBm.pow 2), X_add_one_good.2,
      hBm.natDegree_pow, hBd]
  have hEBz : (EB a).coeff 7 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by have := EB_natDegree_le a; omega)
  rw [EC_eq, coeff_sub, coeff_neg, hEBz, sub_zero, ← hPd, hPm.coeff_natDegree]

theorem EB_coeff_4 (a : ℕ → A) : (EB a).coeff 4 = 1 := by
  obtain ⟨h2m, h2d⟩ := H2_good a
  have h2sqm : (H2 a ^ 2).Monic := h2m.pow 2
  have h2sqd : (H2 a ^ 2).natDegree = 4 := by rw [h2m.natDegree_pow, h2d]
  have hlin : ((X + 1) * C (a 1) : A[X]).natDegree ≤ 1 := by
    refine le_trans natDegree_mul_le ?_
    rw [X_add_one_good.2, natDegree_C]
  have hzlin : ((X + 1) * C (a 1) : A[X]).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hzc : (C (a 0) : A[X]).coeff 4 = 0 := by rw [coeff_C, if_neg (by omega)]
  rw [EB, coeff_sub, coeff_add, coeff_neg, hzlin, neg_zero, zero_add, hzc, sub_zero,
    ← h2sqd, h2sqm.coeff_natDegree]

theorem EA_coeff_zero_above (a : ℕ → A) (B3 C7 : A[X])
    (hBm : B3.Monic) (hBd : B3.natDegree = 3)
    (hCm : C7.Monic) (hCd : C7.natDegree = 7) {i : ℕ} (hi : 14 < i) :
    (EA a B3 C7).coeff i = 0 :=
  coeff_eq_zero_of_natDegree_lt (by have := EA_natDegree_le a B3 C7 hBm hBd hCm hCd; omega)

theorem EC_coeff_zero_above (a : ℕ → A) (B3 : A[X])
    (hBm : B3.Monic) (hBd : B3.natDegree = 3) {i : ℕ} (hi : 7 < i) :
    (EC a B3).coeff i = 0 :=
  coeff_eq_zero_of_natDegree_lt (by have := EC_natDegree_le a B3 hBm hBd; omega)

theorem EB_coeff_zero_above (a : ℕ → A) {i : ℕ} (hi : 4 < i) :
    (EB a).coeff i = 0 :=
  coeff_eq_zero_of_natDegree_lt (by have := EB_natDegree_le a; omega)

theorem T1_good (a : ℕ → A) (A13 B3 : A[X])
    (hAm : A13.Monic) (hAd : A13.natDegree = 13)
    (hBm : B3.Monic) (hBd : B3.natDegree = 3) :
    (T1 a A13 B3).Monic ∧ (T1 a A13 B3).natDegree = 26 := by
  have hAsqm : (A13 ^ 2).Monic := hAm.pow 2
  have hAsqd : (A13 ^ 2).natDegree = 26 := by rw [hAm.natDegree_pow, hAd]
  have hBsqd : (B3 ^ 2).natDegree = 6 := by rw [hBm.natDegree_pow, hBd]
  have he : (-B3 ^ 2 + C (a 1)).natDegree < 26 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · rw [natDegree_neg, hBsqd]
      norm_num
    · rw [natDegree_C]
      norm_num
  have hform : T1 a A13 B3 = A13 ^ 2 + (-B3 ^ 2 + C (a 1)) := by
    rw [T1]
    ring
  rw [hform]
  obtain ⟨hm, hd⟩ := monic_add_low (e := -B3 ^ 2 + C (a 1)) hAsqm
    (Or.inr (by rw [hAsqd]; exact he))
  exact ⟨hm, hd.trans hAsqd⟩

theorem T2_good (a : ℕ → A) (A13 B3 C7 : A[X])
    (hAm : A13.Monic) (hAd : A13.natDegree = 13)
    (hBm : B3.Monic) (hBd : B3.natDegree = 3)
    (hCm : C7.Monic) (hCd : C7.natDegree = 7) :
    (T2 a A13 B3 C7).Monic ∧ (T2 a A13 B3 C7).natDegree = 26 := by
  obtain ⟨htm, htd⟩ := T1_good a A13 B3 hAm hAd hBm hBd
  have hCsqd : (C7 ^ 2).natDegree = 14 := by rw [hCm.natDegree_pow, hCd]
  obtain ⟨h2m, h2d⟩ := H2_good a
  have h2sqd : (H2 a ^ 2).natDegree = 4 := by rw [h2m.natDegree_pow, h2d]
  have he : (C7 ^ 2 - H2 a ^ 2 + C (a 0)).natDegree < 26 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt (by omega) (by omega))
    · rw [natDegree_C]
      norm_num
  have hform : T2 a A13 B3 C7 = T1 a A13 B3 +
      (C7 ^ 2 - H2 a ^ 2 + C (a 0)) := by
    rw [T2]
    ring
  rw [hform]
  obtain ⟨hm, hd⟩ := monic_add_low (e := C7 ^ 2 - H2 a ^ 2 + C (a 0)) htm
    (Or.inr (by rw [htd]; exact he))
  exact ⟨hm, hd.trans htd⟩

end structural

/-! ## Explicit outer decoder -/

structure OuterCert (K : Subalgebra R A) (a : ℕ → A) (A13 B3 C7 : A[X]) : Prop where
  low : ∀ i, i < 4 → a i ∈ V K a A13 B3 C7 i
  Acoeff : ∀ j, A13.coeff j ∈ V K a A13 B3 C7 (j + 14)
  Ccoeff : ∀ j, C7.coeff j ∈ V K a A13 B3 C7 (j + 7)
  Bcoeff : ∀ j, B3.coeff j ∈ V K a A13 B3 C7 (j + 4)
  h2coeff : ∀ j, (H2 a).coeff j ∈ V K a A13 B3 C7 (j + 2)

theorem V_antitone (K : Subalgebra R A) (a : ℕ → A) (A13 B3 C7 : A[X]) :
    Antitone (V K a A13 B3 C7) := fun _ _ hij => Vis_antitone_cutoff hij

theorem L_coeff_3 (a : ℕ → A) : (L a).coeff 3 = -2 * a 3 := by
  rw [L_expanded]
  simp only [coeff_add, coeff_neg, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem L_coeff_2 (a : ℕ → A) : (L a).coeff 2 = -(a 3 ^ 2 + 2 * a 2) := by
  rw [L_expanded]
  simp only [coeff_add, coeff_neg, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem L_coeff_1 (a : ℕ → A) : (L a).coeff 1 = a 1 - 2 * a 3 * a 2 := by
  rw [L_expanded]
  simp only [coeff_add, coeff_neg, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem L_coeff_0 (a : ℕ → A) : (L a).coeff 0 = a 1 - a 2 ^ 2 + a 0 := by
  rw [L_expanded]
  simp only [coeff_add, coeff_neg, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- The degree-27 decoder itself.  Each use of `coeff_mem_of_monic_mul_sq_relative`
records its seam correction in a separate hypothesis. -/
theorem outer_recover [Nontrivial A] (K : Subalgebra R A) (a : ℕ → A)
    (A13 B3 C7 : A[X]) (htwo : IsUnit (2 : R))
    (hAm : A13.Monic) (hAd : A13.natDegree = 13)
    (hBm : B3.Monic) (hBd : B3.natDegree = 3)
    (hCm : C7.Monic) (hCd : C7.natDegree = 7) :
    OuterCert K a A13 B3 C7 := by
  have hanti := V_antitone K a A13 B3 C7
  have lower : ∀ {x : A} {s t : ℕ}, t ≤ s → x ∈ V K a A13 B3 C7 s →
      x ∈ V K a A13 B3 C7 t := by
    intro x s t hst hx
    exact hanti hst hx
  -- Block A: `(X+1)A²`; the seam `EA₁₄=+1` is the leading coefficient of `C²`.
  have hA : ∀ j, A13.coeff j ∈ V K a A13 B3 C7 (j + 14) := by
    intro j
    have hh := coeff_mem_of_X_add_one_mul_sq K hAm hAd htwo
      (fun i hi => EA_coeff_zero_above a B3 C7 hBm hBd hCm hCd hi)
      (show (EA a B3 C7).coeff 14 ∈ K by
        rw [EA_coeff_14 a B3 C7 hBm hBd hCm hCd]
        exact Subalgebra.one_mem _)
      (Phi_eq a A13 B3 C7) j
    simpa only [show 13 + j + 1 = j + 14 by omega] using hh
  have hAsq : ∀ j, (A13 ^ 2).coeff j ∈ V K a A13 B3 C7 (j + 1) := by
    refine coeff_sq_mem_of_schedule _ hanti (le_of_eq hAd) ?_
    intro i
    simpa only [show i + 13 + 1 = i + 14 by omega] using hA i
  have hXAsq : ∀ j, ((X + 1) * A13 ^ 2).coeff j ∈ V K a A13 B3 C7 j :=
    coeff_X_add_one_mul_mem_of_schedule _ hanti hAsq
  have hEAvis : ∀ i, i < 27 → (EA a B3 C7).coeff i ∈ V K a A13 B3 C7 i := by
    intro i hi
    have hp : (Phi a A13 B3 C7).coeff i ∈ V K a A13 B3 C7 i :=
      coeff_mem_Vis (mem_range.2 hi) le_rfl
    have hkey : (EA a B3 C7).coeff i =
        (Phi a A13 B3 C7).coeff i - ((X + 1) * A13 ^ 2).coeff i := by
      rw [Phi_eq, coeff_add]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ hp (hXAsq i)
  -- Block C: the error `EC` reaches the seam with coefficient `-1`.
  have hC : ∀ j, C7.coeff j ∈ V K a A13 B3 C7 (j + 7) := by
    have hrec := coeff_mem_of_monic_mul_sq_relative (V K a A13 B3 C7) hanti
      (M := (1 : A[X])) (S := C7) (E := EC a B3) (Y := EA a B3 C7)
      (m := 0) (d := 7) monic_one natDegree_one
      (fun i t => coeff_one_mem_subalgebra (V K a A13 B3 C7 t) i)
      hCm hCd htwo
      (fun i _ hi => hEAvis i (by omega))
      (fun i hi => EC_coeff_zero_above a B3 hBm hBd hi)
      (by rw [EC_coeff_7 a B3 hBm hBd]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))
      (by rw [EA_eq]; ring)
    intro j
    simpa only [zero_add, Nat.add_comm] using hrec j
  have hCsq : ∀ j, (C7 ^ 2).coeff j ∈ V K a A13 B3 C7 j := by
    refine coeff_sq_mem_of_schedule _ hanti (P := C7) (d := 7) (e := 0)
      (le_of_eq hCd) ?_
    intro i
    simpa only [Nat.add_zero] using hC i
  have hECvis : ∀ i, i < 27 → (EC a B3).coeff i ∈ V K a A13 B3 C7 i := by
    intro i hi
    have hkey : (EC a B3).coeff i = (EA a B3 C7).coeff i - (C7 ^ 2).coeff i := by
      rw [EA_eq, coeff_add]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hEAvis i hi) (hCsq i)
  -- Block B: normalize the sign.  The seam `EB₄=+1` is the leading term of `H₂²`.
  have hB : ∀ j, B3.coeff j ∈ V K a A13 B3 C7 (j + 4) := by
    have hrec := coeff_mem_of_monic_mul_sq_relative (V K a A13 B3 C7) hanti
      (M := (X + 1 : A[X])) (S := B3) (E := EB a) (Y := -(EC a B3))
      (m := 1) (d := 3) X_add_one_good.1 X_add_one_good.2
      (fun i t => coeff_X_add_one_mem_subalgebra (V K a A13 B3 C7 t) i)
      hBm hBd htwo
      (fun i _ hi => Subalgebra.neg_mem _ (hECvis i (by omega)))
      (fun i hi => EB_coeff_zero_above a hi)
      (by rw [EB_coeff_4 a]; exact Subalgebra.one_mem _)
      (by rw [EC_eq]; ring)
    intro j
    simpa only [show 1 + 3 + j = j + 4 by omega] using hrec j
  have hBsq : ∀ j, (B3 ^ 2).coeff j ∈ V K a A13 B3 C7 (j + 1) := by
    refine coeff_sq_mem_of_schedule _ hanti (P := B3) (d := 3) (e := 1)
      (le_of_eq hBd) ?_
    intro i
    simpa only [show i + 3 + 1 = i + 4 by omega] using hB i
  have hXBsq : ∀ j, ((X + 1) * B3 ^ 2).coeff j ∈ V K a A13 B3 C7 j :=
    coeff_X_add_one_mul_mem_of_schedule _ hanti hBsq
  have hLvis : ∀ i, i < 27 → (L a).coeff i ∈ V K a A13 B3 C7 i := by
    intro i hi
    rw [L_eq]
    exact Subalgebra.add_mem _ (hECvis i hi) (hXBsq i)
  -- Final scalar block, rows 3,2,1,0.
  have htwoa3 : 2 * a 3 ∈ V K a A13 B3 C7 3 := by
    have hkey : 2 * a 3 = -(L a).coeff 3 := by rw [L_coeff_3]; ring
    rw [hkey]
    exact Subalgebra.neg_mem _ (hLvis 3 (by omega))
  have ha3 : a 3 ∈ V K a A13 B3 C7 3 := mem_of_two_mul_eq htwo htwoa3 rfl
  have ha3_2 := lower (show 2 ≤ 3 by omega) ha3
  have htwoa2 : 2 * a 2 ∈ V K a A13 B3 C7 2 := by
    have hkey : 2 * a 2 = -((L a).coeff 2 + a 3 * a 3) := by
      rw [L_coeff_2]
      ring
    rw [hkey]
    exact Subalgebra.neg_mem _
      (Subalgebra.add_mem _ (hLvis 2 (by omega)) (Subalgebra.mul_mem _ ha3_2 ha3_2))
  have ha2 : a 2 ∈ V K a A13 B3 C7 2 := mem_of_two_mul_eq htwo htwoa2 rfl
  have ha3_1 := lower (show 1 ≤ 3 by omega) ha3
  have ha2_1 := lower (show 1 ≤ 2 by omega) ha2
  have ha1 : a 1 ∈ V K a A13 B3 C7 1 := by
    have hkey : a 1 = (L a).coeff 1 + (a 3 * a 2 + a 3 * a 2) := by
      rw [L_coeff_1]
      ring
    rw [hkey]
    exact Subalgebra.add_mem _ (hLvis 1 (by omega))
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ ha3_1 ha2_1)
        (Subalgebra.mul_mem _ ha3_1 ha2_1))
  have ha1_0 := lower (show 0 ≤ 1 by omega) ha1
  have ha2_0 := lower (show 0 ≤ 2 by omega) ha2
  have ha0 : a 0 ∈ V K a A13 B3 C7 0 := by
    have hkey : a 0 = (L a).coeff 0 + a 2 * a 2 - a 1 := by
      rw [L_coeff_0]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _
      (Subalgebra.add_mem _ (hLvis 0 (by omega)) (Subalgebra.mul_mem _ ha2_0 ha2_0)) ha1_0
  have hH2coeff : ∀ j, (H2 a).coeff j ∈ V K a A13 B3 C7 (j + 2) := by
    intro j
    match j with
    | 0 =>
        rw [H2_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
        exact ha2
    | 1 =>
        rw [H2_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
        exact ha3
    | 2 =>
        obtain ⟨hm, hd⟩ := H2_good a
        rw [← hd, hm.coeff_natDegree]
        exact Subalgebra.one_mem _
    | j + 3 =>
        have hz : (H2 a).coeff (j + 3) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [(H2_good a).2]; omega)
        rw [hz]
        exact Subalgebra.zero_mem _
  refine ⟨?_, hA, hC, hB, hH2coeff⟩
  intro i hi
  match i with
  | 0 => exact ha0
  | 1 => exact ha1
  | 2 => exact ha2
  | 3 => exact ha3
  | i + 4 => omega

namespace OuterCert

theorem causal [Nontrivial A] {K : Subalgebra R A} {a : ℕ → A} {A13 B3 C7 : A[X]}
    (h : OuterCert K a A13 B3 C7) (hAd : A13.natDegree = 13)
    (hBd : B3.natDegree = 3) (hCd : C7.natDegree = 7) :
    CausalPair K (T1 a A13 B3) (T2 a A13 B3 C7) (range 27) := by
  have hanti := V_antitone K a A13 B3 C7
  have lower : ∀ {x : A} {s t : ℕ}, t ≤ s → x ∈ V K a A13 B3 C7 s →
      x ∈ V K a A13 B3 C7 t := by
    intro x s t hst hx
    exact hanti hst hx
  have hAsq : ∀ j, (A13 ^ 2).coeff j ∈ V K a A13 B3 C7 (j + 1) := by
    refine coeff_sq_mem_of_schedule _ hanti (P := A13) (d := 13) (e := 1)
      (le_of_eq hAd) ?_
    intro i
    simpa only [show i + 13 + 1 = i + 14 by omega] using h.Acoeff i
  have hBsq : ∀ j, (B3 ^ 2).coeff j ∈ V K a A13 B3 C7 (j + 1) := by
    refine coeff_sq_mem_of_schedule _ hanti (P := B3) (d := 3) (e := 1)
      (le_of_eq hBd) ?_
    intro i
    simpa only [show i + 3 + 1 = i + 4 by omega] using h.Bcoeff i
  have hCsq : ∀ j, (C7 ^ 2).coeff j ∈ V K a A13 B3 C7 j := by
    refine coeff_sq_mem_of_schedule _ hanti (P := C7) (d := 7) (e := 0)
      (le_of_eq hCd) ?_
    intro i
    simpa only [Nat.add_zero] using h.Ccoeff i
  have hH2sq : ∀ j, (H2 a ^ 2).coeff j ∈ V K a A13 B3 C7 j := by
    refine coeff_sq_mem_of_schedule _ hanti (P := H2 a) (d := 2) (e := 0)
      (le_of_eq (H2_good a).2) ?_
    intro i
    simpa only [Nat.add_zero] using h.h2coeff i
  have ht1 : ∀ j, (T1 a A13 B3).coeff j ∈ V K a A13 B3 C7 (j + 1) := by
    intro j
    rw [T1, coeff_add, coeff_sub, coeff_C]
    have hmain := Subalgebra.sub_mem _ (hAsq j) (hBsq j)
    split
    · subst j
      exact Subalgebra.add_mem _ hmain (h.low 1 (by omega))
    · exact Subalgebra.add_mem _ hmain (Subalgebra.zero_mem _)
  have ht2 : ∀ j, (T2 a A13 B3 C7).coeff j ∈ V K a A13 B3 C7 j := by
    intro j
    rw [T2, coeff_add, coeff_sub, coeff_add, coeff_C]
    have hmain := Subalgebra.sub_mem _
      (Subalgebra.add_mem _ (lower (by omega) (ht1 j)) (hCsq j)) (hH2sq j)
    split
    · subst j
      exact Subalgebra.add_mem _ hmain (h.low 0 (by omega))
    · exact Subalgebra.add_mem _ hmain (Subalgebra.zero_mem _)
  exact ⟨ht1, ht2⟩

end OuterCert

/-- The generic degree-27 outer shell is a compatible pair. -/
theorem shell_compatible [Nontrivial A] (K : Subalgebra R A) (a : ℕ → A)
    (A13 B3 C7 : A[X]) (htwo : IsUnit (2 : R))
    (hAm : A13.Monic) (hAd : A13.natDegree = 13)
    (hBm : B3.Monic) (hBd : B3.natDegree = 3)
    (hCm : C7.Monic) (hCd : C7.natDegree = 7) :
    CompatiblePair K (T1 a A13 B3) (T2 a A13 B3 C7) 26 (range 27) := by
  obtain ⟨ht1m, ht1d⟩ := T1_good a A13 B3 hAm hAd hBm hBd
  obtain ⟨ht2m, ht2d⟩ := T2_good a A13 B3 C7 hAm hAd hBm hBd hCm hCd
  exact
    { toCausalPair :=
        (outer_recover K a A13 B3 C7 htwo hAm hAd hBm hBd hCm hCd).causal hAd hBd hCd
      monic₁ := ht1m
      monic₂ := ht2m
      natDegree₁ := ht1d
      natDegree₂ := ht2d
      window := by intro i hi; simpa only using hi }

end FastPoly.P27
