import FastPoly.Polynomial.CausalShell
import FastPoly.Section4.FillRec

/-!
# The degree-31 special construction

This file formalizes the outer decoder of the paper's degree-31 cost base.  It follows
the displayed top-down algorithm exactly:

1. recover the monic degree-15 block and its scalar shift from the square gadget;
2. recover the degree-7 block from the relative shell `X * B²`, with seam `+1`;
3. recover the quartic from the shell `H²`, with seam `-1`;
4. read the residual `X * C + r` coefficient by coefficient.

The internal decoders for `barQ₁₅`, `Q₇`, and `Q₃` compose only after these outer
polynomials (and hence their required power data) have been reconstructed.
-/

namespace FastPoly.P31

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

noncomputable def T1 (_a : ℕ → A) (A15 B7 C3 : A[X]) : A[X] :=
  A15 ^ 2 - B7 ^ 2 + C3

noncomputable def T2 (a : ℕ → A) (A15 H4 : A[X]) : A[X] :=
  (A15 + C (a 15)) ^ 2 - H4 ^ 2 + C (a 0)

noncomputable def Phi (a : ℕ → A) (A15 B7 H4 C3 : A[X]) : A[X] :=
  combined (T1 a A15 B7 C3) (T2 a A15 H4)

noncomputable def V (K : Subalgebra R A) (a : ℕ → A)
    (A15 B7 H4 C3 : A[X]) (t : ℕ) : Subalgebra R A :=
  Vis R K (Phi a A15 B7 H4 C3) (range 31) t

/-! The three residuals exposed by the decoder. -/

noncomputable def EH (a : ℕ → A) (C3 : A[X]) : A[X] :=
  -(X * C3) - C (a 0)

noncomputable def EB (a : ℕ → A) (H4 C3 : A[X]) : A[X] :=
  H4 ^ 2 + EH a C3

noncomputable def EA (a : ℕ → A) (B7 H4 C3 : A[X]) : A[X] :=
  -(X * B7 ^ 2) - EB a H4 C3

noncomputable def L (a : ℕ → A) (C3 : A[X]) : A[X] :=
  -(EH a C3)

theorem Phi_eq (a : ℕ → A) (A15 B7 H4 C3 : A[X]) :
    Phi a A15 B7 H4 C3 =
      X * A15 ^ 2 + (A15 + C (a 15)) ^ 2 + EA a B7 H4 C3 := by
  simp only [Phi, T1, T2, EA, EB, EH, combined]
  ring

theorem neg_EA_eq (a : ℕ → A) (B7 H4 C3 : A[X]) :
    -(EA a B7 H4 C3) = B7 ^ 2 * X + EB a H4 C3 := by
  simp only [EA]
  ring

theorem EB_eq (a : ℕ → A) (H4 C3 : A[X]) :
    EB a H4 C3 = H4 ^ 2 + EH a C3 := rfl

theorem L_eq (a : ℕ → A) (C3 : A[X]) :
    L a C3 = X * C3 + C (a 0) := by
  simp only [L, EH]
  ring

theorem L_coeff_zero (a : ℕ → A) (C3 : A[X]) : (L a C3).coeff 0 = a 0 := by
  rw [L_eq, coeff_add, mul_coeff_zero, coeff_X_zero, zero_mul, zero_add, coeff_C_zero]

theorem L_coeff_succ (a : ℕ → A) (C3 : A[X]) (j : ℕ) :
    (L a C3).coeff (j + 1) = C3.coeff j := by
  rw [L_eq, coeff_add, coeff_X_mul, coeff_C, if_neg (by omega), add_zero]

section structural

variable [Nontrivial A]

theorem EH_natDegree_le (a : ℕ → A) (C3 : A[X])
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) : (EH a C3).natDegree ≤ 4 := by
  have hXC : (X * C3).natDegree = 4 := by
    rw [monic_X.natDegree_mul hCm, natDegree_X, hCd]
  rw [EH]
  exact le_trans (natDegree_sub_le _ _)
    (max_le (by rw [natDegree_neg, hXC]) (by rw [natDegree_C]; omega))

theorem EB_natDegree_le (a : ℕ → A) (H4 C3 : A[X])
    (hHm : H4.Monic) (hHd : H4.natDegree = 4)
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) :
    (EB a H4 C3).natDegree ≤ 8 := by
  have hHsq : (H4 ^ 2).natDegree = 8 := by rw [hHm.natDegree_pow, hHd]
  rw [EB]
  exact le_trans (natDegree_add_le _ _)
    (max_le (by omega) (by have := EH_natDegree_le a C3 hCm hCd; omega))

theorem EA_natDegree_le (a : ℕ → A) (B7 H4 C3 : A[X])
    (hBm : B7.Monic) (hBd : B7.natDegree = 7)
    (hHm : H4.Monic) (hHd : H4.natDegree = 4)
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) :
    (EA a B7 H4 C3).natDegree ≤ 15 := by
  have hBsq : (B7 ^ 2).natDegree = 14 := by rw [hBm.natDegree_pow, hBd]
  have hXB : (X * B7 ^ 2).natDegree = 15 := by
    rw [monic_X.natDegree_mul (hBm.pow 2), natDegree_X, hBsq]
  rw [EA]
  exact le_trans (natDegree_sub_le _ _)
    (max_le (by rw [natDegree_neg, hXB])
      (by have := EB_natDegree_le a H4 C3 hHm hHd hCm hCd; omega))

theorem EH_coeff_four (a : ℕ → A) (C3 : A[X])
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) : (EH a C3).coeff 4 = -1 := by
  have hXCm : (X * C3).Monic := monic_X.mul hCm
  have hXCd : (X * C3).natDegree = 4 := by
    rw [monic_X.natDegree_mul hCm, natDegree_X, hCd]
  have hc : (C (a 0) : A[X]).coeff 4 = 0 := by rw [coeff_C, if_neg (by omega)]
  rw [EH, coeff_sub, coeff_neg, hc, sub_zero, ← hXCd, hXCm.coeff_natDegree]

theorem EB_coeff_eight (a : ℕ → A) (H4 C3 : A[X])
    (hHm : H4.Monic) (hHd : H4.natDegree = 4)
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) :
    (EB a H4 C3).coeff 8 = 1 := by
  have hHsqm : (H4 ^ 2).Monic := hHm.pow 2
  have hHsqd : (H4 ^ 2).natDegree = 8 := by rw [hHm.natDegree_pow, hHd]
  have hEHz : (EH a C3).coeff 8 = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (by have := EH_natDegree_le a C3 hCm hCd; omega)
  rw [EB, coeff_add, hEHz, add_zero, ← hHsqd, hHsqm.coeff_natDegree]

theorem EA_coeff_fifteen (a : ℕ → A) (B7 H4 C3 : A[X])
    (hBm : B7.Monic) (hBd : B7.natDegree = 7)
    (hHm : H4.Monic) (hHd : H4.natDegree = 4)
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) :
    (EA a B7 H4 C3).coeff 15 = -1 := by
  have hXBm : (X * B7 ^ 2).Monic := monic_X.mul (hBm.pow 2)
  have hXBd : (X * B7 ^ 2).natDegree = 15 := by
    rw [monic_X.natDegree_mul (hBm.pow 2), natDegree_X, hBm.natDegree_pow, hBd]
  have hEBz : (EB a H4 C3).coeff 15 = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (by have := EB_natDegree_le a H4 C3 hHm hHd hCm hCd; omega)
  rw [EA, coeff_sub, coeff_neg, hEBz, sub_zero, ← hXBd, hXBm.coeff_natDegree]

theorem EH_coeff_zero_above (a : ℕ → A) (C3 : A[X])
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) {i : ℕ} (hi : 4 < i) :
    (EH a C3).coeff i = 0 :=
  coeff_eq_zero_of_natDegree_lt
    (by have := EH_natDegree_le a C3 hCm hCd; omega)

theorem EB_coeff_zero_above (a : ℕ → A) (H4 C3 : A[X])
    (hHm : H4.Monic) (hHd : H4.natDegree = 4)
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) {i : ℕ} (hi : 8 < i) :
    (EB a H4 C3).coeff i = 0 :=
  coeff_eq_zero_of_natDegree_lt
    (by have := EB_natDegree_le a H4 C3 hHm hHd hCm hCd; omega)

theorem EA_coeff_zero_above (a : ℕ → A) (B7 H4 C3 : A[X])
    (hBm : B7.Monic) (hBd : B7.natDegree = 7)
    (hHm : H4.Monic) (hHd : H4.natDegree = 4)
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) {i : ℕ} (hi : 15 < i) :
    (EA a B7 H4 C3).coeff i = 0 :=
  coeff_eq_zero_of_natDegree_lt
    (by have := EA_natDegree_le a B7 H4 C3 hBm hBd hHm hHd hCm hCd; omega)

theorem A_shift_good (a : ℕ → A) (A15 : A[X])
    (hAm : A15.Monic) (hAd : A15.natDegree = 15) :
    (A15 + C (a 15)).Monic ∧ (A15 + C (a 15)).natDegree = 15 := by
  obtain ⟨hm, hd'⟩ := monic_add_low (e := C (a 15)) hAm
    (Or.inr (by rw [natDegree_C, hAd]; omega))
  exact ⟨hm, hd'.trans hAd⟩

theorem T1_good (a : ℕ → A) (A15 B7 C3 : A[X])
    (hAm : A15.Monic) (hAd : A15.natDegree = 15)
    (hBm : B7.Monic) (hBd : B7.natDegree = 7)
    (hCd : C3.natDegree = 3) :
    (T1 a A15 B7 C3).Monic ∧ (T1 a A15 B7 C3).natDegree = 30 := by
  have hAsqm : (A15 ^ 2).Monic := hAm.pow 2
  have hAsqd : (A15 ^ 2).natDegree = 30 := by rw [hAm.natDegree_pow, hAd]
  have hBsqd : (B7 ^ 2).natDegree = 14 := by rw [hBm.natDegree_pow, hBd]
  have he : (-B7 ^ 2 + C3).natDegree < 30 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · rw [natDegree_neg, hBsqd]
      norm_num
    · omega
  have hform : T1 a A15 B7 C3 = A15 ^ 2 + (-B7 ^ 2 + C3) := by
    rw [T1]
    ring
  rw [hform]
  obtain ⟨hm, hd'⟩ := monic_add_low (e := -B7 ^ 2 + C3) hAsqm
    (Or.inr (by rw [hAsqd]; exact he))
  exact ⟨hm, hd'.trans hAsqd⟩

theorem T2_good (a : ℕ → A) (A15 H4 : A[X])
    (hAm : A15.Monic) (hAd : A15.natDegree = 15)
    (hHm : H4.Monic) (hHd : H4.natDegree = 4) :
    (T2 a A15 H4).Monic ∧ (T2 a A15 H4).natDegree = 30 := by
  obtain ⟨hSm, hSd⟩ := A_shift_good a A15 hAm hAd
  have hSsqm : ((A15 + C (a 15)) ^ 2).Monic := hSm.pow 2
  have hSsqd : ((A15 + C (a 15)) ^ 2).natDegree = 30 := by
    rw [hSm.natDegree_pow, hSd]
  have hHsqd : (H4 ^ 2).natDegree = 8 := by rw [hHm.natDegree_pow, hHd]
  have he : (-H4 ^ 2 + C (a 0)).natDegree < 30 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · rw [natDegree_neg, hHsqd]
      norm_num
    · rw [natDegree_C]
      norm_num
  have hform : T2 a A15 H4 = (A15 + C (a 15)) ^ 2 + (-H4 ^ 2 + C (a 0)) := by
    rw [T2]
    ring
  rw [hform]
  obtain ⟨hm, hd'⟩ := monic_add_low (e := -H4 ^ 2 + C (a 0)) hSsqm
    (Or.inr (by rw [hSsqd]; exact he))
  exact ⟨hm, hd'.trans hSsqd⟩

end structural

/-! ## Explicit outer decoder -/

structure OuterCert (K : Subalgebra R A) (a : ℕ → A)
    (A15 B7 H4 C3 : A[X]) : Prop where
  low : a 0 ∈ V K a A15 B7 H4 C3 0
  shift : a 15 ∈ V K a A15 B7 H4 C3 15
  Acoeff : ∀ j, A15.coeff j ∈ V K a A15 B7 H4 C3 (j + 16)
  Bcoeff : ∀ j, B7.coeff j ∈ V K a A15 B7 H4 C3 (j + 8)
  Hcoeff : ∀ j, H4.coeff j ∈ V K a A15 B7 H4 C3 (j + 4)
  Ccoeff : ∀ j, C3.coeff j ∈ V K a A15 B7 H4 C3 (j + 1)

theorem V_antitone (K : Subalgebra R A) (a : ℕ → A) (A15 B7 H4 C3 : A[X]) :
    Antitone (V K a A15 B7 H4 C3) := fun _ _ hij => Vis_antitone_cutoff hij

/-- The degree-31 outer decoder, with every seam coefficient supplied explicitly. -/
theorem outer_recover [Nontrivial A] (K : Subalgebra R A) (a : ℕ → A)
    (A15 B7 H4 C3 : A[X]) (htwo : IsUnit (2 : R))
    (hAm : A15.Monic) (hAd : A15.natDegree = 15)
    (hBm : B7.Monic) (hBd : B7.natDegree = 7)
    (hHm : H4.Monic) (hHd : H4.natDegree = 4)
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) :
    OuterCert K a A15 B7 H4 C3 := by
  have hanti := V_antitone K a A15 B7 H4 C3
  have lower : ∀ {x : A} {s t : ℕ}, t ≤ s → x ∈ V K a A15 B7 H4 C3 s →
      x ∈ V K a A15 B7 H4 C3 t := by
    intro x s t hst hx
    exact hanti hst hx
  -- Top square gadget: recover `A15` and the scalar shift at the `-1` seam.
  obtain ⟨hAraw, hs⟩ := coeff_mem_of_square_gadget_relative
    (V K a A15 B7 H4 C3) hanti hAm hAd (by omega) htwo
    (fun i _ hi => coeff_mem_Vis (mem_range.2 hi) le_rfl)
    (fun i hi => EA_coeff_zero_above a B7 H4 C3 hBm hBd hHm hHd hCm hCd hi)
    (by
      rw [EA_coeff_fifteen a B7 H4 C3 hBm hBd hHm hHd hCm hCd]
      exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))
    (Phi_eq a A15 B7 H4 C3)
  have hA : ∀ j, A15.coeff j ∈ V K a A15 B7 H4 C3 (j + 16) := by
    intro j
    simpa only [show 15 + j + 1 = j + 16 by omega] using hAraw j
  have hAsq : ∀ j, (A15 ^ 2).coeff j ∈ V K a A15 B7 H4 C3 (j + 1) := by
    refine coeff_sq_mem_of_schedule _ hanti (P := A15) (d := 15) (e := 1)
      (le_of_eq hAd) ?_
    intro i
    simpa only [show i + 15 + 1 = i + 16 by omega] using hA i
  have hXAsq : ∀ j, (X * A15 ^ 2).coeff j ∈ V K a A15 B7 H4 C3 j :=
    coeff_X_mul_mem_of_schedule _ hAsq
  have hAshift : ∀ i, (A15 + C (a 15)).coeff i ∈
      V K a A15 B7 H4 C3 (i + 15) := by
    intro i
    rw [coeff_add, coeff_C]
    split
    · subst i
      exact Subalgebra.add_mem _ (lower (by omega) (hA 0)) hs
    · exact Subalgebra.add_mem _ (lower (by omega) (hA i)) (Subalgebra.zero_mem _)
  have hAshiftSq : ∀ j, ((A15 + C (a 15)) ^ 2).coeff j ∈
      V K a A15 B7 H4 C3 j := by
    refine coeff_sq_mem_of_schedule _ hanti (P := A15 + C (a 15)) (d := 15) (e := 0)
      (le_of_eq (A_shift_good a A15 hAm hAd).2) ?_
    intro i
    simpa only [Nat.add_zero] using hAshift i
  have hEAvis : ∀ i, i < 31 →
      (EA a B7 H4 C3).coeff i ∈ V K a A15 B7 H4 C3 i := by
    intro i hi
    have hp : (Phi a A15 B7 H4 C3).coeff i ∈ V K a A15 B7 H4 C3 i :=
      coeff_mem_Vis (mem_range.2 hi) le_rfl
    have hkey : (EA a B7 H4 C3).coeff i =
        (Phi a A15 B7 H4 C3).coeff i - (X * A15 ^ 2).coeff i -
          ((A15 + C (a 15)) ^ 2).coeff i := by
      rw [Phi_eq, coeff_add, coeff_add]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hp (hXAsq i)) (hAshiftSq i)
  -- Degree-seven shell: `-EA = X*B7² + EB`, seam `+1` in row eight.
  have hB : ∀ j, B7.coeff j ∈ V K a A15 B7 H4 C3 (j + 8) := by
    have hrec := coeff_mem_of_monic_mul_sq_relative (V K a A15 B7 H4 C3) hanti
      (M := (X : A[X])) (S := B7) (E := EB a H4 C3) (Y := -(EA a B7 H4 C3))
      (m := 1) (d := 7) monic_X natDegree_X
      (fun i t => coeff_X_mem_subalgebra (V K a A15 B7 H4 C3 t) i)
      hBm hBd htwo
      (fun i _ hi => Subalgebra.neg_mem _ (hEAvis i (by omega)))
      (fun i hi => EB_coeff_zero_above a H4 C3 hHm hHd hCm hCd hi)
      (by
        rw [EB_coeff_eight a H4 C3 hHm hHd hCm hCd]
        exact Subalgebra.one_mem _)
      (neg_EA_eq a B7 H4 C3)
    intro j
    simpa only [show 1 + 7 + j = j + 8 by omega] using hrec j
  have hBsq : ∀ j, (B7 ^ 2).coeff j ∈ V K a A15 B7 H4 C3 (j + 1) := by
    refine coeff_sq_mem_of_schedule _ hanti (P := B7) (d := 7) (e := 1)
      (le_of_eq hBd) ?_
    intro i
    simpa only [show i + 7 + 1 = i + 8 by omega] using hB i
  have hXBsq : ∀ j, (X * B7 ^ 2).coeff j ∈ V K a A15 B7 H4 C3 j :=
    coeff_X_mul_mem_of_schedule _ hBsq
  have hEBvis : ∀ i, i < 31 →
      (EB a H4 C3).coeff i ∈ V K a A15 B7 H4 C3 i := by
    intro i hi
    have hpoly : EB a H4 C3 = -(EA a B7 H4 C3) - X * B7 ^ 2 := by
      simp only [EA]
      ring
    have hkey : (EB a H4 C3).coeff i =
        -(EA a B7 H4 C3).coeff i - (X * B7 ^ 2).coeff i := by
      rw [hpoly, coeff_sub, coeff_neg]
    rw [hkey]
    exact Subalgebra.sub_mem _ (Subalgebra.neg_mem _ (hEAvis i hi)) (hXBsq i)
  -- Quartic shell: `EB = H4² + EH`, seam `-1` in row four.
  have hH : ∀ j, H4.coeff j ∈ V K a A15 B7 H4 C3 (j + 4) := by
    have hrec := coeff_mem_of_monic_mul_sq_relative (V K a A15 B7 H4 C3) hanti
      (M := (1 : A[X])) (S := H4) (E := EH a C3) (Y := EB a H4 C3)
      (m := 0) (d := 4) monic_one natDegree_one
      (fun i t => coeff_one_mem_subalgebra (V K a A15 B7 H4 C3 t) i)
      hHm hHd htwo
      (fun i _ hi => hEBvis i (by omega))
      (fun i hi => EH_coeff_zero_above a C3 hCm hCd hi)
      (by
        rw [EH_coeff_four a C3 hCm hCd]
        exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))
      (by rw [EB_eq]; ring)
    intro j
    simpa only [zero_add, Nat.add_comm] using hrec j
  have hHsq : ∀ j, (H4 ^ 2).coeff j ∈ V K a A15 B7 H4 C3 j := by
    refine coeff_sq_mem_of_schedule _ hanti (P := H4) (d := 4) (e := 0)
      (le_of_eq hHd) ?_
    intro i
    simpa only [Nat.add_zero] using hH i
  have hLvis : ∀ i, i < 31 → (L a C3).coeff i ∈ V K a A15 B7 H4 C3 i := by
    intro i hi
    have hkey : (L a C3).coeff i = (H4 ^ 2).coeff i - (EB a H4 C3).coeff i := by
      rw [L, EB, coeff_neg, coeff_add]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hHsq i) (hEBvis i hi)
  have ha0 : a 0 ∈ V K a A15 B7 H4 C3 0 := by
    rw [← L_coeff_zero a C3]
    exact hLvis 0 (by omega)
  have hC : ∀ j, C3.coeff j ∈ V K a A15 B7 H4 C3 (j + 1) := by
    intro j
    by_cases hj : j + 1 < 31
    · rw [← L_coeff_succ a C3 j]
      exact hLvis (j + 1) hj
    · have hz : C3.coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hCd]; omega)
      rw [hz]
      exact Subalgebra.zero_mem _
  exact ⟨ha0, hs, hA, hB, hH, hC⟩

namespace OuterCert

theorem causal [Nontrivial A] {K : Subalgebra R A} {a : ℕ → A}
    {A15 B7 H4 C3 : A[X]} (h : OuterCert K a A15 B7 H4 C3)
    (hAd : A15.natDegree = 15) (hBd : B7.natDegree = 7)
    (hHd : H4.natDegree = 4) :
    CausalPair K (T1 a A15 B7 C3) (T2 a A15 H4) (range 31) := by
  have hanti := V_antitone K a A15 B7 H4 C3
  have lower : ∀ {x : A} {s t : ℕ}, t ≤ s → x ∈ V K a A15 B7 H4 C3 s →
      x ∈ V K a A15 B7 H4 C3 t := by
    intro x s t hst hx
    exact hanti hst hx
  have hAsq : ∀ j, (A15 ^ 2).coeff j ∈ V K a A15 B7 H4 C3 (j + 1) := by
    refine coeff_sq_mem_of_schedule _ hanti (P := A15) (d := 15) (e := 1)
      (le_of_eq hAd) ?_
    intro i
    simpa only [show i + 15 + 1 = i + 16 by omega] using h.Acoeff i
  have hBsq : ∀ j, (B7 ^ 2).coeff j ∈ V K a A15 B7 H4 C3 (j + 1) := by
    refine coeff_sq_mem_of_schedule _ hanti (P := B7) (d := 7) (e := 1)
      (le_of_eq hBd) ?_
    intro i
    simpa only [show i + 7 + 1 = i + 8 by omega] using h.Bcoeff i
  have ht1 : ∀ j, (T1 a A15 B7 C3).coeff j ∈ V K a A15 B7 H4 C3 (j + 1) := by
    intro j
    rw [T1, coeff_add, coeff_sub]
    exact Subalgebra.add_mem _ (Subalgebra.sub_mem _ (hAsq j) (hBsq j)) (h.Ccoeff j)
  have hAshift : ∀ i, (A15 + C (a 15)).coeff i ∈
      V K a A15 B7 H4 C3 (i + 15) := by
    intro i
    rw [coeff_add, coeff_C]
    split
    · subst i
      exact Subalgebra.add_mem _ (lower (by omega) (h.Acoeff 0)) h.shift
    · exact Subalgebra.add_mem _ (lower (by omega) (h.Acoeff i)) (Subalgebra.zero_mem _)
  have hAshiftSq : ∀ j, ((A15 + C (a 15)) ^ 2).coeff j ∈
      V K a A15 B7 H4 C3 j := by
    refine coeff_sq_mem_of_schedule _ hanti (P := A15 + C (a 15)) (d := 15) (e := 0)
      (by
        have hle : (A15 + C (a 15)).natDegree ≤ 15 := by
          refine le_trans (natDegree_add_le _ _) (max_le (le_of_eq hAd) ?_)
          rw [natDegree_C]
          omega
        exact hle) ?_
    intro i
    simpa only [Nat.add_zero] using hAshift i
  have hHsq : ∀ j, (H4 ^ 2).coeff j ∈ V K a A15 B7 H4 C3 j := by
    refine coeff_sq_mem_of_schedule _ hanti (P := H4) (d := 4) (e := 0)
      (le_of_eq hHd) ?_
    intro i
    simpa only [Nat.add_zero] using h.Hcoeff i
  have ht2 : ∀ j, (T2 a A15 H4).coeff j ∈ V K a A15 B7 H4 C3 j := by
    intro j
    rw [T2, coeff_add, coeff_sub, coeff_C]
    have hmain := Subalgebra.sub_mem _ (hAshiftSq j) (hHsq j)
    split
    · subst j
      exact Subalgebra.add_mem _ hmain h.low
    · exact Subalgebra.add_mem _ hmain (Subalgebra.zero_mem _)
  exact ⟨ht1, ht2⟩

end OuterCert

/-- The generic degree-31 outer shell is a compatible pair. -/
theorem shell_compatible [Nontrivial A] (K : Subalgebra R A) (a : ℕ → A)
    (A15 B7 H4 C3 : A[X]) (htwo : IsUnit (2 : R))
    (hAm : A15.Monic) (hAd : A15.natDegree = 15)
    (hBm : B7.Monic) (hBd : B7.natDegree = 7)
    (hHm : H4.Monic) (hHd : H4.natDegree = 4)
    (hCm : C3.Monic) (hCd : C3.natDegree = 3) :
    CompatiblePair K (T1 a A15 B7 C3) (T2 a A15 H4) 30 (range 31) := by
  obtain ⟨ht1m, ht1d⟩ := T1_good a A15 B7 C3 hAm hAd hBm hBd hCd
  obtain ⟨ht2m, ht2d⟩ := T2_good a A15 H4 hAm hAd hHm hHd
  exact
    { toCausalPair :=
        (outer_recover K a A15 B7 H4 C3 htwo hAm hAd hBm hBd hHm hHd hCm hCd).causal
          hAd hBd hHd
      monic₁ := ht1m
      monic₂ := ht2m
      natDegree₁ := ht1d
      natDegree₂ := ht2d
      window := by intro i hi; simpa only using hi }

end FastPoly.P31
