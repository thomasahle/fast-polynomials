import FastPoly.Examples.BarQ15Structural
import FastPoly.Examples.P15
import FastPoly.Examples.P31
import FastPoly.Section4.Peeled

/-!
# The complete degree-31 special construction

`P31.lean` proves the causal outer decoder with four opaque monic blocks.  Here
we instantiate those blocks by the paper's actual `barQ₁₅`, `Q₇`, and `Q₃`
circuits and explicitly discharge their conditional power data.  The order is

1. decode the outer square shells;
2. recover the parameters of `H₄`, hence the coefficients of `H₂`;
3. decode `barQ₁₅`, `Q₇`, and `Q₃` relative to those recovered powers.

This separation rules out circular use of an internal power: every conditional
decoder is transported only after all of its side information belongs to the
output coefficient algebra.
-/

namespace FastPoly.P31Full

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-! ## The actual inner blocks -/

noncomputable abbrev H2 (a : ℕ → A) : A[X] := P15.H2 a
noncomputable abbrev H4 (a : ℕ → A) : A[X] := P15.H4 a

noncomputable def Hp (a : ℕ → A) : ℕ → A[X]
  | 1 => H2 a
  | 2 => H4 a
  | _ => 0

noncomputable def A15 (a : ℕ → A) : A[X] :=
  BarQ15.barQ15 (a 6) (a 7) (P15.h0 a) (P15.h1 a) (P15.h2 a) (P15.h3 a)
    (fun t => a (16 + t))

noncomputable def B7 (a : ℕ → A) : A[X] :=
  peel (Hp a) 3 (fun t => a (8 + t))

noncomputable def C3 (a : ℕ → A) : A[X] :=
  peel (Hp a) 2 (fun t => a (1 + t))

noncomputable def T1 (a : ℕ → A) : A[X] := P31.T1 a (A15 a) (B7 a) (C3 a)
noncomputable def T2 (a : ℕ → A) : A[X] := P31.T2 a (A15 a) (H4 a)

noncomputable def V (K : Subalgebra R A) (a : ℕ → A) : Subalgebra R A :=
  P31.V K a (A15 a) (B7 a) (H4 a) (C3 a) 0

/-! ## Structural endpoints -/

section structural

variable [Nontrivial A]

theorem H2_good (a : ℕ → A) : (H2 a).Monic ∧ (H2 a).natDegree = 2 :=
  P15.H2_good a

theorem H4_good (a : ℕ → A) : (H4 a).Monic ∧ (H4 a).natDegree = 4 :=
  P15.H4_good a

theorem Hp_good (a : ℕ → A) :
    ∀ i, 1 ≤ i → i < 3 → (Hp a i).Monic ∧ (Hp a i).natDegree = 2 ^ i := by
  intro i hi1 hi3
  match i with
  | 0 => omega
  | 1 => simpa only [Hp, pow_one] using H2_good a
  | 2 => simpa only [Hp] using H4_good a
  | i + 3 => omega

theorem A15_good (a : ℕ → A) : (A15 a).Monic ∧ (A15 a).natDegree = 15 := by
  simpa only [A15] using BarQ15.barQ15_good (a 6) (a 7) (P15.h0 a) (P15.h1 a)
    (P15.h2 a) (P15.h3 a) (fun t => a (16 + t))

theorem B7_good (a : ℕ → A) : (B7 a).Monic ∧ (B7 a).natDegree = 7 := by
  have h := peel_monic (Hp a) 3 (Hp_good a) (by omega) (fun t => a (8 + t))
  simpa only [B7] using h

theorem C3_good (a : ℕ → A) : (C3 a).Monic ∧ (C3 a).natDegree = 3 := by
  have hp : ∀ i, 1 ≤ i → i < 2 →
      (Hp a i).Monic ∧ (Hp a i).natDegree = 2 ^ i := by
    intro i hi1 hi2
    exact Hp_good a i hi1 (by omega)
  have h := peel_monic (Hp a) 2 hp (by omega) (fun t => a (1 + t))
  simpa only [C3] using h

/-- The actual degree-31 pair has the outer shell's unconditional compatibility
certificate.  No inner decoder is used in this statement. -/
theorem compatible (K : Subalgebra R A) (a : ℕ → A) (htwo : IsUnit (2 : R)) :
    CompatiblePair K (T1 a) (T2 a) 30 (range 31) := by
  obtain ⟨hAm, hAd⟩ := A15_good a
  obtain ⟨hBm, hBd⟩ := B7_good a
  obtain ⟨hHm, hHd⟩ := H4_good a
  obtain ⟨hCm, hCd⟩ := C3_good a
  simpa only [T1, T2] using
    P31.shell_compatible K a (A15 a) (B7 a) (H4 a) (C3 a) htwo
      hAm hAd hBm hBd hHm hHd hCm hCd

end structural

/-! ## The quartic-to-quadratic seam -/

theorem H2_coeff_zero (a : ℕ → A) : (H2 a).coeff 0 = a 6 := by
  change (P15.H2 a).coeff 0 = a 6
  rw [P15.H2_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem H2_coeff_one (a : ℕ → A) : (H2 a).coeff 1 = a 7 := by
  change (P15.H2 a).coeff 1 = a 7
  rw [P15.H2_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem H4_coeff_h3 (a : ℕ → A) : (H4 a).coeff 3 = P15.h3 a := by
  change (P15.H4 a).coeff 3 = P15.h3 a
  rw [P15.H4_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem H4_coeff_h2 (a : ℕ → A) : (H4 a).coeff 2 = P15.h2 a := by
  change (P15.H4 a).coeff 2 = P15.h2 a
  rw [P15.H4_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem H4_coeff_h1 (a : ℕ → A) : (H4 a).coeff 1 = P15.h1 a := by
  change (P15.H4 a).coeff 1 = P15.h1 a
  rw [P15.H4_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem H4_coeff_h0 (a : ℕ → A) : (H4 a).coeff 0 = P15.h0 a := by
  change (P15.H4 a).coeff 0 = P15.h0 a
  rw [P15.H4_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem H4_coeff_three (a : ℕ → A) : (H4 a).coeff 3 = 2 * a 7 := by
  rw [H4_coeff_h3, P15.h3]

theorem H4_coeff_two (a : ℕ → A) :
    (H4 a).coeff 2 = a 7 ^ 2 + 2 * a 6 - 1 := by
  rw [H4_coeff_h2, P15.h2]

theorem H4_coeff_one (a : ℕ → A) :
    (H4 a).coeff 1 = 2 * a 7 * a 6 - 2 * a 5 := by
  rw [H4_coeff_h1, P15.h1]

theorem H4_coeff_zero (a : ℕ → A) :
    (H4 a).coeff 0 = a 6 ^ 2 - a 5 ^ 2 + a 4 := by
  rw [H4_coeff_h0, P15.h0]

/-! ## Full explicit decoder -/

/-- All `31` parameters of the actual special construction belong to the
algebra generated by its output coefficients.  Conditional gadget decoders are
discharged explicitly; the proof never assumes the correctness of an inner
construction while recovering the outer shells. -/
theorem decodable [Nontrivial A] (K : Subalgebra R A) (a : ℕ → A)
    (htwo : IsUnit (2 : R)) :
    ∀ i, i < 31 → a i ∈ V K a := by
  obtain ⟨hAm, hAd⟩ := A15_good a
  obtain ⟨hBm, hBd⟩ := B7_good a
  obtain ⟨hHm, hHd⟩ := H4_good a
  obtain ⟨hCm, hCd⟩ := C3_good a
  let cert := P31.outer_recover K a (A15 a) (B7 a) (H4 a) (C3 a) htwo
    hAm hAd hBm hBd hHm hHd hCm hCd
  have hanti := P31.V_antitone K a (A15 a) (B7 a) (H4 a) (C3 a)
  have lower : ∀ {x : A} {t : ℕ},
      x ∈ P31.V K a (A15 a) (B7 a) (H4 a) (C3 a) t → x ∈ V K a := by
    intro x t hx
    simpa only [V] using hanti (Nat.zero_le t) hx

  have ha0 : a 0 ∈ V K a := lower cert.low
  have ha15 : a 15 ∈ V K a := lower cert.shift
  have hAcoeff : ∀ j, (A15 a).coeff j ∈ V K a := fun j => lower (cert.Acoeff j)
  have hBcoeff : ∀ j, (B7 a).coeff j ∈ V K a := fun j => lower (cert.Bcoeff j)
  have hHcoeff : ∀ j, (H4 a).coeff j ∈ V K a := fun j => lower (cert.Hcoeff j)
  have hCcoeff : ∀ j, (C3 a).coeff j ∈ V K a := fun j => lower (cert.Ccoeff j)

  -- The four displayed quartic pivots recover a₇,a₆,a₅,a₄, in that order.
  have htwoa7 : 2 * a 7 ∈ V K a := by
    rw [← H4_coeff_three]
    exact hHcoeff 3
  have ha7 : a 7 ∈ V K a := mem_of_two_mul_eq htwo htwoa7 rfl
  have htwoa6 : 2 * a 6 ∈ V K a := by
    have hkey : 2 * a 6 = (H4 a).coeff 2 - a 7 * a 7 + 1 := by
      rw [H4_coeff_two]
      ring
    rw [hkey]
    exact Subalgebra.add_mem _
      (Subalgebra.sub_mem _ (hHcoeff 2) (Subalgebra.mul_mem _ ha7 ha7))
      (Subalgebra.one_mem _)
  have ha6 : a 6 ∈ V K a := mem_of_two_mul_eq htwo htwoa6 rfl
  have htwoa5 : 2 * a 5 ∈ V K a := by
    have hkey : 2 * a 5 = (a 7 * a 6 + a 7 * a 6) - (H4 a).coeff 1 := by
      rw [H4_coeff_one]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ ha7 ha6)
        (Subalgebra.mul_mem _ ha7 ha6)) (hHcoeff 1)
  have ha5 : a 5 ∈ V K a := mem_of_two_mul_eq htwo htwoa5 rfl
  have ha4 : a 4 ∈ V K a := by
    have hkey : a 4 = (H4 a).coeff 0 - a 6 * a 6 + a 5 * a 5 := by
      rw [H4_coeff_zero]
      ring
    rw [hkey]
    exact Subalgebra.add_mem _
      (Subalgebra.sub_mem _ (hHcoeff 0) (Subalgebra.mul_mem _ ha6 ha6))
      (Subalgebra.mul_mem _ ha5 ha5)

  have hH2coeff : ∀ j, (H2 a).coeff j ∈ V K a := by
    intro j
    match j with
    | 0 =>
        rw [H2_coeff_zero]
        exact ha6
    | 1 =>
        rw [H2_coeff_one]
        exact ha7
    | 2 =>
        rw [← (H2_good a).2, (H2_good a).1.coeff_natDegree]
        exact Subalgebra.one_mem _
    | j + 3 =>
        have hz : (H2 a).coeff (j + 3) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [(H2_good a).2]; omega)
        rw [hz]
        exact Subalgebra.zero_mem _

  -- Discharge the finite barred decoder after both power polynomials are known.
  have hh0 : P15.h0 a ∈ V K a := by
    rw [← H4_coeff_h0]
    exact hHcoeff 0
  have hh1 : P15.h1 a ∈ V K a := by
    rw [← H4_coeff_h1]
    exact hHcoeff 1
  have hh2 : P15.h2 a ∈ V K a := by
    rw [← H4_coeff_h2]
    exact hHcoeff 2
  have hh3 : P15.h3 a ∈ V K a := by
    rw [← H4_coeff_h3]
    exact hHcoeff 3
  have hbarLe : BarQ15.barQ15Alg (V K a) (a 6) (a 7) (P15.h0 a) (P15.h1 a)
      (P15.h2 a) (P15.h3 a) (fun t => a (16 + t)) ≤ V K a := by
    rw [BarQ15.barQ15Alg]
    refine sup_le le_rfl (adjoin_le ?_)
    rintro _ ⟨j, rfl⟩
    simpa only [A15] using hAcoeff j
  have hAparams : ∀ t, t < 15 → a (16 + t) ∈ V K a := by
    intro t ht
    exact hbarLe (BarQ15.barQ15_recover (V K a) (a 6) (a 7) (P15.h0 a)
      (P15.h1 a) (P15.h2 a) (P15.h3 a) (fun q => a (16 + q))
      ha6 ha7 hh0 hh1 hh2 hh3 t ht)

  -- The same known-power package discharges Q₇ and its Q₃ subcase.
  have hpKnown : ∀ q, 1 ≤ q → q < 3 →
      (Hp a q).Monic ∧ (Hp a q).natDegree = 2 ^ q ∧
        ∀ j, (Hp a q).coeff j ∈ V K a := by
    intro q hq1 hq3
    match q with
    | 0 => omega
    | 1 =>
        obtain ⟨hm, hd⟩ := H2_good a
        exact ⟨hm, hd.trans (by norm_num), hH2coeff⟩
    | 2 =>
        obtain ⟨hm, hd⟩ := H4_good a
        exact ⟨hm, hd.trans (by norm_num), hHcoeff⟩
    | q + 3 => omega
  have hBparams : ∀ t, t < 7 → a (8 + t) ∈ V K a := by
    intro t ht
    have h := peel_correct (K := V K a) (Hp a) 3 hpKnown (by omega)
      (fun q => a (8 + q)) (V K a) le_rfl
      (by intro j; simpa only [B7] using hBcoeff j) t
      (by norm_num; omega)
    exact h
  have hpKnown2 : ∀ q, 1 ≤ q → q < 2 →
      (Hp a q).Monic ∧ (Hp a q).natDegree = 2 ^ q ∧
        ∀ j, (Hp a q).coeff j ∈ V K a := by
    intro q hq1 hq2
    exact hpKnown q hq1 (by omega)
  have hCparams : ∀ t, t < 3 → a (1 + t) ∈ V K a := by
    intro t ht
    have h := peel_correct (K := V K a) (Hp a) 2 hpKnown2 (by omega)
      (fun q => a (1 + q)) (V K a) le_rfl
      (by intro j; simpa only [C3] using hCcoeff j) t
      (by norm_num; omega)
    exact h

  intro i hi
  by_cases hi0 : i = 0
  · simpa only [hi0] using ha0
  by_cases hi4 : i < 4
  · have ht : i - 1 < 3 := by omega
    simpa only [show 1 + (i - 1) = i by omega] using hCparams (i - 1) ht
  by_cases hi8 : i < 8
  · have hcases : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact ha4
    · exact ha5
    · exact ha6
    · exact ha7
  by_cases hi15 : i < 15
  · have ht : i - 8 < 7 := by omega
    simpa only [show 8 + (i - 8) = i by omega] using hBparams (i - 8) ht
  by_cases hi16 : i < 16
  · have hi15eq : i = 15 := by omega
    simpa only [hi15eq] using ha15
  · have ht : i - 16 < 15 := by omega
    simpa only [show 16 + (i - 16) = i by omega] using hAparams (i - 16) ht

end FastPoly.P31Full
