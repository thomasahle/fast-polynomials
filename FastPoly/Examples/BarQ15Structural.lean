import FastPoly.Examples.BarQ15
import FastPoly.Section4.KnownPowers

/-!
# Structural facts for the finite barred degree-15 gadget

`BarQ15.lean` proves the explicit coefficient decoder.  This file records the
orthogonal structural fact needed by outer constructions: every wire in the
barred circuit is monic of its advertised degree.  Keeping this separate makes
the decoder independent of a `Nontrivial` hypothesis and gives consumers one
small, reusable endpoint.
-/

namespace FastPoly.BarQ15

open Polynomial

variable {A : Type*} [CommRing A] [Nontrivial A]

private theorem add_C_good {P : A[X]} (hPm : P.Monic) (hPd : P.natDegree = d)
    (z : A) (hd : 0 < d) :
    (P + C z).Monic ∧ (P + C z).natDegree = d := by
  obtain ⟨hm, hn⟩ := monic_add_low (P := P) (e := C z) hPm
    (Or.inr (by rw [natDegree_C, hPd]; omega))
  exact ⟨hm, hn.trans hPd⟩

private theorem add_monomial_good {P : A[X]} (hPm : P.Monic)
    (hPd : P.natDegree = d) (z : A) (hi : i < d) :
    (P + C z * X ^ i).Monic ∧ (P + C z * X ^ i).natDegree = d := by
  have he : (C z * X ^ i : A[X]).natDegree < P.natDegree := by
    refine lt_of_le_of_lt natDegree_mul_le ?_
    rw [natDegree_C, natDegree_X_pow, hPd]
    omega
  obtain ⟨hm, hn⟩ := monic_add_low (P := P) (e := C z * X ^ i) hPm (Or.inr he)
  exact ⟨hm, hn.trans hPd⟩

theorem H2_good (r0 r1 : A) :
    (H2 r0 r1).Monic ∧ (H2 r0 r1).natDegree = 2 := by
  have hlinm : ((X + C r1) * X : A[X]).Monic := (monic_X_add_C r1).mul monic_X
  have hlind : ((X + C r1) * X : A[X]).natDegree = 2 := by
    rw [(monic_X_add_C r1).natDegree_mul monic_X, natDegree_X_add_C, natDegree_X]
  have hform : H2 r0 r1 = (X + C r1) * X + C r0 := by
    simp only [H2]
    ring
  rw [hform]
  exact add_C_good hlinm hlind r0 (by omega)

theorem H4_good (s0 s1 s2 s3 : A) :
    (H4 s0 s1 s2 s3).Monic ∧ (H4 s0 s1 s2 s3).natDegree = 4 := by
  have h0 : (X ^ 4 : A[X]).Monic ∧ (X ^ 4 : A[X]).natDegree = 4 := by
    exact ⟨monic_X.pow 4, by rw [natDegree_X_pow]⟩
  have h1 := add_monomial_good h0.1 h0.2 s3 (i := 3) (by omega)
  have h2 := add_monomial_good h1.1 h1.2 s2 (i := 2) (by omega)
  have h3 := add_monomial_good h2.1 h2.2 s1 (i := 1) (by omega)
  have h4 := add_monomial_good h3.1 h3.2 s0 (i := 0) (by omega)
  simpa only [H4, pow_zero, mul_one] using h4

theorem H8_good (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (H8 r0 r1 s0 s1 s2 s3 alpha).Monic ∧
      (H8 r0 r1 s0 s1 s2 s3 alpha).natDegree = 8 := by
  obtain ⟨h2m, h2d⟩ := H2_good r0 r1
  obtain ⟨h4m, h4d⟩ := H4_good s0 s1 s2 s3
  obtain ⟨hleftm, hleftd⟩ := monic_add_low (P := H4 s0 s1 s2 s3)
    (e := X + C (u alpha)) h4m
    (Or.inr (by rw [natDegree_X_add_C, h4d]; omega))
  obtain ⟨h2vm, h2vd⟩ := add_C_good h2m h2d (v alpha) (by omega)
  obtain ⟨hrightm, hrightd⟩ := monic_add_low (P := H4 s0 s1 s2 s3)
    (e := H2 r0 r1 + C (v alpha)) h4m
    (Or.inr (by rw [h2vd, h4d]; omega))
  have hprodm : ((H4 s0 s1 s2 s3 + (X + C (u alpha))) *
      (H4 s0 s1 s2 s3 + (H2 r0 r1 + C (v alpha)))).Monic :=
    hleftm.mul hrightm
  have hprodd : ((H4 s0 s1 s2 s3 + (X + C (u alpha))) *
      (H4 s0 s1 s2 s3 + (H2 r0 r1 + C (v alpha)))).natDegree = 8 := by
    rw [hleftm.natDegree_mul hrightm, hleftd, hrightd]
    omega
  rw [H8]
  exact add_C_good hprodm hprodd (w alpha) (by omega)

theorem Q3_good (r0 r1 : A) (alpha : ℕ → A) :
    (Q3 r0 r1 alpha).Monic ∧ (Q3 r0 r1 alpha).natDegree = 3 := by
  obtain ⟨h2m, h2d⟩ := H2_good r0 r1
  obtain ⟨hrightm, hrightd⟩ := add_C_good h2m h2d (a alpha 4) (by omega)
  have hleftm : (X + C (a alpha 5) : A[X]).Monic := monic_X_add_C _
  have hleftd : (X + C (a alpha 5) : A[X]).natDegree = 1 := natDegree_X_add_C _
  have hprodm : ((X + C (a alpha 5)) * (H2 r0 r1 + C (a alpha 4))).Monic :=
    hleftm.mul hrightm
  have hprodd : ((X + C (a alpha 5)) *
      (H2 r0 r1 + C (a alpha 4))).natDegree = 3 := by
    rw [hleftm.natDegree_mul hrightm, hleftd, hrightd]
  rw [Q3]
  exact add_C_good hprodm hprodd (a alpha 3) (by omega)

theorem U0_good (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (U0 r0 r1 s0 s1 s2 s3 alpha).Monic ∧
      (U0 r0 r1 s0 s1 s2 s3 alpha).natDegree = 12 := by
  obtain ⟨h4m, h4d⟩ := H4_good s0 s1 s2 s3
  obtain ⟨h8m, h8d⟩ := H8_good r0 r1 s0 s1 s2 s3 alpha
  obtain ⟨hqm, hqd⟩ := Q3_good r0 r1 alpha
  obtain ⟨hfm, hfd⟩ := add_C_good h4m h4d (b alpha 3) (by omega)
  have hpm : ((H4 s0 s1 s2 s3 + C (b alpha 3)) *
      H8 r0 r1 s0 s1 s2 s3 alpha).Monic := hfm.mul h8m
  have hpd : ((H4 s0 s1 s2 s3 + C (b alpha 3)) *
      H8 r0 r1 s0 s1 s2 s3 alpha).natDegree = 12 := by
    rw [hfm.natDegree_mul h8m, hfd, h8d]
  rw [U0]
  obtain ⟨hm, hd⟩ := monic_add_low hpm (Or.inr (by rw [hqd, hpd]; omega))
  exact ⟨hm, hd.trans hpd⟩

theorem V0_good (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (V0 r0 r1 s0 s1 s2 s3 alpha).Monic ∧
      (V0 r0 r1 s0 s1 s2 s3 alpha).natDegree = 12 := by
  obtain ⟨h4m, h4d⟩ := H4_good s0 s1 s2 s3
  obtain ⟨h8m, h8d⟩ := H8_good r0 r1 s0 s1 s2 s3 alpha
  obtain ⟨hfm, hfd⟩ := add_C_good h4m h4d (b alpha 4) (by omega)
  obtain ⟨hg, hgd⟩ := add_C_good h8m h8d (rho alpha) (by omega)
  have hpm : ((H4 s0 s1 s2 s3 + C (b alpha 4)) *
      (H8 r0 r1 s0 s1 s2 s3 alpha + C (rho alpha))).Monic := hfm.mul hg
  have hpd : ((H4 s0 s1 s2 s3 + C (b alpha 4)) *
      (H8 r0 r1 s0 s1 s2 s3 alpha + C (rho alpha))).natDegree = 12 := by
    rw [hfm.natDegree_mul hg, hfd, hgd]
  rw [V0]
  exact add_C_good hpm hpd (a alpha 2) (by omega)

theorem C1_good (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (C1 r0 r1 s0 s1 s2 s3 alpha).Monic ∧
      (C1 r0 r1 s0 s1 s2 s3 alpha).natDegree = 14 := by
  obtain ⟨h2m, h2d⟩ := H2_good r0 r1
  obtain ⟨hUm, hUd⟩ := U0_good r0 r1 s0 s1 s2 s3 alpha
  obtain ⟨hfm, hfd⟩ := add_C_good h2m h2d (b alpha 1) (by omega)
  have hpm : ((H2 r0 r1 + C (b alpha 1)) *
      U0 r0 r1 s0 s1 s2 s3 alpha).Monic := hfm.mul hUm
  have hpd : ((H2 r0 r1 + C (b alpha 1)) *
      U0 r0 r1 s0 s1 s2 s3 alpha).natDegree = 14 := by
    rw [hfm.natDegree_mul hUm, hfd, hUd]
  rw [C1]
  exact add_C_good hpm hpd (a alpha 1) (by omega)

theorem C2_good (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (C2 r0 r1 s0 s1 s2 s3 alpha).Monic ∧
      (C2 r0 r1 s0 s1 s2 s3 alpha).natDegree = 14 := by
  obtain ⟨h2m, h2d⟩ := H2_good r0 r1
  obtain ⟨hVm, hVd⟩ := V0_good r0 r1 s0 s1 s2 s3 alpha
  obtain ⟨hfm, hfd⟩ := add_C_good h2m h2d (b alpha 2) (by omega)
  have hpm : ((H2 r0 r1 + C (b alpha 2)) *
      V0 r0 r1 s0 s1 s2 s3 alpha).Monic := hfm.mul hVm
  have hpd : ((H2 r0 r1 + C (b alpha 2)) *
      V0 r0 r1 s0 s1 s2 s3 alpha).natDegree = 14 := by
    rw [hfm.natDegree_mul hVm, hfd, hVd]
  rw [C2]
  exact add_C_good hpm hpd (a alpha 0) (by omega)

/-- The finite barred circuit is monic of degree `15`, independently of its
coefficient decoder. -/
theorem barQ15_good (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (barQ15 r0 r1 s0 s1 s2 s3 alpha).Monic ∧
      (barQ15 r0 r1 s0 s1 s2 s3 alpha).natDegree = 15 := by
  obtain ⟨hC1m, hC1d⟩ := C1_good r0 r1 s0 s1 s2 s3 alpha
  obtain ⟨hC2m, hC2d⟩ := C2_good r0 r1 s0 s1 s2 s3 alpha
  have hxm : (X + C (b alpha 0) : A[X]).Monic := monic_X_add_C _
  have hxd : (X + C (b alpha 0) : A[X]).natDegree = 1 := natDegree_X_add_C _
  have hpm : ((X + C (b alpha 0)) * C1 r0 r1 s0 s1 s2 s3 alpha).Monic :=
    hxm.mul hC1m
  have hpd : ((X + C (b alpha 0)) *
      C1 r0 r1 s0 s1 s2 s3 alpha).natDegree = 15 := by
    rw [hxm.natDegree_mul hC1m, hxd, hC1d]
  rw [barQ15]
  obtain ⟨hm, hd⟩ := monic_add_low hpm (Or.inr (by rw [hC2d, hpd]; omega))
  exact ⟨hm, hd.trans hpd⟩

end FastPoly.BarQ15
