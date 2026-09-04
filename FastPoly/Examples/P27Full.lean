import FastPoly.Examples.P27Composition
import FastPoly.Section5.QFourKOne

/-!
# The complete degree-27 special construction

`P27.lean` proves the causal outer square-shell decoder with opaque monic
blocks.  `P27Composition.lean` proves the non-circular substitution order

`Q₁₃ → H₄ → Q₇ → Q₃`.

This file fixes the paper's actual `Q₁₃ = q4k1` instance and its exact
parameter layout.  The final decoder therefore has a single, narrow remaining
input: the public relative decoder/byproduct contract for that instance.
-/

namespace FastPoly.P27Full

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-! ## Actual inner blocks -/

noncomputable abbrev H2 (theta : ℕ → A) : A[X] := P27Composition.H2 theta

/-- Quartic byproduct of the `Q₁₃` crown. -/
noncomputable def H4 (theta : ℕ → A) : A[X] :=
  crownH4 ((H2 theta).coeff 1) ((H2 theta).coeff 0 + theta 25)
    (theta 23) (theta 22)

/-- The degree-13 block, with internal rows `14,…,21` and outer crown
parameters `e,a,ρ,γ,β = 22,…,26`. -/
noncomputable def A13 (theta : ℕ → A) : A[X] :=
  q4k1 (H2 theta) (theta 25) (theta 24) (theta 23) (theta 22) (theta 26) 3
    (fun t => theta (14 + t))

noncomputable abbrev B3 (theta : ℕ → A) : A[X] :=
  P27Composition.B3 theta (H4 theta)

noncomputable abbrev C7 (theta : ℕ → A) : A[X] :=
  P27Composition.C7 theta (H4 theta)

noncomputable def T1 (theta : ℕ → A) : A[X] :=
  P27Composition.T1 theta (A13 theta) (H4 theta)

noncomputable def T2 (theta : ℕ → A) : A[X] :=
  P27Composition.T2 theta (A13 theta) (H4 theta)

noncomputable def V (K : Subalgebra R A) (theta : ℕ → A) : Subalgebra R A :=
  P27Composition.V K theta (A13 theta) (H4 theta)

/-! ## A known-shift extraction primitive -/

/-- If the scalar in `(X + shift) T₁ + T₂` is already known, compatibility
recovers both components from the shifted combination without any restriction
on whether the compatibility window contains the top row.  This is the
descending half of `x_alpha_mem`; separating it is useful here because the
five crown pivots recover the shift before the internal remainder block. -/
theorem pair_coeffs_mem_of_known_shift
    {S : Subalgebra R A} {G : Finset ℕ} {n : ℕ}
    {U W P : A[X]} {shift : A}
    (hpair : CompatiblePair S U W n G) (hshift : shift ∈ S)
    (hPcoeff : ∀ i, P.coeff i ∈ S)
    (hP : P = (X + C shift) * U + W) :
    ∀ j, U.coeff j ∈ S ∧ W.coeff j ∈ S := by
  have hPc : P = combined U W + C shift * U := by
    rw [hP]
    simp only [combined]
    ring
  have hUlead : U.coeff n = 1 := by
    rw [← hpair.natDegree₁]
    exact hpair.monic₁.coeff_natDegree
  have hWlead : W.coeff n = 1 := by
    rw [← hpair.natDegree₂]
    exact hpair.monic₂.coeff_natDegree
  have hhigh : ∀ j, n ≤ j → U.coeff j ∈ S ∧ W.coeff j ∈ S := by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hj
    · rw [hUlead, hWlead]
      exact ⟨Subalgebra.one_mem _, Subalgebra.one_mem _⟩
    · have hUz : U.coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hpair.natDegree₁]; omega)
      have hWz : W.coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hpair.natDegree₂]; omega)
      rw [hUz, hWz]
      exact ⟨Subalgebra.zero_mem _, Subalgebra.zero_mem _⟩
  have hcombined : ∀ i, (combined U W).coeff i = P.coeff i - shift * U.coeff i := by
    intro i
    rw [hPc, coeff_add, coeff_C_mul]
    ring
  have main : ∀ fuel j, n - j ≤ fuel → U.coeff j ∈ S ∧ W.coeff j ∈ S := by
    intro fuel
    induction fuel with
    | zero =>
        intro j hj
        exact hhigh j (by omega)
    | succ fuel ih =>
        intro j hj
        rcases Nat.lt_or_ge j n with hjn | hjn
        · have hVisU : Vis R S (combined U W) G (j + 1) ≤ S := by
            refine Vis_le le_rfl ?_
            intro i hi hii
            have hiU : U.coeff i ∈ S := (ih i (by omega)).1
            rw [hcombined i]
            exact Subalgebra.sub_mem _ (hPcoeff i)
              (Subalgebra.mul_mem _ hshift hiU)
          have hUj : U.coeff j ∈ S := hVisU (hpair.mem₁ j)
          have hVisW : Vis R S (combined U W) G j ≤ S := by
            refine Vis_le le_rfl ?_
            intro i hi hii
            have hiU : U.coeff i ∈ S := by
              rcases eq_or_lt_of_le hii with rfl | hij
              · exact hUj
              · exact (ih i (by omega)).1
            rw [hcombined i]
            exact Subalgebra.sub_mem _ (hPcoeff i)
              (Subalgebra.mul_mem _ hshift hiU)
          exact ⟨hUj, hVisW (hpair.mem₂ j)⟩
        · exact hhigh j hjn
  exact fun j => main (n - j) j le_rfl

/-! ## Structural endpoints -/

section structural

variable [Nontrivial A]

theorem H2_good (theta : ℕ → A) :
    (H2 theta).Monic ∧ (H2 theta).natDegree = 2 :=
  P27Composition.H2_good theta

theorem H4_good (theta : ℕ → A) :
    (H4 theta).Monic ∧ (H4 theta).natDegree = 4 := by
  simpa only [H4] using crownH4_monic
    (A := A) (b := (H2 theta).coeff 1)
      (c := (H2 theta).coeff 0 + theta 25) (a := theta 23) (e := theta 22)

/-- Structural correctness of the actual `Q₁₃` block.  The unit
hypotheses are used only to reuse the already sealed compatible crown pair;
the resulting monicity and degree statement is independent of the decoder. -/
theorem A13_good (K : Subalgebra R A) (theta : ℕ → A)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 6 → IsUnit (((n : ℕ) : ℤ) : R)) :
    (A13 theta).Monic ∧ (A13 theta).natDegree = 13 := by
  let U : A[X] :=
    (Tpair
      (crownHp ((H2 theta).coeff 1) ((H2 theta).coeff 0 + theta 25)
        (theta 23) (theta 22))
      (H4 theta + C (theta 24)) 3 2 (fun t => theta (14 + t))).1
  let W : A[X] :=
    (Tpair
      (crownHp ((H2 theta).coeff 1) ((H2 theta).coeff 0 + theta 25)
        (theta 23) (theta 22))
      (H4 theta + C (theta 24)) 3 2 (fun t => theta (14 + t))).2
  have hpair : CompatiblePair K U W 12 (range 13) := by
    simpa only [U, W, H4] using
      fourk_crown_compatible (K := K) (k := 3)
        (α := fun t => theta (14 + t)) (by omega) hadm
        ((H2 theta).coeff 1) ((H2 theta).coeff 0 + theta 25)
        (theta 23) (theta 22) (theta 24)
  have hXm : (X + C (theta 26) : A[X]).Monic := monic_X_add_C (theta 26)
  have hPm : ((X + C (theta 26)) * U : A[X]).Monic := hXm.mul hpair.monic₁
  have hPd : ((X + C (theta 26)) * U : A[X]).natDegree = 13 := by
    rw [hXm.natDegree_mul hpair.monic₁, natDegree_X_add_C, hpair.natDegree₁]
  have hlow : W.natDegree < ((X + C (theta 26)) * U : A[X]).natDegree := by
    rw [hpair.natDegree₂, hPd]
    norm_num
  obtain ⟨hm, hd⟩ := monic_add_low hPm (Or.inr hlow)
  have hform : A13 theta = (X + C (theta 26)) * U + W := by
    simp only [A13, q4k1, U, W, H4]
  rw [hform]
  exact ⟨hm, hd.trans hPd⟩

/-- The actual degree-27 pair inherits the unconditional causal certificate
of the outer shell. -/
theorem compatible (K : Subalgebra R A) (theta : ℕ → A)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 6 → IsUnit (((n : ℕ) : ℤ) : R)) :
    CompatiblePair K (T1 theta) (T2 theta) 26 (range 27) := by
  have htwo : IsUnit (2 : R) := by
    have h := hadm 2 (by omega) (by omega)
    norm_num at h
    exact h
  obtain ⟨hAm, hAd⟩ := A13_good K theta hadm
  obtain ⟨hHm, hHd⟩ := H4_good theta
  simpa only [T1, T2] using
    P27Composition.compatible K theta (A13 theta) (H4 theta) htwo
      hAm hAd hHm hHd

end structural

/-! ## Decoder handoff -/

/-- The actual `q4k1` instance satisfies precisely the relative decoder and
quartic-byproduct contract consumed by the degree-27 composition.  The proof
has three explicit stages: five crown pivots, known-shift extraction of the
pair, and the eight-row `Rk2l_triangular` decoder. -/
theorem q13_decoder [Nontrivial A]
    (theta : ℕ → A)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 6 → IsUnit (((n : ℕ) : ℤ) : R)) :
    P27Composition.Q13Decoder (R := R) theta (A13 theta) (H4 theta) := by
  intro S hH2coeff hAcoeff
  obtain ⟨hH2m, hH2d⟩ := H2_good theta

  have hVisLe : ∀ t, Vis R S (A13 theta) (range 14) t ≤ S := by
    intro t
    exact Vis_le le_rfl (fun i _ _ => hAcoeff i)

  -- Five descending crown pivots: β, γ, a, e, ρ.
  obtain ⟨hBetaV, hGammaV, hCrownAV, hEV, hRhoV⟩ :=
    q4k1_param_vis (K := S) (H2 := H2 theta) (k := 3)
      (α := fun t => theta (14 + t)) (by omega) hadm hH2m hH2d hH2coeff
      (theta 25) (theta 24) (theta 23) (theta 22) (theta 26)
  have hBeta : theta 26 ∈ S := by
    apply hVisLe 12
    simpa only [A13] using hBetaV
  have hGamma : theta 25 ∈ S := by
    apply hVisLe 11
    simpa only [A13] using hGammaV
  have hCrownA : theta 23 ∈ S := by
    apply hVisLe 10
    simpa only [A13] using hCrownAV
  have hE : theta 22 ∈ S := by
    apply hVisLe 9
    simpa only [A13] using hEV
  have hRho : theta 24 ∈ S := by
    apply hVisLe 8
    simpa only [A13] using hRhoV

  -- Coefficients of the recovered quartic byproduct, displayed one row at a time.
  have hb : (H2 theta).coeff 1 ∈ S := hH2coeff 1
  have hc : (H2 theta).coeff 0 + theta 25 ∈ S :=
    Subalgebra.add_mem _ (hH2coeff 0) hGamma
  have hH4coeff : ∀ j, (H4 theta).coeff j ∈ S := by
    intro j
    match j with
    | 0 =>
        rw [H4, crownH4_coeff_zero]
        exact Subalgebra.add_mem _
          (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hc hc)
            (Subalgebra.mul_mem _ hCrownA hCrownA)) hE
    | 1 =>
        rw [H4, crownH4_coeff_one]
        exact Subalgebra.sub_mem _
          (Subalgebra.add_mem _ (Subalgebra.mul_mem _ hb hc)
            (Subalgebra.mul_mem _ hb hc))
          (Subalgebra.add_mem _ hCrownA hCrownA)
    | 2 =>
        rw [H4, crownH4_coeff_two]
        exact Subalgebra.sub_mem _
          (Subalgebra.add_mem _ (Subalgebra.mul_mem _ hb hb)
            (Subalgebra.add_mem _ hc hc)) (Subalgebra.one_mem _)
    | 3 =>
        rw [H4, crownH4_coeff_three]
        exact Subalgebra.add_mem _ hb hb
    | 4 =>
        rw [← (H4_good theta).2, (H4_good theta).1.coeff_natDegree]
        exact Subalgebra.one_mem _
    | j + 5 =>
        have hz : (H4 theta).coeff (j + 5) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [(H4_good theta).2]; omega)
        rw [hz]
        exact Subalgebra.zero_mem _

  -- Name the internal pair once; all subsequent recovery is relative to `S`.
  let Hp : ℕ → A[X] :=
    crownHp ((H2 theta).coeff 1) ((H2 theta).coeff 0 + theta 25)
      (theta 23) (theta 22)
  let Ht : A[X] := H4 theta + C (theta 24)
  let alpha : ℕ → A := fun t => theta (14 + t)
  let U : A[X] := (Tpair Hp Ht 3 2 alpha).1
  let W : A[X] := (Tpair Hp Ht 3 2 alpha).2

  have hpair : CompatiblePair S U W 12 (range 13) := by
    simpa only [U, W, Hp, Ht, alpha, H4] using
      fourk_crown_compatible (K := S) (k := 3)
        (α := fun t => theta (14 + t)) (by omega) hadm
        ((H2 theta).coeff 1) ((H2 theta).coeff 0 + theta 25)
        (theta 23) (theta 22) (theta 24)
  have hAform : A13 theta = (X + C (theta 26)) * U + W := by
    simp only [A13, q4k1, U, W, Hp, Ht, alpha, H4]
  have hUW : ∀ j, U.coeff j ∈ S ∧ W.coeff j ∈ S :=
    pair_coeffs_mem_of_known_shift hpair hBeta hAcoeff hAform

  -- The recovered crown data make the whole power tower known in `S`.
  have hHpKnown : ∀ i, 1 ≤ i → i ≤ 2 →
      (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧ ∀ j, (Hp i).coeff j ∈ S := by
    intro i hi1 hi2
    match i with
    | 0 => omega
    | 1 =>
        obtain ⟨hm, hd⟩ := crownH2_monic
          (A := A) (b := (H2 theta).coeff 1)
            (c := (H2 theta).coeff 0 + theta 25)
        refine ⟨hm, hd.trans (by norm_num), ?_⟩
        intro j
        have heq := crownH2_shift hH2m hH2d (theta 25)
        change (crownH2 ((H2 theta).coeff 1)
          ((H2 theta).coeff 0 + theta 25)).coeff j ∈ S
        rw [← heq, coeff_add, coeff_C]
        exact Subalgebra.add_mem _ (hH2coeff j) (by
          split
          · exact hGamma
          · exact Subalgebra.zero_mem _)
    | 2 =>
        obtain ⟨hm, hd⟩ := H4_good theta
        refine ⟨?_, ?_, ?_⟩
        · simpa only [Hp, crownHp_two, H4] using hm
        · simpa only [Hp, crownHp_two, H4] using hd.trans (by norm_num)
        · intro j
          simpa only [Hp, crownHp_two, H4] using hH4coeff j
    | i + 3 => omega

  obtain ⟨hH4m, hH4d⟩ := H4_good theta
  obtain ⟨hHtm, hHtd0⟩ := monic_add_low hH4m (Or.inr (by
    rw [natDegree_C, hH4d]
    norm_num : (C (theta 24) : A[X]).natDegree < (H4 theta).natDegree))
  have hHtd : Ht.natDegree = 4 := by
    simpa only [Ht] using hHtd0.trans hH4d
  have hHtm' : Ht.Monic := by simpa only [Ht] using hHtm
  have hHtcoeff : ∀ j, Ht.coeff j ∈ S := by
    intro j
    change (H4 theta + C (theta 24)).coeff j ∈ S
    rw [coeff_add, coeff_C]
    exact Subalgebra.add_mem _ (hH4coeff j) (by
      split
      · exact hRho
      · exact Subalgebra.zero_mem _)

  have hcert := Rk2l_triangular 3 (by omega) 2 Hp Ht alpha S (by omega)
    hHpKnown hHtm' hHtd hHtcoeff
    (fun _ _ _ => ⟨theta 24, by
      change (H4 theta + C (theta 24)) - H4 theta = C (theta 24)
      ring⟩)
    (fun n hn1 hn3 => hadm n hn1 (by omega))

  have hR₁ : ∀ j, (Rpair Hp Ht 3 2 alpha).1.coeff j ∈ S := by
    intro j
    change (U - Hp 2 ^ 3).coeff j ∈ S
    rw [coeff_sub]
    exact Subalgebra.sub_mem _ (hUW j).1
      (coeff_mem_pow (hHpKnown 2 (by omega) (by omega)).2.2 3 j)
  have hR₂ : ∀ j, (Rpair Hp Ht 3 2 alpha).2.coeff j ∈ S := by
    intro j
    change (W - Ht ^ 3).coeff j ∈ S
    rw [coeff_sub]
    exact Subalgebra.sub_mem _ (hUW j).2 (coeff_mem_pow hHtcoeff 3 j)
  have hRcombined : ∀ j,
      (combined (Rpair Hp Ht 3 2 alpha).1 (Rpair Hp Ht 3 2 alpha).2).coeff j ∈ S := by
    intro j
    match j with
    | 0 => simpa only [coeff_combined_zero] using hR₂ 0
    | j + 1 =>
        rw [coeff_combined]
        exact Subalgebra.add_mem _ (hR₁ j) (hR₂ (j + 1))
  have hslot : ∀ j, j < 8 → rSlot (A := A) 3 2 alpha j ∈ S := by
    intro j hj
    have hmem := hcert.param_mem j (by norm_num; omega)
    refine (sup_le le_rfl (adjoin_le ?_)) hmem
    rintro _ ⟨i, _, rfl⟩
    exact hRcombined i
  have hinner : ∀ j, j < 8 → theta (14 + j) ∈ S := by
    intro j hj
    have hs := hslot j hj
    have hslotEq : rSlot (A := A) 3 2 alpha j = alpha j := by
      by_cases hj4 : j < 4
      · exact rSlot_ob_low (k := 3) (α := alpha) (by norm_num) (by omega) hj4
      · exact rSlot_ob_band (k := 3) (α := alpha) (by norm_num) (by omega) (by omega)
    rw [hslotEq] at hs
    simpa only [alpha] using hs

  constructor
  · intro t ht
    by_cases ht8 : t < 8
    · exact hinner t ht8
    have hcases : t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · simpa only using hE
    · simpa only using hCrownA
    · simpa only using hRho
    · simpa only using hGamma
    · simpa only using hBeta
  · exact hH4coeff

/-- Once the actual `q4k1` instance supplies its relative decoder/byproduct
contract, the complete degree-27 decoder is just the already verified
composition theorem. -/
theorem decodable_of_q13 [Nontrivial A]
    (K : Subalgebra R A) (theta : ℕ → A)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 6 → IsUnit (((n : ℕ) : ℤ) : R))
    (hQ13 : P27Composition.Q13Decoder (R := R) theta (A13 theta) (H4 theta)) :
    ∀ i, i < 27 → theta i ∈ V K theta := by
  have htwo : IsUnit (2 : R) := by
    have h := hadm 2 (by omega) (by omega)
    norm_num at h
    exact h
  obtain ⟨hAm, hAd⟩ := A13_good K theta hadm
  obtain ⟨hHm, hHd⟩ := H4_good theta
  simpa only [V] using
    P27Composition.decodable_of_q13 K theta (A13 theta) (H4 theta) htwo
      hAm hAd hHm hHd hQ13

/-- All 27 parameters of the paper's actual special construction are
recoverable from its output coefficients. -/
theorem decodable [Nontrivial A]
    (K : Subalgebra R A) (theta : ℕ → A)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 6 → IsUnit (((n : ℕ) : ℤ) : R)) :
    ∀ i, i < 27 → theta i ∈ V K theta :=
  decodable_of_q13 K theta hadm (q13_decoder theta hadm)

end FastPoly.P27Full
