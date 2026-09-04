import FastPoly.Examples.P27
import FastPoly.Section4.Peeled

/-!
# Conditional composition for the degree-27 special construction

The outer square-shell decoder in `P27.lean` is independent of the internal
implementation of `Q₁₃`.  This file packages the remaining substitution step.
It assumes only the exact public contract needed from a conditional `Q₁₃`
decoder: from the given quadratic and the coefficients of `Q₁₃`, recover its
thirteen parameters and the coefficients of its quartic byproduct.

The proof then decodes `Q₇` and `Q₃` explicitly through `peel_correct`.  In
particular, the quartic is supplied to `Q₇` only after the `Q₁₃` decoder has
recovered it, so the composition cannot hide circular side information.
-/

namespace FastPoly.P27Composition

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The quadratic used by all three inner gadgets. -/
noncomputable abbrev H2 (a : ℕ → A) : A[X] := P27.H2 a

/-- The two-power tower supplied to the Mersenne `Q₃` and `Q₇` gadgets. -/
noncomputable def Hp (a : ℕ → A) (H4 : A[X]) : ℕ → A[X]
  | 1 => H2 a
  | 2 => H4
  | _ => 0

noncomputable def B3 (a : ℕ → A) (H4 : A[X]) : A[X] :=
  peel (Hp a H4) 2 (fun t => a (4 + t))

noncomputable def C7 (a : ℕ → A) (H4 : A[X]) : A[X] :=
  peel (Hp a H4) 3 (fun t => a (7 + t))

noncomputable def T1 (a : ℕ → A) (A13 H4 : A[X]) : A[X] :=
  P27.T1 a A13 (B3 a H4)

noncomputable def T2 (a : ℕ → A) (A13 H4 : A[X]) : A[X] :=
  P27.T2 a A13 (B3 a H4) (C7 a H4)

noncomputable def V (K : Subalgebra R A) (a : ℕ → A) (A13 H4 : A[X]) :
    Subalgebra R A :=
  P27.V K a A13 (B3 a H4) (C7 a H4) 0

/-- The exact relative decoder/byproduct interface required of `Q₁₃`.
It is quantified over the target subalgebra so it composes by ordinary
substitution, without changing the base ring or extending the known context. -/
def Q13Decoder (a : ℕ → A) (A13 H4 : A[X]) : Prop :=
  ∀ S : Subalgebra R A,
    (∀ j, (H2 a).coeff j ∈ S) →
    (∀ j, A13.coeff j ∈ S) →
    (∀ t, t < 13 → a (14 + t) ∈ S) ∧ (∀ j, H4.coeff j ∈ S)

section structural

variable [Nontrivial A]

theorem H2_good (a : ℕ → A) : (H2 a).Monic ∧ (H2 a).natDegree = 2 :=
  P27.H2_good a

theorem Hp_good (a : ℕ → A) (H4 : A[X])
    (hHm : H4.Monic) (hHd : H4.natDegree = 4) :
    ∀ i, 1 ≤ i → i < 3 →
      (Hp a H4 i).Monic ∧ (Hp a H4 i).natDegree = 2 ^ i := by
  intro i hi1 hi3
  match i with
  | 0 => omega
  | 1 => simpa only [Hp, pow_one] using H2_good a
  | 2 => simpa only [Hp] using And.intro hHm (hHd.trans (by norm_num))
  | i + 3 => omega

theorem B3_good (a : ℕ → A) (H4 : A[X])
    (hHm : H4.Monic) (hHd : H4.natDegree = 4) :
    (B3 a H4).Monic ∧ (B3 a H4).natDegree = 3 := by
  have hp : ∀ i, 1 ≤ i → i < 2 →
      (Hp a H4 i).Monic ∧ (Hp a H4 i).natDegree = 2 ^ i := by
    intro i hi1 hi2
    exact Hp_good a H4 hHm hHd i hi1 (by omega)
  have h := peel_monic (Hp a H4) 2 hp (by omega) (fun t => a (4 + t))
  simpa only [B3] using h

theorem C7_good (a : ℕ → A) (H4 : A[X])
    (hHm : H4.Monic) (hHd : H4.natDegree = 4) :
    (C7 a H4).Monic ∧ (C7 a H4).natDegree = 7 := by
  have h := peel_monic (Hp a H4) 3 (Hp_good a H4 hHm hHd) (by omega)
    (fun t => a (7 + t))
  simpa only [C7] using h

/-- The actual `Q₃,Q₇` specialization inherits the unconditional causal
compatibility of the degree-27 outer shell. -/
theorem compatible (K : Subalgebra R A) (a : ℕ → A) (A13 H4 : A[X])
    (htwo : IsUnit (2 : R))
    (hAm : A13.Monic) (hAd : A13.natDegree = 13)
    (hHm : H4.Monic) (hHd : H4.natDegree = 4) :
    CompatiblePair K (T1 a A13 H4) (T2 a A13 H4) 26 (range 27) := by
  obtain ⟨hBm, hBd⟩ := B3_good a H4 hHm hHd
  obtain ⟨hCm, hCd⟩ := C7_good a H4 hHm hHd
  simpa only [T1, T2] using
    P27.shell_compatible K a A13 (B3 a H4) (C7 a H4) htwo
      hAm hAd hBm hBd hCm hCd

end structural

/-- Complete parameter recovery for the degree-27 shell, conditional only on
the public `Q₁₃` decoder/byproduct contract. -/
theorem decodable_of_q13 [Nontrivial A]
    (K : Subalgebra R A) (a : ℕ → A) (A13 H4 : A[X])
    (htwo : IsUnit (2 : R))
    (hAm : A13.Monic) (hAd : A13.natDegree = 13)
    (hHm : H4.Monic) (hHd : H4.natDegree = 4)
    (hQ13 : Q13Decoder (R := R) a A13 H4) :
    ∀ i, i < 27 → a i ∈ V K a A13 H4 := by
  obtain ⟨hBm, hBd⟩ := B3_good a H4 hHm hHd
  obtain ⟨hCm, hCd⟩ := C7_good a H4 hHm hHd
  let cert := P27.outer_recover K a A13 (B3 a H4) (C7 a H4) htwo
    hAm hAd hBm hBd hCm hCd
  have hanti := P27.V_antitone K a A13 (B3 a H4) (C7 a H4)
  have lower : ∀ {x : A} {t : ℕ},
      x ∈ P27.V K a A13 (B3 a H4) (C7 a H4) t → x ∈ V K a A13 H4 := by
    intro x t hx
    simpa only [V] using hanti (Nat.zero_le t) hx

  have hlow : ∀ i, i < 4 → a i ∈ V K a A13 H4 :=
    fun i hi => lower (cert.low i hi)
  have hAcoeff : ∀ j, A13.coeff j ∈ V K a A13 H4 :=
    fun j => lower (cert.Acoeff j)
  have hBcoeff : ∀ j, (B3 a H4).coeff j ∈ V K a A13 H4 :=
    fun j => lower (cert.Bcoeff j)
  have hCcoeff : ∀ j, (C7 a H4).coeff j ∈ V K a A13 H4 :=
    fun j => lower (cert.Ccoeff j)
  have hH2coeff : ∀ j, (H2 a).coeff j ∈ V K a A13 H4 :=
    fun j => lower (cert.h2coeff j)

  -- First decode Q₁₃.  Its byproduct is exactly the quartic required by Q₇.
  obtain ⟨hAparams, hHcoeff⟩ := hQ13 (V K a A13 H4) hH2coeff hAcoeff

  have hpKnown : ∀ q, 1 ≤ q → q < 3 →
      (Hp a H4 q).Monic ∧ (Hp a H4 q).natDegree = 2 ^ q ∧
        ∀ j, (Hp a H4 q).coeff j ∈ V K a A13 H4 := by
    intro q hq1 hq3
    match q with
    | 0 => omega
    | 1 =>
        obtain ⟨hm, hd⟩ := H2_good a
        exact ⟨hm, hd.trans (by norm_num), hH2coeff⟩
    | 2 => exact ⟨hHm, hHd.trans (by norm_num), hHcoeff⟩
    | q + 3 => omega

  -- Then Q₇, now that the quartic is genuinely available.
  have hCparams : ∀ t, t < 7 → a (7 + t) ∈ V K a A13 H4 := by
    intro t ht
    exact peel_correct (K := V K a A13 H4) (Hp a H4) 3 hpKnown (by omega)
      (fun q => a (7 + q)) (V K a A13 H4) le_rfl
      (by intro j; simpa only [C7] using hCcoeff j) t (by norm_num; omega)

  -- Finally Q₃; it needs only the already recovered quadratic.
  have hpKnown2 : ∀ q, 1 ≤ q → q < 2 →
      (Hp a H4 q).Monic ∧ (Hp a H4 q).natDegree = 2 ^ q ∧
        ∀ j, (Hp a H4 q).coeff j ∈ V K a A13 H4 := by
    intro q hq1 hq2
    exact hpKnown q hq1 (by omega)
  have hBparams : ∀ t, t < 3 → a (4 + t) ∈ V K a A13 H4 := by
    intro t ht
    exact peel_correct (K := V K a A13 H4) (Hp a H4) 2 hpKnown2 (by omega)
      (fun q => a (4 + q)) (V K a A13 H4) le_rfl
      (by intro j; simpa only [B3] using hBcoeff j) t (by norm_num; omega)

  intro i hi
  by_cases hi4 : i < 4
  · exact hlow i hi4
  by_cases hi7 : i < 7
  · have ht : i - 4 < 3 := by omega
    simpa only [show 4 + (i - 4) = i by omega] using hBparams (i - 4) ht
  by_cases hi14 : i < 14
  · have ht : i - 7 < 7 := by omega
    simpa only [show 7 + (i - 7) = i by omega] using hCparams (i - 7) ht
  · have ht : i - 14 < 13 := by omega
    simpa only [show 14 + (i - 14) = i by omega] using hAparams (i - 14) ht

end FastPoly.P27Composition
