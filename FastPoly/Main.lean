import FastPoly.Section6.Dispatch
import FastPoly.Section6.Induction
import FastPoly.Section6.SpecialCases
import FastPoly.Examples.P15
import FastPoly.Examples.P27Full
import FastPoly.Examples.P31Full
import FastPoly.Instantiation
import FastPoly.Examples.Septic
import FastPoly.Cost.Final
import FastPoly.Cost.RealizationBases
import FastPoly.Cost.RealizationCrown
import FastPoly.Cost.RealizationP15
import FastPoly.Cost.RealizationP27
import FastPoly.Cost.RealizationP31
import FastPoly.Cost.RealizationEightThree
import FastPoly.Cost.RealizationOuter
import FastPoly.Cost.RealizedOddGadgetDispatch
import FastPoly.Cost.FreeSpecialization
import FastPoly.Examples.BarredGadgets

/-!
# `thm:odd-realizable-pairs` (structural half)

The master strong induction over odd degree: base `n = 3`, the `4k+1` crown branch,
the special degrees `15, 27, 31`, and the two difference-of-squares induction steps
`8k+3` and `8k+7` composed with the `𝒬_d` gadget dispatch.  Every constructed pair is
compatible over `⊥` and carries the exact-parameter-count decoder invariant together
with its recorded powers.  The `≡ 7 (mod 8)` gadget degrees are realized by the sealed
`lem:barQ8k+7` circuits through the realized dispatcher; the `BarredGadgets`
interface remains as the algebraic existence form.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]

/-! ## Coefficient-membership toolkit -/

theorem quad_coeff_mem {S : Subalgebra R A} {b c : A} (hb : b ∈ S) (hc : c ∈ S) :
    ∀ j, ((X + C b) * X + C c : A[X]).coeff j ∈ S :=
  crownH2_coeff_mem hb hc

theorem quad_good (b c : A) : ((X + C b) * X + C c : A[X]).Monic ∧
    ((X + C b) * X + C c : A[X]).natDegree = 2 :=
  crownH2_monic (b := b) (c := c)

omit [Nontrivial A] in
theorem quad_coeff_zero (b c : A) : ((X + C b) * X + C c : A[X]).coeff 0 = c :=
  crownH2_coeff_zero (b := b) (c := c)

omit [Nontrivial A] in
theorem quad_coeff_one (b c : A) : ((X + C b) * X + C c : A[X]).coeff 1 = b :=
  crownH2_coeff_one (b := b) (c := c)

/-! ## The master induction (`thm:odd-realizable-pairs`, structural content) -/

/-- The master height budget: both pair outputs within `D`, the recorded
quadratic at height one, the quartic at height two. -/
abbrev Cost.JointPairProgram.HeightBounded {m : ℕ}
    (prog : Cost.JointPairProgram R m) (D : ℕ) : Prop :=
  prog.circuit.multDepth (fun _ => 0) 0 ≤ D ∧
  prog.circuit.multDepth (fun _ => 0) 1 ≤ D ∧
  prog.circuit.multDepth (fun _ => 0) 2 ≤ 1 ∧
  prog.circuit.multDepth (fun _ => 0) 3 ≤ 2

omit [Nontrivial A] in
/-- Package a joint realization as its fixed-program existential witness.  Keeping
this generic makes the kernel check the structure projections once, on a variable,
rather than unfolding each branch's concrete circuit inside the master's term. -/
theorem joint_exists {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {m D : ℕ}
    (h : Cost.JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ m)
    (h0 : h.circuit.multDepth (fun _ => 0) 0 ≤ D)
    (h1 : h.circuit.multDepth (fun _ => 0) 1 ≤ D)
    (h2 : h.circuit.multDepth (fun _ => 0) 2 ≤ 1)
    (h3 : h.circuit.multDepth (fun _ => 0) 3 ≤ 2) :
    ∃ prog : Cost.JointPairProgram R m, prog.RealizesAt θ T₁ T₂ H₂ H₄ ∧
      prog.HeightBounded D :=
  ⟨h.program, h.program_realizesAt, h0, h1, h2, h3⟩

/-- Rebuild a joint realization from the induction hypothesis' program. -/
private def sourceRealization {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {m m' : ℕ}
    (prog : Cost.JointPairProgram R m)
    (h : prog.RealizesAt θ T₁ T₂ H₂ H₄) (hm : m = m') :
    Cost.JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ m' where
  circuit := prog.circuit
  eval₁ := h.1
  eval₂ := h.2.1
  evalH₂ := h.2.2.1
  evalH₄ := h.2.2.2
  multiplication_count := by rw [prog.multiplication_count, hm]

/-- Ceiling-log arithmetic closing the `8k+3` height ledger. -/
private theorem eightThree_hbound (k : ℕ) :
    ∀ x, x ≤ max (max (2 * Nat.clog 2 (2 * (2 * k) + 1) + 1)
        (2 * Nat.clog 2 (2 * k + 1) + 3) + 1)
      (2 * Nat.clog 2 (2 * k - 1) + 1) →
      x ≤ 2 * Nat.clog 2 (8 * k + 3) + 3 := by
  intro x hx
  have ha : Nat.clog 2 (2 * (2 * (2 * k) + 1))
      = Nat.clog 2 (2 * (2 * k) + 1) + 1 :=
    Height.clog_two_double _ (by omega)
  have hb : Nat.clog 2 (2 * (2 * (2 * k) + 1)) ≤ Nat.clog 2 (8 * k + 3) :=
    Nat.clog_mono_right 2 (by omega)
  have hc : Nat.clog 2 (2 * (2 * k + 1)) = Nat.clog 2 (2 * k + 1) + 1 :=
    Height.clog_two_double _ (by omega)
  have hd' : Nat.clog 2 (2 * (2 * k + 1)) ≤ Nat.clog 2 (8 * k + 3) :=
    Nat.clog_mono_right 2 (by omega)
  have he : Nat.clog 2 (2 * k - 1) ≤ Nat.clog 2 (8 * k + 3) :=
    Nat.clog_mono_right 2 (by omega)
  omega

/-- Ceiling-log arithmetic closing the `8k+7` height ledger. -/
private theorem eightSeven_hbound (k : ℕ) :
    ∀ x, x ≤ max (max
        (2 * Nat.clog 2 (2 * k + 1) + 1)
        (2 * Nat.clog 2 (4 * k + 3) + 1) + 1)
      (2 * Nat.clog 2 (2 * k + 1) + 3) →
      x ≤ 2 * Nat.clog 2 (8 * k + 7) + 3 := by
  intro x hx
  have ha : Nat.clog 2 (2 * k + 1) ≤ Nat.clog 2 (8 * k + 7) :=
    Nat.clog_mono_right 2 (by omega)
  have hb : Nat.clog 2 (4 * k + 3) ≤ Nat.clog 2 (8 * k + 7) :=
    Nat.clog_mono_right 2 (by omega)
  have hc : Nat.clog 2 (2 * k + 1) ≤ Nat.clog 2 (8 * k + 7) :=
    Nat.clog_mono_right 2 (by omega)
  omega

/-- **`thm:odd-realizable-pairs`**: for every odd `n ≥ 3`, `n ≠ 7`, over an
`n`-admissible base, every fresh parameter block `θ` yields a splittable pair
compatible over `⊥` on an explicit window, recording a monic quadratic (and for
`n ≥ 5` a monic quartic) power, such that every subalgebra containing the coefficients
of `P_n = x·T⁽¹⁾ + T⁽²⁾` contains the whole parameter block and both recorded powers —
together with the joint `(n-1)/2`-realization count: each branch attaches its matching
`Cost.PairCost` constructor at exactly the point where it invokes the corresponding
decoding lemma, so the numerical shadow follows the same case split as the
construction.  The `≡ 7 (mod 8)` gadget degrees are delegated to the `BarredGadgets`
interface. -/
theorem odd_realizable_pairs : ∀ n : ℕ, n % 2 = 1 → 3 ≤ n → n ≠ 7 →
    (∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R)) →
    ∀ θ : ℕ → A,
    ∃ (T₁ T₂ H₂ H₄ : A[X]) (G : Finset ℕ),
      CompatiblePair (⊥ : Subalgebra R A) T₁ T₂ (n - 1) G ∧
      H₂.Monic ∧ H₂.natDegree = 2 ∧
      (5 ≤ n → H₄.Monic ∧ H₄.natDegree = 4) ∧
      (∀ V : Subalgebra R A, (∀ j, (combined T₁ T₂).coeff j ∈ V) →
        (∀ t, t < n → θ t ∈ V) ∧ (∀ j, H₂.coeff j ∈ V) ∧
        (5 ≤ n → ∀ j, H₄.coeff j ∈ V)) ∧
      (∃ prog : Cost.JointPairProgram R ((n - 1) / 2),
        prog.RealizesAt θ T₁ T₂ H₂ H₄ ∧
        prog.HeightBounded (2 * Nat.clog 2 n + 3)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hodd hn3 hn7 hadm θ
  have h2 : IsUnit (2 : R) := isUnit_two_of_cast hadm (by omega)
  rcases (show n = 3 ∨ (n % 4 = 1 ∧ 5 ≤ n) ∨ n = 15 ∨ n = 27 ∨ n = 31
      ∨ (n % 8 = 3 ∧ 11 ≤ n ∧ n ≠ 27)
      ∨ (n % 8 = 7 ∧ 23 ≤ n ∧ n ≠ 31) from by omega)
    with rfl | ⟨h41, h5⟩ | rfl | rfl | rfl | ⟨h83, h11, h27⟩ | ⟨h87, h23, h31⟩
  -- ## base `n = 3`
  · refine ⟨(X + C (θ 2)) * X + C (θ 1), (X + C (θ 2)) * X + C (θ 1) + C (θ 0),
      (X + C (θ 2)) * X + C (θ 1), 0, Finset.range 3,
      base_three_compatible (θ 0) (θ 1) (θ 2), (quad_good _ _).1, (quad_good _ _).2,
      fun h5 => absurd h5 (by omega), ?_,
      joint_exists (Cost.Three.realized (R := R) θ)
        ((Cost.Three.multDepth_circuit_le (R := R)).1.trans (by omega))
        ((Cost.Three.multDepth_circuit_le (R := R)).2.1.trans (by omega))
        (Cost.Three.multDepth_circuit_le (R := R)).2.2.1
        ((Cost.Three.multDepth_circuit_le (R := R)).2.2.2.trans (by omega))⟩
    intro V hPV
    obtain ⟨hT₁V, hT₂V⟩ := CausalPair.coeff_mem_of_le
      (base_three_compatible (K := (⊥ : Subalgebra R A)) (a₀ := θ 0) (a₁ := θ 1)
        (a₂ := θ 2)).toCausalPair bot_le hPV
    have h1 : θ 1 ∈ V := by
      have h := hT₁V 0
      rwa [quad_coeff_zero] at h
    have h2' : θ 2 ∈ V := by
      have h := hT₁V 1
      rwa [quad_coeff_one] at h
    have h0 : θ 0 ∈ V := by
      have hb := hT₂V 0
      rw [coeff_add, quad_coeff_zero, coeff_C, if_pos rfl] at hb
      have hkey : θ 0 = ((X + C (θ 2)) * X + C (θ 1) + C (θ 0) : A[X]).coeff 0
          - θ 1 := by
        rw [coeff_add, quad_coeff_zero, coeff_C, if_pos rfl]
        ring
      rw [hkey]
      exact sub_mem (hT₂V 0) h1
    refine ⟨?_, quad_coeff_mem h2' h1, fun h5 => absurd h5 (by omega)⟩
    intro t ht
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 from by omega) with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2'
  -- ## `n ≡ 1 (mod 4)`, `n ≥ 5`: the crown branch
  · obtain ⟨k, hk1, rfl⟩ : ∃ k, 1 ≤ k ∧ n = 4 * k + 1 := ⟨n / 4, by omega⟩
    have hadm' : ∀ i : ℕ, 1 ≤ i → i ≤ 2 * k → IsUnit (((i : ℕ) : ℤ) : R) :=
      fun i hi1 hi2 => hadm i hi1 (by omega)
    refine ⟨(Tpair (crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4)) k 2 (fun t => θ (5 + t))).1,
      (Tpair (crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4)) k 2 (fun t => θ (5 + t))).2,
      crownH2 (θ 0) (θ 1), crownH4 (θ 0) (θ 1) (θ 2) (θ 3),
      Finset.range (4 * k + 1), ?_,
      (crownH2_monic).1, (crownH2_monic).2,
      fun _ => ⟨(crownH4_monic).1, (crownH4_monic).2⟩, ?_,
      (show 2 * k = (4 * k + 1 - 1) / 2 from by omega) ▸
        joint_exists (Cost.Crown.realized (R := R) θ k hk1)
          (Cost.Crown.multDepth_circuit_le (R := R) k hk1).1
          (Cost.Crown.multDepth_circuit_le (R := R) k hk1).2.1
          (Cost.Crown.multDepth_circuit_le (R := R) k hk1).2.2.1
          (Cost.Crown.multDepth_circuit_le (R := R) k hk1).2.2.2⟩
    · have h := fourk_crown_compatible (K := (⊥ : Subalgebra R A)) hk1 hadm'
        (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (fun t => θ (5 + t))
      have hd : 4 * k + 1 - 1 = 4 * k := by omega
      rwa [hd]
    · intro V hPV
      obtain ⟨⟨hb, hc, ha, he, hρ⟩, hH2V, hH4V, hα⟩ := fourk_decodable hk1 hadm' h2
        (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (fun t => θ (5 + t)) V hPV
      refine ⟨?_, hH2V, fun _ => hH4V⟩
      intro t ht
      rcases Nat.lt_or_ge t 5 with h5' | h5'
      · rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 from by omega)
          with rfl | rfl | rfl | rfl | rfl
        · exact hb
        · exact hc
        · exact ha
        · exact he
        · exact hρ
      · have h := hα (t - 5) (by omega)
        rwa [show 5 + (t - 5) = t from by omega] at h
  -- ## the special degree `15`
  · refine ⟨P15.T1 θ (P15.Q7 θ), P15.T2 θ (P15.Q7 θ), P15.H2 θ, P15.H4 θ,
      Finset.range 15, P15.compatible ⊥ θ h2,
      (P15.H2_good θ).1, (P15.H2_good θ).2, fun _ => P15.H4_good θ, ?_,
      joint_exists (Cost.Fifteen.realized (R := R) θ)
        (Cost.Fifteen.multDepth_circuit_le (R := R)).1
        (Cost.Fifteen.multDepth_circuit_le (R := R)).2.1
        (Cost.Fifteen.multDepth_circuit_le (R := R)).2.2.1
        (Cost.Fifteen.multDepth_circuit_le (R := R)).2.2.2⟩
    intro V hPV
    have hle : P15.V (⊥ : Subalgebra R A) θ (P15.Q7 θ) 0 ≤ V := by
      show Vis R ⊥ (P15.Phi θ (P15.Q7 θ)) (Finset.range 15) 0 ≤ V
      exact Vis_le bot_le fun i _ _ => hPV i
    have hθ : ∀ i, i < 15 → θ i ∈ V := fun i hi => hle (P15.decodable ⊥ θ h2 i hi)
    have hH2eq : P15.H2 θ = (X + C (θ 7)) * X + C (θ 6) := rfl
    have hH2V : ∀ j, (P15.H2 θ).coeff j ∈ V := by
      rw [hH2eq]
      exact quad_coeff_mem (hθ 7 (by omega)) (hθ 6 (by omega))
    have hH4V : ∀ j, (P15.H4 θ).coeff j ∈ V := by
      have hH4eq : P15.H4 θ
          = (P15.H2 θ + (X + C (θ 5))) * (P15.H2 θ - (X + C (θ 5))) + C (θ 4) := rfl
      have hH4c : P15.H4 θ = crownH4 (θ 7) (θ 6) (θ 5) (θ 4) := by
        rw [hH4eq, hH2eq]
        unfold crownH4 crownH2
        ring
      rw [hH4c]
      exact crownH4_coeff_mem (hθ 7 (by omega)) (hθ 6 (by omega))
        (hθ 5 (by omega)) (hθ 4 (by omega))
    exact ⟨fun t ht => hθ t ht, hH2V, fun _ => hH4V⟩
  -- ## the special degree `27`
  · have hadm6 : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → IsUnit (((i : ℕ) : ℤ) : R) :=
      fun i h1 h6 => hadm i h1 (by omega)
    refine ⟨P27Full.T1 θ, P27Full.T2 θ, P27Full.H2 θ, P27Full.H4 θ,
      Finset.range 27, P27Full.compatible ⊥ θ hadm6,
      (P27Composition.H2_good θ).1, (P27Composition.H2_good θ).2,
      fun _ => P27Full.H4_good θ, ?_, joint_exists (Cost.TwentySeven.realized (R := R) θ)
        (Cost.TwentySeven.multDepth_circuit_le (R := R)).1
        (Cost.TwentySeven.multDepth_circuit_le (R := R)).2.1
        (Cost.TwentySeven.multDepth_circuit_le (R := R)).2.2.1
        (Cost.TwentySeven.multDepth_circuit_le (R := R)).2.2.2⟩
    intro V hPV
    have hle : P27Full.V (⊥ : Subalgebra R A) θ ≤ V := by
      show Vis R ⊥ (P27.Phi θ (P27Full.A13 θ)
        (P27Composition.B3 θ (P27Full.H4 θ))
        (P27Composition.C7 θ (P27Full.H4 θ))) (Finset.range 27) 0 ≤ V
      exact Vis_le bot_le fun i _ _ => hPV i
    have hθ : ∀ i, i < 27 → θ i ∈ V :=
      fun i hi => hle (P27Full.decodable ⊥ θ hadm6 i hi)
    have hH2eq : P27Full.H2 θ = (X + C (θ 3)) * X + C (θ 2) := rfl
    have hH2V : ∀ j, (P27Full.H2 θ).coeff j ∈ V := by
      rw [hH2eq]
      exact quad_coeff_mem (hθ 3 (by omega)) (hθ 2 (by omega))
    have hH4V : ∀ j, (P27Full.H4 θ).coeff j ∈ V := by
      have hc1 : (P27Full.H2 θ).coeff 1 ∈ V := by
        rw [hH2eq, quad_coeff_one]
        exact hθ 3 (by omega)
      have hc0 : (P27Full.H2 θ).coeff 0 + θ 25 ∈ V := by
        rw [hH2eq, quad_coeff_zero]
        exact add_mem (hθ 2 (by omega)) (hθ 25 (by omega))
      exact crownH4_coeff_mem hc1 hc0 (hθ 23 (by omega)) (hθ 22 (by omega))
    exact ⟨fun t ht => hθ t ht, hH2V, fun _ => hH4V⟩
  -- ## the special degree `31`
  · refine ⟨P31Full.T1 θ, P31Full.T2 θ, P31Full.H2 θ, P31Full.H4 θ,
      Finset.range 31, P31Full.compatible ⊥ θ h2,
      (P31Full.H2_good θ).1, (P31Full.H2_good θ).2,
      fun _ => P31Full.H4_good θ, ?_, joint_exists (Cost.ThirtyOne.realized (R := R) θ)
        (Cost.ThirtyOne.multDepth_circuit_le (R := R)).1
        (Cost.ThirtyOne.multDepth_circuit_le (R := R)).2.1
        (Cost.ThirtyOne.multDepth_circuit_le (R := R)).2.2.1
        (Cost.ThirtyOne.multDepth_circuit_le (R := R)).2.2.2⟩
    intro V hPV
    have hle : P31Full.V (⊥ : Subalgebra R A) θ ≤ V := by
      show Vis R ⊥ (P31.Phi θ (P31Full.A15 θ) (P31Full.B7 θ) (P31Full.H4 θ)
        (P31Full.C3 θ)) (Finset.range 31) 0 ≤ V
      exact Vis_le bot_le fun i _ _ => hPV i
    have hθ : ∀ i, i < 31 → θ i ∈ V :=
      fun i hi => hle (P31Full.decodable ⊥ θ h2 i hi)
    have hH2eq : P31Full.H2 θ = (X + C (θ 7)) * X + C (θ 6) := rfl
    have hH2V : ∀ j, (P31Full.H2 θ).coeff j ∈ V := by
      rw [hH2eq]
      exact quad_coeff_mem (hθ 7 (by omega)) (hθ 6 (by omega))
    have hH4V : ∀ j, (P31Full.H4 θ).coeff j ∈ V := by
      have hH4eq : P31Full.H4 θ
          = (P31Full.H2 θ + (X + C (θ 5))) * (P31Full.H2 θ - (X + C (θ 5)))
            + C (θ 4) := rfl
      have hH4c : P31Full.H4 θ = crownH4 (θ 7) (θ 6) (θ 5) (θ 4) := by
        rw [hH4eq, hH2eq]
        unfold crownH4 crownH2
        ring
      rw [hH4c]
      exact crownH4_coeff_mem (hθ 7 (by omega)) (hθ 6 (by omega))
        (hθ 5 (by omega)) (hθ 4 (by omega))
    exact ⟨fun t ht => hθ t ht, hH2V, fun _ => hH4V⟩
  -- ## `n ≡ 3 (mod 8)`, `n ≥ 11`, `n ≠ 27`: the `8k+3` induction step
  · obtain ⟨k, hk1, hk3, rfl⟩ : ∃ k, 1 ≤ k ∧ k ≠ 3 ∧ n = 8 * k + 3 :=
      ⟨n / 8, by omega, by omega, by omega⟩
    obtain ⟨S₁, St₁, H₂s, H₄s, Gs, hsmall, hH2sm, hH2sd, hH4sg, hsmalldec,
        hreal⟩ :=
      ih (2 * k + 1) (by omega) (by omega) (by omega) (by omega)
        (fun i h1 h2' => hadm i h1 (by omega))
        θ
    rw [show 2 * k + 1 - 1 = 2 * k from by omega] at hsmall
    obtain ⟨progS, hprogS, hpd0, hpd1, hpd2, hpd3⟩ := hreal
    let source : Cost.JointPairRealization (R := R) θ S₁ St₁ H₂s H₄s k :=
      sourceRealization progS hprogS (by omega)
    obtain ⟨hS₂m, hS₂d⟩ := q4k1_good (H2 := H₂s) (α := fun t => θ (2 * k + 6 + t))
      hk1 (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3)) (θ (2 * k + 4))
      (θ (2 * k + 1))
    obtain ⟨hH4bm, hH4bd⟩ := crownH4_monic (A := A) (b := H₂s.coeff 1)
      (c := H₂s.coeff 0 + θ (2 * k + 2)) (a := θ (2 * k + 3)) (e := θ (2 * k + 4))
    have hi1 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
    have hi4 : 2 * k + 1 + 4 = 2 * k + 5 := by omega
    have hi2 : 2 * k + 1 + 2 = 2 * k + 3 := by omega
    have hi3 : 2 * k + 1 + 3 = 2 * k + 4 := by omega
    have hi0 : 2 * k + 1 + 0 = 2 * k + 1 := by omega
    have hif : (fun i => θ (2 * k + 1 + (5 + i))) = fun t => θ (2 * k + 6 + t) :=
      funext fun i => by congr 1; omega
    have hbundle0 : Cost.OddGadget.q4BundleOutput H₂s (fun i => θ (2 * k + 1 + i)) k 0
        = q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3)) (θ (2 * k + 4))
          (θ (2 * k + 1)) k (fun t => θ (2 * k + 6 + t)) := by
      simp only [Cost.OddGadget.q4BundleOutput, Cost.twoOutputs_zero, hi1, hi4,
        hi2, hi3, hi0, hif]
    have hbundle1 : Cost.OddGadget.q4BundleOutput H₂s (fun i => θ (2 * k + 1 + i)) k 1
        = crownH4 (H₂s.coeff 1) (H₂s.coeff 0 + θ (2 * k + 2)) (θ (2 * k + 3))
          (θ (2 * k + 4)) := by
      simp only [Cost.OddGadget.q4BundleOutput, Cost.twoOutputs_one, hi1, hi2, hi3]
    have hH4bm' : (Cost.OddGadget.q4BundleOutput H₂s
        (fun i => θ (2 * k + 1 + i)) k 1).Monic := by rw [hbundle1]; exact hH4bm
    have hH4bd' : (Cost.OddGadget.q4BundleOutput H₂s
        (fun i => θ (2 * k + 1 + i)) k 1).natDegree = 4 := by
      rw [hbundle1]; exact hH4bd
    obtain ⟨gadget⟩ := Cost.RealizedOddGadget.dispatch (R := R) (2 * k - 1)
      (by omega) (fun i h1 h2' => hadm i h1 (by omega)) hH2sm hH2sd hH4bm' hH4bd'
      (fun t => θ (6 * k + 2 + t))
    set S₃ := gadget.Q with hS₃def
    have hS₃m := gadget.monic
    have hS₃d := gadget.natDegree
    have hS₃dec : ∀ V' : Subalgebra R A, (∀ j, H₂s.coeff j ∈ V') →
        (∀ j, (crownH4 (H₂s.coeff 1) (H₂s.coeff 0 + θ (2 * k + 2)) (θ (2 * k + 3))
          (θ (2 * k + 4))).coeff j ∈ V') →
        (∀ j, S₃.coeff j ∈ V') → ∀ t, t < 2 * k - 1 → θ (6 * k + 2 + t) ∈ V' :=
      fun V' hh2 hh4 hq => gadget.recover V' hh2
        (fun j => by rw [hbundle1]; exact hh4 j) hq
    have hS₃lead : S₃.coeff (2 * k - 1) ∈ (⊥ : Subalgebra R A) := by
      have h := hS₃m.coeff_natDegree
      rw [hS₃d] at h
      rw [h]
      exact one_mem _
    have hcompat := eightk3_compatible (K := (⊥ : Subalgebra R A))
      (a := θ (8 * k + 1)) (α₀ := θ (8 * k + 2)) hk1 h2 hsmall hS₂m hS₂d
      (le_of_eq hS₃d) hS₃lead
    refine ⟨q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3))
        (θ (2 * k + 4)) (θ (2 * k + 1)) k (fun t => θ (2 * k + 6 + t))
        * q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3))
          (θ (2 * k + 4)) (θ (2 * k + 1)) k (fun t => θ (2 * k + 6 + t))
        - S₁ * S₁ + S₃,
      (q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3))
          (θ (2 * k + 4)) (θ (2 * k + 1)) k (fun t => θ (2 * k + 6 + t))
          + C (θ (8 * k + 1)))
        * (q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3))
            (θ (2 * k + 4)) (θ (2 * k + 1)) k (fun t => θ (2 * k + 6 + t))
            + C (θ (8 * k + 1)))
        - St₁ * St₁ + C (θ (8 * k + 2)),
      H₂s, crownH4 (H₂s.coeff 1) (H₂s.coeff 0 + θ (2 * k + 2)) (θ (2 * k + 3))
        (θ (2 * k + 4)),
      Finset.Icc (4 * k + 1) (8 * k + 2) ∪ shiftW (2 * k) Gs
        ∪ Finset.range (2 * k + 1),
      (by rw [show 8 * k + 3 - 1 = 8 * k + 2 from by omega]; exact hcompat),
      hH2sm, hH2sd, fun _ => ⟨hH4bm, hH4bd⟩, ?_, ?_⟩
    swap
    · obtain ⟨hd0, hd1, hd2, hd3⟩ :=
        Cost.Outer.multDepth_eightThreeFromGadget_le (R := R) source hH2sm hH2sd
          k hk1 (2 * k + 1) (6 * k + 2) (8 * k + 1) (8 * k + 2) gadget
          (by omega) (2 * Nat.clog 2 (2 * k + 1) + 3) hpd0 hpd1 hpd2 hpd3
      have hbound := eightThree_hbound k
      obtain ⟨prog, hpr, hh⟩ :=
        joint_exists (Cost.Outer.eightThreeFromGadget (R := R) source hH2sm
          hH2sd k hk1 (2 * k + 1) (6 * k + 2) (8 * k + 1) (8 * k + 2) gadget)
          (hbound _ hd0) (hbound _ hd1) hd2 hd3
      exact (show k + 2 * k + (2 * k - 1) / 2 + 2 = (8 * k + 3 - 1) / 2
        from by omega) ▸
        ⟨prog, ⟨hpr.1.trans (by rw [hbundle0]; ring),
          hpr.2.1.trans (by rw [hbundle0]; ring), hpr.2.2.1,
          hpr.2.2.2.trans hbundle1⟩, hh⟩
    intro V hPV
    have hsmalldec' : ∀ W : Subalgebra R A, (⊥ : Subalgebra R A) ≤ W →
        (∀ j, (combined S₁ St₁).coeff j ∈ W) →
        ((θ '' {t | t < 2 * k + 1}) ∪ Set.range fun j => H₂s.coeff j)
          ⊆ (W : Set A) ∧ (∀ j, H₂s.coeff j ∈ W) := by
      intro W _ hW
      obtain ⟨hθW, hH2W, -⟩ := hsmalldec W hW
      refine ⟨?_, hH2W⟩
      rintro x (⟨t, ht, rfl⟩ | ⟨j, rfl⟩)
      · exact hθW t ht
      · exact hH2W j
    have hS₂dec' : ∀ W : Subalgebra R A, (⊥ : Subalgebra R A) ≤ W →
        (∀ j, (q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3))
          (θ (2 * k + 4)) (θ (2 * k + 1)) k
          (fun t => θ (2 * k + 6 + t))).coeff j ∈ W) →
        (∀ j, H₂s.coeff j ∈ W) →
        ((θ '' {t | 2 * k + 1 ≤ t ∧ t < 6 * k + 2}) ∪ Set.range fun j =>
          (crownH4 (H₂s.coeff 1) (H₂s.coeff 0 + θ (2 * k + 2)) (θ (2 * k + 3))
            (θ (2 * k + 4))).coeff j) ⊆ (W : Set A)
        ∧ (∀ j, (crownH4 (H₂s.coeff 1) (H₂s.coeff 0 + θ (2 * k + 2))
            (θ (2 * k + 3)) (θ (2 * k + 4))).coeff j ∈ W) := by
      intro W _ hS₂W hH2W
      obtain ⟨⟨hβ, hγ, ha, he, hρ⟩, hH4W, hα⟩ := q4k1_decodable hk1
        (fun i h1 h2' => hadm i h1 (by omega)) h2 hH2sm hH2sd
        (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3)) (θ (2 * k + 4))
        (θ (2 * k + 1)) W hH2W hS₂W
      refine ⟨?_, hH4W⟩
      rintro x (⟨t, ⟨ht1, ht2⟩, rfl⟩ | ⟨j, rfl⟩)
      · rcases (show t = 2 * k + 1 ∨ t = 2 * k + 2 ∨ t = 2 * k + 3 ∨ t = 2 * k + 4
            ∨ t = 2 * k + 5 ∨ 2 * k + 6 ≤ t from by omega)
          with rfl | rfl | rfl | rfl | rfl | h6
        · exact hβ
        · exact hγ
        · exact ha
        · exact he
        · exact hρ
        · have h := hα (t - (2 * k + 6)) (by omega)
          rwa [show 2 * k + 6 + (t - (2 * k + 6)) = t from by omega] at h
      · exact hH4W j
    have hS₃dec' : ∀ W : Subalgebra R A, (⊥ : Subalgebra R A) ≤ W →
        (∀ j, S₃.coeff j ∈ W) → (∀ j, H₂s.coeff j ∈ W) →
        (∀ j, (crownH4 (H₂s.coeff 1) (H₂s.coeff 0 + θ (2 * k + 2)) (θ (2 * k + 3))
          (θ (2 * k + 4))).coeff j ∈ W) →
        (θ '' {t | 6 * k + 2 ≤ t ∧ t < 8 * k + 1}) ⊆ (W : Set A) := by
      intro W _ hS₃W hH2W hH4W
      rintro x ⟨t, ⟨ht1, ht2⟩, rfl⟩
      have h := hS₃dec W hH2W hH4W hS₃W (t - (6 * k + 2)) (by omega)
      rwa [show 6 * k + 2 + (t - (6 * k + 2)) = t from by omega] at h
    obtain ⟨ha', hα₀', hΘs, hΘ₂, hΘ₃⟩ := eightk3_decodable
      (K := (⊥ : Subalgebra R A)) hk1 h2 hsmall hS₂m hS₂d (le_of_eq hS₃d) hS₃lead
      hsmalldec' hS₂dec' hS₃dec' rfl
    have hVP : (⊥ : Subalgebra R A) ⊔ adjoin R (Set.range fun i =>
        (combined (q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3))
            (θ (2 * k + 4)) (θ (2 * k + 1)) k (fun t => θ (2 * k + 6 + t))
            * q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3))
              (θ (2 * k + 4)) (θ (2 * k + 1)) k (fun t => θ (2 * k + 6 + t))
            - S₁ * S₁ + S₃)
          ((q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3))
              (θ (2 * k + 4)) (θ (2 * k + 1)) k (fun t => θ (2 * k + 6 + t))
              + C (θ (8 * k + 1)))
            * (q4k1 H₂s (θ (2 * k + 2)) (θ (2 * k + 5)) (θ (2 * k + 3))
                (θ (2 * k + 4)) (θ (2 * k + 1)) k (fun t => θ (2 * k + 6 + t))
                + C (θ (8 * k + 1)))
            - St₁ * St₁ + C (θ (8 * k + 2)))).coeff i) ≤ V :=
      sup_le bot_le (adjoin_le (by rintro _ ⟨i, rfl⟩; exact hPV i))
    refine ⟨?_, fun j => hVP (hΘs (Or.inr ⟨j, rfl⟩)),
      fun _ j => hVP (hΘ₂ (Or.inr ⟨j, rfl⟩))⟩
    intro t ht
    rcases (show t < 2 * k + 1 ∨ (2 * k + 1 ≤ t ∧ t < 6 * k + 2)
        ∨ (6 * k + 2 ≤ t ∧ t < 8 * k + 1) ∨ t = 8 * k + 1 ∨ t = 8 * k + 2
        from by omega) with hcase | hcase | hcase | rfl | rfl
    · exact hVP (hΘs (Or.inl ⟨t, hcase, rfl⟩))
    · exact hVP (hΘ₂ (Or.inl ⟨t, hcase, rfl⟩))
    · exact hVP (hΘ₃ ⟨t, hcase, rfl⟩)
    · exact hVP ha'
    · exact hVP hα₀'
  -- ## `n ≡ 7 (mod 8)`, `n ≥ 23`, `n ≠ 31`: the `8k+7` induction step
  · obtain ⟨k, hk2, hk3, rfl⟩ : ∃ k, 2 ≤ k ∧ k ≠ 3 ∧ n = 8 * k + 7 :=
      ⟨n / 8, by omega, by omega, by omega⟩
    obtain ⟨T₁', T₂', H₂s, H₄s, Gs, hsmall, hH2sm, hH2sd, hH4sg, hsmalldec,
        hreal⟩ :=
      ih (2 * k + 1) (by omega) (by omega) (by omega) (by omega)
        (fun i h1 h2' => hadm i h1 (by omega))
        θ
    rw [show 2 * k + 1 - 1 = 2 * k from by omega] at hsmall
    obtain ⟨hH4sm, hH4sd⟩ := hH4sg (by omega)
    obtain ⟨progS, hprogS, hpd0, hpd1, hpd2, hpd3⟩ := hreal
    let source : Cost.JointPairRealization (R := R) θ T₁' T₂' H₂s H₄s k :=
      sourceRealization progS hprogS (by omega)
    obtain ⟨g₂⟩ := Cost.RealizedOddGadget.dispatch (R := R) (2 * k + 1) (by omega)
      (fun i h1 h2' => hadm i h1 (by omega)) hH2sm hH2sd hH4sm hH4sd
      (fun t => θ (2 * k + 1 + t))
    obtain ⟨g₃⟩ := Cost.RealizedOddGadget.dispatch (R := R) (4 * k + 3) (by omega)
      (fun i h1 h2' => hadm i h1 (by omega)) hH2sm hH2sd hH4sm hH4sd
      (fun t => θ (4 * k + 2 + t))
    set S₂ := g₂.Q with hS₂def
    set S₃ := g₃.Q with hS₃def
    have hS₂m := g₂.monic
    have hS₂d := g₂.natDegree
    have hS₂dec := g₂.recover
    have hS₃m := g₃.monic
    have hS₃d := g₃.natDegree
    have hS₃dec := g₃.recover
    -- the `(s, d)` fresh block of the counted schedule, and its `(a, b)` shadow
    have hu : (↑h2.unit : R) = 2 := h2.unit_spec
    set u := h2.unit with hudef
    have hhalfA : algebraMap R A ↑u⁻¹ * 2 = 1 := by
      rw [show (2 : A) = algebraMap R A 2 from (map_ofNat _ 2).symm, ← hu,
        ← map_mul, Units.inv_mul, map_one]
    set b : A := algebraMap R A ↑u⁻¹ * (θ (8 * k + 5) + θ (8 * k + 6)) with hbdef
    set a : A := algebraMap R A ↑u⁻¹ * (θ (8 * k + 5) - θ (8 * k + 6)) with hadef
    have haux1 : b + a = θ (8 * k + 5) := by
      rw [hbdef, hadef]
      linear_combination (θ (8 * k + 5)) * hhalfA
    have haux2 : b - a = θ (8 * k + 6) := by
      rw [hbdef, hadef]
      linear_combination (θ (8 * k + 6)) * hhalfA
    have hT₂eq : (S₃ + S₂ + C (θ (8 * k + 5))) * (S₃ - S₂ + C (θ (8 * k + 6)))
        + T₂'
        = (S₃ + C b) * (S₃ + C b) - (S₂ + C a) * (S₂ + C a) + T₂' := by
      rw [← haux1, ← haux2]
      simp only [map_add, map_sub]
      ring
    have hcompat := eightk7_compatible (K := (⊥ : Subalgebra R A))
      (a := a) (b := b) (by omega) h2 hsmall hS₂m hS₂d hS₃m hS₃d
    rw [← hT₂eq] at hcompat
    refine ⟨S₃ * S₃ - S₂ * S₂ + T₁',
      (S₃ + S₂ + C (θ (8 * k + 5))) * (S₃ - S₂ + C (θ (8 * k + 6))) + T₂',
      H₂s, H₄s, Finset.Icc (2 * k + 1) (8 * k + 6) ∪ Gs,
      (by rw [show 8 * k + 7 - 1 = 8 * k + 6 from by omega]; exact hcompat),
      hH2sm, hH2sd, fun _ => ⟨hH4sm, hH4sd⟩, ?_, ?_⟩
    swap
    · obtain ⟨hd0, hd1, hd2, hd3⟩ :=
        Cost.Outer.multDepth_eightSevenCircuit_le source
          (Cost.RealizedOddGadget.relative (R := R) source g₂)
          (Cost.RealizedOddGadget.relative (R := R) source g₃)
          (8 * k + 5) (8 * k + 6) (2 * Nat.clog 2 (2 * k + 1) + 3)
          (2 * Nat.clog 2 (2 * k + 1) + 1)
          (2 * Nat.clog 2 (4 * k + 3) + 1)
          hpd0 hpd1 hpd2 hpd3
          (Cost.RealizedOddGadget.relative_circuit_multDepth_le source g₂
            (by omega) hpd2 hpd3)
          (Cost.RealizedOddGadget.relative_circuit_multDepth_le source g₃
            (by omega) hpd2 hpd3)
      have hbound := eightSeven_hbound k
      exact (show k + (2 * k + 1) / 2 + (4 * k + 3) / 2 + 2 = (8 * k + 7 - 1) / 2
        from by omega) ▸
        joint_exists (Cost.Outer.eightSevenRealized source
          (Cost.RealizedOddGadget.relative (R := R) source g₂)
          (Cost.RealizedOddGadget.relative (R := R) source g₃)
          (8 * k + 5) (8 * k + 6))
          (hbound _ hd0) (hbound _ hd1) hd2 hd3
    intro V hPV
    have hsmalldec' : ∀ W : Subalgebra R A, (⊥ : Subalgebra R A) ≤ W →
        (∀ j, (combined T₁' T₂').coeff j ∈ W) →
        (((θ '' {t | t < 2 * k + 1}) ∪ Set.range fun j => H₂s.coeff j)
          ∪ Set.range fun j => H₄s.coeff j) ⊆ (W : Set A)
        ∧ (∀ j, H₂s.coeff j ∈ W) ∧ (∀ j, H₄s.coeff j ∈ W) := by
      intro W _ hW
      obtain ⟨hθW, hH2W, hH4W⟩ := hsmalldec W hW
      refine ⟨?_, hH2W, hH4W (by omega)⟩
      rintro x ((⟨t, ht, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
      · exact hθW t ht
      · exact hH2W j
      · exact hH4W (by omega) j
    have hS₂dec' : ∀ W : Subalgebra R A, (⊥ : Subalgebra R A) ≤ W →
        (∀ j, S₂.coeff j ∈ W) → (∀ j, H₂s.coeff j ∈ W) →
        (∀ j, H₄s.coeff j ∈ W) →
        (θ '' {t | 2 * k + 1 ≤ t ∧ t < 4 * k + 2}) ⊆ (W : Set A) := by
      intro W _ hS₂W hH2W hH4W
      rintro x ⟨t, ⟨ht1, ht2⟩, rfl⟩
      have h := hS₂dec W hH2W hH4W hS₂W (t - (2 * k + 1)) (by omega)
      rwa [show 2 * k + 1 + (t - (2 * k + 1)) = t from by omega] at h
    have hS₃dec' : ∀ W : Subalgebra R A, (⊥ : Subalgebra R A) ≤ W →
        (∀ j, S₃.coeff j ∈ W) → (∀ j, H₂s.coeff j ∈ W) →
        (∀ j, H₄s.coeff j ∈ W) →
        (θ '' {t | 4 * k + 2 ≤ t ∧ t < 8 * k + 5}) ⊆ (W : Set A) := by
      intro W _ hS₃W hH2W hH4W
      rintro x ⟨t, ⟨ht1, ht2⟩, rfl⟩
      have h := hS₃dec W hH2W hH4W hS₃W (t - (4 * k + 2)) (by omega)
      rwa [show 4 * k + 2 + (t - (4 * k + 2)) = t from by omega] at h
    obtain ⟨ha', hb', hΘs, hΘ₂, hΘ₃⟩ := eightk7_decodable
      (K := (⊥ : Subalgebra R A)) (by omega) h2 hsmall hS₂m hS₂d hS₃m hS₃d
      hsmalldec' hS₂dec' hS₃dec'
      (P := combined (S₃ * S₃ - S₂ * S₂ + T₁')
        ((S₃ + S₂ + C (θ (8 * k + 5))) * (S₃ - S₂ + C (θ (8 * k + 6))) + T₂'))
      (by rw [hT₂eq])
    have hVP : (⊥ : Subalgebra R A) ⊔ adjoin R (Set.range fun i =>
        (combined (S₃ * S₃ - S₂ * S₂ + T₁')
          ((S₃ + S₂ + C (θ (8 * k + 5))) * (S₃ - S₂ + C (θ (8 * k + 6)))
            + T₂')).coeff i) ≤ V :=
      sup_le bot_le (adjoin_le (by rintro _ ⟨i, rfl⟩; exact hPV i))
    refine ⟨?_, fun j => hVP (hΘs (Or.inl (Or.inr ⟨j, rfl⟩))),
      fun _ j => hVP (hΘs (Or.inr ⟨j, rfl⟩))⟩
    intro t ht
    rcases (show t < 2 * k + 1 ∨ (2 * k + 1 ≤ t ∧ t < 4 * k + 2)
        ∨ (4 * k + 2 ≤ t ∧ t < 8 * k + 5) ∨ t = 8 * k + 5 ∨ t = 8 * k + 6
        from by omega) with hcase | hcase | hcase | rfl | rfl
    · exact hVP (hΘs (Or.inl (Or.inl ⟨t, hcase, rfl⟩)))
    · exact hVP (hΘ₂ ⟨t, hcase, rfl⟩)
    · exact hVP (hΘ₃ ⟨t, hcase, rfl⟩)
    · have h := add_mem (hVP hb') (hVP ha')
      rwa [haux1] at h
    · have h := sub_mem (hVP hb') (hVP ha')
      rwa [haux2] at h

/-- **Algebraic-existence discharge of the barred interface** (NOT used by the
counting endpoints): the master pair itself supplies a decodable monic gadget of every
degree `8m+7` — its combined polynomial is monic of the right degree and decodes its
full fresh parameter block from its coefficients alone (the supplied powers are not
even needed).  It deliberately spends one more product per barred slot than the
dedicated `lem:barQ8k+7` circuit, so the endpoints below instantiate
`barredGadgets_of_admissible` (the schedule-faithful barred construction) instead;
this lemma remains as an independent, purely algebraic existence argument.  The
recursion is well-founded because every barred degree the master consumes is strictly
below its own degree. -/
theorem barredGadgets_algebraic : ∀ cap : ℕ,
    (∀ i : ℕ, 1 ≤ i → i ≤ cap → IsUnit (((i : ℕ) : ℤ) : R)) →
    BarredGadgets (R := R) (A := A) cap := by
  intro cap hadm H₂ H₄ h2m h2d h4m h4d m hm hcap θ
  obtain ⟨T₁, T₂, H₂', H₄', G, hcp, -, -, -, hdec, -⟩ :=
    odd_realizable_pairs (R := R) (A := A) (8 * m + 7) (by omega) (by omega)
      (by omega) (fun i h1 h2' => hadm i h1 (by omega)) θ
  obtain ⟨hQm, hQd⟩ := combined_good_of_monic hcp.monic₁ hcp.natDegree₁
    hcp.monic₂ hcp.natDegree₂
  refine ⟨combined T₁ T₂, hQm, by rw [hQd]; omega, ?_⟩
  intro V _ _ hQV t ht
  exact (hdec V hQV).1 t ht

/-- **`thm:odd-realizable-pairs`, joint-realization form**: the semantic conjunct is
the fixed base-ring program (`JointPairProgram`), whose circuit is the counted
schedule itself — the barred residue classes are realized internally by the
schedule-faithful `barQ` circuits, so only `n`-admissibility remains. -/
theorem odd_realizable_pairs' (n : ℕ) (hodd : n % 2 = 1) (hn3 : 3 ≤ n) (hn7 : n ≠ 7)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R)) (θ : ℕ → A) :
    ∃ (T₁ T₂ H₂ H₄ : A[X]) (G : Finset ℕ),
      CompatiblePair (⊥ : Subalgebra R A) T₁ T₂ (n - 1) G ∧
      H₂.Monic ∧ H₂.natDegree = 2 ∧
      (5 ≤ n → H₄.Monic ∧ H₄.natDegree = 4) ∧
      (∀ V : Subalgebra R A, (∀ j, (combined T₁ T₂).coeff j ∈ V) →
        (∀ t, t < n → θ t ∈ V) ∧ (∀ j, H₂.coeff j ∈ V) ∧
        (5 ≤ n → ∀ j, H₄.coeff j ∈ V)) ∧
      (∃ prog : Cost.JointPairProgram R ((n - 1) / 2),
        prog.RealizesAt θ T₁ T₂ H₂ H₄ ∧
        prog.HeightBounded (2 * Nat.clog 2 n + 3)) :=
  odd_realizable_pairs n hodd hn3 hn7 hadm θ

section Coverage

variable {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [Nontrivial R'] {n : ℕ}

/-- **`cor:all-odd-decodable` (coverage form)**: instantiating the master construction
at the free coordinate algebra, the resulting monic degree-`n` polynomial has a
bijective coefficient substitution — every monic degree-`n` polynomial is a unique
instance of the decodable family. -/
theorem odd_coefficient_map_bijective (hodd : n % 2 = 1) (hn3 : 3 ≤ n) (hn7 : n ≠ 7)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R')) :
    ∃ (T₁ T₂ : (MvPolynomial (Fin n) R')[X]) (G : Finset ℕ),
      CompatiblePair (⊥ : Subalgebra R' (MvPolynomial (Fin n) R')) T₁ T₂ (n - 1) G ∧
      (combined T₁ T₂).Monic ∧ (combined T₁ T₂).natDegree = n ∧
      Function.Bijective (MvPolynomial.aeval (R := R')
        (fun i : Fin n => (combined T₁ T₂).coeff i)) := by
  obtain ⟨T₁, T₂, H₂, H₄, G, hcp, -, -, -, hdec, -⟩ :=
    odd_realizable_pairs' (R := R') (A := MvPolynomial (Fin n) R') n hodd hn3 hn7
      hadm (fun t => if h : t < n then MvPolynomial.X (⟨t, h⟩ : Fin n) else 0)
  obtain ⟨hPm, hPd⟩ := combined_good_of_monic hcp.monic₁ hcp.natDegree₁
    hcp.monic₂ hcp.natDegree₂
  have hPd' : (combined T₁ T₂).natDegree = n := by rw [hPd]; omega
  refine ⟨T₁, T₂, G, hcp, hPm, hPd', ?_⟩
  apply coefficient_aeval_bijective_of_monic_decodable _ hPm hPd'
  intro i
  have hV : ∀ j, (combined T₁ T₂).coeff j ∈
      (⊥ : Subalgebra R' (MvPolynomial (Fin n) R'))
        ⊔ Algebra.adjoin R' (Set.range fun j : ℕ => (combined T₁ T₂).coeff j) :=
    fun j => (le_sup_right :
      Algebra.adjoin R' (Set.range fun j : ℕ => (combined T₁ T₂).coeff j) ≤ _)
      (Algebra.subset_adjoin ⟨j, rfl⟩)
  have h := (hdec _ hV).1 i.1 i.2
  rw [dif_pos i.2] at h
  exact (sup_le bot_le le_rfl :
    (⊥ : Subalgebra R' (MvPolynomial (Fin n) R'))
      ⊔ Algebra.adjoin R' (Set.range fun j : ℕ => (combined T₁ T₂).coeff j) ≤ _) h

/-- The even lift `P = x·Q + c₀`: a monic degree-`(n-1)` family whose first `n-1`
coordinates decode from its coefficients lifts to a monic degree-`n` family with a
bijective coefficient substitution. -/
theorem even_lift_bijective (hn : 2 ≤ n) (Q : (MvPolynomial (Fin n) R')[X])
    (hQm : Q.Monic) (hQd : Q.natDegree = n - 1)
    (hQdec : ∀ V : Subalgebra R' (MvPolynomial (Fin n) R'),
      (∀ j, Q.coeff j ∈ V) → ∀ i : Fin n, i.1 < n - 1 → MvPolynomial.X i ∈ V) :
    ∃ P : (MvPolynomial (Fin n) R')[X], P.Monic ∧ P.natDegree = n ∧
      Function.Bijective (MvPolynomial.aeval (R := R')
        (fun i : Fin n => P.coeff i)) := by
  have hnn : n - 1 < n := by omega
  set c : Fin n := ⟨n - 1, hnn⟩ with hc
  have hcv : (c : ℕ) = n - 1 := rfl
  have hXQm : (X * Q).Monic := monic_X.mul hQm
  have hXQd : (X * Q).natDegree = n := by
    rw [monic_X.natDegree_mul hQm, natDegree_X, hQd]
    omega
  obtain ⟨hPm, hPd⟩ := monic_add_low (e := C (MvPolynomial.X c)) hXQm
    (Or.inr (by rw [natDegree_C, hXQd]; omega))
  refine ⟨X * Q + C (MvPolynomial.X c), hPm, hPd.trans hXQd, ?_⟩
  apply coefficient_aeval_bijective_of_monic_decodable _ hPm (hPd.trans hXQd)
  intro i
  have hP0 : (X * Q + C (MvPolynomial.X c)).coeff 0 = MvPolynomial.X c := by
    rw [coeff_add, mul_coeff_zero, coeff_X_zero, zero_mul, coeff_C, if_pos rfl,
      zero_add]
  have hPj : ∀ j, (X * Q + C (MvPolynomial.X c)).coeff (j + 1) = Q.coeff j := by
    intro j
    rw [coeff_add, coeff_X_mul, coeff_C, if_neg (by omega), add_zero]
  have hQmem : ∀ j, Q.coeff j ∈ Algebra.adjoin R' (Set.range fun j : ℕ =>
      (X * Q + C (MvPolynomial.X c)).coeff j) := by
    intro j
    rw [← hPj j]
    exact Algebra.subset_adjoin ⟨j + 1, rfl⟩
  rcases Nat.lt_or_ge i.1 (n - 1) with hi | hi
  · exact hQdec _ hQmem i hi
  · have hv : i = c := by
      have hlt := i.2
      exact Fin.ext (by omega)
    have hmem : (X * Q + C (MvPolynomial.X c)).coeff 0
        ∈ Algebra.adjoin R' (Set.range fun j : ℕ =>
          (X * Q + C (MvPolynomial.X c)).coeff j) :=
      Algebra.subset_adjoin ⟨0, rfl⟩
    rw [hP0] at hmem
    rw [hv]
    exact hmem

/-- **`thm:construction-count` (coverage clause)**: for every `n ≥ 1`, the appropriate
family — affine, quadratic, septic, the odd master construction, or the even lift
`P = x·Q_{n-1} + c₀` — yields a monic degree-`n` polynomial over the free coordinate
algebra whose coefficient substitution is bijective: every monic degree-`n`
coefficient vector is a unique instance of a decodable family. -/
theorem monic_coefficient_map_bijective (hn : 1 ≤ n)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R')) :
    ∃ P : (MvPolynomial (Fin n) R')[X], P.Monic ∧ P.natDegree = n ∧
      Function.Bijective (MvPolynomial.aeval (R := R')
        (fun i : Fin n => P.coeff i)) := by
  rcases (show n = 1 ∨ n = 2 ∨ n = 7 ∨ (n % 2 = 1 ∧ 3 ≤ n ∧ n ≠ 7)
      ∨ (n % 2 = 0 ∧ 4 ≤ n) from by omega)
    with rfl | rfl | rfl | ⟨hodd, h3, h7⟩ | ⟨heven, h4⟩
  -- `n = 1`
  · refine ⟨X + C (MvPolynomial.X ⟨0, by omega⟩), monic_X_add_C _,
      natDegree_X_add_C _, ?_⟩
    apply coefficient_aeval_bijective_of_monic_decodable _ (monic_X_add_C _)
      (natDegree_X_add_C _)
    intro i
    have h0 : (X + C (MvPolynomial.X (⟨0, by omega⟩ : Fin 1))
        : (MvPolynomial (Fin 1) R')[X]).coeff 0
        = MvPolynomial.X ⟨0, by omega⟩ := by
      rw [coeff_add, coeff_X_zero, coeff_C, if_pos rfl, zero_add]
    have hmem : (X + C (MvPolynomial.X (⟨0, by omega⟩ : Fin 1))
        : (MvPolynomial (Fin 1) R')[X]).coeff 0
        ∈ Algebra.adjoin R' (Set.range fun j : ℕ =>
          (X + C (MvPolynomial.X (⟨0, by omega⟩ : Fin 1))
            : (MvPolynomial (Fin 1) R')[X]).coeff j) :=
      Algebra.subset_adjoin ⟨0, rfl⟩
    rw [h0] at hmem
    rw [Subsingleton.elim i (⟨0, by omega⟩ : Fin 1)]
    exact hmem
  -- `n = 2`
  · refine ⟨(X + C (MvPolynomial.X ⟨1, by omega⟩)) * X
      + C (MvPolynomial.X ⟨0, by omega⟩), (quad_good _ _).1, (quad_good _ _).2, ?_⟩
    apply coefficient_aeval_bijective_of_monic_decodable _ (quad_good _ _).1
      (quad_good _ _).2
    intro i
    obtain ⟨iv, hiv⟩ := i
    rcases (show iv = 0 ∨ iv = 1 from by omega) with rfl | rfl
    · have hmem : ((X + C (MvPolynomial.X ⟨1, by omega⟩)) * X
          + C (MvPolynomial.X ⟨0, by omega⟩)
          : (MvPolynomial (Fin 2) R')[X]).coeff 0
          ∈ Algebra.adjoin R' (Set.range fun j : ℕ =>
            ((X + C (MvPolynomial.X ⟨1, by omega⟩)) * X
              + C (MvPolynomial.X ⟨0, by omega⟩)
              : (MvPolynomial (Fin 2) R')[X]).coeff j) :=
        Algebra.subset_adjoin ⟨0, rfl⟩
      rw [quad_coeff_zero] at hmem
      exact hmem
    · have hmem : ((X + C (MvPolynomial.X ⟨1, by omega⟩)) * X
          + C (MvPolynomial.X ⟨0, by omega⟩)
          : (MvPolynomial (Fin 2) R')[X]).coeff 1
          ∈ Algebra.adjoin R' (Set.range fun j : ℕ =>
            ((X + C (MvPolynomial.X ⟨1, by omega⟩)) * X
              + C (MvPolynomial.X ⟨0, by omega⟩)
              : (MvPolynomial (Fin 2) R')[X]).coeff j) :=
        Algebra.subset_adjoin ⟨1, rfl⟩
      rw [quad_coeff_one] at hmem
      exact hmem
  -- `n = 7`: the direct septic
  · have h2 : IsUnit (2 : R') := isUnit_two_of_cast hadm (by omega)
    set x7 : Fin 7 → MvPolynomial (Fin 7) R' := MvPolynomial.X with hx7
    obtain ⟨hm, hd⟩ := septic_good (x7 ⟨0, by omega⟩) (x7 ⟨1, by omega⟩)
      (x7 ⟨2, by omega⟩) (x7 ⟨3, by omega⟩) (x7 ⟨4, by omega⟩) (x7 ⟨5, by omega⟩)
      (x7 ⟨6, by omega⟩)
    refine ⟨_, hm, hd, ?_⟩
    apply coefficient_aeval_bijective_of_monic_decodable _ hm hd
    intro i
    have hcoeff : ∀ j, j < 7 → (septic (x7 ⟨0, by omega⟩) (x7 ⟨1, by omega⟩)
        (x7 ⟨2, by omega⟩) (x7 ⟨3, by omega⟩) (x7 ⟨4, by omega⟩) (x7 ⟨5, by omega⟩)
        (x7 ⟨6, by omega⟩)).coeff j
        ∈ Algebra.adjoin R' (Set.range fun j : ℕ =>
          (septic (x7 ⟨0, by omega⟩) (x7 ⟨1, by omega⟩) (x7 ⟨2, by omega⟩)
            (x7 ⟨3, by omega⟩) (x7 ⟨4, by omega⟩) (x7 ⟨5, by omega⟩)
            (x7 ⟨6, by omega⟩)).coeff j) :=
      fun j _ => Algebra.subset_adjoin ⟨j, rfl⟩
    obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ :=
      septic_decodable_of_coeff_mem _ _ _ _ _ _ _ h2 hcoeff
    obtain ⟨iv, hiv⟩ := i
    rcases (show iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 ∨ iv = 4 ∨ iv = 5 ∨ iv = 6
        from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact p0
    · exact p1
    · exact p2
    · exact p3
    · exact p4
    · exact p5
    · exact p6
  -- odd `n ≥ 3`, `n ≠ 7`: the master family
  · obtain ⟨T₁, T₂, G, -, hPm, hPd, hbij⟩ :=
      odd_coefficient_map_bijective (R' := R') hodd h3 h7 hadm
    exact ⟨combined T₁ T₂, hPm, hPd, hbij⟩
  -- even `n ≥ 4`: the lift `P = x·Q_{n-1} + c₀`
  · rcases (show n = 8 ∨ n ≠ 8 from by omega) with rfl | h8
    -- `n = 8`: lift the direct septic
    · have h2 : IsUnit (2 : R') := isUnit_two_of_cast hadm (by omega)
      set x8 : Fin 8 → MvPolynomial (Fin 8) R' := MvPolynomial.X with hx8
      obtain ⟨hm, hd⟩ := septic_good (x8 ⟨0, by omega⟩) (x8 ⟨1, by omega⟩)
        (x8 ⟨2, by omega⟩) (x8 ⟨3, by omega⟩) (x8 ⟨4, by omega⟩)
        (x8 ⟨5, by omega⟩) (x8 ⟨6, by omega⟩)
      refine even_lift_bijective (by omega) _ hm (by rw [hd]) ?_
      intro V hV i hi
      obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ :=
        septic_decodable_of_coeff_mem _ _ _ _ _ _ _ h2 (fun j _ => hV j)
      obtain ⟨iv, hiv⟩ := i
      have hi7 : iv < 7 := hi
      rcases (show iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 ∨ iv = 4 ∨ iv = 5 ∨ iv = 6
          from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact p0
      · exact p1
      · exact p2
      · exact p3
      · exact p4
      · exact p5
      · exact p6
    -- `n ≠ 8`: lift the odd master family
    · obtain ⟨T₁, T₂, H₂, H₄, G, hcp, -, -, -, hdec, -⟩ :=
        odd_realizable_pairs' (R := R') (A := MvPolynomial (Fin n) R') (n - 1)
          (by omega) (by omega) (by omega)
          (fun i h1 h2' => hadm i h1 (by omega))
          (fun t => if h : t < n - 1 then MvPolynomial.X (⟨t, by omega⟩ : Fin n)
            else 0)
      obtain ⟨hQm, hQd⟩ := combined_good_of_monic hcp.monic₁ hcp.natDegree₁
        hcp.monic₂ hcp.natDegree₂
      refine even_lift_bijective (by omega) _ hQm (by rw [hQd]; omega) ?_
      intro V hV i hi
      have hdec' := hdec ((⊥ : Subalgebra R' (MvPolynomial (Fin n) R')) ⊔ V)
        (fun j => (le_sup_right : V ≤ _) (hV j))
      have h := hdec'.1 i.1 (by omega)
      rw [dif_pos hi] at h
      exact (sup_le bot_le le_rfl : (⊥ : Subalgebra R' (MvPolynomial (Fin n) R'))
        ⊔ V ≤ V) h

omit [IsNoetherianRing R'] in
/-- **The free joint-realization certificate**: over the free coordinate algebra, one
fixed base-ring program of `(n-1)/2` multiplications realizes the constructed pair
and both recorded powers at the coordinate environment — the canonical fixed-syntax
witness the uniform family theorem specializes. -/
theorem odd_realizable_pairs_free (hodd : n % 2 = 1) (hn3 : 3 ≤ n) (hn7 : n ≠ 7)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R')) :
    ∃ (T₁ T₂ H₂ H₄ : (MvPolynomial (Fin n) R')[X]) (G : Finset ℕ)
      (prog : Cost.JointPairProgram R' ((n - 1) / 2)),
      CompatiblePair (⊥ : Subalgebra R' (MvPolynomial (Fin n) R')) T₁ T₂ (n - 1) G ∧
      H₂.Monic ∧ H₂.natDegree = 2 ∧
      (5 ≤ n → H₄.Monic ∧ H₄.natDegree = 4) ∧
      (∀ V : Subalgebra R' (MvPolynomial (Fin n) R'),
        (∀ j, (combined T₁ T₂).coeff j ∈ V) →
        (∀ t, t < n → Cost.freeParameterEnv R' n t ∈ V) ∧
        (∀ j, H₂.coeff j ∈ V) ∧ (5 ≤ n → ∀ j, H₄.coeff j ∈ V)) ∧
      prog.RealizesAt (Cost.freeParameterEnv R' n) T₁ T₂ H₂ H₄ ∧
      prog.HeightBounded (2 * Nat.clog 2 n + 3) := by
  obtain ⟨T₁, T₂, H₂, H₄, G, hcp, h2m, h2d, h4g, hdec, prog, hpr, hh⟩ :=
    odd_realizable_pairs' (R := R') (A := MvPolynomial (Fin n) R') n hodd hn3 hn7
      hadm (Cost.freeParameterEnv R' n)
  exact ⟨T₁, T₂, H₂, H₄, G, prog, hcp, h2m, h2d, h4g, hdec, hpr, hh⟩

omit [IsNoetherianRing R'] in
/-- **The uniform joint family** (`thm:odd-realizable-pairs`, semantic-cost form):
the same fixed program computes the specialized pair and powers for every key vector
over every `R'`-algebra `B`. -/
theorem odd_realizable_pairs_uniform_family {B : Type*} [CommRing B] [Algebra R' B]
    (hodd : n % 2 = 1) (hn3 : 3 ≤ n) (hn7 : n ≠ 7)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R')) :
    ∃ (T₁ T₂ H₂ H₄ : (MvPolynomial (Fin n) R')[X])
      (prog : Cost.JointPairProgram R' ((n - 1) / 2)),
      prog.RealizesFiniteFamily
        (fun key : Fin n → B =>
          Polynomial.mapAlgHom (MvPolynomial.aeval (R := R') key) T₁)
        (fun key : Fin n → B =>
          Polynomial.mapAlgHom (MvPolynomial.aeval (R := R') key) T₂)
        (fun key : Fin n → B =>
          Polynomial.mapAlgHom (MvPolynomial.aeval (R := R') key) H₂)
        (fun key : Fin n → B =>
          Polynomial.mapAlgHom (MvPolynomial.aeval (R := R') key) H₄) := by
  obtain ⟨T₁, T₂, H₂, H₄, G, prog, -, -, -, -, -, hpr, -⟩ :=
    odd_realizable_pairs_free (R' := R') (n := n) hodd hn3 hn7 hadm
  exact ⟨T₁, T₂, H₂, H₄, prog,
    Cost.JointPairProgram.realizesFiniteFamily_of_free prog T₁ T₂ H₂ H₄ hpr⟩

end Coverage

end FastPoly
