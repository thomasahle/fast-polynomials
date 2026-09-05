import FastPoly.Main
import FastPoly.Cost.Additions.Realization

/-!
# Decoder and optimized additions on one odd-degree family

This fresh capstone mirrors the master induction while carrying the addition-certified
literal program in the same existential witness.  It exists to close the only semantic
bridge not expressed by the original theorem.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]

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

theorem decoded_addition_odd_realizable_pairs : ∀ n : ℕ, n % 2 = 1 → 3 ≤ n → n ≠ 7 →
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
        prog.HeightBounded (2 * Nat.clog 2 n + 3)) ∧
      (∃ additions : ℕ, Nonempty
        (Cost.AdditionJointPairRealization R θ T₁ T₂ H₂ H₄ n additions)) := by
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
        ((Cost.Three.multDepth_circuit_le (R := R)).2.2.2.trans (by omega)),
      ⟨3, ⟨⟨Cost.AdditionJointPairProgram.three R,
        Cost.AdditionJointPairProgram.three_realizesAt θ⟩⟩⟩⟩
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
          (Cost.Crown.multDepth_circuit_le (R := R) k hk1).2.2.2,
      ⟨Cost.tAdd (2 * k) 1 + 2,
        ⟨⟨Cost.AdditionJointPairProgram.crown R k hk1,
          Cost.AdditionJointPairProgram.crown_realizesAt θ k hk1⟩⟩⟩⟩
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
        (Cost.Fifteen.multDepth_circuit_le (R := R)).2.2.2,
      ⟨23, ⟨⟨Cost.AdditionJointPairProgram.fifteen R,
        Cost.AdditionJointPairProgram.fifteen_realizesAt θ⟩⟩⟩⟩
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
        (Cost.TwentySeven.multDepth_circuit_le (R := R)).2.2.2,
      ⟨43, ⟨⟨Cost.AdditionJointPairProgram.twentySeven R,
        Cost.AdditionJointPairProgram.twentySeven_realizesAt θ⟩⟩⟩⟩
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
        (Cost.ThirtyOne.multDepth_circuit_le (R := R)).2.2.2,
      ⟨43, ⟨⟨Cost.AdditionJointPairProgram.thirtyOne R,
        Cost.AdditionJointPairProgram.thirtyOne_realizesAt θ⟩⟩⟩⟩
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
        hreal, additionsS, ⟨sourceAdd⟩⟩ :=
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
    obtain ⟨additions₃, ⟨third⟩⟩ : ∃ additions₃, Nonempty
        (Cost.AdditionRealizedLowGadget (R := R) H₂s
          (Cost.OddGadget.q4BundleOutput H₂s
            (fun i => θ (2 * k + 1 + i)) k 1)
          (fun i => θ (6 * k + 2 + i)) (2 * k - 1) additions₃) := by
      rcases eq_or_lt_of_le hk1 with rfl | hk2
      · exact ⟨0, ⟨Cost.AdditionRealizedLowGadget.scalar (R := R) H₂s _ _⟩⟩
      · obtain ⟨g, ⟨gadget⟩⟩ := Cost.AdditionRealizedOddGadget.dispatch (R := R)
          (2 * k - 1) (by omega) (fun i h1 h2' => hadm i h1 (by omega))
          hH2sm hH2sd hH4bm' hH4bd' (fun t => θ (6 * k + 2 + t))
        exact ⟨g, ⟨Cost.AdditionRealizedLowGadget.ofGadget (by omega) gadget⟩⟩
    set S₃ := third.Q with hS₃def
    have hS₃d := third.degree_le
    have hS₃dec : ∀ V' : Subalgebra R A, (∀ j, H₂s.coeff j ∈ V') →
        (∀ j, (crownH4 (H₂s.coeff 1) (H₂s.coeff 0 + θ (2 * k + 2)) (θ (2 * k + 3))
          (θ (2 * k + 4))).coeff j ∈ V') →
        (∀ j, S₃.coeff j ∈ V') → ∀ t, t < 2 * k - 1 → θ (6 * k + 2 + t) ∈ V' :=
      fun V' hh2 hh4 hq => third.recover V' hh2
        (fun j => by rw [hbundle1]; exact hh4 j) hq
    have hS₃lead : S₃.coeff (2 * k - 1) ∈ (⊥ : Subalgebra R A) :=
      third.leading_mem _
    have hcompat := eightk3_compatible (K := (⊥ : Subalgebra R A))
      (a := θ (8 * k + 1)) (α₀ := θ (8 * k + 2)) hk1 h2 hsmall hS₂m hS₂d
      hS₃d hS₃lead
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
      hH2sm, hH2sd, fun _ => ⟨hH4bm, hH4bd⟩, ?_, ?_,
      ⟨additionsS + (Cost.tAdd (2 * k) 1 + 3) + additions₃ + 7, ⟨by
        simpa only [hS₃def, hbundle0, hbundle1] using
          (Cost.AdditionJointPairRealization.eightThree hk1 hk3 sourceAdd
            hH2sm hH2sd (2 * k + 1) (6 * k + 2) (8 * k + 1)
            (8 * k + 2) third)⟩⟩⟩
    swap
    · let secondBundle := Cost.OddGadget.Q4Optimized.realized (R := R) (H₄ := H₄s)
        hH2sm hH2sd (fun i => θ (2 * k + 1 + i)) k hk1
      let secondR := Cost.OddGadget.BundleRealization.relative source secondBundle
      let thirdR := Cost.OddGadget.Realization.afterBundle source secondR
        third.realization
      have hsecond0 : secondR.circuit.multDepth
          (Sum.elim (fun _ : Cost.PolyInput => 0)
            (source.circuit.multDepth (fun _ => 0))) 0
          ≤ 2 * Nat.clog 2 (2 * (2 * k) + 1) + 1 := by
        exact (Cost.OddGadget.multDepth_relativeCircuit_le
          secondBundle.circuit (2 * k + 1)
          (source.circuit.multDepth (fun _ => 0)) hpd2 hpd3 0).trans
          (Cost.OddGadget.Q4Optimized.multDepth_circuit_le (R := R) k hk1).1
      have hsecond1 : secondR.circuit.multDepth
          (Sum.elim (fun _ : Cost.PolyInput => 0)
            (source.circuit.multDepth (fun _ => 0))) 1 ≤ 2 := by
        exact (Cost.OddGadget.multDepth_relativeCircuit_le
          secondBundle.circuit (2 * k + 1)
          (source.circuit.multDepth (fun _ => 0)) hpd2 hpd3 1).trans
          (Cost.OddGadget.Q4Optimized.multDepth_circuit_le (R := R) k hk1).2
      have hthird : thirdR.circuit.multDepth
          (Sum.elim (Sum.elim (fun _ : Cost.PolyInput => 0)
            (source.circuit.multDepth (fun _ => 0)))
            (secondR.circuit.multDepth
              (Sum.elim (fun _ : Cost.PolyInput => 0)
                (source.circuit.multDepth (fun _ => 0))))) 0
          ≤ 2 * Nat.clog 2 (2 * k - 1) + 1 := by
        have h := (Cost.OddGadget.multDepth_afterBundleCircuit_le
          third.realization.circuit (6 * k + 2)
          (source.circuit.multDepth (fun _ => 0))
          (secondR.circuit.multDepth
            (Sum.elim (fun _ : Cost.PolyInput => 0)
              (source.circuit.multDepth (fun _ => 0)))) hpd2 hsecond1).trans
          third.realization.depth_le
        rwa [show 2 * ((2 * k - 1) / 2) + 1 = 2 * k - 1 from by omega] at h
      obtain ⟨hd0, hd1, hd2, hd3⟩ :=
        Cost.Outer.multDepth_eightThreeSequentialCircuit_le source secondR thirdR
          (8 * k + 1) (8 * k + 2) (2 * Nat.clog 2 (2 * k + 1) + 3)
          (2 * Nat.clog 2 (2 * (2 * k) + 1) + 1)
          (2 * Nat.clog 2 (2 * k - 1) + 1)
          hpd0 hpd1 hpd2 hsecond0 hsecond1 hthird
      have hbound := eightThree_hbound k
      obtain ⟨prog, hpr, hh⟩ := joint_exists
        (Cost.Outer.eightThreeSequentialRealized source secondR thirdR
          (8 * k + 1) (8 * k + 2))
        (hbound _ hd0) (hbound _ hd1) hd2 hd3
      exact (show k + 2 * k + (2 * k - 1) / 2 + 2 = (8 * k + 3 - 1) / 2
        from by omega) ▸
        ⟨prog, ⟨by
            simpa only [hi1, hi4, hi2, hi3, hi0, hif, hS₃def] using hpr.1,
          by simpa only [hi1, hi4, hi2, hi3, hi0, hif] using hpr.2.1,
          hpr.2.2.1,
          by simpa only [hi1, hi2, hi3] using hpr.2.2.2⟩, hh⟩
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
      (K := (⊥ : Subalgebra R A)) hk1 h2 hsmall hS₂m hS₂d hS₃d hS₃lead
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
        hreal, additionsS, ⟨sourceAdd⟩⟩ :=
      ih (2 * k + 1) (by omega) (by omega) (by omega) (by omega)
        (fun i h1 h2' => hadm i h1 (by omega))
        θ
    rw [show 2 * k + 1 - 1 = 2 * k from by omega] at hsmall
    obtain ⟨hH4sm, hH4sd⟩ := hH4sg (by omega)
    obtain ⟨progS, hprogS, hpd0, hpd1, hpd2, hpd3⟩ := hreal
    let source : Cost.JointPairRealization (R := R) θ T₁' T₂' H₂s H₄s k :=
      sourceRealization progS hprogS (by omega)
    obtain ⟨additions₂, ⟨g₂add⟩⟩ := Cost.AdditionRealizedOddGadget.dispatch
      (R := R) (2 * k + 1) (by omega)
      (fun i h1 h2' => hadm i h1 (by omega)) hH2sm hH2sd hH4sm hH4sd
      (fun t => θ (2 * k + 1 + t))
    obtain ⟨additions₃, ⟨g₃add⟩⟩ := Cost.AdditionRealizedOddGadget.dispatch
      (R := R) (4 * k + 3) (by omega)
      (fun i h1 h2' => hadm i h1 (by omega)) hH2sm hH2sd hH4sm hH4sd
      (fun t => θ (4 * k + 2 + t))
    let g₂ := g₂add.toRealized
    let g₃ := g₃add.toRealized
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
      hH2sm, hH2sd, fun _ => ⟨hH4sm, hH4sd⟩, ?_, ?_,
      ⟨additionsS + additions₂ + additions₃ + 6,
        ⟨Cost.AdditionJointPairRealization.eightSeven hk2 hk3 sourceAdd
          (2 * k + 1) (4 * k + 2) (8 * k + 5) (8 * k + 6) g₂add g₃add⟩⟩⟩
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

end FastPoly
