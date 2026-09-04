import FastPoly.Cost.RealizedOddGadgetOptimized

/-!
# Addition-certified base odd gadgets and canonical dispatch

The three finite base gadgets use the literal circuits already paired with their
decoders.  Their addition counts complete `AdditionRealizedOddGadget` at degrees
one, three, and seven.  The canonical dispatcher then selects one certified realized
gadget in every positive odd degree, using the same residue split and admissibility
hypotheses as `RealizedOddGadget.dispatch`.
-/

namespace FastPoly.Cost

open Polynomial Algebra

universe u v

namespace OddGadget.BaseAdditions

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

omit [CommRing R] in
/-- Literal addition count of the affine degree-one circuit. -/
@[simp] theorem oneCircuit_additions :
    (OddGadget.oneCircuit (R := R)).gates.additions = 1 := by
  rfl

/-- Literal addition count of the degree-three peeled circuit. -/
@[simp] theorem threeCircuit_additions :
    (OddGadget.threeCircuit (R := R)).gates.additions = 3 := by
  rw [OddGadget.threeCircuit,
    gates_peelCircuit_additions_eq_mersAdd (R := R) 2 (by omega),
    mersAdd_of_two_le 2 (by omega)]
  norm_num

/-- Literal addition count of the degree-seven peeled circuit. -/
@[simp] theorem sevenCircuit_additions :
    (OddGadget.sevenCircuit (R := R)).gates.additions = 8 := by
  rw [OddGadget.sevenCircuit,
    gates_peelCircuit_additions_eq_mersAdd (R := R) 3 (by omega),
    mersAdd_of_two_le 3 (by omega)]
  norm_num

/-- Decoder-facing realization of the affine base at its half-degree count. -/
def oneDecoderRealized (H₂ H₄ : A[X]) (theta : ℕ → A) :
    OddGadget.Realization (R := R) H₂ H₄ theta (X + C (theta 0)) (1 / 2) where
  circuit := OddGadget.oneCircuit
  eval_eq := OddGadget.eval_oneCircuit H₂ H₄ theta
  multiplication_count := by
    simpa only using OddGadget.oneCircuit_multiplications (R := R)
  depth_le := by
    simpa only [show 1 / 2 = 0 by omega] using
      (OddGadget.oneRealized (R := R) H₂ H₄ theta).depth_le

/-- The affine helper stores `oneCircuit` literally. -/
@[simp] theorem oneDecoderRealized_circuit (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (oneDecoderRealized (R := R) H₂ H₄ theta).circuit = OddGadget.oneCircuit := by
  rfl

/-- Decoder-facing realization of the degree-three peeled base. -/
def threeDecoderRealized (H₂ H₄ : A[X]) (theta : ℕ → A) :
    OddGadget.Realization (R := R) H₂ H₄ theta
      (FastPoly.peel (OddGadget.suppliedPowers H₂ H₄) 2 theta) (3 / 2) where
  circuit := OddGadget.threeCircuit
  eval_eq := OddGadget.eval_threeCircuit H₂ H₄ theta
  multiplication_count := by
    simpa only [show 3 / 2 = 1 by omega] using
      OddGadget.threeCircuit_multiplications (R := R)
  depth_le := by
    simpa only [show 3 / 2 = 1 by omega] using
      (OddGadget.threeRealized (R := R) H₂ H₄ theta).depth_le

/-- The degree-three helper stores `threeCircuit` literally. -/
@[simp] theorem threeDecoderRealized_circuit (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (threeDecoderRealized (R := R) H₂ H₄ theta).circuit =
      OddGadget.threeCircuit := by
  rfl

/-- Decoder-facing realization of the degree-seven peeled base. -/
def sevenDecoderRealized (H₂ H₄ : A[X]) (theta : ℕ → A) :
    OddGadget.Realization (R := R) H₂ H₄ theta
      (FastPoly.peel (OddGadget.suppliedPowers H₂ H₄) 3 theta) (7 / 2) where
  circuit := OddGadget.sevenCircuit
  eval_eq := OddGadget.eval_sevenCircuit H₂ H₄ theta
  multiplication_count := by
    simpa only [show 7 / 2 = 3 by omega] using
      OddGadget.sevenCircuit_multiplications (R := R)
  depth_le := by
    simpa only [show 7 / 2 = 3 by omega] using
      (OddGadget.sevenRealized (R := R) H₂ H₄ theta).depth_le

/-- The degree-seven helper stores `sevenCircuit` literally. -/
@[simp] theorem sevenDecoderRealized_circuit (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (sevenDecoderRealized (R := R) H₂ H₄ theta).circuit =
      OddGadget.sevenCircuit := by
  rfl

end OddGadget.BaseAdditions

namespace AdditionRealizedOddGadget

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

/-- Addition-certified affine degree-one gadget. -/
noncomputable def one (H₂ H₄ : A[X]) (theta : ℕ → A) :
    AdditionRealizedOddGadget (R := R) H₂ H₄ theta 1 1 where
  Q := X + C (theta 0)
  monic := monic_X_add_C _
  natDegree := natDegree_X_add_C _
  recover := by
    intro V _ _ hQ t ht
    have h0 := hQ 0
    rw [coeff_add, coeff_X_zero, coeff_C, if_pos rfl, zero_add] at h0
    rwa [show t = 0 from by omega]
  realization := OddGadget.BaseAdditions.oneDecoderRealized H₂ H₄ theta
  addition_count := by
    rw [OddGadget.BaseAdditions.oneDecoderRealized_circuit]
    exact OddGadget.BaseAdditions.oneCircuit_additions
  ledger := GadgetAddCost.one

/-- Addition-certified degree-three peeled gadget. -/
noncomputable def three {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (theta : ℕ → A) :
    AdditionRealizedOddGadget (R := R) H₂ H₄ theta 3 3 := by
  let Hp := OddGadget.suppliedPowers H₂ H₄
  have htw : ∀ i, 1 ≤ i → i < 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i := by
    intro i h1 hi
    rw [show i = 1 from by omega]
    change H₂.Monic ∧ H₂.natDegree = 2 ^ 1
    exact ⟨hH₂m, by rw [hH₂d]; norm_num⟩
  obtain ⟨hQm, hQd⟩ := FastPoly.peel_monic Hp 2 htw (by omega) theta
  exact
    { Q := FastPoly.peel Hp 2 theta
      monic := hQm
      natDegree := by simpa using hQd
      recover := by
        intro V hH₂V _ hQV t ht
        refine FastPoly.peel_correct (K := V) Hp 2 ?_ (by omega) theta V le_rfl
          hQV t (by omega)
        intro i h1 hi
        rw [show i = 1 from by omega]
        change H₂.Monic ∧ H₂.natDegree = 2 ^ 1 ∧ (∀ j, H₂.coeff j ∈ V)
        exact ⟨hH₂m, by rw [hH₂d]; norm_num, hH₂V⟩
      realization := by
        simpa only [Hp] using OddGadget.BaseAdditions.threeDecoderRealized
          (R := R) H₂ H₄ theta
      addition_count := by
        simp only [id_eq]
        rw [OddGadget.BaseAdditions.threeDecoderRealized_circuit]
        exact OddGadget.BaseAdditions.threeCircuit_additions
      ledger := GadgetAddCost.three }

/-- Addition-certified degree-seven peeled gadget. -/
noncomputable def seven {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (hH₄m : H₄.Monic)
    (hH₄d : H₄.natDegree = 4) (theta : ℕ → A) :
    AdditionRealizedOddGadget (R := R) H₂ H₄ theta 7 8 := by
  let Hp := OddGadget.suppliedPowers H₂ H₄
  have htw : ∀ i, 1 ≤ i → i < 3 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i := by
    intro i h1 hi
    rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
    · change H₂.Monic ∧ H₂.natDegree = 2 ^ 1
      exact ⟨hH₂m, by rw [hH₂d]; norm_num⟩
    · change H₄.Monic ∧ H₄.natDegree = 2 ^ 2
      exact ⟨hH₄m, by rw [hH₄d]; norm_num⟩
  obtain ⟨hQm, hQd⟩ := FastPoly.peel_monic Hp 3 htw (by omega) theta
  exact
    { Q := FastPoly.peel Hp 3 theta
      monic := hQm
      natDegree := by simpa using hQd
      recover := by
        intro V hH₂V hH₄V hQV t ht
        refine FastPoly.peel_correct (K := V) Hp 3 ?_ (by omega) theta V le_rfl
          hQV t (by omega)
        intro i h1 hi
        rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
        · change H₂.Monic ∧ H₂.natDegree = 2 ^ 1 ∧ (∀ j, H₂.coeff j ∈ V)
          exact ⟨hH₂m, by rw [hH₂d]; norm_num, hH₂V⟩
        · change H₄.Monic ∧ H₄.natDegree = 2 ^ 2 ∧ (∀ j, H₄.coeff j ∈ V)
          exact ⟨hH₄m, by rw [hH₄d]; norm_num, hH₄V⟩
      realization := by
        simpa only [Hp] using OddGadget.BaseAdditions.sevenDecoderRealized
          (R := R) H₂ H₄ theta
      addition_count := by
        simp only [id_eq]
        rw [OddGadget.BaseAdditions.sevenDecoderRealized_circuit]
        exact OddGadget.BaseAdditions.sevenCircuit_additions
      ledger := GadgetAddCost.seven }

/-- Every positive odd degree has a canonical decoder-facing realization whose
selected addition ledger is proved for its literal circuit. -/
theorem dispatch (d : ℕ) (hd : d % 2 = 1)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ d → IsUnit (((n : ℕ) : ℤ) : R))
    {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) (theta : ℕ → A) :
    ∃ additions, Nonempty
      (AdditionRealizedOddGadget (R := R) H₂ H₄ theta d additions) := by
  rcases (show d = 1 ∨ d = 3 ∨ d = 7 ∨ (d % 4 = 1 ∧ 5 ≤ d) ∨
      (d % 8 = 3 ∧ 11 ≤ d) ∨ (d % 8 = 7 ∧ 15 ≤ d) from by omega)
    with rfl | rfl | rfl | ⟨h4, h5⟩ | ⟨h8, h11⟩ | ⟨h8, h15⟩
  · exact ⟨1, ⟨one H₂ H₄ theta⟩⟩
  · exact ⟨3, ⟨three hH₂m hH₂d theta⟩⟩
  · exact ⟨8, ⟨seven hH₂m hH₂d hH₄m hH₄d theta⟩⟩
  · obtain ⟨k, hk, rfl⟩ : ∃ k, 1 ≤ k ∧ d = 4 * k + 1 :=
      ⟨d / 4, by omega⟩
    have hadm' : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k →
        IsUnit (((n : ℕ) : ℤ) : R) :=
      fun n hn hnk => hadm n hn (by omega)
    have h2 : IsUnit (2 : R) := FastPoly.isUnit_two_of_cast hadm (by omega)
    exact ⟨tAdd (2 * k) 1 + 3,
      ⟨q4 hH₂m hH₂d k hk hadm' h2 theta⟩⟩
  · obtain ⟨k, hk, rfl⟩ : ∃ k, 1 ≤ k ∧ d = 8 * k + 3 :=
      ⟨d / 8, by omega⟩
    exact ⟨tAdd (2 * k) 2 + 9,
      ⟨known hH₂m hH₂d hH₄m hH₄d k hk
        (fun n hn hnk => hadm n hn (by omega)) theta⟩⟩
  · obtain ⟨k, hk, rfl⟩ : ∃ k, 1 ≤ k ∧ d = 8 * k + 7 :=
      ⟨d / 8, by omega⟩
    rcases eq_or_lt_of_le hk with rfl | hk2
    · exact ⟨tAdd 1 3 + 19,
        ⟨barredOne hH₂m hH₂d hH₄m hH₄d theta⟩⟩
    · exact ⟨tAdd k 3 + 19,
        ⟨barredGeneral hH₂m hH₂d hH₄m hH₄d k hk2
          (fun n hn hnk => hadm n hn (by omega)) theta⟩⟩

end AdditionRealizedOddGadget

end FastPoly.Cost
