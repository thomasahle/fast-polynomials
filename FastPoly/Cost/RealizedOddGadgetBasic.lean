import FastPoly.Cost.OddGadgetBarQ15
import FastPoly.Cost.RealizedOddGadget
import FastPoly.Section6.GadgetDecoders

/-!
# Realized odd-gadget branches with public algebraic decoders

These constructors join the existing explicit decoder of each basic or barred
auxiliary family to its matching semantic circuit.  The `8k+3` known-powers constructor
is deliberately kept in `RealizedOddGadgetKnown.lean`, where it uses the public
`knownGadget` decoder exported by `Section6.Dispatch`.
-/

namespace FastPoly.Cost.RealizedOddGadget

open Polynomial Algebra

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

/-- The affine degree-one gadget. -/
noncomputable def one (H₂ H₄ : A[X]) (θ : ℕ → A) :
    RealizedOddGadget (R := R) H₂ H₄ θ 1 where
  Q := X + C (θ 0)
  monic := monic_X_add_C _
  natDegree := natDegree_X_add_C _
  recover := by
    intro V _ _ hQ t ht
    have h0 := hQ 0
    rw [coeff_add, coeff_X_zero, coeff_C, if_pos rfl, zero_add] at h0
    rwa [show t = 0 from by omega]
  realization := by
    simpa using OddGadget.oneRealized (R := R) H₂ H₄ θ

/-- The degree-three Mersenne gadget. -/
noncomputable def three {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (θ : ℕ → A) :
    RealizedOddGadget (R := R) H₂ H₄ θ 3 := by
  let Hp := OddGadget.suppliedPowers H₂ H₄
  have htw : ∀ i, 1 ≤ i → i < 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i := by
    intro i h1 hi
    rw [show i = 1 from by omega]
    change H₂.Monic ∧ H₂.natDegree = 2 ^ 1
    exact ⟨hH₂m, by rw [hH₂d]; norm_num⟩
  obtain ⟨hQm, hQd⟩ := FastPoly.peel_monic Hp 2 htw (by omega) θ
  exact
    { Q := FastPoly.peel Hp 2 θ
      monic := hQm
      natDegree := by simpa using hQd
      recover := by
        intro V hH₂V _ hQV t ht
        refine FastPoly.peel_correct (K := V) Hp 2 ?_ (by omega) θ V le_rfl hQV t
          (by omega)
        intro i h1 hi
        rw [show i = 1 from by omega]
        change H₂.Monic ∧ H₂.natDegree = 2 ^ 1 ∧ (∀ j, H₂.coeff j ∈ V)
        exact ⟨hH₂m, by rw [hH₂d]; norm_num, hH₂V⟩
      realization := by
        simpa only [Hp] using OddGadget.threeRealized (R := R) H₂ H₄ θ }

/-- The degree-seven Mersenne gadget. -/
noncomputable def seven {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (hH₄m : H₄.Monic)
    (hH₄d : H₄.natDegree = 4) (θ : ℕ → A) :
    RealizedOddGadget (R := R) H₂ H₄ θ 7 := by
  let Hp := OddGadget.suppliedPowers H₂ H₄
  have htw : ∀ i, 1 ≤ i → i < 3 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i := by
    intro i h1 hi
    rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
    · change H₂.Monic ∧ H₂.natDegree = 2 ^ 1
      exact ⟨hH₂m, by rw [hH₂d]; norm_num⟩
    · change H₄.Monic ∧ H₄.natDegree = 2 ^ 2
      exact ⟨hH₄m, by rw [hH₄d]; norm_num⟩
  obtain ⟨hQm, hQd⟩ := FastPoly.peel_monic Hp 3 htw (by omega) θ
  exact
    { Q := FastPoly.peel Hp 3 θ
      monic := hQm
      natDegree := by simpa using hQd
      recover := by
        intro V hH₂V hH₄V hQV t ht
        refine FastPoly.peel_correct (K := V) Hp 3 ?_ (by omega) θ V le_rfl hQV t
          (by omega)
        intro i h1 hi
        rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
        · change H₂.Monic ∧ H₂.natDegree = 2 ^ 1 ∧ (∀ j, H₂.coeff j ∈ V)
          exact ⟨hH₂m, by rw [hH₂d]; norm_num, hH₂V⟩
        · change H₄.Monic ∧ H₄.natDegree = 2 ^ 2 ∧ (∀ j, H₄.coeff j ∈ V)
          exact ⟨hH₄m, by rw [hH₄d]; norm_num, hH₄V⟩
      realization := by
        simpa only [Hp] using OddGadget.sevenRealized (R := R) H₂ H₄ θ }

/-- The realized `Q_{4k+1}` crown gadget. -/
noncomputable def q4 {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (k : ℕ) (hk : 1 ≤ k)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k → IsUnit (((n : ℕ) : ℤ) : R))
    (h2 : IsUnit (2 : R)) (θ : ℕ → A) :
    RealizedOddGadget (R := R) H₂ H₄ θ (4 * k + 1) := by
  obtain ⟨hQm, hQd⟩ := FastPoly.q4k1_good (α := fun t => θ (5 + t)) hk
    (θ 1) (θ 4) (θ 2) (θ 3) (θ 0)
  exact
    { Q := FastPoly.q4k1 H₂ (θ 1) (θ 4) (θ 2) (θ 3) (θ 0) k
        (fun t => θ (5 + t))
      monic := hQm
      natDegree := hQd
      recover := by
        intro V hH₂V _ hQV t ht
        obtain ⟨⟨hβ, hγ, ha, he, hρ⟩, -, hα⟩ :=
          FastPoly.q4k1_decodable (α := fun u => θ (5 + u)) hk hadm h2
            hH₂m hH₂d (θ 1) (θ 4) (θ 2) (θ 3) (θ 0) V hH₂V hQV
        rcases Nat.lt_or_ge t 5 with ht5 | h5
        · rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 from by omega)
            with rfl | rfl | rfl | rfl | rfl
          · exact hβ
          · exact hγ
          · exact ha
          · exact he
          · exact hρ
        · have h := hα (t - 5) (by omega)
          rwa [show 5 + (t - 5) = t from by omega] at h
      realization := by
        simpa only [show (4 * k + 1) / 2 = 2 * k by omega] using
          OddGadget.q4Realized (R := R) (H₄ := H₄) hH₂m hH₂d θ k hk }

/-- The optimized degree-fifteen barred gadget. -/
noncomputable def barredOne {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (hH₄m : H₄.Monic)
    (hH₄d : H₄.natDegree = 4) (θ : ℕ → A) :
    RealizedOddGadget (R := R) H₂ H₄ θ 15 := by
  let Q := FastPoly.BarQ15.barQ15 (H₂.coeff 0) (H₂.coeff 1)
    (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) θ
  obtain ⟨hQm, hQd⟩ := FastPoly.BarQ15.barQ15_good (A := A)
    (H₂.coeff 0) (H₂.coeff 1)
    (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) θ
  exact
    { Q := Q
      monic := hQm
      natDegree := hQd
      recover := by
        intro V hH₂V hH₄V hQV
        have hraw := FastPoly.BarQ15.barQ15_recover (R := R) V
          (H₂.coeff 0) (H₂.coeff 1)
          (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) θ
          (hH₂V 0) (hH₂V 1) (hH₄V 0) (hH₄V 1) (hH₄V 2) (hH₄V 3)
        have hcollapse : FastPoly.BarQ15.barQ15Alg V
            (H₂.coeff 0) (H₂.coeff 1)
            (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) θ ≤ V := by
          rw [FastPoly.BarQ15.barQ15Alg]
          exact sup_le le_rfl (adjoin_le (by
            rintro _ ⟨j, rfl⟩
            exact hQV j))
        exact fun t ht => hcollapse (hraw t ht)
      realization := by
        simpa only [Q] using OddGadget.barredOneRealized (R := R)
          hH₂m hH₂d hH₄m hH₄d θ }

/-- The uniform barred gadget for `k ≥ 2`. -/
noncomputable def barredGeneral {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (hH₄m : H₄.Monic)
    (hH₄d : H₄.natDegree = 4) (k : ℕ) (hk : 2 ≤ k)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ k → IsUnit (((n : ℕ) : ℤ) : R))
    (θ : ℕ → A) :
    RealizedOddGadget (R := R) H₂ H₄ θ (8 * k + 7) := by
  obtain ⟨hQm, hQd⟩ := FastPoly.BarQGeneral.gadget_good
    hH₂m hH₂d hH₄m hH₄d k (by omega) θ
  exact
    { Q := FastPoly.BarQGeneral.gadget H₂ H₄ k θ
      monic := hQm
      natDegree := hQd
      recover := by
        intro V hH₂V hH₄V hQV
        exact FastPoly.BarQGeneral.gadget_recover hH₂m hH₂d hH₄m hH₄d
          k hk θ hadm hH₂V hH₄V hQV
      realization := by
        simpa only [show (8 * k + 7) / 2 = 4 * k + 3 by omega] using
          OddGadget.barredRealized (R := R) H₂ H₄ θ k (by omega) }

end FastPoly.Cost.RealizedOddGadget
