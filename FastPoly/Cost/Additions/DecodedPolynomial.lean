import FastPoly.Cost.Additions.Decoded
import FastPoly.HeightFinal

/-!
# Decoder, height, and additions on one complete-polynomial family

The older capstones separately exhibited a decoded height-bounded program and an
addition-certified program.  This file strengthens that packaging: both programs
compute the very same polynomial `P`.  Their syntax may differ, since the paper
advertises two arrangements, but their semantic family no longer differs.
-/

namespace FastPoly

open Polynomial Algebra

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

/-- One monic decoded polynomial together with both advertised circuit arrangements.
The `heightProgram` and `additionRealization.program` are permitted to be different
syntax trees, but both have pointwise semantics exactly `P`. -/
structure DecodedAdditionPolynomial (R : Type u) [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (theta : ℕ → A) (degree : ℕ) where
  P : A[X]
  multiplications : ℕ
  additions : ℕ
  multiplication_le : multiplications ≤ degree / 2 + 1
  monic : P.Monic
  natDegree : P.natDegree = degree
  decode : ∀ V : Subalgebra R A, (∀ j, P.coeff j ∈ V) →
    ∀ t, t < degree → theta t ∈ V
  heightProgram : Cost.PolynomialProgram R multiplications
  heightRealizesAt : heightProgram.RealizesAt theta P
  heightBounded : heightProgram.HeightBounded
    (2 * Nat.clog 2 degree + 4 + (degree + 1) % 2)
  additionRealization : Cost.AdditionPolynomialRealization R theta P degree
    multiplications additions

namespace DecodedAdditionPolynomial

/-- Direct affine base, shared by the height and addition arrangements. -/
noncomputable def linear (theta : ℕ → A) :
    DecodedAdditionPolynomial R theta 1 where
  P := X + C (theta 0)
  multiplications := 0
  additions := 1
  multiplication_le := by omega
  monic := monic_X_add_C _
  natDegree := natDegree_X_add_C _
  decode := by
    intro V hV t ht
    have h := hV 0
    rw [coeff_add, coeff_X_zero, coeff_C, if_pos rfl, zero_add] at h
    have ht' : t = 0 := by omega
    rwa [ht']
  heightProgram := Cost.PolynomialProgram.linear
  heightRealizesAt := Cost.PolynomialProgram.linear_realizesAt theta
  heightBounded := (Cost.PolynomialProgram.heightBounded_of_count _).trans (by norm_num)
  additionRealization := Cost.AdditionPolynomialRealization.linear theta

/-- Direct quadratic base, shared by the height and addition arrangements. -/
noncomputable def quadratic (theta : ℕ → A) :
    DecodedAdditionPolynomial R theta 2 where
  P := X * (X + C (theta 1)) + C (theta 0)
  multiplications := 1
  additions := 2
  multiplication_le := by omega
  monic := by
    have hm : (X * (X + C (theta 1))).Monic := monic_X.mul (monic_X_add_C _)
    exact (monic_add_low (e := C (theta 0)) hm
      (Or.inr (by rw [natDegree_C, monic_X.natDegree_mul (monic_X_add_C _),
        natDegree_X, natDegree_X_add_C]; omega))).1
  natDegree := by
    have hm : (X * (X + C (theta 1))).Monic := monic_X.mul (monic_X_add_C _)
    have hd : (X * (X + C (theta 1))).natDegree = 2 := by
      rw [monic_X.natDegree_mul (monic_X_add_C _), natDegree_X, natDegree_X_add_C]
    exact (monic_add_low (e := C (theta 0)) hm
      (Or.inr (by rw [natDegree_C, hd]; omega))).2.trans hd
  decode := by
    intro V hV t ht
    obtain ⟨hQV, h0⟩ := evenLift_coeff_mem hV
    have h1 := hQV 0
    rw [coeff_add, coeff_X_zero, coeff_C, if_pos rfl, zero_add] at h1
    rcases (show t = 0 ∨ t = 1 from by omega) with rfl | rfl
    · exact h0
    · exact h1
  heightProgram := Cost.PolynomialProgram.quadratic
  heightRealizesAt := Cost.PolynomialProgram.quadratic_realizesAt theta
  heightBounded := (Cost.PolynomialProgram.heightBounded_of_count _).trans (by norm_num)
  additionRealization := Cost.AdditionPolynomialRealization.quadratic theta

/-- Direct septic base, shared by the height and addition arrangements. -/
noncomputable def septic (h2 : IsUnit (2 : R)) (theta : ℕ → A) :
    DecodedAdditionPolynomial R theta 7 where
  P := optimizedSeptic
    (theta 0) (theta 1) (theta 2) (theta 3) (theta 4) (theta 5) (theta 6)
  multiplications := 4
  additions := 10
  multiplication_le := by omega
  monic := (Cost.SepticProgram.good (R := R) theta).1
  natDegree := (Cost.SepticProgram.good (R := R) theta).2
  decode := by
    intro V hV t ht
    have hle : optimizedSepticObs (R := R) (theta 0) (theta 1) (theta 2)
        (theta 3) (theta 4) (theta 5) (theta 6) (⊥ : Subalgebra R A) ≤ V := by
      refine sup_le bot_le (Algebra.adjoin_le ?_)
      rintro x ⟨j, -, rfl⟩
      exact hV j
    obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ :=
      optimizedSeptic_decodable (R := R) (theta 0) (theta 1) (theta 2)
        (theta 3) (theta 4) (theta 5) (theta 6) (⊥ : Subalgebra R A) h2
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6
      from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hle p0
    · exact hle p1
    · exact hle p2
    · exact hle p3
    · exact hle p4
    · exact hle p5
    · exact hle p6
  heightProgram := Cost.SepticProgram.program
  heightRealizesAt := Cost.SepticProgram.realizesAt (R := R) theta
  heightBounded := (Cost.PolynomialProgram.heightBounded_of_count _).trans (by norm_num)
  additionRealization := Cost.AdditionPolynomialRealization.septic theta

/-- Complete a decoded, height-bounded, addition-certified odd pair. -/
noncomputable def ofOddPair (n : ℕ) (hodd : n % 2 = 1)
    (T₁ T₂ H₂ H₄ : A[X]) {G : Finset ℕ}
    (hcompat : CompatiblePair (⊥ : Subalgebra R A) T₁ T₂ (n - 1) G)
    (hdecode : ∀ V : Subalgebra R A, (∀ j, (combined T₁ T₂).coeff j ∈ V) →
      (∀ t, t < n → theta t ∈ V))
    (heightPair : Cost.JointPairProgram R ((n - 1) / 2))
    (heightRealizes : heightPair.RealizesAt theta T₁ T₂ H₂ H₄)
    (heightBound : heightPair.HeightBounded (2 * Nat.clog 2 n + 3))
    (additions : ℕ)
    (additionPair : Cost.AdditionJointPairRealization R theta T₁ T₂ H₂ H₄ n additions) :
    DecodedAdditionPolynomial R theta n where
  P := combined T₁ T₂
  multiplications := (n - 1) / 2 + 1
  additions := additions + 1
  multiplication_le := by omega
  monic := (combined_good_of_monic hcompat.monic₁ hcompat.natDegree₁
    hcompat.monic₂ hcompat.natDegree₂).1
  natDegree := by
    rw [(combined_good_of_monic hcompat.monic₁ hcompat.natDegree₁
      hcompat.monic₂ hcompat.natDegree₂).2]
    omega
  decode := hdecode
  heightProgram := Cost.PolynomialProgram.ofJointPair heightPair
  heightRealizesAt := Cost.PolynomialProgram.ofJointPair_realizesAt heightRealizes
  heightBounded := by
    refine (Cost.PolynomialProgram.multDepth_ofOutputs_le heightPair 0 1).trans ?_
    have h0 := heightBound.1
    have h1 := heightBound.2.1
    omega
  additionRealization := Cost.AdditionPolynomialRealization.ofJointPair additionPair

/-- The one-product lift preserves a common semantic polynomial for both arrangements. -/
noncomputable def evenLift {theta : ℕ → A} {n : ℕ} (hodd : n % 2 = 1)
    (source : DecodedAdditionPolynomial R theta n) :
    DecodedAdditionPolynomial R theta (n + 1) where
  P := X * source.P + C (theta n)
  multiplications := source.multiplications + 1
  additions := source.additions + 1
  multiplication_le := by
    have hn : (n + 1) / 2 = n / 2 + 1 := by omega
    rw [hn]
    exact Nat.add_le_add_right source.multiplication_le 1
  monic := by
    have hXQm : (X * source.P).Monic := monic_X.mul source.monic
    exact (monic_add_low (e := C (theta n)) hXQm
      (Or.inr (by rw [natDegree_C, monic_X.natDegree_mul source.monic,
        natDegree_X, source.natDegree]; omega))).1
  natDegree := by
    have hXQm : (X * source.P).Monic := monic_X.mul source.monic
    have hXQd : (X * source.P).natDegree = n + 1 := by
      rw [monic_X.natDegree_mul source.monic, natDegree_X, source.natDegree]
      omega
    exact (monic_add_low (e := C (theta n)) hXQm
      (Or.inr (by rw [natDegree_C, hXQd]; omega))).2.trans hXQd
  decode := by
    intro V hV t ht
    obtain ⟨hQV, hcV⟩ := evenLift_coeff_mem hV
    rcases Nat.lt_or_ge t n with hlt | hge
    · exact source.decode V hQV t hlt
    · have ht' : t = n := by omega
      rwa [ht']
  heightProgram := Cost.PolynomialProgram.evenLift source.heightProgram n
  heightRealizesAt := Cost.PolynomialProgram.evenLift_realizesAt
    source.heightRealizesAt n
  heightBounded := by
    refine (Cost.PolynomialProgram.multDepth_evenLift_le source.heightProgram n).trans ?_
    have hh := source.heightBounded
    have hc : Nat.clog 2 n ≤ Nat.clog 2 (n + 1) := Nat.clog_mono_right 2 (by omega)
    omega
  additionRealization := Cost.AdditionPolynomialRealization.evenLift
    source.additionRealization hodd n

end DecodedAdditionPolynomial

/-! ## Existence in every positive degree -/

/-- Every admissible odd degree has one decoded polynomial shared by the height and
addition arrangements. -/
theorem decodedAdditionPolynomial_exists_odd (n : ℕ) (hodd : n % 2 = 1)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R))
    (theta : ℕ → A) : Nonempty (DecodedAdditionPolynomial R theta n) := by
  rcases eq_or_ne n 1 with rfl | hn1
  · exact ⟨DecodedAdditionPolynomial.linear theta⟩
  rcases eq_or_ne n 7 with rfl | hn7
  · exact ⟨DecodedAdditionPolynomial.septic
      (isUnit_two_of_cast hadm (by omega)) theta⟩
  obtain ⟨T₁, T₂, H₂, H₄, G, hcompat, -, -, -, hdecode,
      ⟨heightPair, heightRealizes, heightBound⟩,
      additions, ⟨additionPair⟩⟩ :=
    decoded_addition_odd_realizable_pairs (R := R) (A := A) n hodd
      (by omega) hn7 hadm theta
  exact ⟨DecodedAdditionPolynomial.ofOddPair n hodd T₁ T₂ H₂ H₄ hcompat
    (fun V hV => (hdecode V hV).1) heightPair heightRealizes heightBound
    additions additionPair⟩

/-- **Same-family complete-polynomial existence.**  For every positive admissible
degree, the decoder, multiplicative-height schedule, and literal addition schedule
refer to one common monic polynomial family. -/
theorem decodedAdditionPolynomial_exists (n : ℕ) (hn : 1 ≤ n)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R))
    (theta : ℕ → A) : Nonempty (DecodedAdditionPolynomial R theta n) := by
  by_cases hodd : n % 2 = 1
  · exact decodedAdditionPolynomial_exists_odd n hodd hadm theta
  rcases eq_or_ne n 2 with rfl | hn2
  · exact ⟨DecodedAdditionPolynomial.quadratic theta⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m % 2 = 1 := by omega
  obtain ⟨source⟩ := decodedAdditionPolynomial_exists_odd m hm
    (fun i h1 h2 => hadm i h1 (by omega)) theta
  exact ⟨source.evenLift hm⟩

end FastPoly
