import FastPoly.Examples.OptimizedCircuits
import FastPoly.Section6.GadgetDecoders

/-!
# The degree-17 appendix circuit is the general construction

The reduced-key chain `Chain17` of `sections/appendix_polynomials.tex` equals the
crown `T_{4,4}` pair of the proved `4k+1` family under an explicit integral change
of keys `bof`, and therefore inherits its decoder.
-/

namespace FastPoly

open Polynomial Algebra

variable {A : Type*} [CommRing A]

namespace Chain17

/-- The integral key change: the appendix keys `b` in terms of the construction
parameters `θ = (b, c, a, e, ρ, α₀, …, α₁₁)`. -/
noncomputable def bof (θ : ℕ → A) : ℕ → A
  | 0 => θ 5
  | 1 => θ 6
  | 2 => θ 7 + θ 1
  | 3 => θ 8
  | 4 => θ 13 + θ 9 + θ 3
  | 5 => θ 14 + θ 10 + θ 3
  | 6 => θ 11 + θ 1
  | 7 => θ 12
  | 8 => θ 13 - θ 9 - θ 3
  | 9 => θ 14 - θ 10 - θ 3
  | 10 => θ 4 + θ 3 + θ 15 + θ 1
  | 11 => θ 3 + θ 16 + θ 1
  | 12 => θ 3 - θ 16 - θ 1
  | 13 => θ 1 + θ 2
  | 14 => θ 4 + θ 3 - θ 15 - θ 1
  | 15 => θ 1 - θ 2
  | 16 => θ 0
  | _ + 17 => 0

/-! The construction-side wires of the crown `T_{4,4}` recursion. -/

noncomputable def H2W (θ : ℕ → A) : A[X] := crownH2 (θ 0) (θ 1)
noncomputable def H4W (θ : ℕ → A) : A[X] := crownH4 (θ 0) (θ 1) (θ 2) (θ 3)
noncomputable def Ht4W (θ : ℕ → A) : A[X] := H4W θ + C (θ 4)
noncomputable def H8W (θ : ℕ → A) : A[X] :=
  (H4W θ + (H2W θ + (X + C (θ 16)))) * (H4W θ - (H2W θ + (X + C (θ 16))))
    + (X + C (θ 14))
noncomputable def Ht8W (θ : ℕ → A) : A[X] :=
  (Ht4W θ + (H2W θ + C (θ 15))) * (Ht4W θ - (H2W θ + C (θ 15))) + C (θ 13)
noncomputable def QPW (θ : ℕ → A) : A[X] :=
  (X + C (θ 12)) * (H2W θ + C (θ 11)) + C (θ 10)
noncomputable def QMW (θ : ℕ → A) : A[X] :=
  (X + C (θ 8)) * (H2W θ + C (θ 7)) + C (θ 6)
noncomputable def H16W (θ : ℕ → A) : A[X] :=
  (H8W θ + (H4W θ + QPW θ)) * (H8W θ - (H4W θ + QPW θ)) + QMW θ
noncomputable def Ht16W (θ : ℕ → A) : A[X] :=
  (Ht8W θ + (H4W θ + C (θ 9))) * (Ht8W θ - (H4W θ + C (θ 9))) + C (θ 5)

/-- The crown `T_{4,4}` pair evaluates to the two explicit wires. -/
theorem tpair_eq (θ : ℕ → A) :
    Tpair (crownHp (θ 0) (θ 1) (θ 2) (θ 3))
      (crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4)) 4 2 (fun t => θ (5 + t))
      = (H16W θ, Ht16W θ) := rfl

/-- The appendix chain equals the combined crown pair under the key change. -/
theorem chain_eq (θ : ℕ → A) :
    P (bof θ) = X * H16W θ + Ht16W θ := by
  have hy : yW (bof θ) = H2W θ - C (θ 1) := by
    simp only [yW, bof, H2W, crownH2]
    ring
  have hz : zW (bof θ) = H4W θ - C (θ 3) := by
    simp only [zW, bof, map_add, map_sub]
    rw [hy]
    simp only [H4W, crownH4, H2W]
    ring
  have ht : tW (bof θ) = H8W θ - (X + C (θ 14)) := by
    simp only [tW, bof, map_add, map_sub]
    rw [hy, hz]
    simp only [H8W]
    ring
  have hu : uW (bof θ) = Ht8W θ - C (θ 13) := by
    simp only [uW, bof, map_add, map_sub]
    rw [hy, hz]
    simp only [Ht8W, Ht4W]
    ring
  have hv : vW (bof θ) = QPW θ - C (θ 10) := by
    simp only [vW, bof, map_add]
    rw [hy]
    simp only [QPW]
    ring
  have hw : wW (bof θ) = QMW θ - C (θ 6) := by
    simp only [wW, bof, map_add]
    rw [hy]
    simp only [QMW]
    ring
  have hs : sW (bof θ) = H16W θ - QMW θ := by
    simp only [sW, bof, map_add, map_sub]
    rw [hz, ht, hv]
    simp only [H16W]
    ring
  have hr : rW (bof θ) = Ht16W θ - C (θ 5) := by
    simp only [rW, bof, map_add, map_sub]
    rw [hz, hu]
    simp only [Ht16W]
    ring
  have hq : qW (bof θ) = X * H16W θ := by
    simp only [qW, bof]
    rw [hw, hs]
    ring
  simp only [P, bof]
  rw [hr, hq]
  ring

/-- **The appendix `(17, 9)` circuit is the proved general construction**: under the
integral key change `bof`, the chain equals the combined crown `T_{4,4}` pair. -/
theorem eq_master (θ : ℕ → A) :
    P (bof θ) = combined
      (Tpair (crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4)) 4 2 (fun t => θ (5 + t))).1
      (Tpair (crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4)) 4 2 (fun t => θ (5 + t))).2 := by
  rw [tpair_eq]
  exact chain_eq θ

section decode

variable {R A' : Type*} [CommRing R] [CommRing A'] [Algebra R A'] [Nontrivial A']

/-- **The appendix `(17, 9)` circuit is decodable**: any subalgebra containing the
coefficients of the chain contains all seventeen keys.  Inherited from the proved
`4k+1` family through `eq_master`. -/
theorem decodable (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 8 → IsUnit (((n : ℕ) : ℤ) : R))
    (h2 : IsUnit (2 : R)) (θ : ℕ → A') (V : Subalgebra R A')
    (hPV : ∀ j, (P (bof θ)).coeff j ∈ V) :
    ∀ i, i < 17 → bof θ i ∈ V := by
  have hPV' : ∀ j, (combined
      (Tpair (crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4)) 4 2 (fun t => θ (5 + t))).1
      (Tpair (crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4)) 4 2
        (fun t => θ (5 + t))).2).coeff j ∈ V := by
    intro j
    rw [← eq_master θ]
    exact hPV j
  obtain ⟨⟨hb, hc, ha, he, hρ⟩, -, -, hα⟩ := fourk_decodable (k := 4)
    (by norm_num) hadm h2 (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (fun t => θ (5 + t))
    V hPV'
  have hθ : ∀ i, i < 17 → θ i ∈ V := by
    intro i hi
    rcases Nat.lt_or_ge i 5 with h5 | h5
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 from by omega)
        with rfl | rfl | rfl | rfl | rfl
      · exact hb
      · exact hc
      · exact ha
      · exact he
      · exact hρ
    · have h := hα (i - 5) (by omega)
      rwa [show 5 + (i - 5) = i from by omega] at h
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7
      ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15
      ∨ i = 16 from by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hθ 5 (by omega)
  · exact hθ 6 (by omega)
  · exact add_mem (hθ 7 (by omega)) (hθ 1 (by omega))
  · exact hθ 8 (by omega)
  · exact add_mem (add_mem (hθ 13 (by omega)) (hθ 9 (by omega))) (hθ 3 (by omega))
  · exact add_mem (add_mem (hθ 14 (by omega)) (hθ 10 (by omega))) (hθ 3 (by omega))
  · exact add_mem (hθ 11 (by omega)) (hθ 1 (by omega))
  · exact hθ 12 (by omega)
  · exact sub_mem (sub_mem (hθ 13 (by omega)) (hθ 9 (by omega))) (hθ 3 (by omega))
  · exact sub_mem (sub_mem (hθ 14 (by omega)) (hθ 10 (by omega))) (hθ 3 (by omega))
  · exact add_mem (add_mem (add_mem (hθ 4 (by omega)) (hθ 3 (by omega)))
      (hθ 15 (by omega))) (hθ 1 (by omega))
  · exact add_mem (add_mem (hθ 3 (by omega)) (hθ 16 (by omega))) (hθ 1 (by omega))
  · exact sub_mem (sub_mem (hθ 3 (by omega)) (hθ 16 (by omega))) (hθ 1 (by omega))
  · exact add_mem (hθ 1 (by omega)) (hθ 2 (by omega))
  · exact sub_mem (sub_mem (add_mem (hθ 4 (by omega)) (hθ 3 (by omega)))
      (hθ 15 (by omega))) (hθ 1 (by omega))
  · exact sub_mem (hθ 1 (by omega)) (hθ 2 (by omega))
  · exact hθ 0 (by omega)

end decode

/-- The inverse key change, given `2⁻¹ = v`. -/
noncomputable def thetaOf (v : A) (b : ℕ → A) : ℕ → A
  | 0 => b 16
  | 1 => v * (b 13 + b 15)
  | 2 => v * (b 13 - b 15)
  | 3 => v * (b 11 + b 12)
  | 4 => v * (b 10 + b 14) - v * (b 11 + b 12)
  | 5 => b 0
  | 6 => b 1
  | 7 => b 2 - v * (b 13 + b 15)
  | 8 => b 3
  | 9 => v * (b 4 - b 8) - v * (b 11 + b 12)
  | 10 => v * (b 5 - b 9) - v * (b 11 + b 12)
  | 11 => b 6 - v * (b 13 + b 15)
  | 12 => b 7
  | 13 => v * (b 4 + b 8)
  | 14 => v * (b 5 + b 9)
  | 15 => v * (b 10 - b 14) - v * (b 13 + b 15)
  | 16 => v * (b 11 - b 12) - v * (b 13 + b 15)
  | _ + 17 => 0

/-- The key change is surjective whenever `2` is a unit: every choice of the
seventeen appendix keys is realized by the general construction. -/
theorem bof_surjective (h2 : IsUnit (2 : A)) (b : ℕ → A) :
    ∃ θ : ℕ → A, ∀ i, i < 17 → bof θ i = b i := by
  obtain ⟨u, hu⟩ := h2
  set v : A := ↑u⁻¹ with hv
  have h1 : v * 2 = 1 := by rw [hv, ← hu]; exact u.inv_mul
  refine ⟨thetaOf v b, ?_⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7
      ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15
      ∨ i = 16 from by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simp only [bof, thetaOf]
  · simp only [bof, thetaOf]
  · simp only [bof, thetaOf]; ring
  · simp only [bof, thetaOf]
  · simp only [bof, thetaOf]; linear_combination (b 4) * h1
  · simp only [bof, thetaOf]; linear_combination (b 5) * h1
  · simp only [bof, thetaOf]; ring
  · simp only [bof, thetaOf]
  · simp only [bof, thetaOf]; linear_combination (b 8) * h1
  · simp only [bof, thetaOf]; linear_combination (b 9) * h1
  · simp only [bof, thetaOf]; linear_combination (b 10) * h1
  · simp only [bof, thetaOf]; linear_combination (b 11) * h1
  · simp only [bof, thetaOf]; linear_combination (b 12) * h1
  · simp only [bof, thetaOf]; linear_combination (b 13) * h1
  · simp only [bof, thetaOf]; linear_combination (b 14) * h1
  · simp only [bof, thetaOf]; linear_combination (b 15) * h1
  · simp only [bof, thetaOf]

end Chain17

end FastPoly
