import FastPoly.Char2.SubstH

/-!
# The two universal decoder cells, and the gauge witness

The two local cells of `char2_static_patterns.md` §26, in the filtered form of
the decoder calculus, plus the §27 collision showing why the punctured-pair
interface's zero-constant conditions are load-bearing.

* `twoOffset_mem` — for monic wires of distinct positive degrees, the rows
  `deg B` and `deg A` of `(A+α)(B+β)` recover `β` then `α` with unit slopes
  (characteristic-free).
* `anchored_double_coeff` — two monic degree-`d` factors whose penultimate
  coefficients differ by one force coefficient `1` in degree `2d-1`
  (characteristic two).
* `chain_collision` — the naive Horner-style chain `C_i = (C_{i-1}+x)(H+b_i)`
  identifies the keys `(0,0)` and `(1,1)` at `L = 2`, so a viable state must
  carry punctures/anchors rather than free chain constants.
-/

namespace FastPoly.Char2

open Polynomial Algebra

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Products of visible polynomials have visible coefficients. -/
theorem coeff_mul_mem (V : Subalgebra R A) {P Q : A[X]}
    (hP : ∀ m, P.coeff m ∈ V) (hQ : ∀ m, Q.coeff m ∈ V) :
    ∀ m, (P * Q).coeff m ∈ V := by
  intro m
  rw [coeff_mul]
  exact Subalgebra.sum_mem _ fun p _ => mul_mem (hP p.1) (hQ p.2)

/-- **Two-offset product cell** (§26, cell 1): for monic `P, Q` of distinct
positive degrees, the rows `deg P` and `deg Q` of `(P+α)(Q+β)` recover `β`
then `α` with unit slopes. -/
theorem twoOffset_mem {P Q : A[X]} (hP : P.Monic) (hQ : Q.Monic)
    (h0 : 0 < Q.natDegree) (hlt : Q.natDegree < P.natDegree)
    {α β : A} (V : Subalgebra R A)
    (hprod : ∀ m, ((P + C α) * (Q + C β)).coeff m ∈ V)
    (hPc : ∀ m, P.coeff m ∈ V) (hQc : ∀ m, Q.coeff m ∈ V) :
    β ∈ V ∧ α ∈ V := by
  have hexp : (P + C α) * (Q + C β) = P * Q + C β * P + C α * Q + C α * C β := by
    ring
  have hβ : β ∈ V := by
    have h := hprod P.natDegree
    rw [hexp, coeff_add, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
      hP.coeff_natDegree, coeff_eq_zero_of_natDegree_lt hlt, ← C_mul, coeff_C,
      if_neg (by omega)] at h
    have hkey : β = ((P * Q).coeff P.natDegree + β * 1 + α * 0 + 0)
        - (P * Q).coeff P.natDegree := by ring
    rw [hkey]
    exact sub_mem h (coeff_mul_mem V hPc hQc _)
  refine ⟨hβ, ?_⟩
  have h := hprod Q.natDegree
  rw [hexp, coeff_add, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
    hQ.coeff_natDegree, ← C_mul, coeff_C, if_neg (by omega)] at h
  have hkey : α = ((P * Q).coeff Q.natDegree + β * P.coeff Q.natDegree
      + α * 1 + 0) - (P * Q).coeff Q.natDegree - β * P.coeff Q.natDegree := by
    ring
  rw [hkey]
  exact sub_mem (sub_mem h (coeff_mul_mem V hPc hQc _)) (mul_mem hβ (hPc _))

/-- **Anchored doubling cell** (§26, cell 2): monic degree-`d` factors whose
penultimate coefficients differ by one force coefficient `1` at `2d-1`. -/
theorem anchored_double_coeff [CharP A 2] {d : ℕ} (hd0 : 0 < d)
    {P Q : A[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPd : P.natDegree = d) (hQd : Q.natDegree = d)
    (hanch : P.coeff (d - 1) = Q.coeff (d - 1) + 1) :
    (P * Q).coeff (2 * d - 1) = 1 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsplit : ∀ i ∈ Finset.range (2 * d - 1 + 1),
      P.coeff i * Q.coeff (2 * d - 1 - i)
        = (if i = d - 1 then P.coeff (d - 1) * Q.coeff d else 0)
          + (if i = d then P.coeff d * Q.coeff (d - 1) else 0) := by
    intro i hi
    rcases (show i = d - 1 ∨ i = d ∨ (i < d - 1 ∨ d < i) from by omega)
      with hi1 | hi2 | hout
    · rw [hi1, if_pos rfl, if_neg (by omega), add_zero,
        show 2 * d - 1 - (d - 1) = d from by omega]
    · rw [hi2, if_neg (by omega), if_pos rfl, zero_add,
        show 2 * d - 1 - d = d - 1 from by omega]
    · rw [if_neg (by omega), if_neg (by omega), add_zero]
      rcases hout with hlow | hhigh
      · rw [coeff_eq_zero_of_natDegree_lt (show Q.natDegree < 2 * d - 1 - i
          from by omega), mul_zero]
      · rw [coeff_eq_zero_of_natDegree_lt (show P.natDegree < i from by omega),
          zero_mul]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ (d - 1), Finset.sum_ite_eq' _ d,
    if_pos (Finset.mem_range.2 (by omega)), if_pos (Finset.mem_range.2 (by omega))]
  rw [show Q.coeff d = 1 from hQd ▸ hQ.coeff_natDegree,
    show P.coeff d = 1 from hPd ▸ hP.coeff_natDegree, hanch]
  have h2 : (Q.coeff (d - 1) + Q.coeff (d - 1) : A) = 0 := CharTwo.add_self_eq_zero _
  linear_combination h2

/-- **The separable-crown cell** (§33): for a monic tag `J` strictly above the
perturbation degree, the rows `e+i` of `L_J(Δ) = Δ² + J·Δ` expose the
coefficients of `Δ` descending with unit pivots.  Membership-wise this is
characteristic-free: every square contribution at row `e+i` uses only
indices strictly above `i`. -/
theorem crown_LJ_mem {J Δ : A[X]} (hJ : J.Monic)
    (hΔ : Δ.natDegree < J.natDegree) (V : Subalgebra R A)
    (hL : ∀ m, (Δ ^ 2 + J * Δ).coeff m ∈ V)
    (hJc : ∀ m, J.coeff m ∈ V) :
    ∀ i, Δ.coeff i ∈ V := by
  have hstep : ∀ i, i ≤ Δ.natDegree → (∀ j, i < j → Δ.coeff j ∈ V) →
      Δ.coeff i ∈ V := by
    intro i hi hknown
    have hrow := hL (J.natDegree + i)
    rw [coeff_add, pow_two, coeff_mul, coeff_mul] at hrow
    have hsq : (∑ p ∈ Finset.antidiagonal (J.natDegree + i),
        Δ.coeff p.1 * Δ.coeff p.2) ∈ V := by
      refine Subalgebra.sum_mem _ fun p hp => ?_
      have hpsum := Finset.mem_antidiagonal.1 hp
      rcases Nat.lt_or_ge Δ.natDegree p.1 with h1 | h1
      · rw [coeff_eq_zero_of_natDegree_lt h1, zero_mul]
        exact V.zero_mem
      rcases Nat.lt_or_ge Δ.natDegree p.2 with h2 | h2
      · rw [coeff_eq_zero_of_natDegree_lt h2, mul_zero]
        exact V.zero_mem
      exact mul_mem (hknown p.1 (by omega)) (hknown p.2 (by omega))
    have hmem : ((J.natDegree, i) : ℕ × ℕ)
        ∈ Finset.antidiagonal (J.natDegree + i) :=
      Finset.mem_antidiagonal.2 rfl
    have hJsplit : (∑ p ∈ Finset.antidiagonal (J.natDegree + i),
        J.coeff p.1 * Δ.coeff p.2)
        = J.coeff J.natDegree * Δ.coeff i
          + ∑ p ∈ (Finset.antidiagonal (J.natDegree + i)).erase
              (J.natDegree, i), J.coeff p.1 * Δ.coeff p.2 :=
      (Finset.add_sum_erase _ _ hmem).symm
    have hrest : (∑ p ∈ (Finset.antidiagonal (J.natDegree + i)).erase
        (J.natDegree, i), J.coeff p.1 * Δ.coeff p.2) ∈ V := by
      refine Subalgebra.sum_mem _ fun p hp => ?_
      have hpne := Finset.ne_of_mem_erase hp
      have hpsum := Finset.mem_antidiagonal.1 (Finset.mem_of_mem_erase hp)
      rcases Nat.lt_or_ge J.natDegree p.1 with h1 | h1
      · rw [coeff_eq_zero_of_natDegree_lt h1, zero_mul]
        exact V.zero_mem
      rcases Nat.lt_or_ge p.1 J.natDegree with h1' | h1'
      · exact mul_mem (hJc p.1) (hknown p.2 (by omega))
      · exact absurd (Prod.ext_iff.2 ⟨by omega, by omega⟩) hpne
    rw [hJsplit, hJ.coeff_natDegree, one_mul] at hrow
    have hkey : Δ.coeff i
        = ((∑ p ∈ Finset.antidiagonal (J.natDegree + i),
            Δ.coeff p.1 * Δ.coeff p.2)
          + (Δ.coeff i
            + ∑ p ∈ (Finset.antidiagonal (J.natDegree + i)).erase
                (J.natDegree, i), J.coeff p.1 * Δ.coeff p.2))
          - (∑ p ∈ Finset.antidiagonal (J.natDegree + i),
            Δ.coeff p.1 * Δ.coeff p.2)
          - ∑ p ∈ (Finset.antidiagonal (J.natDegree + i)).erase
              (J.natDegree, i), J.coeff p.1 * Δ.coeff p.2 := by
      ring
    rw [hkey]
    exact sub_mem (sub_mem hrow hsq) hrest
  have main : ∀ fuel i, Δ.natDegree ≤ i + fuel → Δ.coeff i ∈ V := by
    intro fuel
    induction fuel with
    | zero =>
      intro i hi
      rcases Nat.lt_or_ge Δ.natDegree i with hlt | hge
      · rw [coeff_eq_zero_of_natDegree_lt hlt]
        exact V.zero_mem
      · exact hstep i (by omega) fun j hj => by
          rw [coeff_eq_zero_of_natDegree_lt (by omega)]
          exact V.zero_mem
    | succ fuel ih =>
      intro i hi
      rcases Nat.lt_or_ge Δ.natDegree i with hlt | hge
      · rw [coeff_eq_zero_of_natDegree_lt hlt]
        exact V.zero_mem
      · exact hstep i hge fun j hj => ih j (by omega)
  intro i
  exact main Δ.natDegree i (by omega)

/-- **The §27 gauge witness**: at `L = 2` the naive chain identifies the keys
`(b₁,b₂) = (0,0)` and `(1,1)` — punctures and anchors are load-bearing. -/
theorem chain_collision [CharP A 2] :
    (X * (H (A := A)) + X) * H = (X * ((H (A := A)) + 1) + X) * (H + 1) := by
  have h2 := two_eq_zero_poly (A := A)
  linear_combination (-(X * (H (A := A)) + X)) * h2

end FastPoly.Char2
