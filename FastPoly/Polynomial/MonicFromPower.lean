import FastPoly.Recover.Context
import FastPoly.Polynomial.TopWindow

/-!
# Recovering a monic polynomial from a power

`lem:monic-from-power` and `lem:monic-from-power-boundary` of the paper: the top window of
`P^m` is a triangular function of the top window of `P`, with pivot `m`; hence for `m` a unit
the top coefficients of `P` are polynomially recoverable from those of `P^m + E` whenever the
error `E` stays below the window (the boundary coefficient of `E` may be supplied as known
data instead).

The engine is `coeff_pow_sub_mem`: `[x^{mn-s}](P^m) - m·[x^{n-s}]P` is a polynomial in the
strictly higher coefficients of `P` — proved by induction on `m` from `coeff_mul_monic`.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The deviation of a top-window coefficient of `P^m` from `m` times the corresponding
coefficient of `P` involves only strictly higher coefficients of `P`: if all
`[x^{n-s'}]P` with `1 ≤ s' < s` lie in a subalgebra `S`, so does
`[x^{mn-s}](P^m) - m·[x^{n-s}]P`. -/
theorem coeff_pow_sub_mem (S : Subalgebra R A) {P : A[X]} {n : ℕ} (hP : P.Monic)
    (hn : P.natDegree = n) {s : ℕ} (hs1 : 1 ≤ s) (hsn : s ≤ n)
    (hwin : ∀ s', 1 ≤ s' → s' < s → P.coeff (n - s') ∈ S) :
    ∀ m, 1 ≤ m → ∀ s'', 1 ≤ s'' → s'' ≤ s →
      (P ^ m).coeff (m * n - s'') - (m : A) * P.coeff (n - s'') ∈ S := by
  have hwin' : ∀ s', 1 ≤ s' → s' < s → P.coeff (n - s') ∈ S := hwin
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    intro s'' hs''1 hs''s
    rcases Nat.eq_or_lt_of_le hm with hm1 | hm2
    · -- base case m + 1 = 1
      have : m = 0 := by omega
      subst this
      simp only [zero_add, pow_one, Nat.cast_one, one_mul]
      rw [sub_self]
      exact Subalgebra.zero_mem _
    have hm1 : 1 ≤ m := by omega
    have ihm := ih hm1
    have hPm : (P ^ m).natDegree = m * n := by rw [hP.natDegree_pow, hn]
    have hPmMonic : (P ^ m).Monic := hP.pow m
    -- expand [(P^m)·P] at degree (m+1)n - s'' with `coeff_mul_monic`
    have hexp : (P ^ (m + 1)).coeff ((m + 1) * n - s'') =
        (P ^ m).coeff (m * n - s'') +
          ∑ j ∈ range n, P.coeff j * (P ^ m).coeff (n + (m * n - s'') - j) := by
      have h1 : (m + 1) * n - s'' = P.natDegree + (m * n - s'') := by
        have hmul : (m + 1) * n = m * n + n := by ring
        have hnm : s'' ≤ m * n := le_trans (le_trans hs''s hsn) (Nat.le_mul_of_pos_left n hm1)
        rw [hn]; omega
      rw [pow_succ, h1, coeff_mul_monic (P ^ m) P hP, hn]
    -- split off the pivot term j = n - s''
    have hns'' : n - s'' ∈ range n := mem_range.2 (by omega)
    rw [hexp, ← Finset.add_sum_erase _ _ hns'']
    have hpivot : P.coeff (n - s'') * (P ^ m).coeff (n + (m * n - s'') - (n - s'')) =
        P.coeff (n - s'') := by
      have h2 : n + (m * n - s'') - (n - s'') = m * n := by
        have hnm : s'' ≤ m * n := le_trans (le_trans hs''s hsn) (Nat.le_mul_of_pos_left n hm1)
        omega
      rw [h2, ← hPm, hPmMonic.coeff_natDegree, mul_one]
    rw [hpivot]
    have hgoal : (P ^ m).coeff (m * n - s'') +
        (P.coeff (n - s'') + ∑ j ∈ (range n).erase (n - s''),
          P.coeff j * (P ^ m).coeff (n + (m * n - s'') - j)) -
        (↑(m + 1) : A) * P.coeff (n - s'') =
        ((P ^ m).coeff (m * n - s'') - (m : A) * P.coeff (n - s'')) +
          ∑ j ∈ (range n).erase (n - s''),
            P.coeff j * (P ^ m).coeff (n + (m * n - s'') - j) := by
      push_cast; ring
    rw [hgoal]
    refine Subalgebra.add_mem _ (ihm s'' hs''1 hs''s) (Subalgebra.sum_mem _ fun j hj => ?_)
    have hjn : j < n := mem_range.1 (Finset.mem_of_mem_erase hj)
    have hjne : j ≠ n - s'' := Finset.ne_of_mem_erase hj
    by_cases hlow : j < n - s''
    · -- index above the degree of P^m: coefficient vanishes
      have hidx0 : m * n < n + (m * n - s'') - j := by
        have hnm : s'' ≤ m * n := le_trans (le_trans hs''s hsn) (Nat.le_mul_of_pos_left n hm1)
        omega
      have hz : (P ^ m).coeff (n + (m * n - s'') - j) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hPm]; exact hidx0)
      rw [hz, mul_zero]
      exact Subalgebra.zero_mem _
    · -- an inner-window term: both factors in `S`
      push_neg at hlow
      have hjgt : n - s'' < j := lt_of_le_of_ne hlow (Ne.symm hjne)
      set σ := n - j with hσ
      have hσ1 : 1 ≤ σ := by omega
      have hσlt : σ < s'' := by omega
      have hidx : n + (m * n - s'') - j = m * n - (s'' - σ) := by
        have hnm : s'' ≤ m * n := le_trans (le_trans hs''s hsn) (Nat.le_mul_of_pos_left n hm1)
        omega
      have hfac1 : P.coeff j ∈ S := by
        have : j = n - σ := by omega
        rw [this]
        exact hwin' σ hσ1 (lt_of_lt_of_le hσlt hs''s)
      have hfac2 : (P ^ m).coeff (m * n - (s'' - σ)) ∈ S := by
        have hd : (P ^ m).coeff (m * n - (s'' - σ)) =
            ((P ^ m).coeff (m * n - (s'' - σ)) - (m : A) * P.coeff (n - (s'' - σ))) +
              (m : A) * P.coeff (n - (s'' - σ)) := by ring
        rw [hd]
        refine Subalgebra.add_mem _ (ihm (s'' - σ) (by omega) (by omega)) ?_
        refine Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ m) ?_
        exact hwin' (s'' - σ) (by omega) (by omega)
      rw [hidx]
      exact Subalgebra.mul_mem _ hfac1 hfac2

/-- **Recovery of a monic polynomial from a power with a boundary error**
(`lem:monic-from-power-boundary`; `lem:monic-from-power` is the case `E = 0`).
Let `P` be monic of degree `n`, `m ≥ 1` with `(m : R)` a unit, and `W = P^m + E` with
`natDegree E ≤ mn - n` and boundary coefficient `[x^{mn-n}]E` in the known context `K`.
Then every coefficient `[x^{n-s}]P`, `1 ≤ s ≤ n`, lies in the algebra generated by `K` and
the window `[x^{mn-s'}]W`, `1 ≤ s' ≤ s` — causally in `s`. -/
theorem coeff_mem_of_pow_add (K : Subalgebra R A) {P W E : A[X]} {n : ℕ}
    (hP : P.Monic) (hn : P.natDegree = n) {m : ℕ} (hm : 1 ≤ m) (hmu : IsUnit (m : R))
    (hW : W = P ^ m + E) (hE : E.natDegree ≤ m * n - n) (hEb : E.coeff (m * n - n) ∈ K) :
    ∀ s, 1 ≤ s → s ≤ n → P.coeff (n - s) ∈
      K ⊔ adjoin R ((fun s' => W.coeff (m * n - s')) '' Set.Icc 1 s) := by
  intro s hs1 hsn
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    set V := K ⊔ adjoin R ((fun s' => W.coeff (m * n - s')) '' Set.Icc 1 s) with hV
    have hKV : K ≤ V := le_sup_left
    -- the error contribution at degree mn - s is either zero or known
    have hEmem : E.coeff (m * n - s) ∈ K := by
      rcases Nat.lt_or_ge s n with hlt | hge
      · rw [coeff_eq_zero_of_natDegree_lt]
        · exact Subalgebra.zero_mem _
        · have hnm : n ≤ m * n := Nat.le_mul_of_pos_left n hm
          omega
      · have : s = n := le_antisymm hsn hge
        subst this; exact hEb
    -- the deviation of the power coefficient, via the engine
    have hdev : (P ^ m).coeff (m * n - s) - (m : A) * P.coeff (n - s) ∈ V := by
      refine coeff_pow_sub_mem V hP hn hs1 hsn (fun s' hs'1 hs's => ?_) m hm s hs1 le_rfl
      have hmem := ih s' hs's hs'1 (le_trans (le_of_lt hs's) hsn)
      refine SetLike.le_def.1 (sup_le_sup_left (adjoin_mono (Set.image_mono ?_)) K) hmem
      exact Set.Icc_subset_Icc le_rfl (le_of_lt hs's)
    -- solve the pivot
    have hWmem : W.coeff (m * n - s) ∈ V :=
      (le_sup_right : adjoin R _ ≤ V)
        (subset_adjoin ⟨s, Set.mem_Icc.2 ⟨hs1, le_rfl⟩, rfl⟩)
    exact mem_of_nat_mul_eq hmu
      (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hWmem (hKV hEmem)) hdev)
      (by rw [hW, coeff_add]; ring)

/-- **Monic square root of a visible square**: a subalgebra containing every
coefficient of `P * P` contains every coefficient of the monic `P`, provided `2`
is a unit in the scalars.  The leading coefficient is the fixed `1`; below the
degree the window of `P²` decodes causally via `coeff_mem_of_pow_add`. -/
theorem coeff_mem_of_sq_mem (V : Subalgebra R A) {P : A[X]} {n : ℕ}
    (hP : P.Monic) (hn : P.natDegree = n) (h2 : IsUnit ((2 : ℕ) : R))
    (hsq : ∀ j, (P * P).coeff j ∈ V) : ∀ j, P.coeff j ∈ V := by
  intro j
  rcases Nat.lt_or_ge j n with hlt | hge
  · have h := coeff_mem_of_pow_add V hP hn (m := 2) (by omega) h2
      (W := P ^ 2) (E := 0) (by ring) (by
        rw [natDegree_zero]
        omega) (by
        rw [coeff_zero]
        exact Subalgebra.zero_mem _) (n - j) (by omega) (by omega)
    have hidx : n - (n - j) = j := by omega
    rw [hidx] at h
    refine SetLike.le_def.1 (sup_le le_rfl (adjoin_le ?_)) h
    rintro _ ⟨s', -, rfl⟩
    rw [sq]
    exact hsq _
  · rcases eq_or_lt_of_le hge with heq | hgt
    · rw [← heq, ← hn, hP.coeff_natDegree]
      exact Subalgebra.one_mem _
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Subalgebra.zero_mem _

end FastPoly
