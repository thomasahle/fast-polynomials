import FastPoly.Polynomial.MonicFromPower

/-!
# The causal shell engine

Generic top-down decoding steps for difference-of-squares shells, used by the finite
special cases (degrees 15, 27, 31) and by the `8k+3`/`8k+7` induction steps.  The
recurring causal operation:  If

`Y = S² M + E`,

where `M` is a known monic factor, `S` is monic of degree `d`, and `E` reaches at most
the middle boundary row of `S²M`, then the coefficients of `S` are determined causally
from the corresponding top rows of `Y`.  The proof below is the decoder itself: first
divide by `M` coefficient-by-coefficient from the top, then use the unit pivot in

`[x^(2d-s)]Sᵐ = m [x^(d-s)]S + (higher coefficients)`.

For the square shells used here, `m=2`.  The boundary coefficient of `E` is supplied
explicitly; this is the `-1`/`+1` seam in the paper's finite tables.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Coefficients of the constant monic factor `1` belong to every scalar context. -/
theorem coeff_one_mem_subalgebra (V : Subalgebra R A) (i : ℕ) :
    (1 : A[X]).coeff i ∈ V := by
  rw [coeff_one]
  split <;> simp

/-- Coefficients of the monic factor `X` belong to every scalar context. -/
theorem coeff_X_mem_subalgebra (V : Subalgebra R A) (i : ℕ) : X.coeff i ∈ V := by
  rw [coeff_X]
  split <;> simp

/-- Coefficients of the monic factor `X+1` belong to every scalar context. -/
theorem coeff_X_add_one_mem_subalgebra (V : Subalgebra R A) (i : ℕ) :
    (X + 1 : A[X]).coeff i ∈ V := by
  rw [coeff_add]
  exact Subalgebra.add_mem V (coeff_X_mem_subalgebra V i) (coeff_one_mem_subalgebra V i)

/-- Cauchy products preserve affine coefficient schedules.  If `P_i` is visible at
`i+q+e`, `Q_i` at `i+p+e`, and the respective degree bounds are `p,q`, then
`[x^j](P*Q)` is visible at `j+e`.  This is the general row-shift calculation used by all
three finite `CausalPair` proofs. -/
theorem coeff_mul_mem_of_schedules (V : ℕ → Subalgebra R A) (hV : Antitone V)
    {P Q : A[X]} {p q e : ℕ} (hPdeg : P.natDegree ≤ p) (hQdeg : Q.natDegree ≤ q)
    (hP : ∀ i, P.coeff i ∈ V (i + q + e))
    (hQ : ∀ i, Q.coeff i ∈ V (i + p + e)) :
    ∀ j, (P * Q).coeff j ∈ V (j + e) := by
  intro j
  rw [coeff_mul]
  refine Subalgebra.sum_mem _ fun x hx => ?_
  have hsum : x.1 + x.2 = j := mem_antidiagonal.1 hx
  rcases le_or_gt x.1 p with hi | hi
  · rcases le_or_gt x.2 q with hk | hk
    · exact Subalgebra.mul_mem _
        (hV (by omega) (hP x.1)) (hV (by omega) (hQ x.2))
    · have hz : Q.coeff x.2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, mul_zero]
      exact Subalgebra.zero_mem _
  · have hz : P.coeff x.1 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, zero_mul]
    exact Subalgebra.zero_mem _

/-- Square specialization of `coeff_mul_mem_of_schedules`. -/
theorem coeff_sq_mem_of_schedule (V : ℕ → Subalgebra R A) (hV : Antitone V)
    {P : A[X]} {d e : ℕ} (hPdeg : P.natDegree ≤ d)
    (hP : ∀ i, P.coeff i ∈ V (i + d + e)) :
    ∀ j, (P ^ 2).coeff j ∈ V (j + e) := by
  rw [show P ^ 2 = P * P by ring]
  exact coeff_mul_mem_of_schedules V hV hPdeg hPdeg hP hP

/-- Multiplication by `X` lowers a coefficient schedule by one row. -/
theorem coeff_X_mul_mem_of_schedule (V : ℕ → Subalgebra R A)
    {P : A[X]} (hP : ∀ i, P.coeff i ∈ V (i + 1)) :
    ∀ j, (X * P).coeff j ∈ V j := by
  intro j
  match j with
  | 0 =>
      rw [mul_coeff_zero, coeff_X_zero, zero_mul]
      exact Subalgebra.zero_mem _
  | j + 1 =>
      rw [coeff_X_mul]
      exact hP j

/-- Multiplication by `X+1` lowers a coefficient schedule by one row. -/
theorem coeff_X_add_one_mul_mem_of_schedule (V : ℕ → Subalgebra R A) (hV : Antitone V)
    {P : A[X]} (hP : ∀ i, P.coeff i ∈ V (i + 1)) :
    ∀ j, ((X + 1) * P).coeff j ∈ V j := by
  intro j
  have hpoly : (X + 1) * P = X * P + P := by ring
  rcases j with _ | j
  · rw [hpoly, coeff_add, mul_coeff_zero, coeff_X_zero, zero_mul, zero_add]
    exact hV (by omega) (hP 0)
  · rw [hpoly, coeff_add, coeff_X_mul]
    exact Subalgebra.add_mem _ (hP j) (hV (by omega) (hP (j + 1)))

/-- Recover a monic polynomial causally from a scheduled top window of one of its powers.
The coefficient `[x^j]S` has pivot row `(m-1)d+j` in `S^m`, with slope `m`.  This
schedule form is convenient when the rows have first been peeled out of a larger circuit. -/
theorem coeff_mem_of_monic_pow_schedule (V : ℕ → Subalgebra R A) (hV : Antitone V)
    {S : A[X]} {d m : ℕ} (hS : S.Monic) (hd : S.natDegree = d) (hm : 1 ≤ m)
    (hmu : IsUnit (m : R))
    (hpow : ∀ i, (m - 1) * d ≤ i → i ≤ m * d → (S ^ m).coeff i ∈ V i) :
    ∀ j, S.coeff j ∈ V ((m - 1) * d + j) := by
  have hmd : m * d = (m - 1) * d + d := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [Nat.add_mul, one_mul]
  have hroot : ∀ s, 1 ≤ s → s ≤ d → S.coeff (d - s) ∈ V (m * d - s) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        intro hs1 hsd
        have hdev : (S ^ m).coeff (m * d - s) - (m : A) * S.coeff (d - s) ∈
            V (m * d - s) := by
          refine coeff_pow_sub_mem (V (m * d - s)) hS hd hs1 hsd
            (fun s' hs'1 hs's => ?_) m hm s hs1 le_rfl
          exact hV (by omega) (ih s' hs's hs'1 (by omega))
        have hpivot : (m : A) * S.coeff (d - s) =
            (S ^ m).coeff (m * d - s) -
              ((S ^ m).coeff (m * d - s) - (m : A) * S.coeff (d - s)) := by ring
        exact mem_of_nat_mul_eq hmu
          (Subalgebra.sub_mem _ (hpow (m * d - s) (by omega) (by omega)) hdev) hpivot
  intro j
  rcases lt_trichotomy j d with hj | rfl | hj
  · have hh := hroot (d - j) (by omega) (by omega)
    simpa only [show d - (d - j) = j by omega,
      show m * d - (d - j) = (m - 1) * d + j by omega] using hh
  · rw [← hd, hS.coeff_natDegree]
    exact Subalgebra.one_mem _
  · have hz : S.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz]
    exact Subalgebra.zero_mem _

/-- Square specialization of `coeff_mem_of_monic_pow_schedule`. -/
theorem coeff_mem_of_monic_sq_schedule (V : ℕ → Subalgebra R A) (hV : Antitone V)
    {S : A[X]} {d : ℕ} (hS : S.Monic) (hd : S.natDegree = d) (h2 : IsUnit (2 : R))
    (hsq : ∀ i, d ≤ i → i ≤ 2 * d → (S ^ 2).coeff i ∈ V i) :
    ∀ j, S.coeff j ∈ V (d + j) := by
  have hpow : ∀ i, (2 - 1) * d ≤ i → i ≤ 2 * d → (S ^ 2).coeff i ∈ V i := by
    intro i hi hi2
    exact hsq i (by simpa only [Nat.reduceSubDiff, one_mul] using hi) hi2
  simpa only [Nat.reduceSubDiff, one_mul] using
    coeff_mem_of_monic_pow_schedule V hV hS hd (by norm_num : 1 ≤ 2) h2 hpow

/-- **Relative monic-factor square shell.**  Suppose `Y = S² M + E`, where `M` is a
known monic polynomial of degree `m`, `S` is monic of degree `d`, and the error is zero
strictly above the seam row `m+d`.  From a descending schedule for the rows of `Y`, first
divide by `M` on the top half, then take the monic square root.  The fixed leading row
`m+2d` is not observed.

This is the common decoder for all square blocks in the degree `15`, `27`, and `31`
constructions; there `M` is respectively one of `1`, `X`, and `X+1`. -/
theorem coeff_mem_of_monic_mul_sq_relative (V : ℕ → Subalgebra R A) (hV : Antitone V)
    {M S E Y : A[X]} {m d : ℕ}
    (hM : M.Monic) (hm : M.natDegree = m)
    (hMcoeff : ∀ i t, M.coeff i ∈ V t)
    (hS : S.Monic) (hd : S.natDegree = d) (h2 : IsUnit (2 : R))
    (hYrows : ∀ i, m + d ≤ i → i < m + 2 * d → Y.coeff i ∈ V i)
    (hEz : ∀ i, m + d < i → E.coeff i = 0)
    (hEb : E.coeff (m + d) ∈ V (m + d))
    (hY : Y = S ^ 2 * M + E) :
    ∀ j, S.coeff j ∈ V (m + d + j) := by
  have hAmonic : (S ^ 2).Monic := hS.pow 2
  have hAdeg : (S ^ 2).natDegree = 2 * d := by
    rw [hS.natDegree_pow, hd]
  -- Descending monic division: row `m+i` recovers square coefficient `i`.
  have hA_mem : ∀ fuel i, d ≤ i → i ≤ 2 * d → 2 * d - i ≤ fuel →
      (S ^ 2).coeff i ∈ V (m + i) := by
    intro fuel
    induction fuel with
    | zero =>
        intro i hdi hi2 hf
        have hi : i = 2 * d := by omega
        subst i
        rw [← hAdeg, hAmonic.coeff_natDegree]
        exact Subalgebra.one_mem _
    | succ fuel ih =>
        intro i hdi hi2 hf
        rcases Nat.eq_or_lt_of_le hi2 with hi | hi
        · subst i
          rw [← hAdeg, hAmonic.coeff_natDegree]
          exact Subalgebra.one_mem _
        · set W := V (m + i) with hW
          have hYi : Y.coeff (m + i) ∈ W := hYrows (m + i) (by omega) (by omega)
          have hEi : E.coeff (m + i) ∈ W := by
            rcases eq_or_lt_of_le hdi with rfl | hdi'
            · simpa only using hEb
            · have hz : E.coeff (m + i) = 0 := hEz (m + i) (by omega)
              rw [hz]
              exact Subalgebra.zero_mem _
          have htail : ∑ j ∈ range m, M.coeff j * (S ^ 2).coeff (m + i - j) ∈ W := by
            refine Subalgebra.sum_mem _ fun j hj =>
              Subalgebra.mul_mem _ (hMcoeff j (m + i)) ?_
            have hjm : j < m := mem_range.1 hj
            by_cases hk : 2 * d < m + i - j
            · have hz : (S ^ 2).coeff (m + i - j) = 0 :=
                coeff_eq_zero_of_natDegree_lt (by rw [hAdeg]; exact hk)
              rw [hz]
              exact Subalgebra.zero_mem _
            · push_neg at hk
              have hh := ih (m + i - j) (by omega) hk (by omega)
              exact hV (by omega) hh
          have hrow : Y.coeff (m + i) = (S ^ 2).coeff i +
              ∑ j ∈ range m, M.coeff j * (S ^ 2).coeff (m + i - j) + E.coeff (m + i) := by
            rw [hY, coeff_add, show m + i = M.natDegree + i by omega,
              coeff_mul_monic (S ^ 2) M hM, hm]
          have hkey : (S ^ 2).coeff i = Y.coeff (m + i) -
              ∑ j ∈ range m, M.coeff j * (S ^ 2).coeff (m + i - j) - E.coeff (m + i) := by
            rw [hrow]
            ring
          rw [hkey]
          exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hYi htail) hEi
  have hA : ∀ i, d ≤ i → i ≤ 2 * d → (S ^ 2).coeff i ∈ V (m + i) :=
    fun i hdi hi2 => hA_mem (2 * d - i) i hdi hi2 le_rfl
  let W : ℕ → Subalgebra R A := fun i => V (m + i)
  have hWanti : Antitone W := fun _ _ hij => hV (by omega)
  have hroot := coeff_mem_of_monic_sq_schedule W hWanti hS hd h2
    (fun i hdi hi2 => hA i hdi hi2)
  intro j
  simpa only [W, Nat.add_assoc] using hroot j

/-- **Causal square-gadget shell.**  From

`Y = X*S² + (S+δ)² + E`,

where `E` is supported in degrees at most `d = natDegree S`, recover the coefficient
`S_j` at cutoff `d+j+1` and recover `δ` at cutoff `d`.  The proof first regards the
top rows as the relative shell `(X+1)S²`; the shift contributes only below its seam.
The boundary row then has the explicit slope-two pivot for `δ`.
-/
theorem coeff_mem_of_square_gadget_relative [Nontrivial A]
    (V : ℕ → Subalgebra R A) (hV : Antitone V)
    {S E Y : A[X]} {δ : A} {d : ℕ}
    (hS : S.Monic) (hd : S.natDegree = d) (hd1 : 1 ≤ d) (h2 : IsUnit (2 : R))
    (hYrows : ∀ i, d ≤ i → i < 2 * d + 1 → Y.coeff i ∈ V i)
    (hEz : ∀ i, d < i → E.coeff i = 0) (hEb : E.coeff d ∈ V d)
    (hY : Y = X * S ^ 2 + (S + C δ) ^ 2 + E) :
    (∀ j, S.coeff j ∈ V (d + j + 1)) ∧ δ ∈ V d := by
  have hdiff : (S + C δ) ^ 2 = S ^ 2 + (2 * S * C δ + C δ * C δ) := by
    rw [add_sq]
    ring
  have hshift : ∀ i, d < i → ((S + C δ) ^ 2).coeff i = (S ^ 2).coeff i := by
    intro i hi
    have hSi : S.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hlin : (2 * S * C δ).coeff i = (S.coeff i + S.coeff i) * δ := by
      rw [coeff_mul_C, two_mul, coeff_add]
    have hconst : (C δ * C δ).coeff i = 0 := by
      rw [← map_mul, coeff_C, if_neg (by omega)]
    rw [hdiff, coeff_add, coeff_add, hlin, hSi, hconst]
    ring
  let Etop : A[X] := (S + C δ) ^ 2 - S ^ 2 + E
  have hEtopz : ∀ i, d < i → Etop.coeff i = 0 := by
    intro i hi
    dsimp only [Etop]
    rw [coeff_add, coeff_sub, hshift i hi, hEz i hi]
    ring
  have hXm : (X + 1 : A[X]).Monic := by
    simpa only [C_1] using monic_X_add_C (1 : A)
  have hXd : (X + 1 : A[X]).natDegree = 1 := by
    simpa only [C_1] using natDegree_X_add_C (1 : A)
  have hXcoeff : ∀ i t, (X + 1 : A[X]).coeff i ∈ V t :=
    fun i t => coeff_X_add_one_mem_subalgebra (V t) i
  have htoprows : ∀ i, 1 + d ≤ i → i < 1 + 2 * d → Y.coeff i ∈ V i := by
    intro i hi hit
    exact hYrows i (by omega) (by omega)
  have hboundary : Etop.coeff (1 + d) ∈ V (1 + d) := by
    rw [hEtopz (1 + d) (by omega)]
    exact Subalgebra.zero_mem _
  have hform : Y = S ^ 2 * (X + 1) + Etop := by
    rw [hY]
    dsimp only [Etop]
    ring
  have hrec := coeff_mem_of_monic_mul_sq_relative V hV hXm hXd hXcoeff hS hd h2
    htoprows (fun i hi => hEtopz i (by omega)) hboundary hform
  have hSco : ∀ j, S.coeff j ∈ V (d + j + 1) := by
    intro j
    simpa only [show 1 + d + j = d + j + 1 by omega] using hrec j
  have hSsq : ∀ j, (S ^ 2).coeff j ∈ V (j + 1) := by
    refine coeff_sq_mem_of_schedule V hV (P := S) (d := d) (e := 1)
      (le_of_eq hd) ?_
    intro i
    simpa only [show i + d + 1 = d + i + 1 by omega] using hSco i
  have hXm1 : (X * S ^ 2).coeff d = (S ^ 2).coeff (d - 1) := by
    obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [he, coeff_X_mul]
    congr 1
  have hSd : S.coeff d = 1 := by rw [← hd, hS.coeff_natDegree]
  have hshiftd : ((S + C δ) ^ 2).coeff d = (S ^ 2).coeff d + (1 + 1) * δ := by
    have hlin : (2 * S * C δ).coeff d = (S.coeff d + S.coeff d) * δ := by
      rw [coeff_mul_C, two_mul, coeff_add]
    have hconst : (C δ * C δ).coeff d = 0 := by
      rw [← map_mul, coeff_C, if_neg (by omega)]
    rw [hdiff, coeff_add, coeff_add, hlin, hconst, hSd]
    ring
  have hrow : Y.coeff d = (S ^ 2).coeff (d - 1) + (S ^ 2).coeff d +
      (1 + 1) * δ + E.coeff d := by
    rw [hY, coeff_add, coeff_add, hXm1, hshiftd]
    ring
  have hSm1 : (S ^ 2).coeff (d - 1) ∈ V d := by
    simpa only [show d - 1 + 1 = d by omega] using hSsq (d - 1)
  have hSdmem : (S ^ 2).coeff d ∈ V d := hV (by omega) (hSsq d)
  have hYd : Y.coeff d ∈ V d := hYrows d le_rfl (by omega)
  have htwoδ : 2 * δ ∈ V d := by
    have hkey : 2 * δ = Y.coeff d - (S ^ 2).coeff (d - 1) -
        (S ^ 2).coeff d - E.coeff d := by
      rw [hrow]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _
      (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hYd hSm1) hSdmem) hEb
  exact ⟨hSco, mem_of_two_mul_eq h2 htwoδ rfl⟩

/-- Causal recovery from the most common shell `(X+1)S²+E`, specialized to the
visible rows `range (2d+1)`.  The omitted coefficient in degree `2d+1` is the fixed monic
leading coefficient. -/
theorem coeff_mem_of_X_add_one_mul_sq [Nontrivial A]
    (K : Subalgebra R A) {S E Φ : A[X]} {d : ℕ}
    (hS : S.Monic) (hd : S.natDegree = d) (h2 : IsUnit (2 : R))
    (hEz : ∀ i, d + 1 < i → E.coeff i = 0) (hEb : E.coeff (d + 1) ∈ K)
    (hΦ : Φ = (X + 1) * S ^ 2 + E) :
    ∀ j, S.coeff j ∈ Vis R K Φ (range (2 * d + 1)) (d + j + 1) := by
  let V : ℕ → Subalgebra R A := fun t => Vis R K Φ (range (2 * d + 1)) t
  have hV : Antitone V := fun _ _ hij => Vis_antitone_cutoff hij
  have hXm : (X + 1 : A[X]).Monic := by
    simpa only [C_1] using monic_X_add_C (1 : A)
  have hXd : (X + 1 : A[X]).natDegree = 1 := by
    simpa only [C_1] using natDegree_X_add_C (1 : A)
  have hXcoeff : ∀ i t, (X + 1 : A[X]).coeff i ∈ V t :=
    fun i t => coeff_X_add_one_mem_subalgebra (V t) i
  have hrows : ∀ i, 1 + d ≤ i → i < 1 + 2 * d → Φ.coeff i ∈ V i := by
    intro i _ hi
    exact coeff_mem_Vis (mem_range.2 (by omega)) le_rfl
  have hboundary : E.coeff (1 + d) ∈ V (1 + d) := by
    exact known_mem_Vis (by simpa only [Nat.add_comm] using hEb)
  have hform : Φ = S ^ 2 * (X + 1) + E := by
    rw [hΦ]
    ring
  have hrec := coeff_mem_of_monic_mul_sq_relative V hV hXm hXd hXcoeff hS hd h2
    hrows (by intro i hi; exact hEz i (by omega)) hboundary hform
  intro j
  simpa only [V, show 1 + d + j = d + j + 1 by omega] using hrec j

theorem coeff_X_mul_of_pos {P : A[X]} {i : ℕ} (hi : 1 ≤ i) :
    (X * P).coeff i = P.coeff (i - 1) := by
  conv_lhs => rw [show i = (i - 1) + 1 from by omega]
  rw [coeff_X_mul]

end FastPoly
