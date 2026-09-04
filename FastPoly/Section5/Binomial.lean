import FastPoly.Polynomial.TopWindow
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Binomial expansion with degree control

The engine for `lem:Rk2l`(2) and the `R-top-two` invariant: expanding `(P + E)^m` as the
principal part `P^m + m•(E·P^{m-1})` plus a tail of controlled degree.  The paper uses
this with `P` a power `H^2` (or `H̃^2`) and `E = -S₁² + S₂` the first-order correction.
-/

namespace FastPoly

open Polynomial Finset

variable {A : Type*} [CommRing A]

/-- The `q ≥ 2` tail of the binomial expansion of `(P + E)^m`. -/
noncomputable def binTail (P E : A[X]) (m : ℕ) : A[X] :=
  ∑ q ∈ Finset.Icc 2 m, E ^ q * P ^ (m - q) * (m.choose q : A[X])

/-- Exact first-order binomial expansion. -/
theorem pow_add_eq (P E : A[X]) {m : ℕ} (hm : 1 ≤ m) :
    (P + E) ^ m = P ^ m + m • (E * P ^ (m - 1)) + binTail P E m := by
  rw [add_comm P E, add_pow]
  have hsplit : Finset.range (m + 1) = insert 0 (insert 1 (Finset.Icc 2 m)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_Icc]),
    Finset.sum_insert (by simp [Finset.mem_Icc])]
  unfold binTail
  simp only [pow_zero, pow_one, one_mul, Nat.sub_zero, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_one, mul_one, nsmul_eq_mul]
  ring

/-- The tail vanishes for `m < 2`. -/
theorem binTail_eq_zero (P E : A[X]) {m : ℕ} (hm : m < 2) : binTail P E m = 0 := by
  unfold binTail
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-- Degree bound for the tail: with `deg E ≤ e ≤ p` and `deg P ≤ p`, every `q ≥ 2`
summand has degree at most `2e + (m-2)p`. -/
theorem natDegree_binTail_le {P E : A[X]} {p e : ℕ} (hP : P.natDegree ≤ p)
    (hE : E.natDegree ≤ e) (hep : e ≤ p) (m : ℕ) :
    (binTail P E m).natDegree ≤ 2 * e + (m - 2) * p := by
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro q hq
  obtain ⟨h2q, hqm⟩ := Finset.mem_Icc.1 hq
  have h1 : (E ^ q).natDegree ≤ q * e :=
    le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hE)
  have h2 : (P ^ (m - q)).natDegree ≤ (m - q) * p :=
    le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hP)
  have h3 : ((m.choose q : A[X])).natDegree = 0 := natDegree_natCast _
  have h5 : (E ^ q * P ^ (m - q)).natDegree ≤ q * e + (m - q) * p :=
    le_trans natDegree_mul_le (Nat.add_le_add h1 h2)
  have h4 : (E ^ q * P ^ (m - q) * (m.choose q : A[X])).natDegree
      ≤ q * e + (m - q) * p := by
    refine le_trans natDegree_mul_le ?_
    omega
  refine le_trans h4 ?_
  have key : (q - 2) * e ≤ (q - 2) * p := Nat.mul_le_mul_left _ hep
  have e1 : q * e = 2 * e + (q - 2) * e := by
    have hq2 : q = 2 + (q - 2) := by omega
    calc q * e = (2 + (q - 2)) * e := by rw [← hq2]
    _ = 2 * e + (q - 2) * e := by ring
  have e2 : (q - 2) * p + (m - q) * p = (m - 2) * p := by
    have h6 : q - 2 + (m - q) = m - 2 := by omega
    calc (q - 2) * p + (m - q) * p = (q - 2 + (m - q)) * p := by ring
    _ = (m - 2) * p := by rw [h6]
  omega

/-- Subleading coefficient of a monic power: `[x^{nD-1}] H^n = n·[x^{D-1}] H`. -/
theorem Monic.pow_coeff_sub_one {H : A[X]} (hH : H.Monic) {D : ℕ}
    (hD : H.natDegree = D) (h1 : 1 ≤ D) :
    ∀ n, 1 ≤ n → (H ^ n).coeff (n * D - 1) = n • H.coeff (D - 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [pow_one, show 1 * D - 1 = D - 1 from by omega, one_nsmul]
  | succ n hn ih =>
    have hpm : (H ^ n).Monic := hH.pow n
    have hpd : (H ^ n).natDegree = n * D := by
      rw [hH.natDegree_pow, hD]
    have h1nd : 1 ≤ n * D := Nat.mul_pos (by omega) (by omega)
    have hd1 : (n + 1) * D = n * D + D := by ring
    have hcm := coeff_mul_monic (H ^ n) H hH (n * D - 1)
    rw [hD] at hcm
    have hidx2 : (n + 1) * D - 1 = D + (n * D - 1) := by omega
    have hsum : ∑ j ∈ Finset.range D, H.coeff j * (H ^ n).coeff (D + (n * D - 1) - j)
        = H.coeff (D - 1) := by
      rw [Finset.sum_eq_single_of_mem (D - 1) (Finset.mem_range.2 (by omega))]
      · have hidx : D + (n * D - 1) - (D - 1) = n * D := by omega
        have hlead : (H ^ n).coeff (n * D) = 1 := by
          rw [← hpd]
          exact hpm.coeff_natDegree
        rw [hidx, hlead, mul_one]
      · intro j hj hne
        have hjr := Finset.mem_range.1 hj
        have hz : (H ^ n).coeff (D + (n * D - 1) - j) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hpd]; omega)
        rw [hz, mul_zero]
    rw [pow_succ, hidx2, hcm, hsum, ih, succ_nsmul]

/-- Top two coefficients of `low - S²` for `S` monic of degree `r ≥ 1` and `low` of
degree at most `2r - 2`: degree `≤ 2r`, leading `-1`, subleading `-2·[x^{r-1}]S`. -/
theorem low_sub_sq_top {S low : A[X]} {r : ℕ} (hS : S.Monic) (hSd : S.natDegree = r)
    (h1 : 1 ≤ r) (hlow : low.natDegree ≤ 2 * r - 2) :
    (low - S ^ 2).natDegree ≤ 2 * r ∧
    (low - S ^ 2).coeff (2 * r) = -1 ∧
    (low - S ^ 2).coeff (2 * r - 1) = -(2 • S.coeff (r - 1)) := by
  have hsqm : (S ^ 2).Monic := hS.pow 2
  have hsqd : (S ^ 2).natDegree = 2 * r := by rw [hS.natDegree_pow, hSd]
  have hsub : (S ^ 2).coeff (2 * r - 1) = 2 • S.coeff (r - 1) :=
    FastPoly.Monic.pow_coeff_sub_one hS hSd h1 2 (by omega)
  have hz1 : low.coeff (2 * r) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hz2 : low.coeff (2 * r - 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hlead : (S ^ 2).coeff (2 * r) = 1 := by
    rw [← hsqd]
    exact hsqm.coeff_natDegree
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (natDegree_sub_le _ _) (max_le (by omega) (le_of_eq hsqd))
  · rw [coeff_sub, hz1, hlead]
    ring
  · rw [coeff_sub, hz2, hsub]
    ring

/-- Subleading coefficient of a product of monics:
`[x^{p+q-1}](P·Q) = [x^{p-1}]P + [x^{q-1}]Q`. -/
theorem monic_mul_coeff_sub_one {P Q : A[X]} (hP : P.Monic) (hQ : Q.Monic)
    {p q : ℕ} (hp : P.natDegree = p) (hq : Q.natDegree = q)
    (hp1 : 1 ≤ p) (hq1 : 1 ≤ q) :
    (P * Q).coeff (p + q - 1) = P.coeff (p - 1) + Q.coeff (q - 1) := by
  have hcm := coeff_mul_monic P Q hQ (p - 1)
  rw [hq] at hcm
  have hidx : p + q - 1 = q + (p - 1) := by omega
  have hsum : ∑ j ∈ Finset.range q, Q.coeff j * P.coeff (q + (p - 1) - j)
      = Q.coeff (q - 1) := by
    rw [Finset.sum_eq_single_of_mem (q - 1) (Finset.mem_range.2 (by omega))]
    · have hix : q + (p - 1) - (q - 1) = p := by omega
      have hlead : P.coeff p = 1 := by
        rw [← hp]
        exact hP.coeff_natDegree
      rw [hix, hlead, mul_one]
    · intro j hj hne
      have hjr := Finset.mem_range.1 hj
      have hz : P.coeff (q + (p - 1) - j) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hp]; omega)
      rw [hz, mul_zero]
  rw [hidx, hcm, hsum]

end FastPoly
