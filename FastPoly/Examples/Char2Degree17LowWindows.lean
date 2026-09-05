import FastPoly.Examples.Char2Degree17EPivot

/-! Local windows needed by the last two supplied Frobenius pivots.
The septic and sextic remain opaque: only rows 10, 9, and 8 of their product
and rows 3, 2, and 1 of the small factor product are read. -/
namespace FastPoly.Char2Degree17LowWindows

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TerminalFrame Char2Degree17TerminalPivots Char2Degree17Q8Pivot
open Char2Degree17HighFrame Char2Degree17HighSignature Char2Degree17RRow
open Char2Degree17Q0Pivot Char2Degree17EPivot

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem mul76_coeff10 (p q : R[X]) (hp : IsMonicOfDegree p 7) (hq : IsMonicOfDegree q 6) :
    (p * q).coeff 10 = p.coeff 4 + p.coeff 5 * q.coeff 5 + p.coeff 6 * q.coeff 4 + q.coeff 3 := by
  have hp8 : p.coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 8))
  have hp9 : p.coeff 9 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 9))
  have hp10 : p.coeff 10 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 10))
  have hq7 : q.coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 7))
  have hq8 : q.coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 8))
  have hq9 : q.coeff 9 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 9))
  have hq10 : q.coeff 10 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 10))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    hp8, hp9, hp10, hq7, hq8, hq9, hq10, monic_row hp, monic_row hq,
    zero_mul, mul_zero, mul_one, one_mul, add_zero, zero_add]

theorem mul76_coeff9 (p q : R[X]) (hp : IsMonicOfDegree p 7) (hq : IsMonicOfDegree q 6) :
    (p * q).coeff 9 = p.coeff 3 + p.coeff 4 * q.coeff 5 + p.coeff 5 * q.coeff 4 + p.coeff 6 * q.coeff 3 + q.coeff 2 := by
  have hp8 : p.coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 8))
  have hp9 : p.coeff 9 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 9))
  have hq7 : q.coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 7))
  have hq8 : q.coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 8))
  have hq9 : q.coeff 9 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 9))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    hp8, hp9, hq7, hq8, hq9, monic_row hp, monic_row hq,
    zero_mul, mul_zero, mul_one, one_mul, add_zero, zero_add]

theorem mul76_coeff8 (p q : R[X]) (hp : IsMonicOfDegree p 7) (hq : IsMonicOfDegree q 6) :
    (p * q).coeff 8 = p.coeff 2 + p.coeff 3 * q.coeff 5 + p.coeff 4 * q.coeff 4 + p.coeff 5 * q.coeff 3 + p.coeff 6 * q.coeff 2 + q.coeff 1 := by
  have hp8 : p.coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 8))
  have hq7 : q.coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 7))
  have hq8 : q.coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 8))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    hp8, hq7, hq8, monic_row hp, monic_row hq,
    zero_mul, mul_zero, mul_one, one_mul, add_zero, zero_add]

theorem small_coeff1 (p q : R[X]) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub, zero_add]

theorem small_coeff2 (p q : R[X]) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 +
      p.coeff 2 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub, zero_add]

theorem small_coeff3 (p q : R[X]) :
    (p * q).coeff 3 = p.coeff 0 * q.coeff 3 + p.coeff 1 * q.coeff 2 +
      p.coeff 2 * q.coeff 1 + p.coeff 3 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub, zero_add]

noncomputable def K (q : Vector R) : R := (av q).1 + (au q).1
noncomputable def T (q : Vector R) : R := (uHigher q).coeff 0
noncomputable def c (q : Vector R) : R := (au q).2 + (av q).2
noncomputable def D (q : Vector R) : R :=
  E q + (B q).coeff 0 + q 2 + q 1 ^ 2 + q 1 * q 3

theorem uHigher_row1 (q : Vector R) : (uHigher q).coeff 1 = q 2 + q 4 := by
  have ht : (dt q).coeff 1 = q 4 := congrArg Prod.snd (t_rows q)
  simp only [uHigher, coeff_add, coeff_C, one_ne_zero, ite_false, add_zero, z_row1, ht]

theorem S6_row3 (q : Vector R) : (S6 q).coeff 3 =
    (q 0 + 1) * (q 1 + q 3) + (q 2 + q 4) + c q := by
  have hz : (sLower q).coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((sLower_monic q).natDegree_eq ▸ (by omega : 2 < 3))
  rw [S6_eq, coeff_add, small_coeff3, uHigher_row3, mul_zero, zero_add,
    sLower_row1, monic_row (sLower_monic q), uHigher_row2, uHigher_row1,
    hz, zero_mul, one_mul, add_zero]
  simp only [sCorrection, coeff_C_mul, monic_row (B_monic q), mul_one, c]

theorem S6_row2 (q : Vector R) : (S6 q).coeff 2 =
    K q * (q 1 + q 3) + (q 0 + 1) * (q 2 + q 4) + T q + c q * q 1 := by
  rw [S6_eq, coeff_add, small_coeff2, sLower_row0, sLower_row1,
    monic_row (sLower_monic q), uHigher_row2, uHigher_row1, one_mul]
  simp only [sCorrection, coeff_C_mul, B_row2, K, T, c]

theorem S6_row1 (q : Vector R) : (S6 q).coeff 1 =
    K q * (q 2 + q 4) + (q 0 + 1) * T q + c q * (q 2 + 1) := by
  rw [S6_eq, coeff_add, small_coeff1, sLower_row0, sLower_row1, uHigher_row1]
  simp only [sCorrection, coeff_C_mul, B_row1, K, T, c]

theorem uLower_row0 (q : Vector R) : (uLower q).coeff 0 = K q + (B q).coeff 0 := by
  have hb : (B q).coeff 0 = (dz q).coeff 0 + (av q).1 := by
    simp only [B, coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
  rw [hb]
  simp only [uLower, coeff_add, y_row0, coeff_C_zero, zero_add, K,
    add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left, add_zero]

theorem u_row3 (q : Vector R) : (du q).coeff 3 = q 6 :=
  congrArg Prod.snd (u_rows q)

theorem u_row3_window (q : Vector R) : q 6 =
    (q 0 + q 2) * (q 1 + q 3) + (1 + q 1) * (q 2 + q 4) + T q := by
  rw [← u_row3 q]
  change (uLower q * uHigher q).coeff 3 = _
  rw [small_coeff3, uHigher_row3, mul_zero, zero_add, uLower_row1,
    uLower_row2, monic_row (uLower_monic q), one_mul, uHigher_row2, uHigher_row1]
  rfl

theorem T_eq (q : Vector R) : T q =
    q 6 + (q 0 + q 2) * (q 1 + q 3) + (q 1 + 1) * (q 2 + q 4) := by
  rw [u_row3_window q]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero,
    CharTwo.add_cancel_left, zero_add, add_zero]

theorem A_row3 (q : Vector R) : (A q).coeff 3 = q 6 := by
  have hn : (1 : ℕ) ≠ 3 := by omega
  simp only [A, coeff_add, coeff_X, hn, ite_false, zero_add, u_row3]

theorem A_row2 (q : Vector R) : (A q).coeff 2 =
    (K q + (B q).coeff 0) * (q 1 + q 3) +
      (q 0 + q 2) * (q 2 + q 4) + (1 + q 1) * T q := by
  have hn : (1 : ℕ) ≠ 2 := by omega
  simp only [A, coeff_add, coeff_X, hn, ite_false, zero_add]
  change (uLower q * uHigher q).coeff 2 = _
  rw [small_coeff2, uLower_row0, uLower_row1, uLower_row2,
    uHigher_row2, uHigher_row1]
  rfl

theorem S4_eq (q : Vector R) : (S6 q).coeff 4 = q 5 ^ 2 + D q := by
  have h := E_row4 q
  change q 5 ^ 2 + (S6 q).coeff 4 = D q at h
  rw [← h, CharTwo.add_cancel_left]

theorem K_eq (q : Vector R) : K q = q 5 ^ 2 + D q + (q 1 + q 3) := by
  have h := S6_row4 q
  change (S6 q).coeff 4 = K q + (q 1 + q 3) at h
  rw [← S4_eq, h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem q4_eq (q : Vector R) : q 4 = E q + q 5 ^ 2 + q 5 := by
  simp only [E, add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero,
    CharTwo.add_cancel_left, add_zero, zero_add]

theorem outputQ_middle (q : Vector R) (j : ℕ) (hj : 7 < j) :
    (outputQ q).coeff j = (high q).coeff j + (aw q).1 * (du q + dv q).coeff j := by
  have hjm : IsMonicOfDegree (dj q) 3 := by simpa only [j_keys] using j_monic (keys q)
  have hlm : IsMonicOfDegree (dell q) 7 := by simpa only [ell_keys] using ell_monic (keys q)
  have hjz : (dj q).coeff j = 0 := coeff_eq_zero_of_natDegree_lt (hjm.natDegree_eq ▸ (by omega : 3 < j))
  have hlz : (dell q).coeff j = 0 := coeff_eq_zero_of_natDegree_lt (hlm.natDegree_eq ▸ hj)
  have haz : (A q).coeff j = 0 := coeff_eq_zero_of_natDegree_lt ((A_monic q).natDegree_eq ▸ hj)
  have hne : j ≠ 0 := by omega
  rw [outputQ_split]
  simp only [coeff_add, correction, coeff_C_mul, coeff_C, hjz, hlz, haz,
    hne, ite_false, mul_zero, zero_add, add_zero]

theorem AB_row (q : Vector R) (j : ℕ) :
    (A q * B q).coeff (j + 3) = (A q).coeff j + (A q).coeff (j + 1) * q 1 +
      (A q).coeff (j + 2) * (q 2 + 1) + (A q).coeff (j + 3) * (B q).coeff 0 := by
  conv_lhs => rw [B_form]
  exact cubic_product_row _ _ _ _ j

theorem H_row9 (q : Vector R) : (du q + dv q).coeff 9 = 1 := by
  have hs : (S6 q).coeff 9 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((S6_monic q).natDegree_eq ▸ (by omega : 6 < 9))
  have h8 : (A q).coeff 8 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((A_monic q).natDegree_eq ▸ (by omega : 7 < 8))
  have h9 : (A q).coeff 9 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((A_monic q).natDegree_eq ▸ (by omega : 7 < 9))
  have hb := AB_row q 6
  simp only [Nat.reduceAdd] at hb
  rw [higher_eq, coeff_add, hs, add_zero, hb, A_row6, monic_row (A_monic q),
    h8, h9, one_mul, zero_mul, add_zero]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_mul, add_zero, zero_add]

theorem H_row8 (q : Vector R) : (du q + dv q).coeff 8 =
    ((q 0 + q 2) + (q 1 + q 3)) + (q 1 + 1) * q 1 + (q 2 + 1) := by
  have hs : (S6 q).coeff 8 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((S6_monic q).natDegree_eq ▸ (by omega : 6 < 8))
  have h8 : (A q).coeff 8 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((A_monic q).natDegree_eq ▸ (by omega : 7 < 8))
  have hb := AB_row q 5
  simp only [Nat.reduceAdd] at hb
  rw [higher_eq, coeff_add, hs, add_zero, hb, A_row5, A_row6,
    monic_row (A_monic q), h8, one_mul, zero_mul, add_zero]

theorem a14_eq (q : Vector R) : (aw q).1 = q 14 + (high q).coeff 10 := by
  change q 14 + (A q * (du q + dv q)).coeff 10 = _
  have h : A q * (du q + dv q) = high q := by rw [higher_eq]; unfold high; ring
  rw [h]

end FastPoly.Char2Degree17LowWindows
