import FastPoly.Examples.Char2Degree17Q0Pivot

/-!
# The normalized E / row-eleven unit pivot

Two small product windows recover the sextic's row four and the known
offset sum a7+a5. Their characteristic-two cancellation isolates
E=Q4+Q5^2+Q5. Every tail quantity is already read before E in decoder order.
-/

namespace FastPoly.Char2Degree17EPivot

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TerminalFrame Char2Degree17TerminalPivots Char2Degree17Q8Pivot
open Char2Degree17HighFrame Char2Degree17HighSignature Char2Degree17RRow
open Char2Degree17TriangularCoordinates Char2Degree17LeadingInverse Char2Degree17Q0Pivot

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem mul24_coeff4 (p q : R[X]) (hp : IsMonicOfDegree p 2) (hq : IsMonicOfDegree q 4) :
    (p * q).coeff 4 = p.coeff 0 + p.coeff 1 * q.coeff 3 + q.coeff 2 := by
  have hp3 : p.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 2 < 3))
  have hp4 : p.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 2 < 4))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    hp3, hp4, monic_row hp, monic_row hq, zero_mul, mul_one, one_mul, add_zero, zero_add]

theorem mul34_coeff4 (p q : R[X]) (hp : IsMonicOfDegree p 3) (hq : IsMonicOfDegree q 4) :
    (p * q).coeff 4 = p.coeff 0 + p.coeff 1 * q.coeff 3 +
      p.coeff 2 * q.coeff 2 + q.coeff 1 := by
  have hp4 : p.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 3 < 4))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    hp4, monic_row hp, monic_row hq, zero_mul, mul_one, one_mul, add_zero, zero_add]

theorem y_row0 (q : Vector R) : (dy q).coeff 0 = 0 := coeff_X_mul_zero _

theorem sLower_row0 (q : Vector R) : (sLower q).coeff 0 = (av q).1 + (au q).1 := by
  simp only [sLower, coeff_add, coeff_X_zero, y_row0, coeff_C_zero, zero_add]

theorem S6_row4 (q : Vector R) : (S6 q).coeff 4 = ((av q).1 + (au q).1) + (q 1 + q 3) := by
  have hz : (sCorrection q).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((sCorrection_degree q).trans_lt (by omega))
  rw [S6_eq, coeff_add, hz, add_zero,
    mul24_coeff4 _ _ (sLower_monic q) (uHigher_monic q),
    uHigher_row3, mul_zero, add_zero, uHigher_row2, sLower_row0]

theorem u_baseline_row4 (q : Vector R) :
    ((dy q + dz q) * (dz q + dt q)).coeff 4 =
      (dz q).coeff 0 + (1 + q 1) * (q 1 + q 3) + (q 2 + q 4) := by
  have hl : IsMonicOfDegree (dy q + dz q) 3 := add_monic (frame_y_monic q) (frame_z_monic q) (by omega)
  have hh : IsMonicOfDegree (dz q + dt q) 4 := add_monic (frame_z_monic q) (frame_t_monic q) (by omega)
  have h3 : (dz q + dt q).coeff 3 = 0 := by
    rw [coeff_add, monic_row (frame_z_monic q), Char2Degree17Q9Pivot.t_coeff_three, CharTwo.add_self_eq_zero]
  have h4 : (dt q).coeff 1 = q 4 := congrArg Prod.snd (t_rows q)
  rw [mul34_coeff4 _ _ hl hh, h3, mul_zero, add_zero]
  simp only [coeff_add, y_row0, monic_row (frame_y_monic q), z_row2,
    z_row1, Char2Degree17Q9Pivot.t_coeff_two, h4, zero_add]

theorem a5_eq (q : Vector R) : (au q).1 = q 5 +
    ((dz q).coeff 0 + (1 + q 1) * (q 1 + q 3) + (q 2 + q 4)) := by
  change q 5 + ((dy q + dz q) * (dz q + dt q)).coeff 4 = _
  rw [u_baseline_row4]

private theorem offset_reorder (a7 z0 q5 q1 q2 q3 q4 : R) :
    a7 + (q5 + (z0 + (1 + q1) * (q1 + q3) + (q2 + q4))) =
      (z0 + a7) + q5 + (q1 + 1) * (q1 + q3) + q2 + q4 := by ring

theorem offset_sum (q : Vector R) : (av q).1 + (au q).1 =
    (B q).coeff 0 + q 5 + (q 1 + 1) * (q 1 + q 3) + q 2 + q 4 := by
  have hb : (B q).coeff 0 = (dz q).coeff 0 + (av q).1 := by
    simp only [B, coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
  rw [a5_eq, hb]
  exact offset_reorder _ _ _ _ _ _ _

def E (q : Vector R) : R := q 4 + q 5 ^ 2 + q 5

private theorem scalar_E (a b c d e t : R) :
    e ^ 2 + ((t + e + (a + 1) * (a + c) + b + d) + (a + c)) =
      (d + e ^ 2 + e) + t + b + a ^ 2 + a * c := by
  simp only [mul_add, add_mul, one_mul, pow_two, add_assoc, add_comm,
    add_left_comm, CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem E_row4 (q : Vector R) : q 5 ^ 2 + (S6 q).coeff 4 =
    E q + (B q).coeff 0 + q 2 + q 1 ^ 2 + q 1 * q 3 := by
  rw [S6_row4, offset_sum]
  exact scalar_E _ _ _ _ _ _

theorem mul76_coeff11 (p q : R[X]) (hp : IsMonicOfDegree p 7) (hq : IsMonicOfDegree q 6) :
    (p * q).coeff 11 = p.coeff 5 + p.coeff 6 * q.coeff 5 + q.coeff 4 := by
  have hp8 : p.coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 8))
  have hp9 : p.coeff 9 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 9))
  have hp10 : p.coeff 10 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 10))
  have hp11 : p.coeff 11 = 0 := coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ (by omega : 7 < 11))
  have hq7 : q.coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 7))
  have hq8 : q.coeff 8 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 8))
  have hq9 : q.coeff 9 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 9))
  have hq10 : q.coeff 10 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 10))
  have hq11 : q.coeff 11 = 0 := coeff_eq_zero_of_natDegree_lt (hq.natDegree_eq ▸ (by omega : 6 < 11))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
    hp8, hp9, hp10, hp11, hq7, hq8, hq9, hq10, hq11, monic_row hp, monic_row hq,
    zero_mul, mul_zero, mul_one, one_mul, add_zero, zero_add]

theorem AS6_row11 (q : Vector R) : (A q * S6 q).coeff 11 =
    ((q 0 + q 2) + (q 1 + q 3)) + (q 1 + 1) * (q 0 + 1) + (S6 q).coeff 4 := by
  rw [mul76_coeff11 _ _ (A_monic q) (S6_monic q), A_row5, A_row6, S6_row5]

private theorem collect_E (c t a b s : R) : c + t + (a + b + s) = (c + s) + t + a + b := by ring

theorem outputQ_row11 (q : Vector R) :
    (outputQ q).coeff 11 = E q + (B q).coeff 0 + q 2 + q 1 ^ 2 + q 1 * q 3 +
      ((q 0 + q 2) + (q 1 + q 3)) ^ 2 * (q 2 + 1) +
        ((q 0 + q 2) + (q 1 + q 3)) + (q 1 + 1) * (q 0 + 1) := by
  have hb := squareB_row q 8
  simp only [Nat.reduceAdd] at hb
  have h8 : (A q ^ 2).coeff 8 = q 5 ^ 2 := by
    have hh : (A q ^ 2).coeff 8 = (A q).coeff 4 ^ 2 :=
      Char2Degree19Crown.square_coeff_even (A q) 4
    rw [A_row4] at hh
    exact hh
  have h9 : (A q ^ 2).coeff 9 = 0 := Char2Degree19Crown.square_coeff_odd (A q) 4
  rw [outputQ_coeff_high q 11 (by omega), high, coeff_add, hb, h8, h9,
    squareA_row10, squareA_row11, AS6_row11]
  simp only [zero_mul, add_zero]
  rw [collect_E, E_row4]

theorem normalized_E (z : Vector R) : E (qOfZ z) = z 5 := by
  change (z 5 + (z 8 ^ 2 + z 8)) + z 8 ^ 2 + z 8 = z 5
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

def eTail (a b s r t : R) : R :=
  (r + bTail a b s) + b + a ^ 2 + a * (s + t) +
    (s + (b + a)) ^ 2 * (b + 1) + (s + (b + a)) + (a + 1) * (t + 1)

private theorem eTail_collect (e a b s r t : R) :
    e + (r + bTail a b s) + b + a ^ 2 + a * (s + t) +
      (s + (b + a)) ^ 2 * (b + 1) + (s + (b + a)) + (a + 1) * (t + 1) =
        e + eTail a b s r t := by
  simp only [eTail, add_assoc]

theorem outputZ_row11 (z : Vector R) :
    (outputZ z).coeff 11 = z 5 + eTail (z 0) (z 1) (z 2) (z 3) (z 4) := by
  change (outputQ (qOfZ z)).coeff 11 = _
  rw [outputQ_row11, normalized_E, normalized_B0, normalized_A5]
  change z 5 + (z 3 + bTail (z 0) (z 1) (z 2)) + z 1 + z 0 ^ 2 + z 0 * (z 2 + z 4) +
    (z 2 + (z 1 + z 0)) ^ 2 * (z 1 + 1) + (z 2 + (z 1 + z 0)) +
      (z 0 + 1) * (z 4 + 1) = _
  exact eTail_collect (z 5) (z 0) (z 1) (z 2) (z 3) (z 4)

def eEquiv (a b s r t : R) : R ≃ R := Char2Decoder.unitPivot (eTail a b s r t)

theorem decode_actual_E (z : Vector R) :
    (eEquiv (z 0) (z 1) (z 2) (z 3) (z 4)).symm ((outputZ z).coeff 11) = z 5 := by
  rw [outputZ_row11]
  exact (eEquiv (z 0) (z 1) (z 2) (z 3) (z 4)).symm_apply_apply (z 5)

theorem row11_congr (z w : Vector R) (he : ∀ i : Fin 17, i.val ≤ 5 → z i = w i) :
    (outputZ z).coeff 11 = (outputZ w).coeff 11 := by
  rw [outputZ_row11, outputZ_row11, he 0 (by omega), he 1 (by omega),
    he 2 (by omega), he 3 (by omega), he 4 (by omega), he 5 (by omega)]

theorem row11_future (z : Vector R) (j : Fin 17) (δ : R) (hj : 5 < j.val) :
    (outputZ (shift z j δ)).coeff 11 = (outputZ z).coeff 11 := by
  apply row11_congr
  intro i hi
  have hne : i ≠ j := by intro h; have hv := congrArg Fin.val h; omega
  exact shift_other z j i δ hne

end FastPoly.Char2Degree17EPivot
