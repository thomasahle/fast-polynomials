import FastPoly.Examples.Char2Degree17LeadingInverse

/-!
# The normalized Q0 / row-twelve unit pivot

Only the next-to-leading rows of two monic products are read. The factored
sextic has row five Q0+1; this isolates Q0 in `A^2*B+A*S6`. The displayed
scalar decoder is the unit translation by the named earlier-coordinate tail.
-/

namespace FastPoly.Char2Degree17Q0Pivot

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TerminalFrame Char2Degree17TerminalPivots Char2Degree17Q8Pivot
open Char2Degree17HighFrame Char2Degree17HighSignature Char2Degree17RRow
open Char2Degree17TriangularCoordinates Char2Degree17LeadingInverse

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem next_product_row (p q : R[X]) (d e : ℕ)
    (hp : IsMonicOfDegree p d) (hq : IsMonicOfDegree q e) (hd : 0 < d) (he : 0 < e) :
    (p * q).coeff (d + e - 1) = p.coeff (d - 1) + q.coeff (e - 1) := by
  have hm := hp.mul hq
  have hdp : 0 < p.natDegree := hp.natDegree_eq ▸ hd
  have hdq : 0 < q.natDegree := hq.natDegree_eq ▸ he
  have hdm : 0 < (p * q).natDegree := by rw [hm.natDegree_eq]; omega
  have hh := hp.monic.nextCoeff_mul hq.monic
  rw [nextCoeff_of_natDegree_pos hdm, nextCoeff_of_natDegree_pos hdp,
    nextCoeff_of_natDegree_pos hdq, hm.natDegree_eq, hp.natDegree_eq, hq.natDegree_eq] at hh
  exact hh

noncomputable def sLower (q : Vector R) : R[X] := X + dy q + C ((av q).1 + (au q).1)
noncomputable def sCorrection (q : Vector R) : R[X] := C ((au q).2 + (av q).2) * B q

theorem S6_eq (q : Vector R) : S6 q = sLower q * uHigher q + sCorrection q := rfl

theorem sLower_monic (q : Vector R) : IsMonicOfDegree (sLower q) 2 :=
  shifted_monic (add_monic (isMonicOfDegree_X R) (frame_y_monic q) (by omega))
    (by omega) ((av q).1 + (au q).1)

theorem sLower_row1 (q : Vector R) : (sLower q).coeff 1 = q 0 + 1 := by
  simp only [sLower, coeff_add, coeff_X, coeff_C, ite_true, one_ne_zero,
    ite_false, y_row1, add_zero]
  exact add_comm _ _

theorem sCorrection_degree (q : Vector R) : (sCorrection q).natDegree ≤ 3 :=
  (natDegree_C_mul_le _ _).trans (B_monic q).natDegree_eq.le

theorem S6_row5 (q : Vector R) : (S6 q).coeff 5 = q 0 + 1 := by
  have hz : (sCorrection q).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((sCorrection_degree q).trans_lt (by omega))
  have hp : (sLower q * uHigher q).coeff 5 = (sLower q).coeff 1 + (uHigher q).coeff 3 :=
    next_product_row _ _ 2 4 (sLower_monic q) (uHigher_monic q) (by omega) (by omega)
  rw [S6_eq, coeff_add, hz, add_zero, hp, sLower_row1, uHigher_row3, add_zero]

private theorem cancel_ones (a b : R) : (a + 1) + (b + 1) = b + a := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem AS6_row12 (q : Vector R) : (A q * S6 q).coeff 12 = q 0 + q 1 := by
  have hp : (A q * S6 q).coeff 12 = (A q).coeff 6 + (S6 q).coeff 5 :=
    next_product_row _ _ 7 6 (A_monic q) (S6_monic q) (by omega) (by omega)
  rw [hp, A_row6, S6_row5]
  exact cancel_ones _ _

private theorem row_shuffle (a b c d : R) : a + b + (c + d) = c + (d + a + b) := by ring

theorem outputQ_row12 (q : Vector R) :
    (outputQ q).coeff 12 = q 0 + (q 1 +
      ((q 0 + q 2) + (q 1 + q 3)) ^ 2 * q 1 + (q 1 + 1) ^ 2 * (B q).coeff 0) := by
  have hb := squareB_row q 9
  simp only [Nat.reduceAdd] at hb
  have h9 : (A q ^ 2).coeff 9 = 0 := Char2Degree19Crown.square_coeff_odd (A q) 4
  rw [outputQ_coeff_high q 12 (by omega), high, coeff_add, hb,
    h9, squareA_row10, squareA_row11, squareA_row12, AS6_row12]
  simp only [zero_add, zero_mul, add_zero]
  exact row_shuffle _ _ _ _

def bTail (a b s : R) : R := 1 + (s + (b + a)) * a + (a + 1) * (b + 1)

private theorem normalize_B0 (a b s r t : R) :
    (1 + (r + t)) + (t + (s + (b + a)) * a + (a + 1) * (b + 1)) = r + bTail a b s := by
  simp only [bTail, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem normalized_B0 (z : Vector R) :
    (B (qOfZ z)).coeff 0 = z 3 + bTail (z 0) (z 1) (z 2) := by
  rw [B_row0, normalized_A5]
  exact normalize_B0 (z 0) (z 1) (z 2) (z 3) (z 8)

def q0Tail (a b s r : R) : R :=
  a + (s + (b + a)) ^ 2 * a + (a + 1) ^ 2 * (r + bTail a b s)

theorem outputZ_row12 (z : Vector R) :
    (outputZ z).coeff 12 = z 4 + q0Tail (z 0) (z 1) (z 2) (z 3) := by
  change (outputQ (qOfZ z)).coeff 12 = _
  rw [outputQ_row12, normalized_A5, normalized_B0]
  rfl

/-- The supplied decoder for this scalar row, with both compositions inherited
from the already checked unit translation. -/
def q0Equiv (a b s r : R) : R ≃ R := Char2Decoder.unitPivot (q0Tail a b s r)

theorem decode_actual_Q0 (z : Vector R) :
    (q0Equiv (z 0) (z 1) (z 2) (z 3)).symm ((outputZ z).coeff 12) = z 4 := by
  rw [outputZ_row12]
  exact (q0Equiv (z 0) (z 1) (z 2) (z 3)).symm_apply_apply (z 4)

theorem row12_congr (z w : Vector R) (he : ∀ i : Fin 17, i.val ≤ 4 → z i = w i) :
    (outputZ z).coeff 12 = (outputZ w).coeff 12 := by
  rw [outputZ_row12, outputZ_row12, he 0 (by omega), he 1 (by omega),
    he 2 (by omega), he 3 (by omega), he 4 (by omega)]

theorem row12_future (z : Vector R) (j : Fin 17) (δ : R) (hj : 4 < j.val) :
    (outputZ (shift z j δ)).coeff 12 = (outputZ z).coeff 12 := by
  apply row12_congr
  intro i hi
  have hne : i ≠ j := by intro h; have hv := congrArg Fin.val h; omega
  exact shift_other z j i δ hne

end FastPoly.Char2Degree17Q0Pivot
