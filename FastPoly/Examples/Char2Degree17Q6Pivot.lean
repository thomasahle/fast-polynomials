import FastPoly.Examples.Char2Degree17LowWindows

/-! The supplied Q6-square pivot at row nine. Only local named scalar
cancellations remove Q5 and the later recovered offsets. -/
namespace FastPoly.Char2Degree17Q6Pivot

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TerminalFrame Char2Degree17TerminalPivots Char2Degree17Q8Pivot
open Char2Degree17HighFrame Char2Degree17HighSignature Char2Degree17RRow
open Char2Degree17TriangularCoordinates Char2Degree17LeadingInverse Char2Degree17Q0Pivot
open Char2Degree17EPivot Char2Degree17LowWindows

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem squareA_row6 (q : Vector R) : (A q ^ 2).coeff 6 = q 6 ^ 2 := by
  have hh : (A q ^ 2).coeff 6 = (A q).coeff 3 ^ 2 :=
    Char2Degree19Crown.square_coeff_even (A q) 3
  rw [A_row3] at hh
  exact hh

theorem squareA_row8 (q : Vector R) : (A q ^ 2).coeff 8 = q 5 ^ 2 := by
  have hh : (A q ^ 2).coeff 8 = (A q).coeff 4 ^ 2 :=
    Char2Degree19Crown.square_coeff_even (A q) 4
  rw [A_row4] at hh
  exact hh

theorem high_row10 (q : Vector R) : (high q).coeff 10 =
    q 5 ^ 2 * q 1 + ((q 0 + q 2) + (q 1 + q 3)) ^ 2 * (B q).coeff 0 +
      (q 5 + ((q 0 + q 2) + (q 1 + q 3)) * (q 0 + 1) +
        (q 1 + 1) * (S6 q).coeff 4 + (S6 q).coeff 3) := by
  have hb := squareB_row q 7
  simp only [Nat.reduceAdd] at hb
  have h7 : (A q ^ 2).coeff 7 = 0 := Char2Degree19Crown.square_coeff_odd (A q) 3
  have h9 : (A q ^ 2).coeff 9 = 0 := Char2Degree19Crown.square_coeff_odd (A q) 4
  rw [high, coeff_add, hb, h7, h9, squareA_row8, squareA_row10,
    mul76_coeff10 _ _ (A_monic q) (S6_monic q), A_row4, A_row5, A_row6, S6_row5]
  simp only [zero_add, zero_mul, add_zero]

theorem high_row9 (q : Vector R) : (high q).coeff 9 =
    q 6 ^ 2 + q 5 ^ 2 * (q 2 + 1) +
      (q 6 + q 5 * (q 0 + 1) + ((q 0 + q 2) + (q 1 + q 3)) * (S6 q).coeff 4 +
        (q 1 + 1) * (S6 q).coeff 3 + (S6 q).coeff 2) := by
  have hb := squareB_row q 6
  simp only [Nat.reduceAdd] at hb
  have h7 : (A q ^ 2).coeff 7 = 0 := Char2Degree19Crown.square_coeff_odd (A q) 3
  have h9 : (A q ^ 2).coeff 9 = 0 := Char2Degree19Crown.square_coeff_odd (A q) 4
  rw [high, coeff_add, hb, squareA_row6, h7, squareA_row8, h9,
    mul76_coeff9 _ _ (A_monic q) (S6_monic q), A_row3, A_row4, A_row5, A_row6, S6_row5]
  simp only [zero_mul, add_zero]

/-- The supplied lower-row cancellation removes the last v offset c. -/
private theorem scalar_S32 (a b t g k j v c : R) :
    a * ((t + 1) * g + j + c) +
      (k * g + (t + 1) * j + (v + (t + b) * g + (a + 1) * j) + c * a) =
        (a * (t + 1) + k + t + b) * g + t * j + v := by
  simp only [mul_add, add_mul, one_mul, mul_one, add_assoc, add_comm, add_left_comm,
    mul_assoc, mul_comm, mul_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem S32 (q : Vector R) : q 1 * (S6 q).coeff 3 + (S6 q).coeff 2 =
    (q 1 * (q 0 + 1) + K q + q 0 + q 2) * (q 1 + q 3) +
      q 0 * (q 2 + q 4) + q 6 := by
  rw [S6_row3, S6_row2, T_eq]
  exact scalar_S32 _ _ _ _ _ _ _ _

private theorem row9_collect (v h a b m f n s4 s3 s2 r bc : R) (hn : n = a + 1) :
    (v ^ 2 + h ^ 2 * (b + 1) + (v + h * f + m * s4 + n * s3 + s2)) +
      (r + (h ^ 2 * a + m ^ 2 * bc + (h + m * f + n * s4 + s3))) =
    v ^ 2 + r + h ^ 2 * (b + 1 + a) + m ^ 2 * bc +
      h * (f + 1) + (m + n) * s4 + m * f + v + (a * s3 + s2) := by
  rw [hn]
  have hs : (a + 1) * s3 + s3 = a * s3 := by
    rw [add_mul, one_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  calc
    _ = v ^ 2 + r + h ^ 2 * (b + 1 + a) + m ^ 2 * bc +
      h * (f + 1) + (m + (a + 1)) * s4 + m * f + v +
        (((a + 1) * s3 + s3) + s2) := by ring
    _ = _ := by rw [hs]

/-- Tail expressed in already-decoded scalars; d denotes S6[4]+Q5^2. -/
def nineTail (a b t g bc d r j : R) : R :=
  r + (t + b + g) ^ 2 * bc + (t + b + g) * (t + 1) +
    ((t + b + g) + (a + 1)) * d +
      (a * (t + 1) + d + g + t + b) * g + t * j

private theorem scalar_nine (v h a b t g bc d r j : R) :
    v ^ 2 + r + h ^ 2 * (b + 1 + a) + (t + b + g) ^ 2 * bc +
      h * ((t + 1) + 1) + ((t + b + g) + (a + 1)) * (h ^ 2 + d) +
      (t + b + g) * (t + 1) + v +
      ((a * (t + 1) + (h ^ 2 + d + g) + t + b) * g +
        t * (h ^ 2 + h + j) + v) =
      v ^ 2 + nineTail a b t g bc d r j := by
  have hf : (t + 1) + 1 = t := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hz : (b + 1 + a) + ((t + b + g) + (a + 1)) + g + t = 0 := by
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero, zero_add, add_zero]
  rw [hf]
  calc
    _ = (v ^ 2 + nineTail a b t g bc d r j) +
      h ^ 2 * ((b + 1 + a) + ((t + b + g) + (a + 1)) + g + t) +
        (h * t + t * h) + (v + v) := by unfold nineTail; ring
    _ = _ := by
      rw [hz, mul_zero, add_zero, mul_comm t h, CharTwo.add_self_eq_zero,
        add_zero, CharTwo.add_self_eq_zero, add_zero]

private theorem q4_collect (b e h : R) :
    b + (e + h ^ 2 + h) = h ^ 2 + h + (b + e) := by ring

theorem outputQ_row9 (q : Vector R) :
    (outputQ q).coeff 9 = q 6 ^ 2 +
      nineTail (q 1) (q 2) (q 0) (q 1 + q 3) ((B q).coeff 0)
        (D q) (q 14) (q 2 + E q) := by
  rw [outputQ_middle q 9 (by omega), H_row9, mul_one, a14_eq,
    high_row9, high_row10]
  rw [row9_collect _ _ _ _ _ _ _ _ _ _ _ _ rfl, S32, S4_eq, K_eq, q4_eq q,
    q4_collect]
  exact scalar_nine _ _ _ _ _ _ _ _ _ _

def q6Tail (a b s r t e w : R) : R :=
  nineTail a b t (a + (s + t)) (r + bTail a b s)
    (e + (r + bTail a b s) + b + a ^ 2 + a * (s + t)) w (b + e)

theorem normalized_D (z : Vector R) : D (qOfZ z) =
    z 5 + (z 3 + bTail (z 0) (z 1) (z 2)) + z 1 +
      z 0 ^ 2 + z 0 * (z 2 + z 4) := by
  rw [D, normalized_E, normalized_B0]
  rfl

theorem outputZ_row9 (z : Vector R) :
    (outputZ z).coeff 9 = z 7 ^ 2 +
      q6Tail (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) := by
  change (outputQ (qOfZ z)).coeff 9 = _
  rw [outputQ_row9, normalized_B0, normalized_D, normalized_E]
  rfl

theorem row9_congr (z w : Vector R) (he : ∀ i : Fin 17, i.val ≤ 7 → z i = w i) :
    (outputZ z).coeff 9 = (outputZ w).coeff 9 := by
  rw [outputZ_row9, outputZ_row9, he 0 (by omega), he 1 (by omega),
    he 2 (by omega), he 3 (by omega), he 4 (by omega), he 5 (by omega),
    he 6 (by omega), he 7 (by omega)]

theorem row9_future (z : Vector R) (j : Fin 17) (δ : R) (hj : 7 < j.val) :
    (outputZ (shift z j δ)).coeff 9 = (outputZ z).coeff 9 := by
  apply row9_congr
  intro i hi
  have hne : i ≠ j := by intro h; have hv := congrArg Fin.val h; omega
  exact shift_other z j i δ hne

section ExplicitInverse
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

/-- Both compositions use the supplied inverse Frobenius followed by translation. -/
noncomputable def q6Equiv (a b s r t e w : F) : F ≃ F :=
  (Char2Certificate.frobeniusPivot 1).trans
    (Char2Decoder.unitPivot (q6Tail a b s r t e w))

theorem q6Equiv_apply (a b s r t e w v : F) :
    q6Equiv a b s r t e w v = v ^ 2 + q6Tail a b s r t e w := rfl

theorem decode_actual_Q6 (z : Vector F) :
    (q6Equiv (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6)).symm
      ((outputZ z).coeff 9) = z 7 := by
  rw [outputZ_row9, ← q6Equiv_apply]
  exact (q6Equiv (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6)).symm_apply_apply (z 7)

end ExplicitInverse
end FastPoly.Char2Degree17Q6Pivot
