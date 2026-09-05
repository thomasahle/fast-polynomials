import FastPoly.Examples.Char2Degree17Q6Pivot

/-! The supplied Q5-fourth-power pivot at row eight. The low sextic windows
cancel the recovered offset c; a second scalar cancellation isolates Q5^4.
No raw circuit polynomial is expanded. -/
namespace FastPoly.Char2Degree17Q5Pivot

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TerminalFrame Char2Degree17TerminalPivots Char2Degree17Q8Pivot
open Char2Degree17HighFrame Char2Degree17HighSignature Char2Degree17RRow
open Char2Degree17TriangularCoordinates Char2Degree17LeadingInverse Char2Degree17Q0Pivot
open Char2Degree17EPivot Char2Degree17LowWindows Char2Degree17Q6Pivot

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem high_row8 (q : Vector R) : (high q).coeff 8 =
    q 6 ^ 2 * q 1 + q 5 ^ 2 * (B q).coeff 0 +
      ((A q).coeff 2 + q 6 * (q 0 + 1) + q 5 * (S6 q).coeff 4 +
        ((q 0 + q 2) + (q 1 + q 3)) * (S6 q).coeff 3 +
          (q 1 + 1) * (S6 q).coeff 2 + (S6 q).coeff 1) := by
  have hb := squareB_row q 5
  simp only [Nat.reduceAdd] at hb
  have h5 : (A q ^ 2).coeff 5 = 0 := Char2Degree19Crown.square_coeff_odd (A q) 2
  have h7 : (A q ^ 2).coeff 7 = 0 := Char2Degree19Crown.square_coeff_odd (A q) 3
  rw [high, coeff_add, hb, h5, squareA_row6, h7, squareA_row8,
    mul76_coeff8 _ _ (A_monic q) (S6_monic q), A_row3, A_row4, A_row5, A_row6, S6_row5]
  simp only [zero_mul, add_zero, zero_add]

private theorem three_eq_one : (3 : R) = 1 := by
  calc
    (3 : R) = 1 + (1 + 1) := by ring
    _ = 1 := by rw [CharTwo.add_self_eq_zero, add_zero]

private theorem four_eq_zero : (4 : R) = 0 := by
  calc
    (4 : R) = (2 : R) + 2 := by ring
    _ = 0 := by rw [CharTwo.two_eq_zero, zero_add]

private theorem five_eq_one : (5 : R) = 1 := by
  calc
    (5 : R) = (4 : R) + 1 := by ring
    _ = 1 := by rw [four_eq_zero, zero_add]

private theorem six_eq_zero : (6 : R) = 0 := by
  calc
    (6 : R) = (4 : R) + 2 := by ring
    _ = 0 := by rw [four_eq_zero, CharTwo.two_eq_zero, zero_add]

private theorem seven_eq_one : (7 : R) = 1 := by
  calc
    (7 : R) = (6 : R) + 1 := by ring
    _ = 1 := by rw [six_eq_zero, zero_add]

/-- Named scalars for the H row and the coefficient left after peeling c. -/
def H8 (a b t g : R) : R := (t + b + g) + (a + 1) * a + (b + 1)
def C8 (a t : R) : R := t + a ^ 2 + a + 1

private theorem frame_insert (base u2 vf hs mS3 nS2 s1 α s3 hh : R) :
    base + (u2 + vf + hs + mS3 + nS2 + s1) + (α + s3) * hh =
      base + hs + (u2 + vf + mS3 + nS2 + s1 + hh * s3) + hh * α := by ring

private theorem scalar_window8 (a b t g bc v k j c : R) :
    ((k + bc) * g + (t + b) * j + (1 + a) * (v + (t + b) * g + (a + 1) * j)) +
      v * (t + 1) + (t + b + g) * ((t + 1) * g + j + c) +
      (a + 1) * (k * g + (t + 1) * j + (v + (t + b) * g + (a + 1) * j) + c * a) +
      (k * j + (t + 1) * (v + (t + b) * g + (a + 1) * j) + c * (b + 1)) +
      H8 a b t g * ((t + 1) * g + j + c) =
    (a * k + bc + (t + 1) * ((b + 1 + a * (a + 1)) + (t + b))) * g +
      (k + C8 a t) * j := by
  unfold H8 C8
  ring_nf
  simp only [CharTwo.two_eq_zero, three_eq_one, four_eq_zero, five_eq_one,
    six_eq_zero, seven_eq_one,
    mul_zero, mul_one, add_zero, zero_add]

/-- This identity opens only the three small sextic windows, not any gate DAG. -/
private theorem scalar_frame8 (a b t g bc h v k j c s4 r : R) :
    v ^ 2 * a + h ^ 2 * bc +
      (((k + bc) * g + (t + b) * j + (1 + a) * (v + (t + b) * g + (a + 1) * j)) +
        v * (t + 1) + h * s4 +
        (t + b + g) * ((t + 1) * g + j + c) +
        (a + 1) * (k * g + (t + 1) * j + (v + (t + b) * g + (a + 1) * j) + c * a) +
        (k * j + (t + 1) * (v + (t + b) * g + (a + 1) * j) + c * (b + 1))) +
      (r + (h ^ 2 * a + (t + b + g) ^ 2 * bc +
        (h + (t + b + g) * (t + 1) + (a + 1) * s4 + ((t + 1) * g + j + c)))) *
          H8 a b t g =
    a * v ^ 2 + bc * h ^ 2 + h * s4 +
      (a * k + bc + (t + 1) * ((b + 1 + a * (a + 1)) + (t + b))) * g +
      (k + C8 a t) * j +
      H8 a b t g * (r + a * h ^ 2 + (t + b + g) ^ 2 * bc +
        h + (t + b + g) * (t + 1) + (a + 1) * s4) := by
  have hα : r + (h ^ 2 * a + (t + b + g) ^ 2 * bc +
      (h + (t + b + g) * (t + 1) + (a + 1) * s4 + ((t + 1) * g + j + c))) =
      (r + h ^ 2 * a + (t + b + g) ^ 2 * bc + h +
        (t + b + g) * (t + 1) + (a + 1) * s4) + ((t + 1) * g + j + c) := by
    simp only [add_assoc]
  rw [hα, frame_insert, scalar_window8]
  simp only [add_assoc, mul_comm, mul_left_comm, mul_assoc]

theorem outputQ_frame8 (q : Vector R) : (outputQ q).coeff 8 =
    q 1 * q 6 ^ 2 + (B q).coeff 0 * q 5 ^ 2 + q 5 * (S6 q).coeff 4 +
      (q 1 * K q + (B q).coeff 0 +
        (q 0 + 1) * ((q 2 + 1 + q 1 * (q 1 + 1)) + (q 0 + q 2))) * (q 1 + q 3) +
      (K q + C8 (q 1) (q 0)) * (q 2 + q 4) +
      H8 (q 1) (q 2) (q 0) (q 1 + q 3) *
        (q 14 + q 1 * q 5 ^ 2 + ((q 0 + q 2) + (q 1 + q 3)) ^ 2 * (B q).coeff 0 +
          q 5 + ((q 0 + q 2) + (q 1 + q 3)) * (q 0 + 1) + (q 1 + 1) * (S6 q).coeff 4) := by
  rw [outputQ_middle q 8 (by omega), H_row8, a14_eq, high_row8, high_row10,
    A_row2, S6_row3, S6_row2, S6_row1, T_eq]
  exact scalar_frame8 _ _ _ _ _ _ _ _ _ _ _ _

def eightTail (a b t g bc d r j v : R) : R :=
  a * v ^ 2 +
    (a * (d + g) + bc + (t + 1) * ((b + 1 + a * (a + 1)) + (t + b))) * g +
    (d + g + C8 a t) * j +
    H8 a b t g * (r + (t + b + g) ^ 2 * bc +
      (t + b + g) * (t + 1) + (a + 1) * d)

private theorem H8_eq (a b t g : R) : H8 a b t g = g + C8 a t := by
  unfold H8 C8
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

private theorem fourth_small (s a bc d g cc u w h j : R) (hd : d = j + bc + a * g) :
    s + bc * h ^ 2 + h * (h ^ 2 + d) +
      (a * (h ^ 2 + d + g) + u) * g + (h ^ 2 + d + g + cc) * (h ^ 2 + h + j) +
      (g + cc) * (w + a * h ^ 2 + h + (a + 1) * (h ^ 2 + d)) =
    h ^ 4 + (s + (a * (d + g) + u) * g + (d + g + cc) * j +
      (g + cc) * (w + (a + 1) * d)) := by
  rw [hd]
  ring_nf
  simp only [CharTwo.two_eq_zero, three_eq_one, four_eq_zero,
    mul_zero, mul_one, add_zero, zero_add]

private theorem middle_reorder (r ah mb h mf nd : R) :
    r + ah + mb + h + mf + nd = (r + mb + mf) + ah + h + nd := by ring

private theorem fourth_grouped (s a bc d g cc f w1 w2 w3 h j : R)
    (hd : d = j + bc + a * g) :
    s + bc * h ^ 2 + h * (h ^ 2 + d) +
      (a * (h ^ 2 + d + g) + bc + f) * g + (h ^ 2 + d + g + cc) * (h ^ 2 + h + j) +
      (g + cc) * (w1 + a * h ^ 2 + w2 + h + w3 + (a + 1) * (h ^ 2 + d)) =
    h ^ 4 + (s + (a * (d + g) + bc + f) * g + (d + g + cc) * j +
      (g + cc) * (w1 + w2 + w3 + (a + 1) * d)) := by
  rw [middle_reorder w1 (a * h ^ 2) w2 h w3 ((a + 1) * (h ^ 2 + d))]
  simpa only [add_assoc] using
    (fourth_small s a bc d g cc (bc + f) (w1 + w2 + w3) h j hd)

/-- After the recovered-offset cancellation, the Q5^3, Q5^2 and Q5
columns cancel explicitly, leaving the supplied fourth-power column. -/
private theorem scalar_fourth (a b t g bc h v d r j : R) (hd : d = j + bc + a * g) :
    a * v ^ 2 + bc * h ^ 2 + h * (h ^ 2 + d) +
      (a * (h ^ 2 + d + g) + bc +
        (t + 1) * ((b + 1 + a * (a + 1)) + (t + b))) * g +
      ((h ^ 2 + d + g) + C8 a t) * (h ^ 2 + h + j) +
      H8 a b t g * (r + a * h ^ 2 + (t + b + g) ^ 2 * bc +
        h + (t + b + g) * (t + 1) + (a + 1) * (h ^ 2 + d)) =
      h ^ 4 + eightTail a b t g bc d r j v := by
  rw [eightTail, H8_eq]
  exact fourth_grouped (a * v ^ 2) a bc d g (C8 a t)
    ((t + 1) * ((b + 1 + a * (a + 1)) + (t + b)))
    r ((t + b + g) ^ 2 * bc) ((t + b + g) * (t + 1)) h j hd

theorem D_eq (q : Vector R) : D q = (q 2 + E q) + (B q).coeff 0 + q 1 * (q 1 + q 3) := by
  unfold D
  ring

private theorem q4_collect (b e h : R) :
    b + (e + h ^ 2 + h) = h ^ 2 + h + (b + e) := by ring

theorem outputQ_row8 (q : Vector R) :
    (outputQ q).coeff 8 = q 5 ^ 4 +
      eightTail (q 1) (q 2) (q 0) (q 1 + q 3) ((B q).coeff 0)
        (D q) (q 14) (q 2 + E q) (q 6) := by
  rw [outputQ_frame8, S4_eq, K_eq, q4_eq q, q4_collect]
  exact scalar_fourth _ _ _ _ _ _ _ _ _ _ (D_eq q)

def q5Tail (a b s r t e w v : R) : R :=
  eightTail a b t (a + (s + t)) (r + bTail a b s)
    (e + (r + bTail a b s) + b + a ^ 2 + a * (s + t)) w (b + e) v

theorem outputZ_row8 (z : Vector R) :
    (outputZ z).coeff 8 = z 8 ^ 4 +
      q5Tail (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) := by
  change (outputQ (qOfZ z)).coeff 8 = _
  rw [outputQ_row8, normalized_B0, normalized_D, normalized_E]
  rfl

theorem row8_congr (z w : Vector R) (he : ∀ i : Fin 17, i.val ≤ 8 → z i = w i) :
    (outputZ z).coeff 8 = (outputZ w).coeff 8 := by
  rw [outputZ_row8, outputZ_row8, he 0 (by omega), he 1 (by omega),
    he 2 (by omega), he 3 (by omega), he 4 (by omega), he 5 (by omega),
    he 6 (by omega), he 7 (by omega), he 8 (by omega)]

theorem row8_future (z : Vector R) (j : Fin 17) (δ : R) (hj : 8 < j.val) :
    (outputZ (shift z j δ)).coeff 8 = (outputZ z).coeff 8 := by
  apply row8_congr
  intro i hi
  have hne : i ≠ j := by intro h; have hv := congrArg Fin.val h; omega
  exact shift_other z j i δ hne

section ExplicitInverse
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

/-- Supplied inverse fourth Frobenius and translation; both compositions are
inherited from the explicit equivalences, not inferred from a Jacobian. -/
noncomputable def q5Equiv (a b s r t e w v : F) : F ≃ F :=
  (Char2Certificate.frobeniusPivot 2).trans
    (Char2Decoder.unitPivot (q5Tail a b s r t e w v))

theorem q5Equiv_apply (a b s r t e w v h : F) :
    q5Equiv a b s r t e w v h = h ^ 4 + q5Tail a b s r t e w v := rfl

theorem decode_actual_Q5 (z : Vector F) :
    (q5Equiv (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7)).symm
      ((outputZ z).coeff 8) = z 8 := by
  rw [outputZ_row8, ← q5Equiv_apply]
  exact (q5Equiv (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7)).symm_apply_apply (z 8)

end ExplicitInverse
end FastPoly.Char2Degree17Q5Pivot
