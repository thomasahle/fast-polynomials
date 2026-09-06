import FastPoly.Examples.Char2Degree25RowThirteen

/-! The existing raw row-twelve pivot translates a7 and a8 together.
Its w change loses its quadratic leading terms explicitly; the surviving
monic degree-seven j slope supplies the final degree-twelve unit row. -/
namespace FastPoly.Char2Degree25RowTwelve

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame Char2Degree19InnerTail
open Char2Degree25RowThirteen
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift (a : ℕ → R) (delta : R) : ℕ → R
  | 7 => a 7 + delta
  | 8 => a 8 + delta
  | i => a i

noncomputable def wSlope (a : ℕ → R) (delta : R) : R[X] :=
  y + v a + C (a 9) + P a * L a + C delta * L a
noncomputable def inner (a : ℕ → R) (delta : R) : R[X] := L a + wSlope a delta
noncomputable def hSlope (a : ℕ → R) (delta : R) : R[X] := hLeft a * inner a delta
noncomputable def leftSlope (a : ℕ → R) (delta : R) : R[X] :=
  sSlope a + ellSlope a + hSlope a delta + jSlope a
noncomputable def outputSlope (a : ℕ → R) (delta : R) : R[X] :=
  ellSlope a + nRight a * leftSlope a delta

theorem v_shift (a : ℕ → R) (delta : R) :
    v (shift a delta) = v a + C delta * L a := by
  change L a * (y + z a + C (a 7 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (L a) (C delta)]
  rfl

private theorem product_both (p q d l : R[X]) :
    (p + d) * (q + d * l) = p * q + d * (q + p * l + d * l) := by ring

theorem w_shift (a : ℕ → R) (delta : R) :
    w (shift a delta) = w a + C delta * wSlope a delta := by
  change (X + y + z a + C (a 8 + delta)) * (y + v (shift a delta) + C (a 9)) = _
  rw [v_shift, map_add]
  have hp : X + y + z a + (C (a 8) + C delta) = P a + C delta := by
    simp only [P, add_assoc]
  have hq : y + (v a + C delta * L a) + C (a 9) =
      (y + v a + C (a 9)) + C delta * L a := by ac_rfl
  rw [hp, hq, product_both]
  rfl

theorem s_shift (a : ℕ → R) (delta : R) :
    s (shift a delta) = s a + C delta * sSlope a := by
  change (z a + C (a 10)) * (v (shift a delta) + C (a 11)) = _
  rw [v_shift]
  exact product_change _ _ _ _ _

theorem ell_shift (a : ℕ → R) (delta : R) :
    ell (shift a delta) = ell a + C delta * ellSlope a := by
  change (X + C (a 16)) * (z a + v (shift a delta) + C (a 17)) = _
  rw [v_shift]
  exact product_change_middle _ _ _ _ _ _

private theorem collect_right (x v w r c d vs ws : R[X]) :
    x + (v + d * vs) + (w + d * ws) + r + c =
      (x + v + w + r + c) + d * (vs + ws) := by ring

theorem hRight_shift (a : ℕ → R) (delta : R) :
    hRight (shift a delta) = hRight a + C delta * inner a delta := by
  change X + y + z a + u a + v (shift a delta) + w (shift a delta) + r a + C (a 19) = _
  rw [v_shift, w_shift]
  exact collect_right _ _ _ _ _ _ _ _

theorem h_shift (a : ℕ → R) (delta : R) :
    h (shift a delta) = h a + C delta * hSlope a delta := by
  change hLeft a * hRight (shift a delta) = _
  rw [hRight_shift]
  exact product_change_plain _ _ _ _

theorem j_shift (a : ℕ → R) (delta : R) :
    j (shift a delta) = j a + C delta * jSlope a := by
  change jLeft a * (ell (shift a delta) + C (a 21)) = _
  rw [ell_shift]
  exact product_change _ _ _ _ _

private theorem collect_left (x s r g ell h j c d ss es hs js : R[X]) :
    x + (s + d * ss) + r + g + (ell + d * es) + (h + d * hs) + (j + d * js) + c =
      (x + s + r + g + ell + h + j + c) + d * (ss + es + hs + js) := by ring

theorem nLeft_shift (a : ℕ → R) (delta : R) :
    nLeft (shift a delta) = nLeft a + C delta * leftSlope a delta := by
  change X + t a + u a + s (shift a delta) + r a + g a + ell (shift a delta) +
    h (shift a delta) + j (shift a delta) + C (a 22) = _
  rw [s_shift, ell_shift, h_shift, j_shift]
  exact collect_left _ _ _ _ _ _ _ _ _ _ _ _ _

theorem output_shift (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift a delta) =
      Char2Degree25Frame.output a + C delta * outputSlope a delta := by
  change y + z a + u a + ell (shift a delta) +
    nLeft (shift a delta) * nRight a + C (a 24) = _
  rw [ell_shift, nLeft_shift]
  exact collect_output _ _ _ _ _ _ _ _

private theorem cancel_shared (l x y z a b : R[X]) :
    l * (y + z + a) + (x + y + z + b) * l = l * (x + (a + b)) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem v_add_PL (a : ℕ → R) :
    v a + P a * L a = L a * (X + C (a 7 + a 8)) := by
  change L a * (y + z a + C (a 7)) + (X + y + z a + C (a 8)) * L a = _
  rw [map_add]
  exact cancel_shared _ _ _ _ _ _

private theorem quadratic_cancel (x b c : R[X]) :
    x * x + (x + b) * (x + c) = x * (b + c) + b * c := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem quadratic_eq (a : ℕ → R) : y + L a * (X + C (a 7 + a 8)) =
    X * C (a 6 + (a 7 + a 8)) + C (a 6 * (a 7 + a 8)) := by
  change X * X + (X + C (a 6)) * (X + C (a 7 + a 8)) = _
  conv_rhs => rw [map_add, map_mul]
  exact quadratic_cancel (R := R) X (C (a 6)) (C (a 7 + a 8))

private theorem regroup_w (y v c p l d : R[X]) :
    y + v + c + p * l + d * l = (y + (v + p * l)) + c + d * l := by ring

theorem wSlope_eq (a : ℕ → R) (delta : R) : wSlope a delta =
    (X * C (a 6 + (a 7 + a 8)) + C (a 6 * (a 7 + a 8))) +
      C (a 9) + C delta * L a := by
  rw [wSlope, regroup_w, v_add_PL, quadratic_eq]

theorem wSlope_degree (a : ℕ → R) (delta : R) : (wSlope a delta).natDegree ≤ 1 := by
  have hx : (X * C (a 6 + (a 7 + a 8)) : R[X]).natDegree ≤ 1 := by
    apply natDegree_mul_le.trans
    rw [natDegree_X, natDegree_C]
  have hc (r : R) : (C r : R[X]).natDegree ≤ 1 := by rw [natDegree_C]; omega
  have hl : (C delta * L a).natDegree ≤ 1 := by
    apply natDegree_mul_le.trans
    rw [natDegree_C, (L_monic a).natDegree_eq]
  rw [wSlope_eq]
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hx (hc _)) (hc _)) hl

theorem inner_degree (a : ℕ → R) (delta : R) : (inner a delta).natDegree ≤ 1 :=
  natDegree_add_le_of_degree_le (L_monic a).natDegree_eq.le (wSlope_degree a delta)

theorem hSlope_degree (a : ℕ → R) (delta : R) : (hSlope a delta).natDegree ≤ 6 :=
  natDegree_mul_le.trans (Nat.add_le_add (hLeft_monic a).natDegree_eq.le (inner_degree a delta))

theorem leftSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (leftSlope a delta) 7 := by
  have hl : (sSlope a + ellSlope a + hSlope a delta).natDegree ≤ 6 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le ((sSlope_monic a).natDegree_eq.le.trans (by omega))
        ((ellSlope_monic a).natDegree_eq.le.trans (by omega))) (hSlope_degree a delta)
  exact (jSlope_monic a).add_left (hl.trans_lt (by omega))

theorem outputSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (outputSlope a delta) 12 :=
  ((nRight_monic a).mul (leftSlope_monic a delta)).add_left
    ((ellSlope_monic a).natDegree_eq.trans_lt (by omega))

theorem shift_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift a delta)) 12 delta := by
  apply unit_difference_of_split _ _ (outputSlope a delta) 12 delta 0 (by omega)
    (outputSlope_monic a delta)
  simpa only [map_zero, add_zero] using output_shift a delta

end FastPoly.Char2Degree25RowTwelve
