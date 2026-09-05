import FastPoly.Examples.Char2Degree23SeamPivots

/-!
# A two-wire frame for the six middle degree-23 pivots

Only `W=w+s` and `v` vary in these stages. Their coefficients are the
named monic polynomials `D+1` and `D*(X+a16)+1`. The row-eight offset is
kept explicit and may change arbitrarily: it cannot affect these pivots.
-/

namespace FastPoly.Char2Degree23MiddleFrame

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23Cancellations Char2Degree23HighFrame Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def ellLinear (a : ℕ → R) : R[X] := X + C (a 16)
noncomputable def wFactor (a : ℕ → R) : R[X] := D a + 1
noncomputable def vFactor (a : ℕ → R) : R[X] := D a * ellLinear a + 1
noncomputable def headBase (a : ℕ → R) : R[X] := y + r a + g a
noncomputable def crownBase (a : ℕ → R) : R[X] :=
  X + y + z a + g a + ellLinear a * (z a + C (a 17))
noncomputable def middleConstant (a : ℕ → R) : R[X] :=
  (headBase a + lastFactor a * u a + lastFactor a * C (a 21) + C (a 22)) + D a * crownBase a

omit [CharP R 2] [Nontrivial R] in
theorem head_eq (a : ℕ → R) : head a = v a + W a + headBase a := by
  change y + v a + w a + s a + r a + g a = v a + (w a + s a) + (y + r a + g a)
  simp only [add_assoc, add_comm, add_left_comm]

omit [CharP R 2] [Nontrivial R] in
theorem ell_eq (a : ℕ → R) :
    ell a = ellLinear a * v a + ellLinear a * (z a + C (a 17)) := by
  change ellLinear a * (z a + v a + C (a 17)) = _
  have he : z a + v a + C (a 17) = v a + (z a + C (a 17)) := by
    simp only [add_assoc, add_comm, add_left_comm]
  rw [he, mul_add]

omit [CharP R 2] [Nontrivial R] in
theorem crown_eq (a : ℕ → R) :
    crownRight a = W a + ellLinear a * v a + crownBase a := by
  change X + y + z a + w a + s a + g a + ell a = _
  rw [ell_eq]
  change X + y + z a + w a + s a + g a +
      (ellLinear a * v a + ellLinear a * (z a + C (a 17))) =
    (w a + s a) + ellLinear a * v a +
      (X + y + z a + g a + ellLinear a * (z a + C (a 17)))
  simp only [add_assoc, add_comm, add_left_comm]

omit [CharP R 2] [Nontrivial R] in
private theorem collect (v w h f u b l c k t o : R[X]) :
    (v + w + h) + f * (u + b * ((w + l * v + c) + k) + t) + o =
      (f * b + 1) * w + (((f * b) * l + 1) * v +
        ((h + f * u + f * t + o) + (f * b) * c) + (f * b) * k) := by
  ring

omit [CharP R 2] [Nontrivial R] in
theorem output_eq (a : ℕ → R) :
    output a = wFactor a * W a +
      (vFactor a * v a + middleConstant a + D a * C (a 19)) := by
  change head a + lastFactor a *
    (u a + crownLeft a * (crownRight a + C (a 19)) + C (a 21)) + C (a 22) = _
  rw [head_eq, crown_eq, collect]
  rfl

omit [CharP R 2] in
theorem wFactor_monic (a : ℕ → R) : IsMonicOfDegree (wFactor a) 8 := by
  have h1 : ((1 : R[X])).natDegree < 8 := by rw [natDegree_one]; omega
  exact (D_monic a).add_right h1

omit [CharP R 2] in
theorem vFactor_monic (a : ℕ → R) : IsMonicOfDegree (vFactor a) 9 := by
  have h1 : ((1 : R[X])).natDegree < 9 := by rw [natDegree_one]; omega
  exact ((D_monic a).mul (isMonicOfDegree_X_add_one (a 16))).add_right h1

omit [Nontrivial R] in
private theorem other_difference (f d v v' c : R[X]) (a a' : R) :
    (f * v' + c + d * C a') + (f * v + c + d * C a) =
      f * (v' + v) + d * C (a' + a) := by
  simp only [mul_add, map_add]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

/-- The row-eight correction is explicitly bounded, never unfolded. -/
theorem middle_unit (a b : ℕ → R) (k : ℕ) (delta : R) (hk : 1 ≤ k)
    (hd : D b = D a) (hl : ellLinear b = ellLinear a)
    (hc : middleConstant b = middleConstant a)
    (hw : UnitDifference (W a) (W b) k delta)
    (hv : (vFactor a * (v b + v a)).natDegree < 8 + k) :
    UnitDifference (output a) (output b) (8 + k) delta := by
  have hwa : wFactor b = wFactor a := by change D b + 1 = D a + 1; rw [hd]
  have hva : vFactor b = vFactor a := by
    change D b * ellLinear b + 1 = D a * ellLinear a + 1
    rw [hd, hl]
  have hlow : ((vFactor a * v b + middleConstant a + D a * C (b 19)) +
      (vFactor a * v a + middleConstant a + D a * C (a 19))).natDegree < 8 + k := by
    rw [other_difference]
    have hscalar : (D a * C (b 19 + a 19)).natDegree < 8 + k := by
      apply natDegree_mul_le.trans_lt
      rw [(D_monic a).natDegree_eq, natDegree_C]
      omega
    exact (natDegree_add_le _ _).trans_lt (max_lt hv hscalar)
  rw [output_eq a, output_eq b, hwa, hva, hc, hd]
  exact Char2Degree21Frame.difference_add_lower
    (Char2Degree21Frame.difference_mul hw (wFactor_monic a)) hlow

theorem middle_unit_fixed_v (a b : ℕ → R) (k : ℕ) (delta : R) (hk : 1 ≤ k)
    (hd : D b = D a) (hl : ellLinear b = ellLinear a)
    (hc : middleConstant b = middleConstant a) (hv : v b = v a)
    (hw : UnitDifference (W a) (W b) k delta) :
    UnitDifference (output a) (output b) (8 + k) delta := by
  apply middle_unit a b k delta hk hd hl hc hw
  rw [hv, CharTwo.add_self_eq_zero, mul_zero, natDegree_zero]
  omega


/-- Add a displayed scalar to one raw middle offset. -/
def offset6 (a : ℕ → R) (delta : R) : ℕ → R
  | 6 => a 6 + delta
  | i => a i

def offset7 (a : ℕ → R) (delta : R) : ℕ → R
  | 7 => a 7 + delta
  | i => a i

def offset8 (a : ℕ → R) (delta : R) : ℕ → R
  | 8 => a 8 + delta
  | i => a i

def offset9 (a : ℕ → R) (delta : R) : ℕ → R
  | 9 => a 9 + delta
  | i => a i

def offset10 (a : ℕ → R) (delta : R) : ℕ → R
  | 10 => a 10 + delta
  | i => a i

def offset11 (a : ℕ → R) (delta : R) : ℕ → R
  | 11 => a 11 + delta
  | i => a i

def commonOffsets (a : ℕ → R) (delta : R) : ℕ → R
  | 8 => a 8 + delta
  | 9 => a 9 + delta
  | 10 => a 10 + delta
  | 11 => a 11 + delta
  | i => a i

noncomputable def lowLine (a : ℕ → R) : R[X] :=
  X + C (a 8) + C (a 9) + C (a 10) + C (a 11)

omit [CharP R 2] in
theorem lowLine_monic (a : ℕ → R) : IsMonicOfDegree (lowLine a) 1 := by
  have hc (c : R) : (C c).natDegree < 1 := by rw [natDegree_C]; omega
  exact (((isMonicOfDegree_X_add_one (a 8)).add_right (hc _)).add_right (hc _)).add_right (hc _)

omit [CharP R 2] [Nontrivial R] in
theorem add_constant (p : R[X]) (c d : R) : p + C (c + d) = (p + C c) + C d := by
  rw [map_add, ← add_assoc]

omit [Nontrivial R] in
theorem w_left_sum (a : ℕ → R) :
    wLeft a + (z a + C (a 10)) = wSlope a := by
  change (X + y + z a + C (a 8)) + (z a + C (a 10)) =
    X + y + C (a 8) + C (a 10)
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

omit [Nontrivial R] in
theorem all_factor_sum (a : ℕ → R) :
    wLeft a + (y + v a + C (a 9)) + (z a + C (a 10)) + (v a + C (a 11)) =
      lowLine a := by
  change (X + y + z a + C (a 8)) + (y + v a + C (a 9)) +
    (z a + C (a 10)) + (v a + C (a 11)) =
      X + C (a 8) + C (a 9) + C (a 10) + C (a 11)
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

omit [CharP R 2] [Nontrivial R] in
private theorem two_right (b c l r d : R[X]) :
    b * (l + d) + c * (r + d) = (b * l + c * r) + d * (b + c) := by
  ring

omit [Nontrivial R] in
theorem W_from_v (a b : ℕ → R) (dv : R[X]) (hz : z b = z a) (hv : v b = v a + dv)
    (h8 : b 8 = a 8) (h9 : b 9 = a 9) (h10 : b 10 = a 10) (h11 : b 11 = a 11) :
    W b = W a + dv * wSlope a := by
  have hl : y + v b + C (b 9) = (y + v a + C (a 9)) + dv := by
    rw [hv, h9]
    simp only [add_assoc, add_comm, add_left_comm]
  have hr : v b + C (b 11) = (v a + C (a 11)) + dv := by
    rw [hv, h11]
    simp only [add_assoc, add_comm, add_left_comm]
  change (X + y + z b + C (b 8)) * (y + v b + C (b 9)) +
    (z b + C (b 10)) * (v b + C (b 11)) = _
  rw [hl, hr, hz, h8, h10, two_right]
  change W a + dv * (wLeft a + (z a + C (a 10))) = _
  rw [w_left_sum]

omit [CharP R 2] [Nontrivial R] in
theorem v_offset6 (a : ℕ → R) (delta : R) :
    v (offset6 a delta) = v a + C delta * (y + z a + C (a 7)) := by
  change (X + C (a 6 + delta)) * (y + z a + C (a 7)) = _
  rw [add_constant, add_mul]
  rfl

omit [CharP R 2] [Nontrivial R] in
theorem v_offset7 (a : ℕ → R) (delta : R) :
    v (offset7 a delta) = v a + C delta * (X + C (a 6)) := by
  change (X + C (a 6)) * (y + z a + C (a 7 + delta)) = _
  rw [add_constant, mul_add, mul_comm _ (C delta)]
  rfl

omit [Nontrivial R] in
theorem W_offset6 (a : ℕ → R) (delta : R) :
    W (offset6 a delta) = W a + C delta * ((y + z a + C (a 7)) * wSlope a) := by
  rw [W_from_v a (offset6 a delta) (C delta * (y + z a + C (a 7)))
    rfl (v_offset6 a delta) rfl rfl rfl rfl, mul_assoc]

omit [Nontrivial R] in
theorem W_offset7 (a : ℕ → R) (delta : R) :
    W (offset7 a delta) = W a + C delta * ((X + C (a 6)) * wSlope a) := by
  rw [W_from_v a (offset7 a delta) (C delta * (X + C (a 6)))
    rfl (v_offset7 a delta) rfl rfl rfl rfl, mul_assoc]

omit [CharP R 2] [Nontrivial R] in
theorem W_offset8 (a : ℕ → R) (delta : R) :
    W (offset8 a delta) = W a + C delta * (y + v a + C (a 9)) := by
  change (X + y + z a + C (a 8 + delta)) * (y + v a + C (a 9)) + s a = _
  rw [add_constant, add_mul]
  change (w a + C delta * (y + v a + C (a 9))) + s a =
    (w a + s a) + C delta * (y + v a + C (a 9))
  simp only [add_assoc, add_comm, add_left_comm]

omit [CharP R 2] [Nontrivial R] in
theorem W_offset9 (a : ℕ → R) (delta : R) :
    W (offset9 a delta) = W a + C delta * wLeft a := by
  change wLeft a * (y + v a + C (a 9 + delta)) + s a = _
  rw [add_constant, mul_add, mul_comm _ (C delta)]
  change (w a + C delta * wLeft a) + s a = (w a + s a) + C delta * wLeft a
  simp only [add_assoc, add_comm, add_left_comm]

omit [CharP R 2] [Nontrivial R] in
theorem W_offset10 (a : ℕ → R) (delta : R) :
    W (offset10 a delta) = W a + C delta * (v a + C (a 11)) := by
  change w a + (z a + C (a 10 + delta)) * (v a + C (a 11)) = _
  rw [add_constant, add_mul, ← add_assoc]
  rfl

omit [CharP R 2] [Nontrivial R] in
theorem W_offset11 (a : ℕ → R) (delta : R) :
    W (offset11 a delta) = W a + C delta * (z a + C (a 10)) := by
  change w a + (z a + C (a 10)) * (v a + C (a 11 + delta)) = _
  rw [add_constant, mul_add, mul_comm _ (C delta), ← add_assoc]
  rfl

omit [Nontrivial R] in
private theorem two_common (b c e f d : R[X]) :
    (b + d) * (e + d) + (c + d) * (f + d) =
      (b * e + c * f) + d * (b + e + c + f) := by
  simp only [add_mul, mul_add]
  rw [mul_comm b d, mul_comm c d]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

omit [Nontrivial R] in
theorem W_commonOffsets (a : ℕ → R) (delta : R) :
    W (commonOffsets a delta) = W a + C delta * lowLine a := by
  change (X + y + z a + C (a 8 + delta)) * (y + v a + C (a 9 + delta)) +
    (z a + C (a 10 + delta)) * (v a + C (a 11 + delta)) = _
  rw [add_constant, add_constant, add_constant, add_constant, two_common]
  change W a + C delta *
    (wLeft a + (y + v a + C (a 9)) + (z a + C (a 10)) + (v a + C (a 11))) = _
  rw [all_factor_sum]

omit [Nontrivial R] in
theorem wSlope_commonOffsets (a : ℕ → R) (delta : R) :
    wSlope (commonOffsets a delta) = wSlope a := by
  change X + y + C (a 8 + delta) + C (a 10 + delta) =
    X + y + C (a 8) + C (a 10)
  simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]


end FastPoly.Char2Degree23MiddleFrame
