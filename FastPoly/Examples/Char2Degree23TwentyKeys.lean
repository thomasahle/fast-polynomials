import FastPoly.Examples.Char2Degree23TwentyWires

/-! The final normalized quadratic pivot, with an explicit row-eight correction. -/

namespace FastPoly.Char2Degree23TwentyKeys

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23HighKeys Char2Degree23MiddleFrame Char2Degree23TwentyCoordinates
  Char2Degree23TwentyQuadratic Char2Degree23TwentyWires

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def rowEight (a : ℕ → R) (d : R) : R := d * xi a + d ^ 2 * a 6 +
  sigma a d * (a 8 + a 9 + a 10 + a 11) + cross a d
noncomputable def tail (a : ℕ → R) (d : R) : R[X] :=
  C d ^ 2 * L a + C (sigma a d) * lowLine a + C (cross a d) + C d * L a
noncomputable def low (a : ℕ → R) (d : R) : R[X] := C d * M a + tail a d

private theorem group_M (m t l z c d s : R[X]) :
    (d * m + d ^ 2 * l + s * z + c) + d * t =
      d * (m + t) + d ^ 2 * l + s * z + c := by ring

private theorem linear_cancel (x d g t c z e : R[X]) :
    d * (g * x + t) + d ^ 2 * (x + c) + (d ^ 2 + g * d) * (x + z) + e =
      d * t + d ^ 2 * c + (d ^ 2 + g * d) * z + e := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem scalar_column (a : ℕ → R) (d : R) :
    K a d + C d * (ellLinear a * L a) = C (rowEight a d) := by
  unfold K
  rw [group_M, M_add_ell]
  have hs : C (sigma a d) = C d ^ 2 + C (gammaRaw a) * C d := by
    simp only [sigma, map_add, map_mul, map_pow]
  have hl : lowLine a = X + C (a 8 + a 9 + a 10 + a 11) := by
    simp only [lowLine, map_add, add_assoc]
  rw [hs, hl]
  change C d * (C (gammaRaw a) * X + C (xi a)) + C d ^ 2 * (X + C (a 6)) +
    (C d ^ 2 + C (gammaRaw a) * C d) * (X + C (a 8 + a 9 + a 10 + a 11)) + C (cross a d) = _
  rw [linear_cancel, ← hs]
  simp only [rowEight, map_add, map_mul, map_pow]

private theorem inner_shift (x v c d : R[X]) : x + (v + d) + c = (x + v + c) + d := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem ell_change (a : ℕ → R) (d : R) :
    ell (shift20 a d) = ell a + C d * (ellLinear a * L a) := by
  change ellLinear a * (z a + v (shift20 a d) + C (a 17)) = _
  rw [v_change, inner_shift, mul_add, ← mul_assoc, mul_comm (ellLinear a) (C d), mul_assoc]
  rfl

private theorem head_transport (y v w r dv dw : R[X]) :
    y + (v + dv) + (w + dw) + r = (y + v + w + r) + (dv + dw) := by
  simp only [add_assoc, add_comm, add_left_comm]

private theorem crown_transport (x w l dw dl : R[X]) :
    x + (w + dw) + (l + dl) = (x + w + l) + (dw + dl) := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem head_change (a : ℕ → R) (d : R) :
    head (shift20 a d) = head a + (C d * L a + K a d) := by
  rw [Char2Degree23SixteenFrame.head_grouped, Char2Degree23SixteenFrame.head_grouped,
    v_change, Wg_change]
  exact head_transport _ _ _ _ _ _

theorem crown_change (a : ℕ → R) (d : R) : crownRight (shift20 a d) = crownRight a +
    (K a d + C d * (ellLinear a * L a)) := by
  rw [Char2Degree23SixteenFrame.crown_grouped, Char2Degree23SixteenFrame.crown_grouped,
    Wg_change, ell_change]
  exact crown_transport _ _ _ _ _

private theorem output_transport (h f u c r j t o dh dr : R[X]) :
    (h + dh) + f * (u + c * ((r + dr) + j) + t) + o =
      (h + f * (u + c * (r + j) + t) + o) + (dh + (f * c) * dr) := by ring

theorem output_change (a : ℕ → R) (d : R) :
    output (shift20 a d) = output a + ((C d * L a + K a d) + D a * C (rowEight a d)) := by
  change head (shift20 a d) + lastFactor a *
    (u a + crownLeft a * (crownRight (shift20 a d) + C (a 19)) + C (a 21)) + C (a 22) = _
  rw [head_change, crown_change, output_transport, scalar_column]
  rfl

private theorem residual_collect (l m p q r c : R[X]) :
    (l + (m + p + q + r)) + c = c + (m + (p + q + r + l)) := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem raw_difference (a : ℕ → R) (d : R) :
    output (shift20 a d) + output a = D a * C (rowEight a d) + low a d := by
  rw [output_change, cancel_tail]
  exact residual_collect _ _ _ _ _ _

theorem tail_degree (a : ℕ → R) (d : R) : (tail a d).natDegree < 2 := by
  have hd : (C d ^ 2).natDegree ≤ 0 := by rw [← map_pow, natDegree_C]
  have h1 : (C d ^ 2 * L a).natDegree ≤ 1 :=
    natDegree_mul_le.trans (Nat.add_le_add hd (L_monic a).natDegree_eq.le)
  have h2 : (C (sigma a d) * lowLine a).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (lowLine_monic a).natDegree_eq.le
  have h3 : (C (cross a d)).natDegree ≤ 1 := by rw [natDegree_C]; omega
  have h4 : (C d * L a).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (L_monic a).natDegree_eq.le
  exact (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le h1 h2) h3) h4).trans_lt (by omega)

theorem low_degree (a : ℕ → R) (d : R) : (low a d).natDegree < 8 := by
  have hm : (C d * M a).natDegree ≤ 2 :=
    (natDegree_C_mul_le _ _).trans (M_monic a).natDegree_eq.le
  exact (natDegree_add_le_of_degree_le hm (tail_degree a d).le).trans_lt (by omega)

theorem increment20_change (q : Fin 23 → R) (d : R) :
    output (rawKeys (increment q 20 d)) = output (rawKeys q) + low (rawKeys q) d :=
  Char2Degree23NormalizedPeel.increment (by omega) (slots20 q d) rfl
    (raw_difference (rawKeys q) d) (low_degree (rawKeys q) d)

theorem increment20_unit (q : Fin 23 → R) (d : R) :
    Char2Degree19InnerTail.UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 20 d))) 2 d :=
  Char2Degree19InnerChanges.unit_difference_of_lower _ _ _ _ _ d (M_monic (rawKeys q))
    (tail_degree (rawKeys q) d) (increment20_change q d)

end FastPoly.Char2Degree23TwentyKeys
