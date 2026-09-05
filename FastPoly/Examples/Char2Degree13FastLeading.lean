import FastPoly.Examples.Char2Degree13FastChanges
import FastPoly.Examples.Char2Degree19InnerChanges

/-! The three leading unit pivots of the supplied degree-thirteen decoder.
Changing z has leading term rFactor*delta_z*(w+q7); all other changes are
named products bounded two degrees lower. No output baseline is expanded. -/

namespace FastPoly.Char2Degree13Fast

set_option maxHeartbeats 20000

open Polynomial Char2Degree19InnerTail Char2Degree19InnerChanges

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def slope0 (q : Keys R) : R[X] := z q + v q + C (q 10)
noncomputable def wDelta (q : Keys R) (d : R[X]) : R[X] :=
  d * (d + (y + C (q 5 + q 3)))
noncomputable def zTail (q : Keys R) (d : R[X]) : R[X] :=
  rFactor q * ((aFactor q + C (q 4) + d) * wDelta q d) +
    sFactor q * wDelta q d + (X + C (q 0)) * d

private theorem w_difference (y z p b d : R[X]) :
    (y + (z + d) + p) * ((z + d) + b) =
      (y + z + p) * (z + b) + d * (d + (y + (p + b))) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem w_from_z_change (q q' : Keys R) (d : R[X])
    (hz : z q' = z q + d) (h3 : q' 3 = q 3) (h5 : q' 5 = q 5) :
    w q' = w q + wDelta q d := by
  change (y + z q' + C (q' 5)) * (z q' + C (q' 3)) = _
  rw [hz, h3, h5]
  unfold wDelta
  rw [map_add]
  exact w_difference y (z q) (C (q 5)) (C (q 3)) d

private theorem v_difference (y z c w b d e : R[X]) :
    (y + (z + d) + c) * ((w + e) + b) =
      (y + z + c) * (w + b) + d * (w + b) + (y + z + c + d) * e := by ring

theorem v_from_z_change (q q' : Keys R) (d : R[X])
    (hz : z q' = z q + d) (h4 : q' 4 = q 4) (h7 : q' 7 = q 7)
    (hw : w q' = w q + wDelta q d) :
    v q' = v q + d * (w q + C (q 7)) +
      (aFactor q + C (q 4) + d) * wDelta q d := by
  change (y + z q' + C (q' 4)) * (w q' + C (q' 7)) = _
  rw [hz, h4, h7, hw]
  exact v_difference y (z q) (C (q 4)) (w q) (C (q 7)) d (wDelta q d)

private theorem low_difference (x z a s t b c d : R[X]) :
    x * ((z + d) + a) + s * (t + b) + c =
      (x * (z + a) + s * (t + b) + c) + x * d := by ring

theorem low_from_z_change (q q' : Keys R) (d : R[X])
    (hz : z q' = z q + d) (h0 : q' 0 = q 0) (h6 : q' 6 = q 6)
    (h10 : q' 10 = q 10) (h11 : q' 11 = q 11) (h12 : q' 12 = q 12)
    (ht : t q' = t q) :
    low q' = low q + (X + C (q 0)) * d := by
  change (X + C (q' 0)) * (z q' + C (q' 10)) +
    (y + C (q' 6)) * (t q' + C (q' 11)) + C (q' 12) = _
  rw [hz, h0, h6, h10, h11, h12, ht]
  exact low_difference (X + C (q 0)) (z q) (C (q 10)) (sFactor q)
    (t q) (C (q 11)) (C (q 12)) d

private theorem assemble_z (r s w v l d b e f x : R[X]) :
    r * (v + d * b + e) + s * (w + f) + (l + x * d) =
      (r * v + s * w + l) + (d * (r * b) + (r * e + s * f + x * d)) := by ring

theorem output_from_z_change (q q' : Keys R) (d : R[X])
    (hz : z q' = z q + d) (h0 : q' 0 = q 0) (h3 : q' 3 = q 3)
    (h4 : q' 4 = q 4) (h5 : q' 5 = q 5) (h6 : q' 6 = q 6)
    (h7 : q' 7 = q 7) (h10 : q' 10 = q 10) (h11 : q' 11 = q 11)
    (h12 : q' 12 = q 12) (ht : t q' = t q) :
    output q' = output q +
      (d * (rFactor q * (w q + C (q 7))) + zTail q d) := by
  have hw := w_from_z_change q q' d hz h3 h5
  have hv := v_from_z_change q q' d hz h4 h7 hw
  have hl := low_from_z_change q q' d hz h0 h6 h10 h11 h12 ht
  have hr : rFactor q' = rFactor q := by unfold rFactor; rw [h0]
  have hs : sFactor q' = sFactor q := by unfold sFactor; rw [h6]
  rw [output_split q', hr, hs, hw, hv, hl, output_split q]
  exact assemble_z (rFactor q) (sFactor q) (w q) (v q) (low q) d (w q + C (q 7))
    ((aFactor q + C (q 4) + d) * wDelta q d) (wDelta q d) (X + C (q 0))

private theorem first_factor_increment (a x c d : R[X]) :
    a * (x + (c + d)) = a * (x + c) + d * a := by ring
private theorem first_output_increment (a b c e d f : R[X]) :
    (a + d * f) + b + c + e = (a + b + c + e) + d * f := by ac_rfl

theorem output_increment0 (q : Keys R) (delta : R) :
    output (increment q 0 delta) = output q + C delta * slope0 q := by
  have hu : u (increment q 0 delta) = u q + C delta * slope0 q := by
    change (z q + v q + C (q 10)) * (X + C (q 0 + delta)) = _
    rw [map_add]
    exact first_factor_increment (slope0 q) X (C (q 0)) (C delta)
  rw [output, hu]
  change (u q + C delta * slope0 q) + v q + s q + C (q 12) = _
  rw [output]
  exact first_output_increment ..

theorem z_increment1 (q : Keys R) (delta : R) :
    z (increment q 1 delta) = z q + C delta * (X + y + C (q 2)) := by
  change (X + y + C (q 2)) * (y + C ((q 1 + delta) + q 2)) = _
  rw [add_right_comm (q 1) delta, map_add, ← add_assoc, mul_add,
    mul_comm _ (C delta)]
  rfl

private theorem head_both_change (x y a b d : R[X]) :
    (x + y + (b + d)) * (y + (a + (b + d))) =
      (x + y + b) * (y + (a + b)) + d * (x + (a + d)) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem z_increment2 (q : Keys R) (delta : R) :
    z (increment q 2 delta) = z q + C delta * (X + C (q 1 + delta)) := by
  change (X + y + C (q 2 + delta)) * (y + C (q 1 + (q 2 + delta))) = _
  unfold z
  simp only [map_add]
  exact head_both_change X y (C (q 1)) (C (q 2)) (C delta)

variable [Nontrivial R]

theorem slope0_monic (q : Keys R) : IsMonicOfDegree (slope0 q) 12 :=
  ((v_monic q).add_left ((z_monic q).natDegree_eq ▸ (by omega : 4 < 12))).add_right
    (Char2Degree15Fast.const_lt (q 10) 12 (by omega))

theorem wDelta_degree (q : Keys R) (d : R[X]) (k : ℕ)
    (hk : k ≤ 2) (hd : d.natDegree ≤ k) : (wDelta q d).natDegree ≤ k + 2 := by
  have hy : IsMonicOfDegree (y + C (q 5 + q 3)) 2 :=
    y_monic.add_right (Char2Degree15Fast.const_lt (q 5 + q 3) 2 (by omega))
  have hs : (d + (y + C (q 5 + q 3))).natDegree ≤ 2 :=
    natDegree_add_le_of_degree_le (hd.trans hk) hy.natDegree_eq.le
  exact Char2Degree15Fast.mul_bound hd hs

theorem zTail_degree (q : Keys R) (d : R[X]) (k : ℕ)
    (hk : k ≤ 2) (hd : d.natDegree ≤ k) : (zTail q d).natDegree ≤ k + 7 := by
  have hw := wDelta_degree q d k hk hd
  have ha : (aFactor q + C (q 4) + d).natDegree ≤ 4 :=
    natDegree_add_le_of_degree_le
      ((aFactor_monic q).add_right (Char2Degree15Fast.const_lt (q 4) 4 (by omega))).natDegree_eq.le
      (hd.trans (by omega))
  have h1 : (rFactor q * ((aFactor q + C (q 4) + d) * wDelta q d)).natDegree ≤ k + 7 :=
    (Char2Degree15Fast.mul_bound (rFactor_monic q).natDegree_eq.le
      (Char2Degree15Fast.mul_bound ha hw)).trans (by omega)
  have h2 : (sFactor q * wDelta q d).natDegree ≤ k + 7 :=
    (Char2Degree15Fast.mul_bound (sFactor_monic q).natDegree_eq.le hw).trans (by omega)
  have h3 : ((X + C (q 0)) * d).natDegree ≤ k + 7 :=
    (Char2Degree15Fast.mul_bound (isMonicOfDegree_X_add_one (q 0)).natDegree_eq.le hd).trans (by omega)
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 h2) h3

theorem unit_from_z_change (q q' : Keys R) (slope : R[X]) (k : ℕ) (delta : R)
    (hk : k ≤ 2) (hs : IsMonicOfDegree slope k)
    (hz : z q' = z q + C delta * slope) (h0 : q' 0 = q 0) (h3 : q' 3 = q 3)
    (h4 : q' 4 = q 4) (h5 : q' 5 = q 5) (h6 : q' 6 = q 6)
    (h7 : q' 7 = q 7) (h10 : q' 10 = q 10) (h11 : q' 11 = q 11)
    (h12 : q' 12 = q 12) (ht : t q' = t q) :
    UnitDifference (output q) (output q') (k + 9) delta := by
  have hd : (C delta * slope).natDegree ≤ k :=
    (Char2Degree15Fast.mul_bound (natDegree_C delta).le hs.natDegree_eq.le).trans (by omega)
  have hm : IsMonicOfDegree (slope * (rFactor q * (w q + C (q 7)))) (k + 9) :=
    hs.mul ((rFactor_monic q).mul ((w_monic q).add_right
      (Char2Degree15Fast.const_lt (q 7) 8 (by omega))))
  have he := output_from_z_change q q' (C delta * slope)
    hz h0 h3 h4 h5 h6 h7 h10 h11 h12 ht
  rw [mul_assoc (C delta) slope] at he
  exact unit_difference_of_lower (output q) (output q')
    (slope * (rFactor q * (w q + C (q 7)))) (zTail q (C delta * slope))
    (k + 9) delta hm ((zTail_degree q _ k hk hd).trans_lt (by omega)) he

theorem increment0_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 0 delta)) 12 delta := by
  apply unit_difference_of_split (output q) (output (increment q 0 delta))
    (slope0 q) 12 delta 0 (by omega) (slope0_monic q)
  rw [map_zero, add_zero, output_increment0]

theorem increment1_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 1 delta)) 11 delta :=
  unit_from_z_change q (increment q 1 delta) (X + y + C (q 2)) 2 delta (by omega)
    ((y_monic.add_left (natDegree_X_le.trans_lt (by omega))).add_right
      (Char2Degree15Fast.const_lt (q 2) 2 (by omega)))
    (z_increment1 q delta) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem increment2_unit (q : Keys R) (delta : R) :
    UnitDifference (output q) (output (increment q 2 delta)) 10 delta :=
  unit_from_z_change q (increment q 2 delta) (X + C (q 1 + delta)) 1 delta (by omega)
    (isMonicOfDegree_X_add_one (q 1 + delta))
    (z_increment2 q delta) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end FastPoly.Char2Degree13Fast

