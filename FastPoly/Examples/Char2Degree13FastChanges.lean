import FastPoly.Examples.Char2Degree13FastCore

/-! Exact changes of the supplied degree-thirteen tail coordinates.
Each identity changes named gates only; rFactor*v+sFactor*w is never expanded
into input coefficients. The active simultaneous a3/a4 change is retained. -/

namespace FastPoly.Char2Degree13Fast

set_option maxHeartbeats 20000

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

def increment (q : Keys R) (i : Fin 13) (delta : R) : Keys R :=
  Function.update q i (q i + delta)

noncomputable def slope3 (q : Keys R) : R[X] :=
  cFactor q * (aFactor q + C (q 5))
noncomputable def slope4 (q : Keys R) : R[X] :=
  rFactor q * (w q + C (q 7))
noncomputable def slope5 (q : Keys R) : R[X] := cFactor q * bFactor q
noncomputable def slope6 (q : Keys R) : R[X] := w q + t q + C (q 11)
noncomputable def slope7 (q : Keys R) : R[X] :=
  rFactor q * (aFactor q + C (q 4))
noncomputable def slope8 (q : Keys R) (delta : R) : R[X] :=
  sFactor q * (y + C (q 9 + delta))
noncomputable def slope9 (q : Keys R) : R[X] := sFactor q * (X + C (q 8))
noncomputable def slope10 (q : Keys R) : R[X] := X + C (q 0)
noncomputable def slope11 (q : Keys R) : R[X] := sFactor q

private theorem right_offset (a b c d : R[X]) :
    a * (b + (c + d)) = a * (b + c) + d * a := by ring
private theorem left_offset (a b c d : R[X]) :
    (a + (c + d)) * b = (a + c) * b + d * b := by ring
private theorem nested_right (a b c d e : R[X]) :
    a * (b + d * e + c) = a * (b + c) + d * (a * e) := by ring

theorem w_increment3 (q : Keys R) (delta : R) :
    w (increment q 3 delta) = w q + C delta * (aFactor q + C (q 5)) := by
  change (aFactor q + C (q 5)) * (z q + C (q 3 + delta)) = _
  rw [map_add]
  exact right_offset (aFactor q + C (q 5)) (z q) (C (q 3)) (C delta)

theorem w_increment5 (q : Keys R) (delta : R) :
    w (increment q 5 delta) = w q + C delta * bFactor q := by
  change (aFactor q + C (q 5 + delta)) * bFactor q = _
  rw [map_add]
  exact left_offset (aFactor q) (bFactor q) (C (q 5)) (C delta)

private theorem assemble_w (r s w v e d a b : R[X]) :
    r * (v + d * (a * b)) + s * (w + d * b) + e =
      (r * v + s * w + e) + d * ((r * a + s) * b) := by ring

theorem output_from_w_change (q q' : Keys R) (delta : R) (slope : R[X])
    (hr : rFactor q' = rFactor q) (hs : sFactor q' = sFactor q)
    (ha : aFactor q' + C (q' 4) = aFactor q + C (q 4))
    (h7 : q' 7 = q 7) (hl : low q' = low q)
    (hw : w q' = w q + C delta * slope) :
    output q' = output q + C delta * (cFactor q * slope) := by
  have hv : v q' = v q + C delta * ((aFactor q + C (q 4)) * slope) := by
    change (aFactor q' + C (q' 4)) * (w q' + C (q' 7)) = _
    rw [ha, hw, h7]
    exact nested_right (aFactor q + C (q 4)) (w q) (C (q 7)) (C delta) slope
  rw [output_split q', hr, hs, hv, hw, hl, output_split q]
  exact assemble_w (rFactor q) (sFactor q) (w q) (v q) (low q) (C delta)
    (aFactor q + C (q 4)) slope

theorem output_increment3 (q : Keys R) (delta : R) :
    output (increment q 3 delta) = output q + C delta * slope3 q :=
  output_from_w_change q (increment q 3 delta) delta (aFactor q + C (q 5))
    rfl rfl rfl rfl rfl (w_increment3 q delta)

theorem output_increment5 (q : Keys R) (delta : R) :
    output (increment q 5 delta) = output q + C delta * slope5 q :=
  output_from_w_change q (increment q 5 delta) delta (bFactor q)
    rfl rfl rfl rfl rfl (w_increment5 q delta)

private theorem assemble_v (r s w v e d a : R[X]) :
    r * (v + d * a) + s * w + e = (r * v + s * w + e) + d * (r * a) := by ring

theorem output_from_v_change (q q' : Keys R) (delta : R) (slope : R[X])
    (hr : rFactor q' = rFactor q) (hs : sFactor q' = sFactor q)
    (hw : w q' = w q) (hl : low q' = low q)
    (hv : v q' = v q + C delta * slope) :
    output q' = output q + C delta * (rFactor q * slope) := by
  rw [output_split q', hr, hs, hw, hl, hv, output_split q]
  exact assemble_v ..

theorem v_increment4 (q : Keys R) (delta : R) :
    v (increment q 4 delta) = v q + C delta * (w q + C (q 7)) := by
  change (aFactor q + C (q 4 + delta)) * (w q + C (q 7)) = _
  rw [map_add]
  exact left_offset (aFactor q) (w q + C (q 7)) (C (q 4)) (C delta)

theorem output_increment4 (q : Keys R) (delta : R) :
    output (increment q 4 delta) = output q + C delta * slope4 q :=
  output_from_v_change q (increment q 4 delta) delta (w q + C (q 7))
    rfl rfl rfl rfl (v_increment4 q delta)

theorem v_increment7 (q : Keys R) (delta : R) :
    v (increment q 7 delta) = v q + C delta * (aFactor q + C (q 4)) := by
  change (aFactor q + C (q 4)) * (w q + C (q 7 + delta)) = _
  rw [map_add]
  exact right_offset (aFactor q + C (q 4)) (w q) (C (q 7)) (C delta)

theorem output_increment7 (q : Keys R) (delta : R) :
    output (increment q 7 delta) = output q + C delta * slope7 q :=
  output_from_v_change q (increment q 7 delta) delta (aFactor q + C (q 4))
    rfl rfl rfl rfl (v_increment7 q delta)

private theorem assemble_sum (a b c e d f : R[X]) :
    a + b + (c + d * f) + e = (a + b + c + e) + d * f := by ac_rfl

theorem output_from_s_change (q q' : Keys R) (delta : R) (slope : R[X])
    (hu : u q' = u q) (hv : v q' = v q) (hc : q' 12 = q 12)
    (hs : s q' = s q + C delta * slope) :
    output q' = output q + C delta * slope := by
  change u q' + v q' + s q' + C (q' 12) = _
  rw [hu, hv, hs, hc, output]
  exact assemble_sum ..

theorem output_increment6 (q : Keys R) (delta : R) :
    output (increment q 6 delta) = output q + C delta * slope6 q := by
  apply output_from_s_change q (increment q 6 delta) delta (slope6 q) rfl rfl rfl
  change (w q + t q + C (q 11)) * (y + C (q 6 + delta)) = _
  rw [map_add]
  exact right_offset (w q + t q + C (q 11)) y (C (q 6)) (C delta)

private theorem both_t_factors (x y a b d : R[X]) :
    (x + y + ((a + d) + b)) * (x + (a + d)) =
      (x + y + (a + b)) * (x + a) + d * (y + (b + d)) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem t_increment8 (q : Keys R) (delta : R) :
    t (increment q 8 delta) = t q + C delta * (y + C (q 9 + delta)) := by
  change (X + y + C ((q 8 + delta) + q 9)) * (X + C (q 8 + delta)) = _
  unfold t
  simp only [map_add]
  exact both_t_factors X y (C (q 8)) (C (q 9)) (C delta)

theorem t_increment9 (q : Keys R) (delta : R) :
    t (increment q 9 delta) = t q + C delta * (X + C (q 8)) := by
  change (X + y + C (q 8 + (q 9 + delta))) * (X + C (q 8)) = _
  rw [← add_assoc (q 8), map_add]
  exact left_offset (X + y) (X + C (q 8)) (C (q 8 + q 9)) (C delta)

private theorem nested_t (w t c s d a : R[X]) :
    (w + (t + d * a) + c) * s = (w + t + c) * s + d * (s * a) := by ring

theorem s_from_t_change (q q' : Keys R) (delta : R) (slope : R[X])
    (hw : w q' = w q) (hs : sFactor q' = sFactor q) (hc : q' 11 = q 11)
    (ht : t q' = t q + C delta * slope) :
    s q' = s q + C delta * (sFactor q * slope) := by
  change (w q' + t q' + C (q' 11)) * sFactor q' = _
  rw [hw, ht, hs, hc, s]
  exact nested_t ..

theorem output_increment8 (q : Keys R) (delta : R) :
    output (increment q 8 delta) = output q + C delta * slope8 q delta :=
  output_from_s_change q (increment q 8 delta) delta (slope8 q delta) rfl rfl rfl
    (s_from_t_change q (increment q 8 delta) delta (y + C (q 9 + delta))
      rfl rfl rfl (t_increment8 q delta))

theorem output_increment9 (q : Keys R) (delta : R) :
    output (increment q 9 delta) = output q + C delta * slope9 q :=
  output_from_s_change q (increment q 9 delta) delta (slope9 q) rfl rfl rfl
    (s_from_t_change q (increment q 9 delta) delta (X + C (q 8))
      rfl rfl rfl (t_increment9 q delta))

private theorem assemble_first (a b c e d f : R[X]) :
    (a + d * f) + b + c + e = (a + b + c + e) + d * f := by ac_rfl

theorem output_increment10 (q : Keys R) (delta : R) :
    output (increment q 10 delta) = output q + C delta * slope10 q := by
  have hu : u (increment q 10 delta) = u q + C delta * (X + C (q 0)) := by
    change (z q + v q + C (q 10 + delta)) * (X + C (q 0)) = _
    rw [map_add]
    exact left_offset (z q + v q) (X + C (q 0)) (C (q 10)) (C delta)
  rw [output, hu]
  change (u q + C delta * (X + C (q 0))) + v q + s q + C (q 12) = _
  rw [output]
  exact assemble_first ..

theorem output_increment11 (q : Keys R) (delta : R) :
    output (increment q 11 delta) = output q + C delta * slope11 q := by
  apply output_from_s_change q (increment q 11 delta) delta (slope11 q) rfl rfl rfl
  change (w q + t q + C (q 11 + delta)) * sFactor q = _
  rw [map_add]
  exact left_offset (w q + t q) (sFactor q) (C (q 11)) (C delta)

theorem output_increment12 (q : Keys R) (delta : R) :
    output (increment q 12 delta) = output q + C delta := by
  change u q + v q + s q + C (q 12 + delta) = _
  rw [map_add, ← add_assoc]
  rfl

end FastPoly.Char2Degree13Fast
