import FastPoly.Examples.Char2Degree23MiddleCoordinates
import FastPoly.Examples.Char2Degree23MiddlePivots
import FastPoly.Examples.Char2Degree23LowKeys

/-! Transport the six checked middle pivots through the supplied key inverse. -/

namespace FastPoly.Char2Degree23MiddleKeys

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23HighKeys Char2Degree23LowKeys Char2Degree23MiddleFrame
  Char2Degree23MiddlePivots Char2Degree23MiddleCoordinates Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

structure SameRaw (a b : ℕ → R) : Prop where
  h0 : a 0 = b 0
  h1 : a 1 = b 1
  h2 : a 2 = b 2
  h3 : a 3 = b 3
  h4 : a 4 = b 4
  h5 : a 5 = b 5
  h6 : a 6 = b 6
  h7 : a 7 = b 7
  h8 : a 8 = b 8
  h9 : a 9 = b 9
  h10 : a 10 = b 10
  h11 : a 11 = b 11
  h12 : a 12 = b 12
  h13 : a 13 = b 13
  h14 : a 14 = b 14
  h15 : a 15 = b 15
  h16 : a 16 = b 16
  h17 : a 17 = b 17
  h18 : a 18 = b 18
  h20 : a 20 = b 20
  h21 : a 21 = b 21
  h22 : a 22 = b 22

private theorem offset_difference (p d : R[X]) (c c' : R) :
    (p + d * C c') + (p + d * C c) = d * C (c' + c) := by
  simp only [map_add, mul_add]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem SameRaw.output_difference_degree {a b : ℕ → R} (he : SameRaw a b) :
    (output b + output a).natDegree ≤ 8 := by
  have hz : z a = z b := by rw [z, he.h0, he.h1]; rfl
  have ht : t a = t b := by rw [t, he.h2, hz, he.h3]; rfl
  have hu : u a = u b := by rw [u, hz, ht, he.h4, he.h5]; rfl
  have hv : v a = v b := by rw [v, he.h6, hz, he.h7]; rfl
  have hw : w a = w b := by rw [w, hz, he.h8, hv, he.h9]; rfl
  have hs : s a = s b := by rw [s, hz, he.h10, hv, he.h11]; rfl
  have hr : r a = r b := by rw [r, ht, he.h12, hu, he.h13]; rfl
  have hg : g a = g b := by rw [g, hz, ht, he.h14, hu, he.h15]; rfl
  have hl : ell a = ell b := by rw [ell, he.h16, hz, hv, he.h17]; rfl
  have hcl : crownLeft a = crownLeft b := by rw [crownLeft, hz, he.h18]; rfl
  have hcr : crownRight a = crownRight b := by rw [crownRight, hz, hw, hs, hg, hl]; rfl
  have hf : lastFactor a = lastFactor b := by rw [lastFactor, hz, he.h20]; rfl
  have hh : head a = head b := by rw [head, hv, hw, hs, hr, hg]; rfl
  have hc : baseline a = baseline b := by rw [baseline, hh, hf, hu, hcl, hcr, he.h21]; rfl
  have hd : D a = D b := by rw [D, hf, hcl]; rfl
  have hout (c : ℕ → R) : output c = (baseline c + C (c 22)) + D c * C (c 19) := by
    change finish c (c 19) (c 22) = _
    rw [finish_eq]
    change (baseline c + D c * C (c 19)) + C (c 22) = _
    simp only [add_assoc, add_comm, add_left_comm]
  rw [hout b, hout a, ← hc, ← hd, ← he.h22, offset_difference]
  apply natDegree_mul_le.trans
  rw [(D_monic a).natDegree_eq, natDegree_C, add_zero]

theorem correction_rawKeys (q : Fin 23 → R) (d : R) :
    correction (rawKeys q) d = d * Char2Degree23Coordinates.eta q := by
  unfold correction Char2Degree23MiddlePivots.eta
  rw [top14, top5, rawKeys_core _ 15 (by omega) (by omega)]
  change d * ((q 7 + q 16) * q 16 + q 20) = _
  rw [add_mul, ← pow_two]
  rfl

theorem slots8 (q : Fin 23 → R) (d : R) :
    SameRaw (shift8 (rawKeys q) d) (rawKeys (increment q 8 d)) := by
  constructor <;>
    simp only [shift8, offset11, offset6, correction_rawKeys] <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_8 q d).symm | exact (a9_8 q d).symm |
    exact (a10_8 q d).symm | exact (a11_8 q d).symm

theorem slots9 (q : Fin 23 → R) (d : R) :
    SameRaw (shift9 (rawKeys q) d) (rawKeys (increment q 9 d)) := by
  constructor <;>
    simp only [shift9, offset8, commonOffsets, correction_rawKeys] <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_9 q d).symm | exact (a9_9 q d).symm |
    exact (a10_9 q d).symm | exact (a11_9 q d).symm

theorem slots10 (q : Fin 23 → R) (d : R) :
    SameRaw (shift10 (rawKeys q) d) (rawKeys (increment q 10 d)) := by
  constructor <;> simp only [shift10, offset9] <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a9_10 q d).symm

theorem slots11 (q : Fin 23 → R) (d : R) :
    SameRaw (shift11 (rawKeys q) d) (rawKeys (increment q 11 d)) := by
  constructor <;>
    simp only [shift11, offset7, commonOffsets, correction_rawKeys] <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_11 q d).symm | exact (a9_11 q d).symm |
    exact (a10_11 q d).symm | exact (a11_11 q d).symm |
    (change (q 11 + Char2Degree23Coordinates.eta q) + d =
      (q 11 + d) + Char2Degree23Coordinates.eta q;
      simp only [add_assoc, add_comm, add_left_comm])

theorem slots12 (q : Fin 23 → R) (d : R) :
    SameRaw (Char2Degree23MiddlePivots.shift12 (rawKeys q) d) (rawKeys (increment q 12 d)) := by
  constructor <;> simp only [Char2Degree23MiddlePivots.shift12, offset10, offset8] <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_12 q d).symm | exact (a10_12 q d).symm

theorem slots13 (q : Fin 23 → R) (d : R) :
    SameRaw (Char2Degree23MiddlePivots.shift13 (rawKeys q) d) (rawKeys (increment q 13 d)) := by
  constructor <;> simp only [Char2Degree23MiddlePivots.shift13, commonOffsets] <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_13 q d).symm | exact (a9_13 q d).symm |
    exact (a10_13 q d).symm | exact (a11_13 q d).symm

theorem increment8_unit (q : Fin 23 → R) (d : R) :
    UnitDifference (output (rawKeys q)) (output (rawKeys (increment q 8 d))) 14 d :=
  Char2Degree21Frame.difference_lower (Char2Degree23MiddlePivots.shift8_unit (rawKeys q) d)
    ((slots8 q d).output_difference_degree.trans_lt (by omega))

theorem increment9_unit (q : Fin 23 → R) (d : R) :
    UnitDifference (output (rawKeys q)) (output (rawKeys (increment q 9 d))) 13 d :=
  Char2Degree21Frame.difference_lower (Char2Degree23MiddlePivots.shift9_unit (rawKeys q) d)
    ((slots9 q d).output_difference_degree.trans_lt (by omega))

theorem increment10_unit (q : Fin 23 → R) (d : R) :
    UnitDifference (output (rawKeys q)) (output (rawKeys (increment q 10 d))) 12 d :=
  Char2Degree21Frame.difference_lower (Char2Degree23MiddlePivots.shift10_unit (rawKeys q) d)
    ((slots10 q d).output_difference_degree.trans_lt (by omega))

theorem increment11_unit (q : Fin 23 → R) (d : R) :
    UnitDifference (output (rawKeys q)) (output (rawKeys (increment q 11 d))) 11 d :=
  Char2Degree21Frame.difference_lower (Char2Degree23MiddlePivots.shift11_unit (rawKeys q) d)
    ((slots11 q d).output_difference_degree.trans_lt (by omega))

theorem increment12_unit (q : Fin 23 → R) (d : R) :
    UnitDifference (output (rawKeys q)) (output (rawKeys (increment q 12 d))) 10 d :=
  Char2Degree21Frame.difference_lower (Char2Degree23MiddlePivots.shift12_unit (rawKeys q) d)
    ((slots12 q d).output_difference_degree.trans_lt (by omega))

theorem increment13_unit (q : Fin 23 → R) (d : R) :
    UnitDifference (output (rawKeys q)) (output (rawKeys (increment q 13 d))) 9 d :=
  Char2Degree21Frame.difference_lower (Char2Degree23MiddlePivots.shift13_unit (rawKeys q) d)
    ((slots13 q d).output_difference_degree.trans_lt (by omega))

end FastPoly.Char2Degree23MiddleKeys
