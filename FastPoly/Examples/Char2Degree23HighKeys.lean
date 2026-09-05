import FastPoly.Examples.Char2Degree23Keys
import FastPoly.Examples.Char2Degree23HighPivots
import FastPoly.Examples.Char2Degree23SeamPivots

/-!
# The supplied normalized keys at the eight leading degree-23 pivots

Only nine raw slots enter the high frame. The other key-coordinate changes,
including the row-eight baseline correction, affect a remainder whose leading
coefficient is fixed. Thus the checked raw pivots transfer without expanding
any of the nonlinear lower-key formulas.
-/

namespace FastPoly.Char2Degree23HighKeys

open Polynomial Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23HighDifference Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

structure SameTop (a b : ℕ → R) : Prop where
  h0 : a 0 = b 0
  h1 : a 1 = b 1
  h2 : a 2 = b 2
  h3 : a 3 = b 3
  h4 : a 4 = b 4
  h5 : a 5 = b 5
  h14 : a 14 = b 14
  h18 : a 18 = b 18
  h20 : a 20 = b 20

theorem SameTop.high_eq {a b : ℕ → R} (he : SameTop a b) : high a = high b := by
  have hz : z a = z b := by rw [z, he.h0, he.h1]; rfl
  have ht : t a = t b := by rw [t, he.h2, he.h3, hz]; rfl
  have hh : h a = h b := by rw [h, hz, ht]; rfl
  have hf : lastFactor a = lastFactor b := by rw [lastFactor, hz, he.h20]; rfl
  have hb : crownLeft a = crownLeft b := by rw [crownLeft, hz, he.h18]; rfl
  have hd : D a = D b := by rw [D, hf, hb]; rfl
  have he' : E a = E b := by rw [E, hh, he.h14]; rfl
  have hg : G a = G b := by rw [G, hh, he.h4]; rfl
  have hr : H a = H b := by rw [H, hh, he.h5]; rfl
  rw [high, hd, he', hg, hr]
  rfl

private theorem cancel_high (h p q : R[X]) :
    (h + p) + (h + q) = p + q := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem SameTop.output_difference_degree {a b : ℕ → R} (he : SameTop a b) :
    (output b + output a).natDegree ≤ 14 := by
  rw [Char2Degree23HighFrame.output_eq b, Char2Degree23HighFrame.output_eq a,
    ← he.high_eq, cancel_high]
  exact remainder_sum_degree a b

/-- The actual original-key circuit environment after the supplied inverse. -/
noncomputable def rawKeys (q : Fin 23 → R) : ℕ → R :=
  Char2Degree23Keys.raw (Char2Degree23Keys.keyEquiv q)

def increment (q : Fin 23 → R) (i : Fin 23) (delta : R) : Fin 23 → R :=
  Function.update q i (q i + delta)

theorem top0 (q : Fin 23 → R) : rawKeys q 0 = q 2 := by
  change Char2Degree23Keys.keyEquiv q 0 = _
  rw [Char2Degree23Keys.keyEquiv_other q 0 (by omega)]
  rfl

theorem top1 (q : Fin 23 → R) : rawKeys q 1 = q 1 + q 2 := by
  change Char2Degree23Keys.keyEquiv q 1 = _
  rw [Char2Degree23Keys.keyEquiv_other q 1 (by omega)]
  rfl

theorem top2 (q : Fin 23 → R) : rawKeys q 2 = q 0 := by
  change Char2Degree23Keys.keyEquiv q 2 = _
  rw [Char2Degree23Keys.keyEquiv_other q 2 (by omega)]
  rfl

theorem top3 (q : Fin 23 → R) : rawKeys q 3 = q 3 + q 5 + q 6 := by
  change Char2Degree23Keys.keyEquiv q 3 = _
  rw [Char2Degree23Keys.keyEquiv_other q 3 (by omega)]
  change q 3 + (q 5 + q 6) = _
  ac_rfl

theorem top4 (q : Fin 23 → R) : rawKeys q 4 = q 4 + q 5 + q 6 + q 7 := by
  change Char2Degree23Keys.keyEquiv q 4 = _
  rw [Char2Degree23Keys.keyEquiv_other q 4 (by omega)]
  change q 4 + (q 7 + q 5 + q 6) = _
  ac_rfl

theorem top5 (q : Fin 23 → R) : rawKeys q 5 = q 16 := by
  change Char2Degree23Keys.keyEquiv q 5 = _
  rw [Char2Degree23Keys.keyEquiv_other q 5 (by omega)]
  rfl

theorem top14 (q : Fin 23 → R) : rawKeys q 14 = q 7 + q 16 := by
  change Char2Degree23Keys.keyEquiv q 14 = _
  rw [Char2Degree23Keys.keyEquiv_other q 14 (by omega)]
  rfl

theorem top18 (q : Fin 23 → R) : rawKeys q 18 = q 5 := by
  change Char2Degree23Keys.keyEquiv q 18 = _
  rw [Char2Degree23Keys.keyEquiv_other q 18 (by omega)]
  rfl

theorem top20 (q : Fin 23 → R) : rawKeys q 20 = q 6 := by
  change Char2Degree23Keys.keyEquiv q 20 = _
  rw [Char2Degree23Keys.keyEquiv_other q 20 (by omega)]
  rfl

theorem top_increment0 (q : Fin 23 → R) (delta : R) :
    SameTop (Char2Degree23HighPivots.shift0 (rawKeys q) delta)
      (rawKeys (increment q 0 delta)) := by
  constructor <;>
    simp only [Char2Degree23HighPivots.shift0, top0, top1, top2, top3, top4, top5, top14, top18, top20] <;>
    dsimp [increment, Function.update] <;> ac_rfl

theorem increment0_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 0 delta))) 22 delta :=
  Char2Degree21Frame.difference_lower
    (Char2Degree23HighPivots.shift0_unit (rawKeys q) delta)
    ((top_increment0 q delta).output_difference_degree.trans_lt (by omega))

theorem top_increment1 (q : Fin 23 → R) (delta : R) :
    SameTop (Char2Degree23HighPivots.shift1 (rawKeys q) delta)
      (rawKeys (increment q 1 delta)) := by
  constructor <;>
    simp only [Char2Degree23HighPivots.shift1, top0, top1, top2, top3, top4, top5, top14, top18, top20] <;>
    dsimp [increment, Function.update] <;> ac_rfl

theorem increment1_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 1 delta))) 21 delta :=
  Char2Degree21Frame.difference_lower
    (Char2Degree23HighPivots.shift1_unit (rawKeys q) delta)
    ((top_increment1 q delta).output_difference_degree.trans_lt (by omega))

theorem top_increment2 (q : Fin 23 → R) (delta : R) :
    SameTop (Char2Degree23HighPivots.shift2 (rawKeys q) delta)
      (rawKeys (increment q 2 delta)) := by
  constructor <;>
    simp only [Char2Degree23HighPivots.shift2, top0, top1, top2, top3, top4, top5, top14, top18, top20] <;>
    dsimp [increment, Function.update] <;> ac_rfl

theorem increment2_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 2 delta))) 20 delta :=
  Char2Degree21Frame.difference_lower
    (Char2Degree23HighPivots.shift2_unit (rawKeys q) delta)
    ((top_increment2 q delta).output_difference_degree.trans_lt (by omega))

theorem top_increment3 (q : Fin 23 → R) (delta : R) :
    SameTop (Char2Degree23HighPivots.shift3 (rawKeys q) delta)
      (rawKeys (increment q 3 delta)) := by
  constructor <;>
    simp only [Char2Degree23HighPivots.shift3, top0, top1, top2, top3, top4, top5, top14, top18, top20] <;>
    dsimp [increment, Function.update] <;> ac_rfl

theorem increment3_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 3 delta))) 19 delta :=
  Char2Degree21Frame.difference_lower
    (Char2Degree23HighPivots.shift3_unit (rawKeys q) delta)
    ((top_increment3 q delta).output_difference_degree.trans_lt (by omega))

theorem top_increment4 (q : Fin 23 → R) (delta : R) :
    SameTop (Char2Degree23HighPivots.shift4 (rawKeys q) delta)
      (rawKeys (increment q 4 delta)) := by
  constructor <;>
    simp only [Char2Degree23HighPivots.shift4, top0, top1, top2, top3, top4, top5, top14, top18, top20] <;>
    dsimp [increment, Function.update] <;> ac_rfl

theorem increment4_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 4 delta))) 18 delta :=
  Char2Degree21Frame.difference_lower
    (Char2Degree23HighPivots.shift4_unit (rawKeys q) delta)
    ((top_increment4 q delta).output_difference_degree.trans_lt (by omega))

theorem top_increment5 (q : Fin 23 → R) (delta : R) :
    SameTop (Char2Degree23SeamPivots.shift5 (rawKeys q) delta)
      (rawKeys (increment q 5 delta)) := by
  constructor <;>
    simp only [Char2Degree23SeamPivots.shift5, top0, top1, top2, top3, top4, top5, top14, top18, top20] <;>
    dsimp [increment, Function.update] <;> ac_rfl

theorem increment5_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 5 delta))) 17 delta :=
  Char2Degree21Frame.difference_lower
    (Char2Degree23SeamPivots.shift5_unit (rawKeys q) delta)
    ((top_increment5 q delta).output_difference_degree.trans_lt (by omega))

theorem top_increment6 (q : Fin 23 → R) (delta : R) :
    SameTop (Char2Degree23SeamPivots.shift6 (rawKeys q) delta)
      (rawKeys (increment q 6 delta)) := by
  constructor <;>
    simp only [Char2Degree23SeamPivots.shift6, top0, top1, top2, top3, top4, top5, top14, top18, top20] <;>
    dsimp [increment, Function.update] <;> ac_rfl

theorem increment6_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 6 delta))) 16 delta :=
  Char2Degree21Frame.difference_lower
    (Char2Degree23SeamPivots.shift6_unit (rawKeys q) delta)
    ((top_increment6 q delta).output_difference_degree.trans_lt (by omega))

theorem top_increment7 (q : Fin 23 → R) (delta : R) :
    SameTop (Char2Degree23SeamPivots.shift7 (rawKeys q) delta)
      (rawKeys (increment q 7 delta)) := by
  constructor <;>
    simp only [Char2Degree23SeamPivots.shift7, top0, top1, top2, top3, top4, top5, top14, top18, top20] <;>
    dsimp [increment, Function.update] <;> ac_rfl

theorem increment7_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 7 delta))) 15 delta :=
  Char2Degree21Frame.difference_lower
    (Char2Degree23SeamPivots.shift7_unit (rawKeys q) delta)
    ((top_increment7 q delta).output_difference_degree.trans_lt (by omega))

end FastPoly.Char2Degree23HighKeys
