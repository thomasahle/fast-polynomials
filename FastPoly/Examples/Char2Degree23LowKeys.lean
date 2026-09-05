import FastPoly.Examples.Char2Degree23LowFrame

/-!
# Supplied normalized keys for the low linear degree-23 updates

These proofs read only the displayed scalar coordinates. In particular the
row-eight baseline is never unfolded. Its effect is removed by the explicit
unit-slope peel from the preceding module.
-/

namespace FastPoly.Char2Degree23LowKeys

open Polynomial Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23HighKeys Char2Degree23LowFrame Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem rawKeys_core (q : Fin 23 → R) (i : ℕ) (hi : i < 23) (hne : i ≠ 19) :
    rawKeys q i = Char2Degree23Coordinates.keysCore q ⟨i, hi⟩ := by
  unfold rawKeys Char2Degree23Keys.raw
  simp only [Nat.mod_eq_of_lt hi]
  exact Char2Degree23Keys.keyEquiv_other q ⟨i, hi⟩ (by
    intro he
    have hv := congrArg Fin.val he
    exact hne hv)

theorem slots14 (q : Fin 23 → R) (delta : R) :
    SameSlots (rawKeys q) (rawKeys (increment q 14 delta)) := by
  constructor <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)] <;> rfl

theorem slots17 (q : Fin 23 → R) (delta : R) :
    SameSlots (rawKeys q) (rawKeys (increment q 17 delta)) := by
  constructor <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)] <;> rfl

theorem slots19 (q : Fin 23 → R) (delta : R) :
    SameSlots (rawKeys q) (rawKeys (increment q 19 delta)) := by
  constructor <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)] <;> rfl

theorem slots22 (q : Fin 23 → R) (delta : R) :
    SameSlots (rawKeys q) (rawKeys (increment q 22 delta)) := by
  constructor <;>
    rw [rawKeys_core _ _ (by omega) (by omega),
      rawKeys_core _ _ (by omega) (by omega)] <;> rfl

theorem slot13 (q : Fin 23 → R) : rawKeys q 13 = q 17 + q 18 := by
  rw [rawKeys_core _ _ (by omega) (by omega)]
  rfl

theorem slot21 (q : Fin 23 → R) : rawKeys q 21 = q 19 := by
  rw [rawKeys_core _ _ (by omega) (by omega)]
  rfl

theorem slot22 (q : Fin 23 → R) : rawKeys q 22 = q 22 := by
  rw [rawKeys_core _ _ (by omega) (by omega)]
  rfl

theorem same_row_eight (q : Fin 23 → R) (i : Fin 23) (delta : R) (hi : i ≠ 14) :
    (output (rawKeys (increment q i delta))).coeff 8 = (output (rawKeys q)).coeff 8 := by
  change (output (Char2Degree23Keys.raw (Char2Degree23Keys.keyEquiv _))).coeff 8 =
    (output (Char2Degree23Keys.raw (Char2Degree23Keys.keyEquiv _))).coeff 8
  rw [Char2Degree23Keys.output_fourteen, Char2Degree23Keys.output_fourteen]
  exact Function.update_of_ne (Ne.symm hi) ..

private theorem offset_sum (x y d : R) : ((x + d) + y) + (x + y) = d := by
  rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero, Char2Decoder.cancel_tail]

theorem increment17_change (q : Fin 23 → R) (delta : R) :
    output (rawKeys (increment q 17 delta)) =
      output (rawKeys q) + linear (rawKeys q) * C delta := by
  have he := (slots17 q delta).peel (same_row_eight q 17 delta (by omega))
  rw [slot13, slot13, slot21, slot21, slot22, slot22] at he
  dsimp [increment, Function.update] at he
  rw [offset_sum, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    map_zero, mul_zero, add_zero, add_zero] at he
  exact he

theorem increment17_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q)) (output (rawKeys (increment q 17 delta))) 5 delta := by
  apply unit_difference_of_split _ _ (linear (rawKeys q)) 5 delta 0 (by omega)
    (linear_monic (rawKeys q))
  rw [map_zero, add_zero, mul_comm]
  exact increment17_change q delta

theorem increment19_change (q : Fin 23 → R) (delta : R) :
    output (rawKeys (increment q 19 delta)) =
      output (rawKeys q) + lastFactor (rawKeys q) * C delta := by
  have he := (slots19 q delta).peel (same_row_eight q 19 delta (by omega))
  rw [slot13, slot13, slot21, slot21, slot22, slot22] at he
  dsimp [increment, Function.update] at he
  simp only [CharTwo.add_self_eq_zero, Char2Decoder.cancel_tail,
    map_zero, mul_zero, zero_add, add_zero] at he
  exact he

theorem increment22_change (q : Fin 23 → R) (delta : R) :
    output (rawKeys (increment q 22 delta)) = output (rawKeys q) + C delta := by
  have he := (slots22 q delta).peel (same_row_eight q 22 delta (by omega))
  rw [slot13, slot13, slot21, slot21, slot22, slot22] at he
  dsimp [increment, Function.update] at he
  simp only [CharTwo.add_self_eq_zero, Char2Decoder.cancel_tail,
    map_zero, mul_zero, zero_add] at he
  exact he

theorem increment22_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q)) (output (rawKeys (increment q 22 delta))) 0 delta := by
  have hd : output (rawKeys (increment q 22 delta)) + output (rawKeys q) = C delta := by
    rw [increment22_change, Char2Decoder.cancel_tail]
  constructor
  · rw [hd, natDegree_C]
  · rw [hd, coeff_C_zero]

/-- Coordinate 14 is the already installed row-eight value. -/
theorem increment14_change (q : Fin 23 → R) (delta : R) :
    output (rawKeys (increment q 14 delta)) =
      output (rawKeys q) + D (rawKeys q) * C delta := by
  have he := (slots14 q delta).output_difference
  rw [slot13, slot13, slot21, slot21, slot22, slot22] at he
  dsimp [increment, Function.update] at he
  simp only [CharTwo.add_self_eq_zero, map_zero, mul_zero, zero_add, add_zero] at he
  have hk : rawKeys (increment q 14 delta) 19 + rawKeys q 19 = delta := by
    have hc := congrArg (fun p : R[X] => p.coeff 8) he
    have hm : (D (rawKeys q)).coeff 8 = 1 := by
      rw [← (D_monic (rawKeys q)).natDegree_eq]
      exact (D_monic (rawKeys q)).monic.coeff_natDegree
    change (output (rawKeys (increment q 14 delta)) + output (rawKeys q)).coeff 8 =
      (D (rawKeys q) * C _).coeff 8 at hc
    rw [coeff_add, coeff_mul_C, hm, one_mul] at hc
    have hq (q' : Fin 23 → R) : (output (rawKeys q')).coeff 8 = q' 14 :=
      Char2Degree23Keys.output_fourteen q'
    rw [hq, hq] at hc
    dsimp [increment, Function.update] at hc
    rw [Char2Decoder.cancel_tail] at hc
    exact hc.symm
  dsimp only [increment] at hk ⊢
  rw [hk] at he
  have hcancel (p q d : R[X]) (h : q + p = d) : q = p + d := by
    rw [← h, ← add_assoc, add_comm p q, CharTwo.add_cancel_right]
  exact hcancel _ _ _ he

theorem increment14_unit (q : Fin 23 → R) (delta : R) :
    UnitDifference (output (rawKeys q)) (output (rawKeys (increment q 14 delta))) 8 delta := by
  apply unit_difference_of_split _ _ (D (rawKeys q)) 8 delta 0 (by omega)
    (D_monic (rawKeys q))
  rw [map_zero, add_zero, mul_comm]
  exact increment14_change q delta

end FastPoly.Char2Degree23LowKeys
