import FastPoly.Examples.Char2Degree23HighFrame
import FastPoly.Examples.Char2Degree21Frame
import Mathlib.Tactic.Ring

/-!
# Small common-increment identities for the degree-23 top frame

Only a product of three opaque quintic wires is expanded here. Its linear
change has a named monic slope; the quadratic and cubic changes remain
named lower-degree terms. The circuit itself and its coefficient baselines
are never flattened.
-/

namespace FastPoly.Char2Degree23HighDifference

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23HighFrame Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def triple (a : ℕ → R) : R[X] := E a * (G a * H a)
noncomputable def pairSlope (a : ℕ → R) : R[X] :=
  E a * H a + C (a 14 + a 5) * G a
noncomputable def nextSlope (a : ℕ → R) : R[X] := G a + C (a 14 + a 5)

omit [CharP R 2] [Nontrivial R] in
private theorem three_increment (e g h d : R[X]) :
    (e + d) * ((g + d) * (h + d)) =
      e * (g * h) + d * (e * h + (e + h) * g) +
        d ^ 2 * (g + (e + h)) + d ^ 3 := by
  ring

omit [Nontrivial R] in
theorem E_add_H (a : ℕ → R) : E a + H a = C (a 14 + a 5) := by
  change (h a + C (a 14)) + (h a + C (a 5)) = _
  rw [map_add]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

omit [CharP R 2] in
theorem triple_monic (a : ℕ → R) : IsMonicOfDegree (triple a) 15 :=
  (E_monic a).mul ((G_monic a).mul (H_monic a))

omit [CharP R 2] in
theorem pairSlope_monic (a : ℕ → R) : IsMonicOfDegree (pairSlope a) 10 := by
  have hc : (C (a 14 + a 5) * G a).natDegree < 10 := by
    apply natDegree_mul_le.trans_lt
    rw [natDegree_C, (G_monic a).natDegree_eq]
    omega
  exact ((E_monic a).mul (H_monic a)).add_right hc

omit [CharP R 2] in
theorem nextSlope_monic (a : ℕ → R) : IsMonicOfDegree (nextSlope a) 5 := by
  have hc : (C (a 14 + a 5)).natDegree < 5 := by rw [natDegree_C]; omega
  exact (G_monic a).add_right hc

noncomputable def commonTail (a : ℕ → R) (d : R[X]) : R[X] :=
  d ^ 2 * nextSlope a + d ^ 3

omit [CharP R 2] in
theorem commonTail_degree (a : ℕ → R) (d : R[X]) (k : ℕ)
    (hd : d.natDegree ≤ k) (hk : k < 5) :
    (commonTail a d).natDegree < k + 10 := by
  have hd2 : (d ^ 2).natDegree ≤ 2 * k :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hd)
  have hq : (d ^ 2 * nextSlope a).natDegree ≤ 2 * k + 5 :=
    natDegree_mul_le.trans (Nat.add_le_add hd2 (nextSlope_monic a).natDegree_eq.le)
  have hc : (d ^ 3).natDegree ≤ 3 * k :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 3 hd)
  exact (natDegree_add_le _ _).trans_lt (max_lt
    (hq.trans_lt (by omega)) (hc.trans_lt (by omega)))

/-- The common quintic increment has a unit leading coefficient at row `k+10`. -/
theorem triple_unit (a b : ℕ → R) (slope : R[X]) (k : ℕ) (delta : R)
    (hs : IsMonicOfDegree slope k) (hk : k < 5)
    (he : E b = E a + C delta * slope)
    (hg : G b = G a + C delta * slope)
    (hh : H b = H a + C delta * slope) :
    UnitDifference (triple a) (triple b) (k + 10) delta := by
  have hd : (C delta * slope).natDegree ≤ k := by
    apply natDegree_mul_le.trans
    rw [natDegree_C, hs.natDegree_eq, Nat.zero_add]
  apply Char2Degree19InnerChanges.unit_difference_of_lower
    _ _ (slope * pairSlope a) (commonTail a (C delta * slope))
    (k + 10) delta (hs.mul (pairSlope_monic a))
    (commonTail_degree a _ k hd hk)
  change E b * (G b * H b) = _
  rw [he, hg, hh, three_increment]
  simp only [E_add_H]
  change triple a + (C delta * slope) * pairSlope a +
    (C delta * slope) ^ 2 * nextSlope a + (C delta * slope) ^ 3 =
      triple a + (C delta * (slope * pairSlope a) + commonTail a (C delta * slope))
  simp only [commonTail, mul_assoc, add_assoc]

/-- The two remainders have the same fixed leading coefficient. -/
theorem remainder_sum_degree (a b : ℕ → R) :
    (remainder b + remainder a).natDegree ≤ 14 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_add]
  by_cases he : j = 15
  · subst j
    have ha : (remainder a).coeff 15 = 1 := by
      rw [← (remainder_monic a).natDegree_eq]
      exact (remainder_monic a).monic.coeff_natDegree
    have hb : (remainder b).coeff 15 = 1 := by
      rw [← (remainder_monic b).natDegree_eq]
      exact (remainder_monic b).monic.coeff_natDegree
    rw [ha, hb, CharTwo.add_self_eq_zero]
  · have hja : (remainder a).natDegree < j := by
      rw [(remainder_monic a).natDegree_eq]
      omega
    have hjb : (remainder b).natDegree < j := by
      rw [(remainder_monic b).natDegree_eq]
      omega
    have ha : (remainder a).coeff j = 0 := coeff_eq_zero_of_natDegree_lt hja
    have hb : (remainder b).coeff j = 0 := coeff_eq_zero_of_natDegree_lt hjb
    rw [ha, hb, add_zero]

/-- Transport a high-frame pivot through the named lower remainder. -/
theorem output_unit {a b : ℕ → R} {n : ℕ} {delta : R}
    (hu : UnitDifference (high a) (high b) n delta) (hn : 15 ≤ n) :
    UnitDifference (output a) (output b) n delta := by
  rw [Char2Degree23HighFrame.output_eq a, Char2Degree23HighFrame.output_eq b]
  exact Char2Degree21Frame.difference_add_lower hu
    ((remainder_sum_degree a b).trans_lt (by omega))

/-- A moving quartic-pair frame is harmless when its change is sufficiently low. -/
theorem common_output_unit (a b : ℕ → R) (slope : R[X]) (k : ℕ) (delta : R)
    (hs : IsMonicOfDegree slope k) (hk : k < 5)
    (he : E b = E a + C delta * slope)
    (hg : G b = G a + C delta * slope)
    (hh : H b = H a + C delta * slope)
    (hd : (D b + D a).natDegree ≤ k + 2) :
    UnitDifference (output a) (output b) (18 + k) delta := by
  have hu := Char2Degree21Frame.difference_mul (triple_unit a b slope k delta hs hk he hg hh)
    (D_monic a)
  have hl : (high b + D a * triple b).natDegree < 8 + (k + 10) := by
    change (D b * triple b + D a * triple b).natDegree < _
    rw [← add_mul]
    exact (natDegree_mul_le.trans
      (Nat.add_le_add hd (triple_monic b).natDegree_eq.le)).trans_lt (by omega)
  have hf : UnitDifference (high a) (high b) (8 + (k + 10)) delta :=
    Char2Degree21Frame.difference_lower hu hl
  have hn : 8 + (k + 10) = 18 + k := by omega
  rw [hn] at hf
  exact output_unit hf (by omega)

end FastPoly.Char2Degree23HighDifference
