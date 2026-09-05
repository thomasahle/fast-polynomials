import FastPoly.Examples.Char2Degree25HighFrame
import FastPoly.Examples.Char2Degree19InnerChanges

/-! Telescope the supplied product of five named monic quintics.
No factor is expanded into input coefficients. A common change to the five
factors has an explicit monic degree-twenty slope because five is odd; the
three additional z changes remain in a named lower-degree product. -/

namespace FastPoly.Char2Degree25HighDifference

open Polynomial Char2Degree23RowEight Char2Degree23Frame
  Char2Degree25Frame Char2Degree25HighFrame Char2Degree19InnerTail
  Char2Degree19InnerChanges

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def uLeft (a : ℕ → R) : R[X] := y + z a + t a + C (a 4)
noncomputable def uRight (a : ℕ → R) : R[X] := z a + t a + C (a 5)

theorem uLeft_monic (a : ℕ → R) : IsMonicOfDegree (uLeft a) 5 :=
  ((t_monic a).add_left ((y_add_z_monic a).natDegree_eq.trans_lt (by omega))).add_right
    (by rw [natDegree_C]; omega)
theorem uRight_monic (a : ℕ → R) : IsMonicOfDegree (uRight a) 5 :=
  (z_add_t_monic a).add_right (by rw [natDegree_C]; omega)

theorem high_five (a : ℕ → R) :
    high a = nRight a * (hLeft a * (rLeft a * (uLeft a * uRight a))) := rfl

noncomputable def term0 (a b : ℕ → R) : R[X] :=
  hLeft b * (rLeft b * (uLeft b * uRight b))
noncomputable def term1 (a b : ℕ → R) : R[X] :=
  nRight a * (rLeft b * (uLeft b * uRight b))
noncomputable def term2 (a b : ℕ → R) : R[X] :=
  nRight a * (hLeft a * (uLeft b * uRight b))
noncomputable def term3 (a b : ℕ → R) : R[X] :=
  nRight a * (hLeft a * (rLeft a * uRight b))
noncomputable def term4 (a b : ℕ → R) : R[X] :=
  nRight a * (hLeft a * (rLeft a * uLeft a))

noncomputable def fiveSlope (a b : ℕ → R) : R[X] :=
  term0 a b + term1 a b + term2 a b + term3 a b + term4 a b
noncomputable def threeSlope (a b : ℕ → R) : R[X] :=
  term1 a b + term3 a b + term4 a b

theorem term0_monic (a b : ℕ → R) : IsMonicOfDegree (term0 a b) 20 :=
  (hLeft_monic b).mul ((rLeft_monic b).mul ((uLeft_monic b).mul (uRight_monic b)))

theorem term1_monic (a b : ℕ → R) : IsMonicOfDegree (term1 a b) 20 :=
  (nRight_monic a).mul ((rLeft_monic b).mul ((uLeft_monic b).mul (uRight_monic b)))

theorem term2_monic (a b : ℕ → R) : IsMonicOfDegree (term2 a b) 20 :=
  (nRight_monic a).mul ((hLeft_monic a).mul ((uLeft_monic b).mul (uRight_monic b)))

theorem term3_monic (a b : ℕ → R) : IsMonicOfDegree (term3 a b) 20 :=
  (nRight_monic a).mul ((hLeft_monic a).mul ((rLeft_monic a).mul (uRight_monic b)))

theorem term4_monic (a b : ℕ → R) : IsMonicOfDegree (term4 a b) 20 :=
  (nRight_monic a).mul ((hLeft_monic a).mul ((rLeft_monic a).mul (uLeft_monic a)))

private theorem monic_five_sum (p0 p1 p2 p3 p4 : R[X]) (n : ℕ)
    (h0 : IsMonicOfDegree p0 n) (h1 : IsMonicOfDegree p1 n)
    (h2 : IsMonicOfDegree p2 n) (h3 : IsMonicOfDegree p3 n)
    (h4 : IsMonicOfDegree p4 n) :
    IsMonicOfDegree (p0 + p1 + p2 + p3 + p4) n := by
  have hc (p : R[X]) (hp : IsMonicOfDegree p n) : p.coeff n = 1 := by
    rw [← hp.natDegree_eq]
    exact hp.monic.coeff_natDegree
  apply (isMonicOfDegree_iff _ _).mpr
  constructor
  · exact natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le h0.natDegree_eq.le h1.natDegree_eq.le)
          h2.natDegree_eq.le) h3.natDegree_eq.le) h4.natDegree_eq.le
  · rw [coeff_add, coeff_add, coeff_add, coeff_add,
      hc p0 h0, hc p1 h1, hc p2 h2, hc p3 h3, hc p4 h4]
    simp only [CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem fiveSlope_monic (a b : ℕ → R) : IsMonicOfDegree (fiveSlope a b) 20 :=
  monic_five_sum _ _ _ _ _ 20 (term0_monic a b) (term1_monic a b)
    (term2_monic a b) (term3_monic a b) (term4_monic a b)

theorem threeSlope_degree (a b : ℕ → R) : (threeSlope a b).natDegree ≤ 20 :=
  natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (term1_monic a b).natDegree_eq.le (term3_monic a b).natDegree_eq.le)
    (term4_monic a b).natDegree_eq.le

/-- One telescoping identity in ten independent ring elements. -/
private theorem telescope_five (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : R[X]) :
    b0 * (b1 * (b2 * (b3 * b4))) + a0 * (a1 * (a2 * (a3 * a4))) =
      (b0 + a0) * (b1 * (b2 * (b3 * b4))) +
      (b1 + a1) * (a0 * (b2 * (b3 * b4))) +
      (b2 + a2) * (a0 * (a1 * (b3 * b4))) +
      (b3 + a3) * (a0 * (a1 * (a2 * b4))) +
      (b4 + a4) * (a0 * (a1 * (a2 * a3))) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem collect_changes (d e p0 p1 p2 p3 p4 : R[X]) :
    d * p0 + (d + e) * p1 + d * p2 + (d + e) * p3 + (d + e) * p4 =
      d * (p0 + p1 + p2 + p3 + p4) + e * (p1 + p3 + p4) := by ring

theorem high_difference (a b : ℕ → R) (d e : R[X])
    (h0 : nRight b = nRight a + d)
    (h1 : hLeft b = hLeft a + (d + e))
    (h2 : rLeft b = rLeft a + d)
    (h3 : uLeft b = uLeft a + (d + e))
    (h4 : uRight b = uRight a + (d + e)) :
    high b + high a = d * fiveSlope a b + e * threeSlope a b := by
  have h0' : nRight b + nRight a = d := by rw [h0, Char2Decoder.cancel_tail]
  have h1' : hLeft b + hLeft a = d + e := by rw [h1, Char2Decoder.cancel_tail]
  have h2' : rLeft b + rLeft a = d := by rw [h2, Char2Decoder.cancel_tail]
  have h3' : uLeft b + uLeft a = d + e := by rw [h3, Char2Decoder.cancel_tail]
  have h4' : uRight b + uRight a = d + e := by rw [h4, Char2Decoder.cancel_tail]
  rw [high_five b, high_five a, telescope_five, h0', h1', h2', h3', h4']
  exact collect_changes d e (term0 a b) (term1 a b) (term2 a b) (term3 a b) (term4 a b)

theorem unit_from_high_difference (a b : ℕ → R) (slope tail : R[X]) (n : ℕ) (delta : R)
    (hn : 19 < n) (hs : IsMonicOfDegree slope n) (ht : tail.natDegree < n)
    (hh : high b + high a = C delta * slope + tail) :
    UnitDifference (Char2Degree25Frame.output a) (Char2Degree25Frame.output b) n delta := by
  have hr : (remainder b + remainder a).natDegree < n :=
    (remainder_difference_degree a b).trans_lt hn
  have hl : (tail + (remainder b + remainder a)).natDegree < n :=
    (natDegree_add_le _ _).trans_lt (max_lt ht hr)
  have ho : Char2Degree25Frame.output b + Char2Degree25Frame.output a =
      C delta * slope + (tail + (remainder b + remainder a)) := by
    rw [output_eq b, output_eq a]
    calc
      (high b + remainder b) + (high a + remainder a) =
        (high b + high a) + (remainder b + remainder a) := by ac_rfl
      _ = _ := by rw [hh, add_assoc]
  apply unit_difference_of_lower (Char2Degree25Frame.output a) (Char2Degree25Frame.output b)
    slope (tail + (remainder b + remainder a)) n delta hs hl
  calc
    Char2Degree25Frame.output b = Char2Degree25Frame.output a +
      (Char2Degree25Frame.output b + Char2Degree25Frame.output a) := by
        rw [← add_assoc, Char2Decoder.cancel_tail]
    _ = _ := by rw [ho]

/-- Four raw pivots share this five-factor telescope. -/
theorem unit_from_common_change (a b : ℕ → R) (slope e : R[X]) (k : ℕ) (delta : R)
    (hs : IsMonicOfDegree slope k) (he : e.natDegree < k)
    (h0 : nRight b = nRight a + C delta * slope)
    (h1 : hLeft b = hLeft a + (C delta * slope + e))
    (h2 : rLeft b = rLeft a + C delta * slope)
    (h3 : uLeft b = uLeft a + (C delta * slope + e))
    (h4 : uRight b = uRight a + (C delta * slope + e)) :
    UnitDifference (Char2Degree25Frame.output a) (Char2Degree25Frame.output b) (k + 20) delta := by
  have ht : (e * threeSlope a b).natDegree < k + 20 := by
    exact (natDegree_mul_le.trans (Nat.add_le_add_left (threeSlope_degree a b) e.natDegree)).trans_lt
      (Nat.add_lt_add_right he 20)
  have hh := high_difference a b (C delta * slope) e h0 h1 h2 h3 h4
  rw [mul_assoc (C delta) slope] at hh
  exact unit_from_high_difference a b (slope * fiveSlope a b) (e * threeSlope a b)
    (k + 20) delta (by omega) (hs.mul (fiveSlope_monic a b)) ht hh

private theorem single_left_change (a b c u v d : R[X]) :
    a * (b * (c * ((u + d) * v))) =
      a * (b * (c * (u * v))) + d * (a * (b * (c * v))) := by ring

/-- The fifth raw pivot changes just one of the five quintic factors. -/
theorem unit_from_uLeft_change (a b : ℕ → R) (delta : R)
    (h0 : nRight b = nRight a) (h1 : hLeft b = hLeft a)
    (h2 : rLeft b = rLeft a) (h3 : uLeft b = uLeft a + C delta)
    (h4 : uRight b = uRight a) :
    UnitDifference (Char2Degree25Frame.output a) (Char2Degree25Frame.output b) 20 delta := by
  have hh : high b = high a + C delta * term3 a a := by
    rw [high_five b, h0, h1, h2, h3, h4, high_five a]
    exact single_left_change ..
  apply unit_from_high_difference a b (term3 a a) 0 20 delta
    (by omega) (term3_monic a a) (by rw [natDegree_zero]; omega)
  rw [hh, Char2Decoder.cancel_tail, add_zero]

end FastPoly.Char2Degree25HighDifference

