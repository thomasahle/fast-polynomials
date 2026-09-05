import FastPoly.Examples.Char2Degree15FastCore
import FastPoly.Examples.Char2Degree19InnerChanges

/-! Local cubic variation underlying the first four explicit degree-15 pivots.
The degree-five wire stays opaque.  Only a cubic identity in independent named
ring elements is normalized; the original keys are never expanded. -/

namespace FastPoly.Char2Degree15Fast

set_option maxHeartbeats 20000

open Polynomial Char2Degree19InnerTail Char2Degree19InnerChanges

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def mainWire (q : Keys R) : R[X] := t q + C (q 7)
noncomputable def beta (q : Keys R) : R[X] := y + C (q 4 + q 5)
noncomputable def gamma (q : Keys R) : R[X] := z q + C (q 5 + q 7)

theorem r_cubic (q : Keys R) :
    r q = mainWire q * ((mainWire q + beta q) * (mainWire q + gamma q) + C (q 9)) := by
  have hb : y + t q + C (q 4 + q 5 + q 7) = mainWire q + beta q := by
    unfold mainWire beta
    simp only [map_add]
    ac_rfl
  have hg : z q + t q + C (q 5) = mainWire q + gamma q := by
    unfold mainWire gamma
    simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero, add_zero, zero_add]
  change mainWire q * ((y + t q + C (q 4 + q 5 + q 7)) *
    (z q + t q + C (q 5)) + C (q 9)) = _
  rw [hb, hg]

/-- Everything except the monic leading term `d * A²`. -/
noncomputable def cubicTail (a b g c d e : R[X]) : R[X] :=
  d ^ 2 * (a + b + g) + d ^ 3 + d * (b * g + c) +
    e * (a + d) * (a + d + b)

theorem cubic_change (a b g c d e : R[X]) :
    (a + d) * (((a + d) + b) * ((a + d) + (g + e)) + c) =
      a * ((a + b) * (a + g) + c) + (d * a ^ 2 + cubicTail a b g c d e) := by
  have h3 : (3 : R[X]) = 1 := by
    calc
      (3 : R[X]) = 1 + 2 := by ring
      _ = 1 := by rw [CharTwo.two_eq_zero, add_zero]
  unfold cubicTail
  ring_nf
  simp only [CharTwo.two_eq_zero, h3, mul_zero, mul_one, add_zero]

variable [Nontrivial R]

theorem mainWire_monic (q : Keys R) : IsMonicOfDegree (mainWire q) 5 :=
  (t_monic q).add_right (const_lt _ 5 (by omega))

theorem beta_monic (q : Keys R) : IsMonicOfDegree (beta q) 2 :=
  y_monic.add_right (const_lt _ 2 (by omega))

theorem gamma_monic (q : Keys R) : IsMonicOfDegree (gamma q) 4 :=
  (z_monic q).add_right (const_lt _ 4 (by omega))

/-- Four degree inequalities instead of an expanded coefficient calculation. -/
theorem cubicTail_degree (q : Keys R) (d e : R[X]) (k : ℕ)
    (hk : k ≤ 4) (hd : d.natDegree ≤ k) (he : e.natDegree < k) :
    (cubicTail (mainWire q) (beta q) (gamma q) (C (q 9)) d e).natDegree < k + 10 := by
  have ha : (mainWire q).natDegree ≤ 5 := (mainWire_monic q).natDegree_eq.le
  have hb : (beta q).natDegree ≤ 2 := (beta_monic q).natDegree_eq.le
  have hg : (gamma q).natDegree ≤ 4 := (gamma_monic q).natDegree_eq.le
  have habg : (mainWire q + beta q + gamma q).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le ha (hb.trans (by omega))) (hg.trans (by omega))
  have hd2 : (d ^ 2).natDegree ≤ 2 * k :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hd)
  have h1 : (d ^ 2 * (mainWire q + beta q + gamma q)).natDegree < k + 10 :=
    (mul_bound hd2 habg).trans_lt (by omega)
  have h2 : (d ^ 3).natDegree < k + 10 :=
    (natDegree_pow_le.trans (Nat.mul_le_mul_left 3 hd)).trans_lt (by omega)
  have hbg : (beta q * gamma q + C (q 9)).natDegree ≤ 6 :=
    natDegree_add_le_of_degree_le (mul_bound hb hg)
      ((natDegree_C _).le.trans (by omega))
  have h3 : (d * (beta q * gamma q + C (q 9))).natDegree < k + 10 :=
    (mul_bound hd hbg).trans_lt (by omega)
  have had : (mainWire q + d).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le ha (hd.trans (by omega))
  have hadb : (mainWire q + d + beta q).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le had (hb.trans (by omega))
  have h4 : (e * (mainWire q + d) * (mainWire q + d + beta q)).natDegree < k + 10 :=
    (mul_bound (mul_bound (le_refl e.natDegree) had) hadb).trans_lt (by omega)
  have hadd {p p' : R[X]} (hp : p.natDegree < k + 10)
      (hp' : p'.natDegree < k + 10) : (p + p').natDegree < k + 10 :=
    (natDegree_add_le p p').trans_lt (max_lt hp hp')
  exact hadd (hadd (hadd h1 h2) h3) h4

noncomputable def rTail (q : Keys R) (d e : R[X]) : R[X] :=
  cubicTail (mainWire q) (beta q) (gamma q) (C (q 9)) d e

noncomputable def fullTail (q q' : Keys R) (d e : R[X]) : R[X] :=
  rTail q d e + (w q' + s q') + (w q + s q)

theorem r_change (q q' : Keys R) (d e : R[X])
    (ha : mainWire q' = mainWire q + d)
    (hb : beta q' = beta q) (hg : gamma q' = gamma q + e)
    (hc : q' 9 = q 9) :
    r q' = r q + (d * mainWire q ^ 2 + rTail q d e) := by
  rw [r_cubic q', ha, hb, hg, hc, cubic_change, ← r_cubic q]
  rfl

private theorem assemble_cubic (p p' r term tail c : R[X]) :
    p' + (r + (term + tail)) + c =
      (p + r + c) + (term + (tail + p' + p)) := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero]

theorem output_from_r_change (q q' : Keys R) (d e : R[X])
    (hr : r q' = r q + (d * mainWire q ^ 2 + rTail q d e))
    (hout : q' 14 = q 14) :
    output q' = output q + (d * mainWire q ^ 2 + fullTail q q' d e) := by
  rw [output, hr, hout]
  exact assemble_cubic (w q + s q) (w q' + s q') (r q)
    (d * mainWire q ^ 2) (rTail q d e) (C (q 14))

theorem fullTail_degree (q q' : Keys R) (d e : R[X]) (k : ℕ)
    (hk0 : 0 < k) (hk : k ≤ 4) (hd : d.natDegree ≤ k) (he : e.natDegree < k) :
    (fullTail q q' d e).natDegree < k + 10 := by
  have ht0 := cubicTail_degree q d e k hk hd he
  have h1 : (w q' + s q').natDegree < k + 10 := by
    rw [(branches_monic q').natDegree_eq]
    omega
  have h2 : (w q + s q).natDegree < k + 10 := by
    rw [(branches_monic q).natDegree_eq]
    omega
  exact (natDegree_add_le _ _).trans_lt
    (max_lt ((natDegree_add_le _ _).trans_lt (max_lt ht0 h1)) h2)

/-- The first four pivots share this local proof. The cancelled secondary
branch has degree ten, strictly below all four rows being read. -/
theorem unit_from_main_change (q q' : Keys R) (slope e : R[X]) (k : ℕ)
    (delta : R) (hk0 : 0 < k) (hk : k ≤ 4)
    (hs : IsMonicOfDegree slope k) (he : e.natDegree < k)
    (ha : mainWire q' = mainWire q + C delta * slope)
    (hb : beta q' = beta q) (hg : gamma q' = gamma q + e)
    (hc : q' 9 = q 9) (hout : q' 14 = q 14) :
    UnitDifference (output q) (output q') (k + 10) delta := by
  have hd : (C delta * slope).natDegree ≤ k :=
    (mul_bound (natDegree_C delta).le hs.natDegree_eq.le).trans (by omega)
  have hr := r_change q q' (C delta * slope) e ha hb hg hc
  have ho := output_from_r_change q q' (C delta * slope) e hr hout
  rw [mul_assoc (C delta) slope] at ho
  exact unit_difference_of_lower (output q) (output q') (slope * mainWire q ^ 2)
    (fullTail q q' (C delta * slope) e) (k + 10) delta
    (hs.mul ((mainWire_monic q).pow 2))
    (fullTail_degree q q' (C delta * slope) e k hk0 hk hd he) ho

end FastPoly.Char2Degree15Fast
