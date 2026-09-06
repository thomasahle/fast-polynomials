import FastPoly.Examples.Char2Degree25HeadChange

/-! The terminal inverse reads the explicitly supplied small head remainder.
The quotient is displayed, and the preceding coefficient peel supplies the
strict degree bound. This connects remainder units to actual circuit units. -/
namespace FastPoly.Char2Degree25RemainderUnit

open Polynomial Char2Degree25Frame Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem unit_from_head {a b : ℕ → R} {rem quotient : R[X]} {r : ℕ} {d : R}
    (hN : nRight b = nRight a) (h24 : b 24 = a 24)
    (hd : (output b + output a).natDegree ≤ 4)
    (hh : head b + head a = rem + nRight a * quotient)
    (hu : UnitDifference 0 rem r d) (hr : r < 5) : UnitDifference (output a) (output b) r d := by
  have hdN : (output b + output a).natDegree < (nRight a).natDegree := by
    rw [(nRight_monic a).natDegree_eq]
    omega
  have hrem : rem.natDegree < (nRight a).natDegree := by
    have hb : rem.natDegree ≤ r := by simpa only [add_zero] using hu.difference_degree
    rw [(nRight_monic a).natDegree_eq]
    exact hb.trans_lt hr
  have he : output b + output a = rem := by
    apply Char2MonicRemainder.equal_of_low_split
      (q := quotient + (nLeft b + nLeft a)) (nRight_monic a).monic hdN hrem
    rw [Char2Degree25HeadChange.output_difference hN h24, hh]
    simp only [mul_add, add_assoc]
  constructor
  · rw [he]
    simpa only [add_zero] using hu.difference_degree
  · rw [he]
    simpa only [add_zero] using hu.pivot

end FastPoly.Char2Degree25RemainderUnit
