import FastPoly.Examples.Char2Degree19InnerTail
import Mathlib.Algebra.Polynomial.Div

/-! Explicit monic remainder reads for a terminal decoder. Every congruence
below supplies its actual quotient; no ideal-membership or elimination
procedure is used. A low-degree output difference is its own remainder. -/
namespace FastPoly.Char2MonicRemainder

open Polynomial Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [Nontrivial R]

theorem remainder_eq_of_split {p h N q : R[X]} (hN : N.Monic)
    (hp : p.natDegree < N.natDegree) (he : p = h + N * q) : p = h %ₘ N := by
  have hs : p %ₘ N = p := (modByMonic_eq_self_iff hN).mpr (degree_lt_degree hp)
  rw [← hs, he, add_modByMonic, self_mul_modByMonic hN, add_zero]

theorem equal_of_low_split {p r N q : R[X]} (hN : N.Monic)
    (hp : p.natDegree < N.natDegree) (hr : r.natDegree < N.natDegree)
    (he : p = r + N * q) : p = r := by
  rw [remainder_eq_of_split hN hp he]
  exact (modByMonic_eq_self_iff hN).mpr (degree_lt_degree hr)

variable [CharP R 2]

private theorem combine (h k N p q : R[X]) :
    (h + N * p) + (k + N * q) = (h + k) + N * (p + q) := by ring

/-- The displayed final-product frame supplies the quotient of the head
difference directly. The remainder is the exact observed low difference. -/
theorem difference_eq_remainder {p p' h h' N q q' : R[X]} (hN : N.Monic)
    (hp : p = h + N * q) (hp' : p' = h' + N * q')
    (hd : (p' + p).natDegree < N.natDegree) :
    p' + p = (h' + h) %ₘ N := by
  apply remainder_eq_of_split hN hd
  rw [hp', hp, combine]

private theorem collect_quotients (r N u v : R[X]) :
    (r + N * u) + N * v = r + N * (u + v) := by ring

/-- A supplied small remainder expression is exact once the higher rows have
been explicitly peeled. Neither quotient is expanded. -/
theorem difference_eq_of_head_split {p p' h h' N q q' remainder quotient : R[X]}
    (hN : N.Monic) (hp : p = h + N * q) (hp' : p' = h' + N * q')
    (hd : (p' + p).natDegree < N.natDegree)
    (hr : remainder.natDegree < N.natDegree)
    (hh : h' + h = remainder + N * quotient) : p' + p = remainder := by
  apply equal_of_low_split hN hd hr
  rw [hp', hp, combine, hh, collect_quotients]

end FastPoly.Char2MonicRemainder
