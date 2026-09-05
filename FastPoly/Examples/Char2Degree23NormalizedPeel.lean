import FastPoly.Examples.Char2Degree23MiddleKeys
import FastPoly.Examples.Char2MonicPivotPeel

/-!
# Transporting a low explicit column through the row-eight correction

The supplied normalized inverse changes raw slot 19 to install coefficient
eight. An exact raw column calculation is transported across that correction,
then its monic column is peeled using the already read row. No baseline
coefficient is expanded.
-/

namespace FastPoly.Char2Degree23NormalizedPeel

open Polynomial Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23HighKeys Char2Degree23LowKeys Char2Degree23LowFrame
  Char2Degree23MiddleKeys

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem sameRaw_difference {a b : ℕ → R} (he : SameRaw a b) :
    output b + output a = D a * C (b 19 + a 19) := by
  have hl : SameSlots a b := {
    h0 := he.h0
    h1 := he.h1
    h2 := he.h2
    h3 := he.h3
    h4 := he.h4
    h5 := he.h5
    h6 := he.h6
    h7 := he.h7
    h8 := he.h8
    h9 := he.h9
    h10 := he.h10
    h11 := he.h11
    h12 := he.h12
    h14 := he.h14
    h15 := he.h15
    h16 := he.h16
    h17 := he.h17
    h18 := he.h18
    h20 := he.h20
  }
  have hd := hl.output_difference
  rw [← he.h13, ← he.h21, ← he.h22] at hd
  simpa only [CharTwo.add_self_eq_zero, map_zero, mul_zero, zero_add, add_zero] using hd

private theorem join_differences (p q r : R[X]) :
    r + p = (r + q) + (q + p) := by
  rw [add_assoc r q (q + p), CharTwo.add_cancel_left]

private theorem join_columns (d low : R[X]) (k l : R) :
    d * C k + (d * C l + low) = d * C (k + l) + low := by
  rw [map_add, mul_add, add_assoc]

/-- The explicit coefficient-eight solve removes both known raw corrections. -/
theorem transport {a b c : ℕ → R} {low : R[X]} {k : R}
    (he : SameRaw b c) (hd : D b = D a)
    (hraw : output b + output a = D a * C k + low)
    (hlow : low.natDegree < 8) (hrow : (output c).coeff 8 = (output a).coeff 8) :
    output c = output a + low := by
  have hchange : output c + output a = D a * C ((c 19 + b 19) + k) + low := by
    rw [join_differences (output a) (output b), sameRaw_difference he,
      hraw, hd, join_columns]
  exact Char2MonicPivotPeel.peel_difference (D_monic a) hlow hchange hrow

/-- Specialization to the actual supplied normalized key update. -/
theorem increment {q : Fin 23 → R} {i : Fin 23} {delta k : R}
    {b : ℕ → R} {low : R[X]} (hi : i ≠ 14)
    (he : SameRaw b (rawKeys (Char2Degree23HighKeys.increment q i delta)))
    (hd : D b = D (rawKeys q))
    (hraw : output b + output (rawKeys q) = D (rawKeys q) * C k + low)
    (hlow : low.natDegree < 8) :
    output (rawKeys (Char2Degree23HighKeys.increment q i delta)) = output (rawKeys q) + low :=
  transport he hd hraw hlow (same_row_eight q i delta hi)

end FastPoly.Char2Degree23NormalizedPeel

