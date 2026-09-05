import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# The degree-23 circuit's row-eight pivot, without circuit expansion

The first ten gates are kept named. Only the last two gates are opened to show
that the coefficient of offset `a19` is `(z + a20) * (x + y + z + a18)`.
Both factors are monic quartics, so its row-eight coefficient is exactly one.
This proves the `a19 = q14 + h14` step of
`char2/verify_n23_unitriangular_symbolic.py` over every characteristic-two field
(in fact, every nontrivial characteristic-two commutative ring).

No claim about the remaining coefficient pivots is made here.
-/

namespace FastPoly.Char2Degree23RowEight

set_option maxHeartbeats 20000

open Polynomial Char2Decoder

variable {R : Type*} [CommRing R]

/-- The first two gates, shared by the two monic quartic factors. -/
noncomputable def y : R[X] := X * X

noncomputable def z (a : ℕ → R) : R[X] :=
  (y + C (a 0)) * (X + y + C (a 1))

noncomputable def t (a : ℕ → R) : R[X] := (X + C (a 2)) * (z a + C (a 3))

noncomputable def u (a : ℕ → R) : R[X] :=
  (y + z a + t a + C (a 4)) * (z a + t a + C (a 5))

noncomputable def v (a : ℕ → R) : R[X] := (X + C (a 6)) * (y + z a + C (a 7))

noncomputable def w (a : ℕ → R) : R[X] :=
  (X + y + z a + C (a 8)) * (y + v a + C (a 9))

noncomputable def s (a : ℕ → R) : R[X] := (z a + C (a 10)) * (v a + C (a 11))

noncomputable def r (a : ℕ → R) : R[X] := (X + t a + C (a 12)) * (u a + C (a 13))

noncomputable def g (a : ℕ → R) : R[X] :=
  (z a + t a + C (a 14)) * (X + u a + C (a 15))

noncomputable def ell (a : ℕ → R) : R[X] := (X + C (a 16)) * (z a + v a + C (a 17))

/-- The remaining gates, with the two offsets still to be chosen as separate
arguments. Neither occurs among the named first ten gates. -/
noncomputable def crownLeft (a : ℕ → R) : R[X] := X + y + z a + C (a 18)

noncomputable def crownRight (a : ℕ → R) : R[X] := X + y + z a + w a + s a + g a + ell a

noncomputable def lastFactor (a : ℕ → R) : R[X] := z a + C (a 20)

noncomputable def head (a : ℕ → R) : R[X] := y + v a + w a + s a + r a + g a

noncomputable def finish (a : ℕ → R) (a19 a22 : R) : R[X] :=
  head a + lastFactor a *
    (u a + crownLeft a * (crownRight a + C a19) + C (a 21)) + C a22

/-- The literal output of the supplied 12-product circuit. -/
noncomputable def output (a : ℕ → R) : R[X] := finish a (a 19) (a 22)

/-- The verifier's baseline `p_hat`, with `a19 = a22 = 0`. -/
noncomputable def baseline (a : ℕ → R) : R[X] :=
  head a + lastFactor a * (u a + crownLeft a * crownRight a + C (a 21))

noncomputable def slope (a : ℕ → R) : R[X] := lastFactor a * crownLeft a

/-- A local two-gate identity. All earlier wires are opaque parameters. -/
theorem affine_finish {A : Type*} [CommRing A] (h f u l r k c o : A) :
    h + f * (u + l * (r + c) + k) + o =
      (h + f * (u + l * r + k)) + (f * l) * c + o := by
  rw [mul_add l r c, ← add_assoc u (l * r) (l * c),
    add_right_comm (u + l * r) (l * c) k, mul_add,
    ← mul_assoc f l c, ← add_assoc]

theorem finish_eq (a : ℕ → R) (a19 a22 : R) :
    finish a a19 a22 = baseline a + slope a * C a19 + C a22 :=
  affine_finish (head a) (lastFactor a) (u a) (crownLeft a) (crownRight a)
    (C (a 21)) (C a19) (C a22)

theorem baseline_eq (a : ℕ → R) : baseline a = finish a 0 0 := by
  rw [finish_eq, map_zero, mul_zero, add_zero, add_zero]

section MonicSlope

variable [Nontrivial R]

theorem y_monic : IsMonicOfDegree (y : R[X]) 2 :=
  (isMonicOfDegree_X R).mul (isMonicOfDegree_X R)

theorem x_add_y_monic : IsMonicOfDegree ((X : R[X]) + y) 2 :=
  y_monic.add_left (natDegree_X_le.trans_lt (by omega))

theorem z_monic (a : ℕ → R) : IsMonicOfDegree (z a) 4 := by
  have h0 : (C (a 0)).natDegree < 2 := by rw [natDegree_C]; omega
  have h1 : (C (a 1)).natDegree < 2 := by rw [natDegree_C]; omega
  exact (y_monic.add_right h0).mul (x_add_y_monic.add_right h1)

theorem crownLeft_monic (a : ℕ → R) : IsMonicOfDegree (crownLeft a) 4 := by
  have hxy : ((X : R[X]) + y).natDegree < 4 := by
    rw [x_add_y_monic.natDegree_eq]
    omega
  have hc : (C (a 18)).natDegree < 4 := by rw [natDegree_C]; omega
  exact ((z_monic a).add_left hxy).add_right hc

theorem lastFactor_monic (a : ℕ → R) : IsMonicOfDegree (lastFactor a) 4 := by
  have hc : (C (a 20)).natDegree < 4 := by rw [natDegree_C]; omega
  exact (z_monic a).add_right hc

theorem slope_monic (a : ℕ → R) : IsMonicOfDegree (slope a) 8 :=
  (lastFactor_monic a).mul (crownLeft_monic a)

theorem slope_coeff_eight (a : ℕ → R) : (slope a).coeff 8 = 1 := by
  rw [← (slope_monic a).natDegree_eq]
  exact (slope_monic a).monic.coeff_natDegree

/-- Only a unit-slope coefficient and a constant are read; no preceding gate
is expanded or normalized in this proof. -/
theorem coeff_eight (a : ℕ → R) (a19 a22 : R) :
    (finish a a19 a22).coeff 8 = (baseline a).coeff 8 + a19 := by
  rw [finish_eq, coeff_add, coeff_add, coeff_mul_C, slope_coeff_eight, one_mul]
  simp only [coeff_C, OfNat.ofNat_ne_zero, ite_false, add_zero]

theorem higher_coeff (a : ℕ → R) (a19 a22 : R) (j : ℕ) (hj : 8 < j) :
    (finish a a19 a22).coeff j = (baseline a).coeff j := by
  have hs : (slope a).coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt ((slope_monic a).natDegree_eq.trans_lt hj)
  have hj0 : j ≠ 0 := by omega
  rw [finish_eq, coeff_add, coeff_add, coeff_mul_C, hs, zero_mul]
  simp only [coeff_C, hj0, ite_false, add_zero]

variable [CharP R 2]

/-- The exact `a19 = q14 + h14` decoder from the verifier. -/
noncomputable def decodeOffset (a : ℕ → R) (q14 : R) : R :=
  q14 + (baseline a).coeff 8

theorem decodeOffset_coeff (a : ℕ → R) (a19 a22 : R) :
    decodeOffset a ((finish a a19 a22).coeff 8) = a19 := by
  rw [decodeOffset, coeff_eight]
  exact cancel_tail _ _

theorem coeff_decodeOffset (a : ℕ → R) (q14 a22 : R) :
    (finish a (decodeOffset a q14) a22).coeff 8 = q14 := by
  rw [coeff_eight, decodeOffset, add_comm q14, CharTwo.add_cancel_left]

end MonicSlope

end FastPoly.Char2Degree23RowEight
