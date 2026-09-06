import FastPoly.Examples.Char2Degree25RowFourteen

/-! The supplied raw a17 step and the terminal a24 constant step.
The first slope is `(X+C a16) * (1+nRight*(1+jLeft))`, monic of degree
eleven. Only the affected ell/j/n gates are rewritten; the output is
never expanded into coefficients. These are raw-coordinate unit steps,
not a claim about the remaining normalized decoder coordinates. -/

namespace FastPoly.Char2Degree25RowEleven

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift (a : ℕ → R) (d : R) : ℕ → R
  | 17 => a 17 + d
  | i => a i

noncomputable def ellSlope (a : ℕ → R) : R[X] := X + C (a 16)
noncomputable def jSlope (a : ℕ → R) : R[X] := jLeft a * ellSlope a
noncomputable def leftSlope (a : ℕ → R) : R[X] := ellSlope a + jSlope a
noncomputable def slope (a : ℕ → R) : R[X] :=
  ellSlope a * (1 + nRight a * (1 + jLeft a))

private theorem right_constant (p q c d : R[X]) :
    p * (q + (c + d)) = p * (q + c) + d * p := by ring

theorem ell_change (a : ℕ → R) (d : R) :
    ell (shift a d) = ell a + C d * ellSlope a := by
  change ellSlope a * (z a + v a + C (a 17 + d)) = _
  rw [map_add]
  exact right_constant _ _ _ _

private theorem wire_change (p q c d f : R[X]) :
    p * ((q + d * f) + c) = p * (q + c) + d * (p * f) := by ring

theorem j_change (a : ℕ → R) (d : R) :
    j (shift a d) = j a + C d * jSlope a := by
  change jLeft a * (ell (shift a d) + C (a 21)) = _
  rw [ell_change]
  exact wire_change _ _ _ _ _

private theorem collect_left (p e h j c d f g : R[X]) :
    p + (e + d * f) + h + (j + d * g) + c =
      (p + e + h + j + c) + d * (f + g) := by ring

theorem nLeft_change (a : ℕ → R) (d : R) :
    nLeft (shift a d) = nLeft a + C d * leftSlope a := by
  change (X + t a + u a + s a + r a + g a) + ell (shift a d) +
    Char2Degree25Frame.h a + j (shift a d) + C (a 22) = _
  rw [ell_change, j_change]
  exact collect_left _ _ _ _ _ _ _ _

private theorem product_left (p q d f : R[X]) :
    (p + d * f) * q = p * q + d * (q * f) := by ring

theorem n_change (a : ℕ → R) (d : R) :
    n (shift a d) = n a + C d * (nRight a * leftSlope a) := by
  change nLeft (shift a d) * nRight a = _
  rw [nLeft_change]
  exact product_left _ _ _ _

theorem head_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.head (shift a d) =
      Char2Degree25Frame.head a + C d * ellSlope a := by
  change y + z a + u a + ell (shift a d) = _
  rw [ell_change, ← add_assoc]
  rfl

private theorem collect_output (h n c d e r j : R[X]) :
    (h + d * e) + (n + d * (r * (e + j * e))) + c =
      (h + n + c) + d * (e * (1 + r * (1 + j))) := by ring

theorem output_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.output (shift a d) =
      Char2Degree25Frame.output a + C d * slope a := by
  change Char2Degree25Frame.head (shift a d) + n (shift a d) + C (a 24) = _
  rw [head_change, n_change]
  exact collect_output (Char2Degree25Frame.head a) (n a) (C (a 24))
    (C d) (ellSlope a) (nRight a) (jLeft a)

theorem ellSlope_monic (a : ℕ → R) : IsMonicOfDegree (ellSlope a) 1 :=
  isMonicOfDegree_X_add_one (a 16)

theorem slope_monic (a : ℕ → R) : IsMonicOfDegree (slope a) 11 := by
  have hj : IsMonicOfDegree (1 + jLeft a) 5 :=
    (jLeft_monic a).add_left (by rw [natDegree_one]; omega)
  have hn : IsMonicOfDegree (1 + nRight a * (1 + jLeft a)) 10 :=
    ((nRight_monic a).mul hj).add_left (by rw [natDegree_one]; omega)
  exact (ellSlope_monic a).mul hn

theorem unit (a : ℕ → R) (d : R) :
    Char2Degree19InnerTail.UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift a d)) 11 d := by
  rw [output_change]
  exact Char2Degree21Frame.difference_scaled d (slope_monic a)

def constantShift (a : ℕ → R) (d : R) : ℕ → R
  | 24 => a 24 + d
  | i => a i

theorem constant_output_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.output (constantShift a d) =
      Char2Degree25Frame.output a + C d := by
  change Char2Degree25Frame.head a + n a + C (a 24 + d) = _
  rw [map_add, ← add_assoc]
  rfl

theorem constant_unit (a : ℕ → R) (d : R) :
    Char2Degree19InnerTail.UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (constantShift a d)) 0 d := by
  rw [constant_output_change]
  have hOne : IsMonicOfDegree (1 : R[X]) 0 :=
    { natDegree_eq := natDegree_one, monic := monic_one }
  have h := Char2Degree21Frame.difference_scaled
    (p := Char2Degree25Frame.output a) d hOne
  simpa only [mul_one] using h

end FastPoly.Char2Degree25RowEleven
