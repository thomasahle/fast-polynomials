import FastPoly.Examples.Char2Degree25RowThirteen

/-! Exact named-wire changes for the supplied Middle-coordinate q21 direction.
The two quintic slopes W/V are retained as named polynomials; no output
coefficient or terminal inverse is expanded or asserted here. -/
namespace FastPoly.Char2Degree25TwentyOneWires

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame
open Char2Degree25RowThirteen (B L P)
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift (a : ℕ → R) (d : R) : ℕ → R
  | 7 => a 7 + B a * d
  | 8 => a 8 + d
  | 9 => a 9 + B a * B a * d
  | 13 => a 13 + B a * d
  | 16 => a 16 + d
  | i => a i

noncomputable def A (a : ℕ → R) : R[X] := X + C (a 2)
noncomputable def E (a : ℕ → R) : R[X] := X + C (a 16)
noncomputable def Q (a : ℕ → R) : R[X] := L a + rLeft a + P a * A a
noncomputable def Sleft (a : ℕ → R) : R[X] := z a + C (a 10)
noncomputable def wSlope (a : ℕ → R) (d : R) : R[X] :=
  y + v a + C (a 9) + C (B a) * P a * A a + C (B a * d) * A a
noncomputable def W (a : ℕ → R) (d : R) : R[X] :=
  C (B a) * Q a + y + v a + C (a 9) + C (B a * d) * A a
noncomputable def V (a : ℕ → R) (d : R) : R[X] :=
  z a + v a + C (a 17) + C (B a) * (E a + C d) * L a
noncomputable def leftSlope (a : ℕ → R) (d : R) : R[X] :=
  C (B a) * Sleft a * L a + C (B a) * rLeft a + V a d +
    hLeft a * W a d + jLeft a * V a d
noncomputable def outputSlope (a : ℕ → R) (d : R) : R[X] :=
  V a d + nRight a * leftSlope a d

theorem L_add_B (a : ℕ → R) : L a + C (B a) = A a := by
  simp only [L, B, A, map_add, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem Q_eq_inner (a : ℕ → R) : Q a = Char2Degree25RowThirteen.inner a := by
  rw [Char2Degree25RowThirteen.inner, L_add_B]
  exact add_right_comm (L a) (rLeft a) (P a * A a)

theorem Q_monic (a : ℕ → R) : IsMonicOfDegree (Q a) 3 := by
  rw [Q_eq_inner]
  exact Char2Degree25RowThirteen.inner_monic a

private theorem right_change (p q c d b : R[X]) :
    p * (q + (c + b * d)) = p * (q + c) + d * (b * p) := by ring

theorem v_change (a : ℕ → R) (d : R) :
    v (shift a d) = v a + C d * (C (B a) * L a) := by
  change L a * (y + z a + C (a 7 + B a * d)) = _
  rw [map_add, map_mul]
  exact right_change _ _ _ _ _

private theorem w_right (y v c d b l : R[X]) :
    y + (v + d * (b * l)) + (c + b * b * d) =
      (y + v + c) + d * b * (l + b) := by ring
private theorem w_product (p q d b a : R[X]) :
    (p + d) * (q + d * b * a) =
      p * q + d * (q + b * p * a + (b * d) * a) := by ring

theorem w_change (a : ℕ → R) (d : R) :
    w (shift a d) = w a + C d * wSlope a d := by
  change (X + y + z a + C (a 8 + d)) *
    (y + v (shift a d) + C (a 9 + B a * B a * d)) = _
  rw [v_change, map_add, map_add, map_mul, map_mul, w_right, L_add_B]
  have hp : X + y + z a + (C (a 8) + C d) = P a + C d := by
    simp only [P, add_assoc]
  rw [hp, w_product]
  change w a + C d * (_ + C (B a) * P a * A a + (C (B a) * C d) * A a) = _
  rw [← map_mul]
  rfl

theorem r_change (a : ℕ → R) (d : R) :
    r (shift a d) = r a + C d * (C (B a) * rLeft a) := by
  change rLeft a * (u a + C (a 13 + B a * d)) = _
  rw [map_add, map_mul]
  exact right_change _ _ _ _ _

private theorem h_collect (x v w r c d b l p a y k : R[X]) :
    x + (v + d * (b * l)) + (w + d * (y + v + c + b * p * a + (b * d) * a)) +
      (r + d * (b * k)) = (x + v + w + r) +
        d * (b * (l + k + p * a) + y + v + c + (b * d) * a) := by ring

theorem hRight_change (a : ℕ → R) (d : R) :
    hRight (shift a d) = hRight a + C d * W a d := by
  change (X + y + z a + u a) + v (shift a d) + w (shift a d) +
    r (shift a d) + C (a 19) = _
  rw [v_change, w_change, r_change]
  have hc := h_collect (X + y + z a + u a) (v a) (w a) (r a) (C (a 9))
    (C d) (C (B a)) (L a) (P a) (A a) y (rLeft a)
  simp only [← map_mul] at hc
  rw [show wSlope a d = y + v a + C (a 9) + C (B a) * P a * A a +
    C (B a * d) * A a from rfl, hc]
  exact add_right_comm _ _ _

private theorem product_plain (p q d f : R[X]) :
    p * (q + d * f) = p * q + d * (p * f) := by ring

theorem h_change (a : ℕ → R) (d : R) :
    h (shift a d) = h a + C d * (hLeft a * W a d) := by
  change hLeft a * hRight (shift a d) = _
  rw [hRight_change]
  exact product_plain _ _ _ _

private theorem s_product (p v c d b l : R[X]) :
    p * ((v + d * (b * l)) + c) = p * (v + c) + d * (b * p * l) := by ring

theorem s_change (a : ℕ → R) (d : R) :
    s (shift a d) = s a + C d * (C (B a) * Sleft a * L a) := by
  change Sleft a * (v (shift a d) + C (a 11)) = _
  rw [v_change]
  exact s_product _ _ _ _ _ _

private theorem ell_product (e z v c d b l : R[X]) :
    (e + d) * (z + (v + d * (b * l)) + c) =
      e * (z + v + c) + d * (z + v + c + b * (e + d) * l) := by ring

theorem ell_change (a : ℕ → R) (d : R) :
    ell (shift a d) = ell a + C d * V a d := by
  change (X + C (a 16 + d)) * (z a + v (shift a d) + C (a 17)) = _
  rw [v_change, map_add, ← add_assoc X]
  exact ell_product _ _ _ _ _ _ _

private theorem j_product (p q c d f : R[X]) :
    p * ((q + d * f) + c) = p * (q + c) + d * (p * f) := by ring

theorem j_change (a : ℕ → R) (d : R) :
    j (shift a d) = j a + C d * (jLeft a * V a d) := by
  change jLeft a * (ell (shift a d) + C (a 21)) = _
  rw [ell_change]
  exact j_product _ _ _ _ _

private theorem left_collect (x s r g e h j c d fs fr fe fh fj : R[X]) :
    x + (s + d * fs) + (r + d * fr) + g + (e + d * fe) +
      (h + d * fh) + (j + d * fj) + c =
    (x + s + r + g + e + h + j + c) + d * (fs + fr + fe + fh + fj) := by ring

theorem nLeft_change (a : ℕ → R) (d : R) :
    nLeft (shift a d) = nLeft a + C d * leftSlope a d := by
  change (X + t a + u a) + s (shift a d) + r (shift a d) + g a +
    ell (shift a d) + h (shift a d) + j (shift a d) + C (a 22) = _
  rw [s_change, r_change, ell_change, h_change, j_change]
  exact left_collect _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem head_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.head (shift a d) = Char2Degree25Frame.head a + C d * V a d := by
  change y + z a + u a + ell (shift a d) = _
  rw [ell_change, ← add_assoc]
  rfl

private theorem output_collect (h n r c d v f : R[X]) :
    (h + d * v) + (n + d * f) * r + c = (h + n * r + c) + d * (v + r * f) := by ring

theorem output_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.output (shift a d) =
      Char2Degree25Frame.output a + C d * outputSlope a d := by
  change Char2Degree25Frame.head (shift a d) + nLeft (shift a d) * nRight a + C (a 24) = _
  rw [head_change, nLeft_change]
  exact output_collect _ _ _ _ _ _ _

end FastPoly.Char2Degree25TwentyOneWires
