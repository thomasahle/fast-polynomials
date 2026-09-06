import FastPoly.Examples.Char2Degree25RowThirteen

/-! Exact named-wire changes for the supplied middle-coordinate q22 direction.
Only raw slots 7,8,9,13,14 change. The apparent degree-ten terms cancel through
the shared factor U, leaving a quadratic Q2. No output coefficients expand. -/

namespace FastPoly.Char2Degree25TwentyTwoWires

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame
open Char2Degree25RowThirteen (L P sSlope ellSlope)

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift (a : ℕ → R) (d : R) : ℕ → R
  | 7 => a 7 + d
  | 8 => a 8 + d
  | 9 => a 9 + d
  | 13 => a 13 + d
  | 14 => a 14 + d
  | i => a i

def K (a : ℕ → R) : R := a 4 + a 18
noncomputable def U (a : ℕ → R) : R[X] := z a + t a + C (a 5)
noncomputable def E (a : ℕ → R) : R[X] := X + C (a 16)
noncomputable def wSlope (a : ℕ → R) (d : R) : R[X] :=
  P a * (L a + 1) + y + v a + C (a 9) + C d * (L a + 1)
noncomputable def W (a : ℕ → R) (d : R) : R[X] :=
  L a + wSlope a d + rLeft a
noncomputable def Q2 (a : ℕ → R) (d : R) : R[X] :=
  L a + L a * (X + C (a 7 + a 8)) + C (a 12 + a 8 + a 9 + a 5) +
    C d * (L a + 1)
noncomputable def bracket (a : ℕ → R) (d : R) : R[X] :=
  sSlope a + rLeft a + X + C (a 15) + ellSlope a + C (K a) * U a +
    hLeft a * Q2 a d + jLeft a * ellSlope a
noncomputable def outputSlope (a : ℕ → R) (d : R) : R[X] :=
  ellSlope a + nRight a * bracket a d

theorem v_change (a : ℕ → R) (d : R) :
    v (shift a d) = v a + C d * L a := by
  change L a * (y + z a + C (a 7 + d)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (L a) (C d)]
  rfl

private theorem w_collect (p y v c l d : R[X]) :
    (p + d) * (y + (v + d * l) + (c + d)) =
      p * (y + v + c) + d * (p * (l + 1) + y + v + c + d * (l + 1)) := by ring

theorem w_change (a : ℕ → R) (d : R) :
    w (shift a d) = w a + C d * wSlope a d := by
  change (X + y + z a + C (a 8 + d)) *
    (y + v (shift a d) + C (a 9 + d)) = _
  rw [v_change, map_add, map_add, ← add_assoc (X + y + z a)]
  exact w_collect (P a) y (v a) (C (a 9)) (L a) (C d)

theorem s_change (a : ℕ → R) (d : R) :
    s (shift a d) = s a + C d * sSlope a := by
  change (z a + C (a 10)) * (v (shift a d) + C (a 11)) = _
  rw [v_change]
  exact Char2Degree25RowThirteen.product_change _ _ _ _ _

theorem r_change (a : ℕ → R) (d : R) :
    r (shift a d) = r a + C d * rLeft a := by
  change rLeft a * (u a + C (a 13 + d)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (rLeft a) (C d)]
  rfl

theorem g_change (a : ℕ → R) (d : R) :
    g (shift a d) = g a + C d * (X + u a + C (a 15)) := by
  change (z a + t a + C (a 14 + d)) * (X + u a + C (a 15)) = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

theorem ell_change (a : ℕ → R) (d : R) :
    ell (shift a d) = ell a + C d * ellSlope a := by
  change E a * (z a + v (shift a d) + C (a 17)) = _
  rw [v_change]
  exact Char2Degree25RowThirteen.product_change_middle _ _ _ _ _ _

theorem hRight_change (a : ℕ → R) (d : R) :
    hRight (shift a d) = hRight a + C d * W a d := by
  change X + y + z a + u a + v (shift a d) + w (shift a d) +
    r (shift a d) + C (a 19) = _
  rw [v_change, w_change, r_change]
  exact Char2Degree25RowThirteen.collect_hRight _ _ _ _ _ _ _ _ _

theorem h_change (a : ℕ → R) (d : R) :
    h (shift a d) = h a + C d * (hLeft a * W a d) := by
  change hLeft a * hRight (shift a d) = _
  rw [hRight_change]
  exact Char2Degree25RowThirteen.product_change_plain _ _ _ _

theorem j_change (a : ℕ → R) (d : R) :
    j (shift a d) = j a + C d * (jLeft a * ellSlope a) := by
  change jLeft a * (ell (shift a d) + C (a 21)) = _
  rw [ell_change]
  exact Char2Degree25RowThirteen.product_change _ _ _ _ _

private theorem vP_collect (l x y z c7 c8 : R[X]) :
    l * (y + z + c7) + (x + y + z + c8) * l = l * (x + (c7 + c8)) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add]

theorem v_add_PL (a : ℕ → R) :
    v a + P a * L a = L a * (X + C (a 7 + a 8)) := by
  rw [map_add]
  exact vP_collect (L a) X y (z a) (C (a 7)) (C (a 8))

private theorem WU_collect (l x y z t v c8 c9 c12 c5 d : R[X]) :
    (l + ((x + y + z + c8) * (l + 1) + y + v + c9 + d * (l + 1)) +
      (x + t + c12)) + (z + t + c5) =
    l + (v + (x + y + z + c8) * l) + (c12 + c8 + c9 + c5) + d * (l + 1) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add]

theorem W_add_U (a : ℕ → R) (d : R) : W a d + U a = Q2 a d := by
  have he := WU_collect (L a) X y (z a) (t a) (v a)
    (C (a 8)) (C (a 9)) (C (a 12)) (C (a 5)) (C d)
  change W a d + U a = L a + (v a + P a * L a) +
    (C (a 12) + C (a 8) + C (a 9) + C (a 5)) + C d * (L a + 1) at he
  rw [he, v_add_PL]
  simp only [Q2, map_add]

theorem u_factor (a : ℕ → R) : u a = (hLeft a + C (K a)) * U a := by
  have hc : hLeft a + C (K a) = y + z a + t a + C (a 4) := by
    unfold hLeft K
    rw [map_add, ← add_assoc, add_right_comm (y + z a + t a) (C (a 18)) (C (a 4)),
      CharTwo.add_cancel_right]
  rw [hc]
  rfl

private theorem cancel_shared (ss rr x c e k uu hh ww jj : R[X]) :
    ss + rr + (x + (hh + k) * uu + c) + e + hh * ww + jj =
      ss + rr + x + c + e + k * uu + hh * (ww + uu) + jj := by ring

private theorem nLeft_collect (base s r g e h j c d ss rr gg ee hh jj : R[X]) :
    base + (s + d * ss) + (r + d * rr) + (g + d * gg) + (e + d * ee) +
      (h + d * hh) + (j + d * jj) + c =
    (base + s + r + g + e + h + j + c) + d * (ss + rr + gg + ee + hh + jj) := by ring

theorem nLeft_change (a : ℕ → R) (d : R) :
    nLeft (shift a d) = nLeft a + C d * bracket a d := by
  change (X + t a + u a) + s (shift a d) + r (shift a d) + g (shift a d) +
    ell (shift a d) + h (shift a d) + j (shift a d) + C (a 22) = _
  rw [s_change, r_change, g_change, ell_change, h_change, j_change,
    nLeft_collect]
  have hb : sSlope a + rLeft a + (X + u a + C (a 15)) + ellSlope a +
      hLeft a * W a d + jLeft a * ellSlope a = bracket a d := by
    rw [u_factor, cancel_shared, W_add_U]
    rfl
  rw [hb]
  rfl

theorem head_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.head (shift a d) =
      Char2Degree25Frame.head a + C d * ellSlope a := by
  change y + z a + u a + ell (shift a d) = _
  rw [ell_change, ← add_assoc]
  rfl

private theorem output_collect (head nl nr c d e b : R[X]) :
    (head + d * e) + (nl + d * b) * nr + c =
      (head + nl * nr + c) + d * (e + nr * b) := by ring

theorem output_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.output (shift a d) =
      Char2Degree25Frame.output a + C d * outputSlope a d := by
  change Char2Degree25Frame.head (shift a d) + nLeft (shift a d) * nRight a + C (a 24) = _
  rw [head_change, nLeft_change]
  exact output_collect _ _ _ _ _ _ _

end FastPoly.Char2Degree25TwentyTwoWires
