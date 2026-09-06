import FastPoly.Examples.Char2Degree25HighFrame
import FastPoly.Examples.Char2Degree25RowThirteen

/-! Exact named changes of the supplied middle-coordinate q20 direction.
No high output coefficient or recursive gate polynomial is expanded here. -/
namespace FastPoly.Char2Degree25TwentyWires

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def K (a : ℕ → R) : R := a 4 + a 18
def B (a : ℕ → R) : R := a 2 + a 6
def l (a : ℕ → R) (d : R) : R := d * (K a + d)
def k (a : ℕ → R) (d : R) : R := l a d + (B a + 1) * d
def c (a : ℕ → R) (d : R) : R := B a * (B a + 1) * d

def shift (a : ℕ → R) (d : R) : ℕ → R
  | 4 => a 4 + d
  | 18 => a 18 + d
  | 8 => a 8 + l a d
  | 7 => a 7 + k a d
  | 13 => a 13 + k a d
  | 9 => a 9 + c a d
  | i => a i

noncomputable def A (a : ℕ → R) : R[X] := X + C (a 2)
noncomputable def L (a : ℕ → R) : R[X] := X + C (a 6)
noncomputable def U (a : ℕ → R) : R[X] := z a + t a + C (a 5)
noncomputable def G (a : ℕ → R) : R[X] := z a + t a + C (a 14)
noncomputable def E (a : ℕ → R) : R[X] := X + C (a 16)
noncomputable def S (a : ℕ → R) : R[X] := z a + C (a 10)
noncomputable def P (a : ℕ → R) : R[X] := X + y + z a + C (a 8)
noncomputable def Q (a : ℕ → R) : R[X] := L a + rLeft a + P a * A a
noncomputable def W (a : ℕ → R) (d : R) : R[X] :=
  y + v a + C (B a) * P a + C (a 9) + C (k a d) * L a + C (c a d)

noncomputable def wDelta (a : ℕ → R) (d : R) : R[X] :=
  C (k a d) * P a * L a + C (c a d) * P a +
    C (l a d) * (y + v a + C (a 9)) +
    C (l a d) * C (k a d) * L a + C (l a d) * C (c a d)

noncomputable def hSmall (a : ℕ → R) : R[X] :=
  X + y + z a + v a + w a + rLeft a * C (a 13) + C (a 19)
noncomputable def hDelta (a : ℕ → R) (d : R) : R[X] :=
  C (l a d) * (rLeft a + 1) * U a + C d * hSmall a +
    (hLeft a + C d) * (C (k a d) * Q a + C (l a d) * W a d)

noncomputable def T1 (a : ℕ → R) : R[X] := (rLeft a + G a + 1) * U a + w a
noncomputable def T2 (a : ℕ → R) (d : R) : R[X] :=
  (rLeft a + 1) * U a + (hLeft a + C d) * W a d
noncomputable def T3 (a : ℕ → R) (d : R) : R[X] :=
  (hLeft a + C d) * Q a + jLeft a * E a * L a
noncomputable def low (a : ℕ → R) (d : R) : R[X] :=
  C (k a d) * (S a * L a + rLeft a + E a * L a) +
    C d * (X + y + z a + v a + rLeft a * C (a 13) + C (a 19))
noncomputable def deltaN (a : ℕ → R) (d : R) : R[X] :=
  C d * T1 a + C (l a d) * T2 a d + C (k a d) * T3 a d + low a d
noncomputable def outputDelta (a : ℕ → R) (d : R) : R[X] :=
  C d * U a + C (k a d) * (E a * L a) + nRight a * deltaN a d

theorem u_eq (a : ℕ → R) : u a = (hLeft a + C (K a)) * U a := by
  have he : hLeft a + C (K a) = y + z a + t a + C (a 4) := by
    simp only [hLeft, K, map_add, add_assoc, add_comm, add_left_comm,
      CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]
  rw [he]
  rfl

theorem L_eq (a : ℕ → R) : L a = A a + C (B a) := by
  simp only [L, A, B, map_add, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem Q_eq_inner (a : ℕ → R) : Q a = Char2Degree25RowThirteen.inner a := by
  rw [Char2Degree25RowThirteen.inner, Char2Degree25RowThirteen.L_add_B]
  change L a + rLeft a + P a * A a = L a + P a * A a + rLeft a
  exact add_right_comm _ _ _

private theorem scalar_B (b l d : R) :
    (l + (b + 1) * d) * b + b * (b + 1) * d = b * l := by
  rw [add_mul]
  have he : (b + 1) * d * b = b * (b + 1) * d := by ring
  rw [he, add_assoc, CharTwo.add_self_eq_zero, add_zero, mul_comm]

theorem Bk_c (a : ℕ → R) (d : R) :
    C (k a d) * C (B a) + C (c a d) = C (B a) * C (l a d) := by
  rw [← map_mul, ← map_add, ← map_mul]
  exact congrArg C (scalar_B (B a) (l a d) d)

theorem l_poly (a : ℕ → R) (d : R) :
    C (l a d) = C d * (C (K a) + C d) := by
  rw [l, map_mul, map_add]

theorem u_shift (a : ℕ → R) (d : R) :
    u (shift a d) = u a + C d * U a := by
  change (y + z a + t a + C (a 4 + d)) * U a = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

theorem v_shift (a : ℕ → R) (d : R) :
    v (shift a d) = v a + C (k a d) * L a := by
  change L a * (y + z a + C (a 7 + k a d)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (L a) (C (k a d))]
  rfl

private theorem w_change (p y v a9 l k c L : R[X]) :
    (p + l) * (y + (v + k * L) + (a9 + c)) =
      p * (y + v + a9) + (k * p * L + c * p +
        l * (y + v + a9) + l * k * L + l * c) := by ring

theorem w_shift (a : ℕ → R) (d : R) :
    w (shift a d) = w a + wDelta a d := by
  change (X + y + z a + C (a 8 + l a d)) *
    (y + v (shift a d) + C (a 9 + c a d)) = _
  have h8 : (C (a 8 + l a d) : R[X]) = C (a 8) + C (l a d) := map_add C _ _
  have h9 : (C (a 9 + c a d) : R[X]) = C (a 9) + C (c a d) := map_add C _ _
  rw [v_shift, h8, h9]
  have hp : X + y + z a + (C (a 8) + C (l a d)) = P a + C (l a d) := by
    simp only [P, add_assoc]
  rw [hp]
  exact w_change _ _ _ _ _ _ _ _

theorem s_shift (a : ℕ → R) (d : R) :
    s (shift a d) = s a + C (k a d) * (S a * L a) := by
  change S a * (v (shift a d) + C (a 11)) = _
  rw [v_shift]
  exact Char2Degree25RowThirteen.product_change _ _ _ _ _

private theorem r_change (r u a d U k : R[X]) :
    r * ((u + d * U) + (a + k)) = r * (u + a) + d * r * U + k * r := by ring

theorem r_shift (a : ℕ → R) (d : R) :
    r (shift a d) = r a + C d * rLeft a * U a + C (k a d) * rLeft a := by
  change rLeft a * (u (shift a d) + C (a 13 + k a d)) = _
  rw [u_shift, map_add]
  exact r_change _ _ _ _ _ _

theorem g_shift (a : ℕ → R) (d : R) :
    g (shift a d) = g a + C d * (G a * U a) := by
  change G a * (X + u (shift a d) + C (a 15)) = _
  rw [u_shift]
  exact Char2Degree25RowThirteen.product_change_middle _ _ _ _ _ _

theorem ell_shift (a : ℕ → R) (d : R) :
    ell (shift a d) = ell a + C (k a d) * (E a * L a) := by
  change E a * (z a + v (shift a d) + C (a 17)) = _
  rw [v_shift]
  exact Char2Degree25RowThirteen.product_change_middle _ _ _ _ _ _

theorem j_shift (a : ℕ → R) (d : R) :
    j (shift a d) = j a + C (k a d) * (jLeft a * (E a * L a)) := by
  change jLeft a * (ell (shift a d) + C (a 21)) = _
  rw [ell_shift]
  exact Char2Degree25RowThirteen.product_change _ _ _ _ _

theorem hLeft_shift (a : ℕ → R) (d : R) :
    hLeft (shift a d) = hLeft a + C d := by
  change y + z a + t a + C (a 18 + d) = _
  rw [map_add, ← add_assoc]
  rfl

private theorem right_group (x u v w r a d U k L wd R : R[X]) :
    x + (u + d * U) + (v + k * L) + (w + wd) + (r + d * R * U + k * R) + a =
      (x + u + v + w + r + a) + (d * (1 + R) * U + k * (L + R) + wd) := by ring

private theorem right_core1 (r L p V d U k l c : R[X]) :
    d * (1 + r) * U + k * (L + r) +
      (k * p * L + c * p + l * V + l * k * L + l * c) =
    d * (1 + r) * U + k * (L + r + p * L) + c * p + l * (V + k * L + c) := by ring

private theorem right_core2 (r L p A b V d U k l c : R[X]) :
    d * (1 + r) * U + k * (L + r + (p * A + b * p)) + c * p + l * (V + k * L + c) =
      d * (1 + r) * U + k * (L + r + p * A) + (k * b + c) * p + l * (V + k * L + c) := by ring

private theorem right_core3 (d U r k q b l p V L c : R[X]) :
    d * (1 + r) * U + k * q + (b * l) * p + l * (V + k * L + c) =
      d * (1 + r) * U + k * q + l * (V + b * p + k * L + c) := by ring

theorem W_reorder (a : ℕ → R) (d : R) :
    (y + v a + C (a 9)) + C (B a) * P a + C (k a d) * L a + C (c a d) = W a d := by
  unfold W
  ac_rfl

theorem hRight_shift (a : ℕ → R) (d : R) :
    hRight (shift a d) = hRight a +
      (C d * (1 + rLeft a) * U a + C (k a d) * Q a + C (l a d) * W a d) := by
  change X + y + z a + u (shift a d) + v (shift a d) + w (shift a d) +
    r (shift a d) + C (a 19) = _
  rw [u_shift, v_shift, w_shift, r_shift, right_group]
  have hp : P a * L a = P a * A a + C (B a) * P a := by rw [L_eq]; ring
  rw [wDelta, right_core1, hp, right_core2, Bk_c, right_core3, W_reorder]
  rfl

private theorem hRight_factor (x u v w r a13 a19 : R[X]) :
    x + u + v + w + r * (u + a13) + a19 =
      (1 + r) * u + (x + v + w + r * a13 + a19) := by ring

theorem hRight_eq (a : ℕ → R) :
    hRight a = (1 + rLeft a) * ((hLeft a + C (K a)) * U a) + hSmall a := by
  change X + y + z a + u a + v a + w a + rLeft a * (u a + C (a 13)) + C (a 19) = _
  rw [hRight_factor, u_eq]
  rfl

private theorem h_cancel (H rr U K d small tail : R[X]) :
    (H + d) * ((1 + rr) * ((H + K) * U) + small +
      (d * (1 + rr) * U + tail)) =
      H * ((1 + rr) * ((H + K) * U) + small) +
        (d * (K + d) * (rr + 1) * U + d * small + (H + d) * tail) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem h_shift (a : ℕ → R) (d : R) :
    h (shift a d) = h a + hDelta a d := by
  change hLeft (shift a d) * hRight (shift a d) = _
  rw [hLeft_shift, hRight_shift]
  have hr := hRight_eq a
  rw [hr]
  have ht : C d * (1 + rLeft a) * U a + C (k a d) * Q a + C (l a d) * W a d =
      C d * (1 + rLeft a) * U a + (C (k a d) * Q a + C (l a d) * W a d) := by
    rw [add_assoc]
  rw [ht, h_cancel]
  change hLeft a * ((1 + rLeft a) * ((hLeft a + C (K a)) * U a) + hSmall a) + _ = _
  rw [← hr]
  change h a + (C d * (C (K a) + C d) * (rLeft a + 1) * U a +
    C d * hSmall a + (hLeft a + C d) * (C (k a d) * Q a + C (l a d) * W a d)) = _
  rw [← l_poly]
  rfl

private theorem left_group (x u s r g ell h j a d U k SL L rr G E J hd : R[X]) :
    x + (u + d * U) + (s + k * (SL * L)) + (r + d * rr * U + k * rr) +
      (g + d * (G * U)) + (ell + k * (E * L)) + (h + hd) + (j + k * (J * (E * L))) + a =
      (x + u + s + r + g + ell + h + j + a) +
        (d * U + k * (SL * L) + d * rr * U + k * rr + d * (G * U) +
          k * (E * L) + hd + k * (J * (E * L))) := by ring

private theorem delta_group (d k l U SL L rr G E J H Q W x v w a13 a19 : R[X]) :
    d * U + k * (SL * L) + d * rr * U + k * rr + d * (G * U) + k * (E * L) +
      (l * (rr + 1) * U + d * (x + v + w + rr * a13 + a19) +
        (H + d) * (k * Q + l * W)) + k * (J * (E * L)) =
      d * ((rr + G + 1) * U + w) + l * ((rr + 1) * U + (H + d) * W) +
        k * ((H + d) * Q + J * E * L) +
          (k * (SL * L + rr + E * L) + d * (x + v + rr * a13 + a19)) := by ring

theorem nLeft_shift (a : ℕ → R) (d : R) :
    nLeft (shift a d) = nLeft a + deltaN a d := by
  change X + t a + u (shift a d) + s (shift a d) + r (shift a d) + g (shift a d) +
    ell (shift a d) + h (shift a d) + j (shift a d) + C (a 22) = _
  rw [u_shift, s_shift, r_shift, g_shift, ell_shift, h_shift, j_shift, left_group]
  rw [hDelta, hSmall, delta_group]
  rfl

private theorem output_group (head u ell nl nr a d U k E L dn : R[X]) :
    head + (u + d * U) + (ell + k * (E * L)) + (nl + dn) * nr + a =
      (head + u + ell + nl * nr + a) + (d * U + k * (E * L) + nr * dn) := by ring

theorem output_shift (a : ℕ → R) (d : R) :
    Char2Degree25Frame.output (shift a d) = Char2Degree25Frame.output a + outputDelta a d := by
  change y + z a + u (shift a d) + ell (shift a d) + nLeft (shift a d) * nRight a + C (a 24) = _
  rw [u_shift, ell_shift, nLeft_shift]
  exact output_group _ _ _ _ _ _ _ _ _ _ _ _

end FastPoly.Char2Degree25TwentyWires
