import FastPoly.Examples.Char2Frobenius

/-! The two explicit Frobenius inverses in equations (11.1)--(11.2).
This is the scalar six-row interface of the appendix's degree-eleven circuit,
not the different website circuit. The actual coefficient bridge is separate.
-/
namespace FastPoly.Char2PaperDegree11HeadInverse

set_option maxHeartbeats 20000
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

@[ext] structure Head (F : Type*) where
  a0 : F
  a3 : F
  a4 : F
  h : F
  s : F
  a1 : F

@[ext] structure Rows (F : Type*) where
  c10 : F
  c9 : F
  c8 : F
  c7 : F
  c6 : F
  c5 : F

def k7 (a0 a3 : F) : F := 1 + a0^2 + a0^4 + a3
def k6 (a0 a4 : F) : F := 1 + a0 + a0^3 + a0^5 + a4
def k5 (a0 a3 : F) : F := a0 + a0^2 + a0^4*a3 + a0^2*a3 + a3

def encode (p : Head F) : Rows F where
  c10 := p.a0
  c9 := p.a3 + 1
  c8 := p.a4 + p.a0
  c7 := k7 p.a0 p.a3 + p.s^2 + p.h
  c6 := k6 p.a0 p.a4 + p.a0*p.s^2 + (p.a0+1)*p.h
  c5 := k5 p.a0 p.a3 + p.a0^2*(p.s^2+p.h) + p.s + p.a1^2 +
    p.a3*p.s^2 + p.s*p.h + p.a3*p.h

noncomputable def root (x : F) : F := (Char2Certificate.frobeniusPivot 1).symm x
theorem root_square (x : F) : root (x^2) = x :=
  (Char2Certificate.frobeniusPivot 1).symm_apply_apply x
theorem square_root (x : F) : root x ^ 2 = x :=
  (Char2Certificate.frobeniusPivot 1).apply_symm_apply x

def d0 (c : Rows F) : F := c.c10
def d3 (c : Rows F) : F := c.c9 + 1
def d4 (c : Rows F) : F := c.c8 + d0 c
def dr (c : Rows F) : F := c.c7 + k7 (d0 c) (d3 c)
def dh (c : Rows F) : F := c.c6 + k6 (d0 c) (d4 c) + d0 c * dr c
noncomputable def ds (c : Rows F) : F := root (dr c + dh c)
noncomputable def d1 (c : Rows F) : F :=
  root (c.c5 + k5 (d0 c) (d3 c) + d0 c^2*dr c + ds c +
    d3 c*(ds c)^2 + ds c*dh c + d3 c*dh c)

noncomputable def decode (c : Rows F) : Head F :=
  ⟨d0 c, d3 c, d4 c, dh c, ds c, d1 c⟩

theorem d0_encode (p : Head F) : d0 (encode p) = p.a0 := rfl
theorem d3_encode (p : Head F) : d3 (encode p) = p.a3 := by
  exact CharTwo.add_cancel_right p.a3 1
theorem d4_encode (p : Head F) : d4 (encode p) = p.a4 := by
  exact CharTwo.add_cancel_right p.a4 p.a0
theorem dr_encode (p : Head F) : dr (encode p) = p.s^2+p.h := by
  rw [dr, d0_encode, d3_encode]
  change (k7 p.a0 p.a3 + p.s^2 + p.h) + k7 p.a0 p.a3 = _
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

private theorem mix (k a s h : F) :
    (k+a*s+(a+1)*h)+k+a*(s+h) = h := by
  rw [add_mul, one_mul, mul_add]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem dh_encode (p : Head F) : dh (encode p) = p.h := by
  rw [dh, d0_encode, d4_encode, dr_encode]
  exact mix _ _ _ _
theorem ds_encode (p : Head F) : ds (encode p) = p.s := by
  rw [ds, dr_encode, dh_encode, CharTwo.add_cancel_right, root_square]
theorem d1_encode (p : Head F) : d1 (encode p) = p.a1 := by
  rw [d1, d0_encode, d3_encode, dr_encode, ds_encode, dh_encode]
  change root ((k5 p.a0 p.a3 + p.a0^2*(p.s^2+p.h) + p.s + p.a1^2 +
    p.a3*p.s^2 + p.s*p.h + p.a3*p.h) + k5 p.a0 p.a3 +
    p.a0^2*(p.s^2+p.h) + p.s + p.a3*p.s^2 + p.s*p.h + p.a3*p.h) = p.a1
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero, root_square]

theorem decode_encode (p : Head F) : decode (encode p) = p := by
  apply Head.ext
  · exact d0_encode p
  · exact d3_encode p
  · exact d4_encode p
  · exact dh_encode p
  · exact ds_encode p
  · exact d1_encode p

theorem ds_square (c : Rows F) : ds c ^ 2 = dr c + dh c := square_root _
theorem d1_square (c : Rows F) : d1 c ^ 2 =
    c.c5 + k5 (d0 c) (d3 c) + d0 c^2*dr c + ds c +
      d3 c*(ds c)^2 + ds c*dh c + d3 c*dh c := square_root _

private theorem undo_mix (k a r h : F) : k + a*(r+h)+(a+1)*h = k+a*r+h := by
  rw [mul_add, add_mul, one_mul]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem encode_decode (c : Rows F) : encode (decode c) = c := by
  apply Rows.ext
  · rfl
  · exact CharTwo.add_cancel_right c.c9 1
  · exact CharTwo.add_cancel_right c.c8 (d0 c)
  · change k7 (d0 c) (d3 c) + ds c^2 + dh c = c.c7
    rw [ds_square, ← add_assoc, CharTwo.add_cancel_right, dr,
      add_comm c.c7 (k7 (d0 c) (d3 c)), CharTwo.add_cancel_left]
  · change k6 (d0 c) (d4 c) + d0 c*ds c^2 + (d0 c+1)*dh c = c.c6
    rw [ds_square, undo_mix, dh]
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero, zero_add, add_zero]
  · change k5 (d0 c) (d3 c) + d0 c^2*(ds c^2+dh c) + ds c + d1 c^2 +
      d3 c*ds c^2 + ds c*dh c + d3 c*dh c = c.c5
    rw [d1_square]
    have hr : ds c^2 + dh c = dr c := by rw [ds_square, CharTwo.add_cancel_right]
    rw [hr]
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero, zero_add, add_zero]

noncomputable def equiv : Head F ≃ Rows F where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

end FastPoly.Char2PaperDegree11HeadInverse
