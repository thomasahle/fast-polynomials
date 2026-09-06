import FastPoly.Examples.Char2DecoderSteps

/-! The literal four-scalar inverse (11.4) in the current appendix.
The previously recovered context stays fixed. Every cancellation acts on a
named scalar; no circuit coefficient polynomial or generic solve is used. -/

namespace FastPoly.Char2PaperDegree11TailInverse

set_option maxHeartbeats 20000

variable {F : Type*} [CommRing F] [CharP F 2]

structure Context (F : Type*) where
  a0 : F
  a3 : F
  a4 : F
  a6 : F
  h : F

structure Keys (F : Type*) where
  a5 : F
  a7 : F
  a9 : F
  a10 : F

structure Rows (F : Type*) where
  d3 : F
  d2 : F
  d1 : F
  d0 : F

def a8 (c : Context F) (k : Keys F) : F := c.h + k.a5 + k.a7
def kappa (c : Context F) (k : Keys F) : F := k.a5 * (c.h + k.a5)
def row3 (c : Context F) (k : Keys F) : F := kappa c k + k.a7 + k.a9

def encode (c : Context F) (k : Keys F) : Rows F where
  d3 := row3 c k
  d2 := c.a0 * row3 c k + k.a5
  d1 := c.a3 * row3 c k + c.a0 * k.a5 + k.a7
  d0 := kappa c k * c.a4 + k.a7 * c.a6 + k.a9 * a8 c k + k.a10

def recover5 (c : Context F) (r : Rows F) : F := r.d2 + c.a0 * r.d3
def recover7 (c : Context F) (r : Rows F) : F :=
  r.d1 + c.a3 * r.d3 + c.a0 * recover5 c r
def recoverKappa (c : Context F) (r : Rows F) : F := recover5 c r * (c.h + recover5 c r)
def recover9 (c : Context F) (r : Rows F) : F := r.d3 + recoverKappa c r + recover7 c r
def recover8 (c : Context F) (r : Rows F) : F := c.h + recover5 c r + recover7 c r
def recover10 (c : Context F) (r : Rows F) : F :=
  r.d0 + recoverKappa c r * c.a4 + recover7 c r * c.a6 + recover9 c r * recover8 c r

/-- The displayed sequential scalar formulas, in their original key order. -/
def decode (c : Context F) (r : Rows F) : Keys F where
  a5 := recover5 c r
  a7 := recover7 c r
  a9 := recover9 c r
  a10 := recover10 c r

private theorem cancel_two (p q x : F) : (p + q + x) + p + q = x := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

private theorem cancel_three (p q r x : F) : (p + q + r + x) + p + q + r = x := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem recover5_encode (c : Context F) (k : Keys F) : recover5 c (encode c k) = k.a5 :=
  Char2Decoder.cancel_tail _ _

theorem recover7_encode (c : Context F) (k : Keys F) : recover7 c (encode c k) = k.a7 := by
  unfold recover7
  rw [recover5_encode]
  exact cancel_two _ _ _

theorem recoverKappa_encode (c : Context F) (k : Keys F) :
    recoverKappa c (encode c k) = kappa c k := by
  unfold recoverKappa
  rw [recover5_encode]
  rfl

theorem recover9_encode (c : Context F) (k : Keys F) : recover9 c (encode c k) = k.a9 := by
  unfold recover9
  rw [recoverKappa_encode, recover7_encode]
  exact cancel_two _ _ _

theorem recover8_encode (c : Context F) (k : Keys F) : recover8 c (encode c k) = a8 c k := by
  unfold recover8
  rw [recover5_encode, recover7_encode]
  rfl

theorem recover10_encode (c : Context F) (k : Keys F) : recover10 c (encode c k) = k.a10 := by
  unfold recover10
  rw [recoverKappa_encode, recover7_encode, recover9_encode, recover8_encode]
  exact cancel_three _ _ _ _

theorem decode_encode (c : Context F) (k : Keys F) : decode c (encode c k) = k := by
  cases k with
  | mk a5 a7 a9 a10 =>
    simp only [decode, recover5_encode, recover7_encode, recover9_encode, recover10_encode]

theorem kappa_decode (c : Context F) (r : Rows F) : kappa c (decode c r) = recoverKappa c r := rfl
theorem a8_decode (c : Context F) (r : Rows F) : a8 c (decode c r) = recover8 c r := rfl

theorem row3_decode (c : Context F) (r : Rows F) : row3 c (decode c r) = r.d3 := by
  change recoverKappa c r + recover7 c r + (r.d3 + recoverKappa c r + recover7 c r) = r.d3
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem row2_decode (c : Context F) (r : Rows F) : (encode c (decode c r)).d2 = r.d2 := by
  change c.a0 * row3 c (decode c r) + recover5 c r = r.d2
  rw [row3_decode, recover5, add_comm r.d2, CharTwo.add_cancel_left]

theorem row1_decode (c : Context F) (r : Rows F) : (encode c (decode c r)).d1 = r.d1 := by
  change c.a3 * row3 c (decode c r) + c.a0 * recover5 c r + recover7 c r = r.d1
  rw [row3_decode, recover7]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem row0_decode (c : Context F) (r : Rows F) : (encode c (decode c r)).d0 = r.d0 := by
  change recoverKappa c r * c.a4 + recover7 c r * c.a6 + recover9 c r * recover8 c r +
    recover10 c r = r.d0
  rw [recover10]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, zero_add, add_zero]

theorem encode_decode (c : Context F) (r : Rows F) : encode c (decode c r) = r := by
  have h3 : (encode c (decode c r)).d3 = r.d3 := row3_decode c r
  have h2 := row2_decode c r
  have h1 := row1_decode c r
  have h0 := row0_decode c r
  cases he : encode c (decode c r)
  cases r
  simp only [he] at h3 h2 h1 h0
  cases h3
  cases h2
  cases h1
  cases h0
  rfl

/-- Its inverse is the literal formula above, parameterized by the already
recovered context. Both compositions are proved separately. -/
def equiv (c : Context F) : Keys F ≃ Rows F where
  toFun := encode c
  invFun := decode c
  left_inv := decode_encode c
  right_inv := encode_decode c

end FastPoly.Char2PaperDegree11TailInverse
