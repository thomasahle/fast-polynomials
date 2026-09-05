import FastPoly.Examples.Char2DecoderSteps

/-!
# The degree-23 verifier's explicit four-row inverse

This is the terminal block of `char2/verify_n23_unitriangular_symbolic.py`,
equations (12)--(14). The prefix has already recovered `q0,...,q17`.
Both inverse directions are proved by named one-step identities. In particular,
the possibly large coefficient `T` is never expanded during a proof.

This module proves the terminal algebra, including the known row corrections.
It does not yet identify these rows with coefficients of the 12-product circuit;
that coefficient bridge and the preceding scalar pivots are separate obligations.
-/

namespace FastPoly.Char2Degree23Terminal

set_option maxHeartbeats 20000

open Char2Decoder

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The four unknowns, in exactly the verifier's order. -/
structure Keys (R : Type*) where
  q18 : R
  q19 : R
  q20 : R
  q21 : R

/-- The four corrected coefficient rows, in descending order. -/
structure Rows (R : Type*) where
  e4 : R
  e3 : R
  e2 : R
  e1 : R

omit [CommRing R] [CharP R 2] in
private theorem keys_ext {q r : Keys R} (h18 : q.q18 = r.q18)
    (h19 : q.q19 = r.q19) (h20 : q.q20 = r.q20) (h21 : q.q21 = r.q21) : q = r := by
  cases q; cases r; cases h18; cases h19; cases h20; cases h21; rfl

omit [CommRing R] [CharP R 2] in
private theorem rows_ext {e f : Rows R} (h4 : e.e4 = f.e4)
    (h3 : e.e3 = f.e3) (h2 : e.e2 = f.e2) (h1 : e.e1 = f.e1) : e = f := by
  cases e; cases f; cases h4; cases h3; cases h2; cases h1; rfl

/-- Quantities supplied by the decoded prefix. Keeping `T` abstract is important:
the inverse only cancels `T * q18`, irrespective of how `T` was computed. -/
structure Parameters (R : Type*) where
  a : R -- q0 + q8
  b : R -- q1
  c : R -- q2
  d : R -- q8
  T : R

/-- The literal prefix quantities from the Python verifier. -/
def parameters (q : ℕ → R) : Parameters R where
  a := q 0 + q 8
  b := q 1
  c := q 2
  d := q 8
  T := q 0 * q 2 + q 2 * q 8 + q 2 + q 3 + q 5 + q 6 +
    q 7 * q 16 + q 11 + q 16 ^ 2 + 1

def tail2 (p : Parameters R) (x y : R) : R :=
  (p.b * (p.a + 1) + p.d) * x + p.b * y

def tail1 (p : Parameters R) (x y z : R) : R :=
  p.T * x + p.c * y + p.d * z + x * z + z

def encode (p : Parameters R) (q : Keys R) : Rows R where
  e4 := (p.a + 1) * q.q18 + q.q19
  e3 := p.a * q.q18 + q.q19
  e2 := tail2 p q.q18 q.q19 + q.q20
  e1 := tail1 p q.q18 q.q19 q.q20 + q.q21

def recover18 (e : Rows R) : R := e.e4 + e.e3

def recover19 (p : Parameters R) (e : Rows R) : R :=
  e.e3 + p.a * recover18 e

def recover20 (p : Parameters R) (e : Rows R) : R :=
  e.e2 + tail2 p (recover18 e) (recover19 p e)

def recover21 (p : Parameters R) (e : Rows R) : R :=
  e.e1 + tail1 p (recover18 e) (recover19 p e) (recover20 p e)

def decode (p : Parameters R) (e : Rows R) : Keys R :=
  ⟨recover18 e, recover19 p e, recover20 p e, recover21 p e⟩

/-- The sole distributive step in the inverse: add the first two rows. -/
theorem first_pair (a x y : R) : ((a + 1) * x + y) + (a * x + y) = x := by
  rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero, add_mul, one_mul]
  exact cancel_tail (a * x) x

theorem recover18_encode (p : Parameters R) (q : Keys R) :
    recover18 (encode p q) = q.q18 := first_pair p.a q.q18 q.q19

theorem recover19_encode (p : Parameters R) (q : Keys R) :
    recover19 p (encode p q) = q.q19 := by
  rw [recover19, recover18_encode]
  exact cancel_tail (p.a * q.q18) q.q19

theorem recover20_encode (p : Parameters R) (q : Keys R) :
    recover20 p (encode p q) = q.q20 := by
  rw [recover20, recover18_encode, recover19_encode]
  exact cancel_tail (tail2 p q.q18 q.q19) q.q20

theorem recover21_encode (p : Parameters R) (q : Keys R) :
    recover21 p (encode p q) = q.q21 := by
  rw [recover21, recover18_encode, recover19_encode, recover20_encode]
  exact cancel_tail (tail1 p q.q18 q.q19 q.q20) q.q21

theorem decode_encode (p : Parameters R) (q : Keys R) : decode p (encode p q) = q :=
  keys_ext (recover18_encode p q) (recover19_encode p q)
    (recover20_encode p q) (recover21_encode p q)

theorem row3_decode (p : Parameters R) (e : Rows R) :
    (encode p (decode p e)).e3 = e.e3 := by
  change p.a * recover18 e + (e.e3 + p.a * recover18 e) = e.e3
  rw [add_comm e.e3, CharTwo.add_cancel_left]

theorem row4_decode (p : Parameters R) (e : Rows R) :
    (encode p (decode p e)).e4 = e.e4 := by
  change (p.a + 1) * recover18 e + recover19 p e = e.e4
  rw [add_mul, one_mul, add_comm (p.a * recover18 e), add_assoc]
  change recover18 e + (encode p (decode p e)).e3 = e.e4
  rw [row3_decode, recover18, CharTwo.add_cancel_right]

theorem row2_decode (p : Parameters R) (e : Rows R) :
    (encode p (decode p e)).e2 = e.e2 := by
  change tail2 p (recover18 e) (recover19 p e) +
    (e.e2 + tail2 p (recover18 e) (recover19 p e)) = e.e2
  rw [add_comm e.e2, CharTwo.add_cancel_left]

theorem row1_decode (p : Parameters R) (e : Rows R) :
    (encode p (decode p e)).e1 = e.e1 := by
  change tail1 p (recover18 e) (recover19 p e) (recover20 p e) +
    (e.e1 + tail1 p (recover18 e) (recover19 p e) (recover20 p e)) = e.e1
  rw [add_comm e.e1, CharTwo.add_cancel_left]

theorem encode_decode (p : Parameters R) (e : Rows R) : encode p (decode p e) = e :=
  rows_ext (row4_decode p e) (row3_decode p e) (row2_decode p e) (row1_decode p e)

/-- The explicit inverse works over every characteristic-two commutative ring,
not just a finite or perfect field. -/
def blockEquiv (p : Parameters R) : Keys R ≃ Rows R where
  toFun := encode p
  invFun := decode p
  left_inv := decode_encode p
  right_inv := encode_decode p

/-- The four known coefficients multiplying `q14` in the verifier. -/
def lambdas (q : ℕ → R) : Rows R where
  e4 := q 1 ^ 2 + q 1 + q 5 + q 6 + 1
  e3 := q 1 + q 2 + q 5 + q 6
  e2 := q 1 * q 2 + q 1 * q 5 + q 1 * q 6 + q 2 + q 6
  e1 := q 1 * q 2 + q 2 ^ 2 + q 2 * q 5 + q 2 * q 6 + q 6

/-- Strip a known correction independently in each row. -/
def rowTranslation (h : Rows R) : Rows R ≃ Rows R where
  toFun e := ⟨e.e4 + h.e4, e.e3 + h.e3, e.e2 + h.e2, e.e1 + h.e1⟩
  invFun e := ⟨e.e4 + h.e4, e.e3 + h.e3, e.e2 + h.e2, e.e1 + h.e1⟩
  left_inv e := rows_ext (CharTwo.add_cancel_right e.e4 h.e4)
    (CharTwo.add_cancel_right e.e3 h.e3) (CharTwo.add_cancel_right e.e2 h.e2)
    (CharTwo.add_cancel_right e.e1 h.e1)
  right_inv e := rows_ext (CharTwo.add_cancel_right e.e4 h.e4)
    (CharTwo.add_cancel_right e.e3 h.e3) (CharTwo.add_cancel_right e.e2 h.e2)
    (CharTwo.add_cancel_right e.e1 h.e1)

/-- The baseline `kappa` remains named, even if its defining polynomial is large. -/
def correction (q14 : R) (lam kappa : Rows R) : Rows R :=
  ⟨lam.e4 * q14 + kappa.e4, lam.e3 * q14 + kappa.e3,
    lam.e2 * q14 + kappa.e2, lam.e1 * q14 + kappa.e1⟩

/-- The inverse first strips the known row corrections, then runs the block
solve. Neither stage expands the prefix or the baseline. -/
def correctedBlockEquiv (q : ℕ → R) (kappa : Rows R) : Keys R ≃ Rows R :=
  (blockEquiv (parameters q)).trans (rowTranslation (correction (q 14) (lambdas q) kappa))

end FastPoly.Char2Degree23Terminal
