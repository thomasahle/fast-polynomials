import FastPoly.Examples.Char2Degree25MiddleKeys

/-! Small scalar formulas from the existing middle-coordinate substitutions.
These identities expose the four remaining directions without opening any
polynomial gate or expanding a later coefficient correction. -/
namespace FastPoly.Char2Degree25LateScalars

open Char2Degree25MiddleCoordinates Char2Degree25PrefixCoordinates
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2]

def K (q : Fin 25 → R) : R := q 4 + q 5 + q 7
def l (q : Fin 25 → R) (d : R) : R := d * (K q + d)
def k (q : Fin 25 → R) (d : R) : R := l q d + (B q + 1) * d
def c (q : Fin 25 → R) (d : R) : R := B q * (B q + 1) * d

private theorem group_inner (a b c d e t : R) :
    a + c + d + b + e + t + 1 = (a + b) + (c + d + e) + t + 1 := by ring

theorem tail11_grouped (q : Fin 25 → R) :
    tail11 q = B q * q 21 + q 20 * (B q + K q + q 20 + 1) + q 22 := by
  unfold tail11
  rw [group_inner]
  rfl

private theorem expand13 (o b e t k f : R) :
    o + (b * e + t * (b + k + t + 1) + f) =
      o + b * e + (b + k + 1) * t + t ^ 2 + f := by ring
private theorem expand8 (o k t f e : R) :
    o + (t * (k + t) + f + e) = o + k * t + t ^ 2 + f + e := by ring
private theorem cancel9 (o b k t i f e : R) :
    o + (b * (t * (k + t) + i + f) + f) +
      b * (b * e + t * (b + k + t + 1) + f) =
      o + b * i + b * (b + 1) * t + b * b * e + f := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem a13_eq (q : Fin 25 → R) : a13 q =
    q 11 + B q * q 21 + (B q + K q + 1) * q 20 + (q 20)^2 + q 22 := by
  rw [a13, tail11_grouped]
  exact expand13 _ _ _ _ _ _
theorem a8_eq (q : Fin 25 → R) : a8 q =
    q 12 + K q * q 20 + (q 20)^2 + q 22 + q 21 :=
  expand8 _ _ _ _ _
theorem a9_eq (q : Fin 25 → R) : a9 q =
    q 10 + B q * q 11 + B q * (B q + 1) * q 20 + B q * B q * q 21 + q 22 := by
  rw [a9, tail11_grouped]
  exact cancel9 _ _ _ _ _ _ _

private theorem delta13 (o b e t k f d : R) :
    o + b * e + (b + k + 1) * (t + d) + (t + d)^2 + f =
      (o + b * e + (b + k + 1) * t + t^2 + f) +
        (d * (k + d) + (b + 1) * d) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]
private theorem delta8 (o k t f e d : R) :
    o + k * (t + d) + (t + d)^2 + f + e =
      (o + k * t + t^2 + f + e) + d * (k + d) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]
private theorem delta9 (o b i t e f d : R) :
    o + b * i + b * (b + 1) * (t + d) + b * b * e + f =
      (o + b * i + b * (b + 1) * t + b * b * e + f) + b * (b + 1) * d := by ring

theorem a13_increment20 (q : Fin 25 → R) (d : R) :
    a13 (increment q 20 d) = a13 q + k q d := by
  rw [a13_eq, a13_eq]
  exact delta13 _ _ _ _ _ _ _
theorem a8_increment20 (q : Fin 25 → R) (d : R) :
    a8 (increment q 20 d) = a8 q + l q d := by
  rw [a8_eq, a8_eq]
  exact delta8 _ _ _ _ _ _
theorem a9_increment20 (q : Fin 25 → R) (d : R) :
    a9 (increment q 20 d) = a9 q + c q d := by
  rw [a9_eq, a9_eq]
  exact delta9 _ _ _ _ _ _ _
theorem a7_increment20 (q : Fin 25 → R) (d : R) :
    a7 (increment q 20 d) = a7 q + k q d := by
  rw [a7, a13_increment20]
  change q 9 + (a13 q + k q d) + q 12 = _
  simp only [a7, add_assoc, add_comm, add_left_comm]

private theorem middle_linear (o b e t k f d : R) :
    o + b * (e + d) + (b + k + 1) * t + t^2 + f =
      (o + b * e + (b + k + 1) * t + t^2 + f) + b * d := by ring
private theorem last_linear (o b i t e f d : R) :
    o + b * i + b * (b + 1) * t + b * b * (e + d) + f =
      (o + b * i + b * (b + 1) * t + b * b * e + f) + b * b * d := by ring

theorem a13_increment21 (q : Fin 25 → R) (d : R) :
    a13 (increment q 21 d) = a13 q + B q * d := by
  rw [a13_eq, a13_eq]
  exact middle_linear _ _ _ _ _ _ _
theorem a8_increment21 (q : Fin 25 → R) (d : R) :
    a8 (increment q 21 d) = a8 q + d := by
  rw [a8_eq, a8_eq]
  exact (add_assoc _ _ _).symm
theorem a9_increment21 (q : Fin 25 → R) (d : R) :
    a9 (increment q 21 d) = a9 q + B q * B q * d := by
  rw [a9_eq, a9_eq]
  exact last_linear _ _ _ _ _ _ _
theorem a7_increment21 (q : Fin 25 → R) (d : R) :
    a7 (increment q 21 d) = a7 q + B q * d := by
  rw [a7, a13_increment21]
  change q 9 + (a13 q + B q * d) + q 12 = _
  simp only [a7, add_assoc, add_comm, add_left_comm]

theorem a13_increment22 (q : Fin 25 → R) (d : R) :
    a13 (increment q 22 d) = a13 q + d := by
  rw [a13_eq, a13_eq]
  exact (add_assoc _ _ _).symm
theorem a8_increment22 (q : Fin 25 → R) (d : R) :
    a8 (increment q 22 d) = a8 q + d := by
  rw [a8_eq, a8_eq]
  change (q 12 + K q * q 20 + (q 20)^2) + (q 22 + d) + q 21 = _
  simp only [add_assoc, add_comm, add_left_comm]
theorem a9_increment22 (q : Fin 25 → R) (d : R) :
    a9 (increment q 22 d) = a9 q + d := by
  rw [a9_eq, a9_eq]
  exact (add_assoc _ _ _).symm
theorem a7_increment22 (q : Fin 25 → R) (d : R) :
    a7 (increment q 22 d) = a7 q + d := by
  rw [a7, a13_increment22]
  change q 9 + (a13 q + d) + q 12 = _
  simp only [a7, add_assoc, add_comm, add_left_comm]

end FastPoly.Char2Degree25LateScalars
