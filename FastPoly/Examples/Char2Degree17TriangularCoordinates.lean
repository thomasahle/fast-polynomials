import FastPoly.Examples.Char2Degree17GateCoordinates

/-!
# The supplied S/R/E coordinate change for degree seventeen

The three self-inverse translations and the permutation are written in
both directions. These are key coordinates, not output coefficient identities.
-/

namespace FastPoly.Char2Degree17TriangularCoordinates

set_option maxHeartbeats 20000

open Char2Degree17Wires

variable {R : Type*} [CommRing R] [CharP R 2]

/-- From decoder order `(Q1,Q2,S,R,Q0,E,Q14,Q6,Q5,Q15,Q8,Q9,Q12,Q13,Q10,Q11,Q16)`
back to the internal gate coordinates Q0,...,Q16. -/
def qOfZ (z : Vector R) (i : Fin 17) : R :=
  match i.val with
  | 0 => z 4
  | 1 => z 0
  | 2 => z 1
  | 3 => z 2 + z 4
  | 4 => z 5 + (z 8 ^ 2 + z 8)
  | 5 => z 8
  | 6 => z 7
  | 7 => z 3 + z 8
  | 8 => z 10
  | 9 => z 11
  | 10 => z 14
  | 11 => z 15
  | 12 => z 12
  | 13 => z 13
  | 14 => z 6
  | 15 => z 9
  | _ => z 16

/-- The forward translations, grouped around the same named correction. -/
def zOfQ (q : Vector R) (i : Fin 17) : R :=
  match i.val with
  | 0 => q 1
  | 1 => q 2
  | 2 => q 3 + q 0
  | 3 => q 7 + q 5
  | 4 => q 0
  | 5 => q 4 + (q 5 ^ 2 + q 5)
  | 6 => q 14
  | 7 => q 6
  | 8 => q 5
  | 9 => q 15
  | 10 => q 8
  | 11 => q 9
  | 12 => q 12
  | 13 => q 13
  | 14 => q 10
  | 15 => q 11
  | _ => q 16

theorem zOfQ_qOfZ (z : Vector R) : zOfQ (qOfZ z) = z := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem qOfZ_zOfQ (q : Vector R) : qOfZ (zOfQ q) = q := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def triangularCoordinates : Vector R ≃ Vector R where
  toFun := zOfQ
  invFun := qOfZ
  left_inv := qOfZ_zOfQ
  right_inv := zOfQ_qOfZ

/-- The complete raw-offset to decoder-coordinate change, with the composed
supplied inverse. Output-coefficient pivots are not claimed by this equivalence. -/
noncomputable def rawEquiv [Nontrivial R] : Vector R ≃ Vector R :=
  Char2Degree17GateCoordinates.coordinateEquiv.trans triangularCoordinates

end FastPoly.Char2Degree17TriangularCoordinates
