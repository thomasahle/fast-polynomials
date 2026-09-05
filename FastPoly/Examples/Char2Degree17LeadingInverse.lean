import FastPoly.Examples.Char2Degree17RRow
import FastPoly.Examples.Char2Frobenius

/-!
# The supplied leading four-row inverse for degree seventeen

The order is rows 16,15,13,14, corresponding to Q1,Q2,S,R. The S row has
the supplied Frobenius square pivot. The actual row-fourteen R change
preserves row thirteen, even though that row has already been decoded.
Both compositions of this four-coordinate inverse are checked explicitly.
-/

namespace FastPoly.Char2Degree17LeadingInverse

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17TriangularCoordinates
open Char2Degree17TerminalFrame Char2Degree17TerminalPivots Char2Degree17HighSignature
open Char2Degree17RRow

variable {R : Type*} [CommRing R] [CharP R 2]

def squareTail (a b : R) : R := (b + a) ^ 2 + (a + 1) ^ 2 * (b + 1) + 1

def rTail (a b s : R) : R :=
  1 + (s + (b + a)) * a + (a + 1) * (b + 1) + (a + 1) ^ 2 * a

theorem normalized_A5 (z : Vector R) :
    ((qOfZ z 0 + qOfZ z 2) + (qOfZ z 1 + qOfZ z 3)) = z 2 + (z 1 + z 0) := by
  change (z 4 + z 1) + (z 0 + (z 2 + z 4)) = _
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem normalize_R (a b s r t : R) :
    (1 + (r + t)) + (t + (s + (b + a)) * a + (a + 1) * (b + 1)) +
      (a + 1) ^ 2 * a = r + rTail a b s := by
  simp only [rTail, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero]

section Nontrivial

variable [Nontrivial R]

theorem outputZ_row16 (z : Vector R) : (outputZ z).coeff 16 = z 0 :=
  outputQ_row16 (qOfZ z)

theorem outputZ_row15 (z : Vector R) : (outputZ z).coeff 15 = z 1 + z 0 ^ 2 := by
  change (outputQ (qOfZ z)).coeff 15 = _
  rw [outputQ_row15]
  change (z 0 + 1) ^ 2 + (z 1 + 1) = z 1 + z 0 ^ 2
  rw [CharTwo.add_sq, one_pow]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem outputZ_row13 (z : Vector R) :
    (outputZ z).coeff 13 = z 2 ^ 2 + squareTail (z 0) (z 1) := by
  change (outputQ (qOfZ z)).coeff 13 = _
  rw [outputQ_row13, normalized_A5]
  change (z 2 + (z 1 + z 0)) ^ 2 + (z 0 + 1) ^ 2 * (z 1 + 1) + 1 = _
  rw [CharTwo.add_sq]
  simp only [squareTail, add_assoc]

theorem outputZ_row14 (z : Vector R) :
    (outputZ z).coeff 14 = z 3 + rTail (z 0) (z 1) (z 2) := by
  change (outputQ (qOfZ z)).coeff 14 = _
  rw [outputQ_row14, normalized_A5]
  change (1 + (z 3 + z 8)) +
    (z 8 + (z 2 + (z 1 + z 0)) * z 0 + (z 0 + 1) * (z 1 + 1)) +
      (z 0 + 1) ^ 2 * z 0 = _
  exact normalize_R (z 0) (z 1) (z 2) (z 3) (z 8)

end Nontrivial

abbrev Head (R : Type*) := Fin 4 → R

def headInput (z : Vector R) : Head R := fun i => z ⟨i.val, by omega⟩

def headEncode (q : Head R) (i : Fin 4) : R :=
  match i.val with
  | 0 => q 0
  | 1 => q 1 + q 0 ^ 2
  | 2 => q 2 ^ 2 + squareTail (q 0) (q 1)
  | _ => q 3 + rTail (q 0) (q 1) (q 2)

def headRow (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 16
  | 1 => 15
  | 2 => 13
  | _ => 14

noncomputable def headRows (z : Vector R) : Head R := fun i => (outputZ z).coeff (headRow i)

theorem actual_head [Nontrivial R] (z : Vector R) : headRows z = headEncode (headInput z) := by
  funext i
  fin_cases i
  · exact outputZ_row16 z
  · exact outputZ_row15 z
  · exact outputZ_row13 z
  · exact outputZ_row14 z

theorem headRows_congr [Nontrivial R] (z w : Vector R) (i : Fin 4)
    (he : ∀ k : Fin 17, k.val ≤ i.val → z k = w k) : headRows z i = headRows w i := by
  fin_cases i
  · change (∀ k : Fin 17, k.val ≤ 0 → z k = w k) at he
    change (outputZ z).coeff 16 = (outputZ w).coeff 16
    rw [outputZ_row16, outputZ_row16, he 0 (by omega)]
  · change (∀ k : Fin 17, k.val ≤ 1 → z k = w k) at he
    change (outputZ z).coeff 15 = (outputZ w).coeff 15
    rw [outputZ_row15, outputZ_row15, he 0 (by omega), he 1 (by omega)]
  · change (∀ k : Fin 17, k.val ≤ 2 → z k = w k) at he
    change (outputZ z).coeff 13 = (outputZ w).coeff 13
    rw [outputZ_row13, outputZ_row13, he 0 (by omega), he 1 (by omega), he 2 (by omega)]
  · change (∀ k : Fin 17, k.val ≤ 3 → z k = w k) at he
    change (outputZ z).coeff 14 = (outputZ w).coeff 14
    rw [outputZ_row14, outputZ_row14, he 0 (by omega), he 1 (by omega),
      he 2 (by omega), he 3 (by omega)]

theorem headRows_shift_future [Nontrivial R] (z : Vector R) (i : Fin 4) (j : Fin 17)
    (δ : R) (hij : i.val < j.val) : headRows (shift z j δ) i = headRows z i := by
  apply headRows_congr
  intro k hk
  have hkj : k ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    omega
  exact shift_other z j k δ hkj

/-- Crucial for the swapped row order: the later R pivot leaves the S row intact. -/
theorem R_preserves_row13 [Nontrivial R] (z : Vector R) (δ : R) :
    (outputZ (shift z 3 δ)).coeff 13 = (outputZ z).coeff 13 :=
  headRows_shift_future z 2 3 δ (by omega)

section ExplicitInverse

variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

def readQ2 (c : Head F) : F := c 1 + c 0 ^ 2

noncomputable def readS (c : Head F) : F :=
  (Char2Certificate.frobeniusPivot 1).symm (c 2 + squareTail (c 0) (readQ2 c))

noncomputable def readR (c : Head F) : F := c 3 + rTail (c 0) (readQ2 c) (readS c)

noncomputable def headDecode (c : Head F) (i : Fin 4) : F :=
  match i.val with
  | 0 => c 0
  | 1 => readQ2 c
  | 2 => readS c
  | _ => readR c

theorem readQ2_encode (q : Head F) : readQ2 (headEncode q) = q 1 :=
  CharTwo.add_cancel_right _ _

theorem readS_encode (q : Head F) : readS (headEncode q) = q 2 := by
  rw [readS, readQ2_encode]
  change (Char2Certificate.frobeniusPivot 1).symm
    ((q 2 ^ 2 + squareTail (q 0) (q 1)) + squareTail (q 0) (q 1)) = q 2
  rw [CharTwo.add_cancel_right]
  exact (Char2Certificate.frobeniusPivot 1).symm_apply_apply (q 2)

theorem readR_encode (q : Head F) : readR (headEncode q) = q 3 := by
  rw [readR, readQ2_encode, readS_encode]
  exact CharTwo.add_cancel_right _ _

theorem headDecode_encode (q : Head F) : headDecode (headEncode q) = q := by
  funext i
  fin_cases i
  · rfl
  · exact readQ2_encode q
  · exact readS_encode q
  · exact readR_encode q

theorem readS_squared (c : Head F) : readS c ^ 2 = c 2 + squareTail (c 0) (readQ2 c) :=
  (Char2Certificate.frobeniusPivot 1).apply_symm_apply _

theorem headEncode_decode (c : Head F) : headEncode (headDecode c) = c := by
  funext i
  fin_cases i
  · rfl
  · exact CharTwo.add_cancel_right _ _
  · change readS c ^ 2 + squareTail (c 0) (readQ2 c) = c 2
    rw [readS_squared, CharTwo.add_cancel_right]
  · exact CharTwo.add_cancel_right _ _

noncomputable def headEquiv : Head F ≃ Head F where
  toFun := headEncode
  invFun := headDecode
  left_inv := headDecode_encode
  right_inv := headEncode_decode

/-- The displayed inverse decodes the actual circuit's four leading rows. -/
theorem decode_actual_head (z : Vector F) : headDecode (headRows z) = headInput z := by
  rw [actual_head, headDecode_encode]

end ExplicitInverse

end FastPoly.Char2Degree17LeadingInverse
