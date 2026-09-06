import FastPoly.Examples.Char2PaperDegree11HeadInverse
import FastPoly.Examples.Char2PaperDegree11Tail
import FastPoly.Examples.Char2PaperDegree11TailInverse
import Mathlib.Tactic.FinCases

/-! Explicit raw-key coordinates for the retained paper degree-eleven
decoder. The six head quantities, the a6 baseline pivot, and four low
keys give a displayed two-sided coordinate change; no circuit is expanded. -/
namespace FastPoly.Char2PaperDegree11Coordinates

set_option maxHeartbeats 20000
variable {F : Type*} [CommRing F] [CharP F 2]

@[ext] structure Coordinates (F : Type*) where
  head : Char2PaperDegree11HeadInverse.Head F
  a6 : F
  low : Char2PaperDegree11TailInverse.Keys F

def rawInput (a : Fin 11 → F) : Coordinates F where
  head := ⟨a 0, a 3, a 4, a 5 + a 7 + a 8, a 1 + a 2, a 1⟩
  a6 := a 6
  low := ⟨a 5, a 7, a 9, a 10⟩

def keys (p : Coordinates F) : ℕ → F
  | 0 => p.head.a0
  | 1 => p.head.a1
  | 2 => p.head.s + p.head.a1
  | 3 => p.head.a3
  | 4 => p.head.a4
  | 5 => p.low.a5
  | 6 => p.a6
  | 7 => p.low.a7
  | 8 => p.head.h + p.low.a5 + p.low.a7
  | 9 => p.low.a9
  | 10 => p.low.a10
  | _ => 0

def rawKeys (p : Coordinates F) (i : Fin 11) : F := keys p i.val

theorem rawInput_rawKeys (p : Coordinates F) : rawInput (rawKeys p) = p := by
  apply Coordinates.ext
  · apply Char2PaperDegree11HeadInverse.Head.ext <;> first
      | rfl
      | simp only [rawInput, rawKeys, keys, add_assoc, add_comm, add_left_comm,
          CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]
  · rfl
  · rfl

theorem rawKeys_rawInput (a : Fin 11 → F) : rawKeys (rawInput a) = a := by
  funext i
  fin_cases i <;> first
    | rfl
    | simp only [rawInput, rawKeys, keys, add_assoc, add_comm, add_left_comm,
        CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add] <;> rfl

def rawEquiv : (Fin 11 → F) ≃ Coordinates F where
  toFun := rawInput
  invFun := rawKeys
  left_inv := rawKeys_rawInput
  right_inv := rawInput_rawKeys

theorem h_keys (p : Coordinates F) : Char2PaperDegree11.h (keys p) = p.head.h := by
  simp only [Char2PaperDegree11.h, keys, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem sumKeys_keys (p : Coordinates F) : Char2PaperDegree11.sumKeys (keys p) = p.head.s := by
  simp only [Char2PaperDegree11.sumKeys, keys, add_assoc, add_comm, add_left_comm,
    CharTwo.add_cancel_left, CharTwo.add_self_eq_zero, add_zero, zero_add]

/-- Exactly the supplied baseline, parameterized by the recovered head and a6. -/
def baseKeys (p : Char2PaperDegree11HeadInverse.Head F) (a6 : F) : ℕ → F
  | 0 => p.a0
  | 1 => p.a1
  | 2 => p.s + p.a1
  | 3 => p.a3
  | 4 => p.a4
  | 6 => a6
  | 8 => p.h
  | _ => 0

theorem baselineKeys_eq (p : Coordinates F) :
    Char2PaperDegree11.baselineKeys (keys p) = baseKeys p.head p.a6 := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first
    | rfl
    | exact h_keys p

theorem baseline0Keys_eq (p : Coordinates F) :
    Char2PaperDegree11.baseline0Keys (keys p) = baseKeys p.head 0 := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first
    | rfl
    | exact h_keys p

def lowCtx (p : Coordinates F) : Char2PaperDegree11TailInverse.Context F where
  a0 := p.head.a0
  a3 := p.head.a3
  a4 := p.head.a4
  a6 := p.a6
  h := p.head.h

end FastPoly.Char2PaperDegree11Coordinates
