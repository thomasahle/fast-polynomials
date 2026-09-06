import FastPoly.Examples.Char2Degree25LateScalars
import FastPoly.Examples.Char2Degree25TwentyWires
import FastPoly.Examples.Char2Degree25TwentyOneWires
import FastPoly.Examples.Char2Degree25TwentyTwoBounds

/-! The four remaining literal Middle-coordinate changes, identified with
their supplied raw gate-offset changes by the small scalar formulas. -/
namespace FastPoly.Char2Degree25LateKeys

open Char2Degree25MiddleCoordinates Char2Degree25MiddleKeys
  Char2Degree25LateScalars Char2Degree25PrefixCoordinates
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem K_factored (q : Fin 25 → R) :
    Char2Degree25TwentyWires.K (factoredKeys q) = K q := by
  change (K q + q 20) + q 20 = K q
  exact CharTwo.add_cancel_right _ _
theorem B_factored (q : Fin 25 → R) :
    Char2Degree25TwentyWires.B (factoredKeys q) = B q := rfl
theorem B13_factored (q : Fin 25 → R) :
    Char2Degree25RowThirteen.B (factoredKeys q) = B q := rfl
theorem l_factored (q : Fin 25 → R) (d : R) :
    Char2Degree25TwentyWires.l (factoredKeys q) d = l q d := by
  rw [Char2Degree25TwentyWires.l, K_factored]
  rfl
theorem k_factored (q : Fin 25 → R) (d : R) :
    Char2Degree25TwentyWires.k (factoredKeys q) d = k q d := by
  rw [Char2Degree25TwentyWires.k, l_factored, B_factored]
  rfl
theorem c_factored (q : Fin 25 → R) (d : R) :
    Char2Degree25TwentyWires.c (factoredKeys q) d = c q d := by
  rw [Char2Degree25TwentyWires.c, B_factored]
  rfl

theorem keys_increment20 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 20 d) =
      Char2Degree25TwentyWires.shift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  unfold Char2Degree25TwentyWires.shift
  simp only [l_factored, k_factored, c_factored]
  funext i
  by_cases hi : i < 25
  · interval_cases i
    all_goals first
      | rfl
      | exact (add_assoc (K q) (q 20) d).symm
      | exact a7_increment20 q d
      | exact a8_increment20 q d
      | exact a9_increment20 q d
      | exact a13_increment20 q d
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_increment21 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 21 d) =
      Char2Degree25TwentyOneWires.shift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  unfold Char2Degree25TwentyOneWires.shift
  simp only [B13_factored]
  funext i
  by_cases hi : i < 25
  · interval_cases i
    all_goals first
      | rfl
      | exact a7_increment21 q d
      | exact a8_increment21 q d
      | exact a9_increment21 q d
      | exact a13_increment21 q d
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_increment22 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 22 d) =
      Char2Degree25TwentyTwoWires.shift (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i
    all_goals first
      | rfl
      | exact a7_increment22 q d
      | exact a8_increment22 q d
      | exact a9_increment22 q d
      | exact a13_increment22 q d
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem keys_increment23 (q : Fin 25 → R) (d : R) :
    Char2Degree25MiddleCoordinates.keys (increment q 23 d) =
      Char2Degree25TwentyTwoBounds.shift23 (Char2Degree25MiddleCoordinates.keys q) d := by
  rw [keys_formula, keys_formula]
  funext i
  by_cases hi : i < 25
  · interval_cases i <;> rfl
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

end FastPoly.Char2Degree25LateKeys
