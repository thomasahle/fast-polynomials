import FastPoly.Examples.Char2Degree25PrefixPivots
import FastPoly.Examples.Char2Degree25MiddleCoordinates
import FastPoly.Examples.Char2Degree25MiddleFrame

/-! Transport the first nine supplied pivots through the next four coordinate
shears. Their extra raw changes affect only rows at most15, so every earlier
unit column is preserved. This is a checked partial inverse layer, not the
complete degree25 decoder. -/
namespace FastPoly.Char2Degree25HighKeys

open Polynomial Char2Degree25MiddleCoordinates Char2Degree25MiddleFrame
  Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

open Char2Degree25PrefixCoordinates (increment)

theorem prefix_same_fixed {q r : Vector R}
    (he : ∀ j : Fin 25, j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 12 → q j = r j) :
    SameFixed (Char2Degree25PrefixCoordinates.keys q)
      (Char2Degree25PrefixCoordinates.keys r) := by
  have h0 := he 0 (by omega) (by omega) (by omega) (by omega)
  have h1 := he 1 (by omega) (by omega) (by omega) (by omega)
  have h2 := he 2 (by omega) (by omega) (by omega) (by omega)
  have h3 := he 3 (by omega) (by omega) (by omega) (by omega)
  have h4 := he 4 (by omega) (by omega) (by omega) (by omega)
  have h5 := he 5 (by omega) (by omega) (by omega) (by omega)
  have h6 := he 6 (by omega) (by omega) (by omega) (by omega)
  have h7 := he 7 (by omega) (by omega) (by omega) (by omega)
  have h8 := he 8 (by omega) (by omega) (by omega) (by omega)
  have h13 := he 13 (by omega) (by omega) (by omega) (by omega)
  have h14 := he 14 (by omega) (by omega) (by omega) (by omega)
  have h15 := he 15 (by omega) (by omega) (by omega) (by omega)
  have h16 := he 16 (by omega) (by omega) (by omega) (by omega)
  have h17 := he 17 (by omega) (by omega) (by omega) (by omega)
  have h18 := he 18 (by omega) (by omega) (by omega) (by omega)
  have h19 := he 19 (by omega) (by omega) (by omega) (by omega)
  have h20 := he 20 (by omega) (by omega) (by omega) (by omega)
  have h21 := he 21 (by omega) (by omega) (by omega) (by omega)
  have h22 := he 22 (by omega) (by omega) (by omega) (by omega)
  have h23 := he 23 (by omega) (by omega) (by omega) (by omega)
  have h24 := he 24 (by omega) (by omega) (by omega) (by omega)
  constructor <;>
    simp only [Char2Degree25PrefixCoordinates.keys, h0, h1, h2, h3, h4, h5, h6, h7, h8, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]

theorem increment_fixed (q : Vector R) (i : Fin 25) (δ : R) (j : Fin 25)
    (h9 : j ≠ 9) (h10 : j ≠ 10) (h11 : j ≠ 11) (h12 : j ≠ 12) :
    increment (middleEquiv q) i δ j = middleEquiv (increment q i δ) j := by
  rw [middle_other _ j h9 h10 h11 h12]
  by_cases hji : j = i
  · subst j
    change Function.update _ i _ i = Function.update _ i _ i
    rw [Function.update_self, Function.update_self, middle_other q i h9 h10 h11 h12]
  · change Function.update _ i _ j = Function.update _ i _ j
    rw [Function.update_of_ne hji, Function.update_of_ne hji, middle_other q j h9 h10 h11 h12]

theorem increment_slots (q : Vector R) (i : Fin 25) (δ : R) :
    SameFixed (Char2Degree25PrefixCoordinates.keys (increment (middleEquiv q) i δ))
      (keys (increment q i δ)) :=
  prefix_same_fixed (increment_fixed q i δ)

/-- A named low correction cannot change a higher supplied unit pivot. -/
theorem transport {p b c : R[X]} {n : ℕ} {δ : R}
    (hu : UnitDifference p b n δ) (hc : (c + b).natDegree < n) :
    UnitDifference p c n δ := by
  have he : c + p = (b + p) + (c + b) := by
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
      CharTwo.add_self_eq_zero, zero_add, add_zero]
  constructor
  · rw [he]
    exact natDegree_add_le_of_degree_le hu.difference_degree hc.le
  · have hz : (c + b).coeff n = 0 := coeff_eq_zero_of_natDegree_lt hc
    rw [he, coeff_add, hu.pivot, hz, add_zero]

theorem prefix_unit (q : Vector R) (i : Fin 9) (δ : R) :
    UnitDifference (Char2Degree25Frame.output (Char2Degree25PrefixCoordinates.keys q))
      (Char2Degree25Frame.output (Char2Degree25PrefixCoordinates.keys
        (increment q ⟨i.val, by omega⟩ δ))) (24 - i.val) δ := by
  fin_cases i
  · exact Char2Degree25PrefixPivots.increment0_unit q δ
  · exact Char2Degree25PrefixPivots.increment1_unit q δ
  · exact Char2Degree25PrefixPivots.increment2_unit q δ
  · exact Char2Degree25PrefixPivots.increment3_unit q δ
  · exact Char2Degree25PrefixPivots.increment4_unit q δ
  · exact Char2Degree25PrefixPivots.increment5_unit q δ
  · exact Char2Degree25PrefixPivots.increment6_unit q δ
  · exact Char2Degree25PrefixPivots.increment7_unit q δ
  · exact Char2Degree25PrefixPivots.increment8_unit q δ

/-- The nine actual output pivots after all thirteen supplied coordinate steps. -/
theorem increment_high_unit (q : Vector R) (i : Fin 9) (δ : R) :
    UnitDifference (Char2Degree25Frame.output (keys q))
      (Char2Degree25Frame.output (keys (increment q ⟨i.val, by omega⟩ δ)))
      (24 - i.val) δ := by
  have hc := (increment_slots q ⟨i.val, by omega⟩ δ).output_difference_degree
  apply transport (prefix_unit (middleEquiv q) i δ)
  apply hc.trans_lt
  have hi := i.isLt
  omega

end FastPoly.Char2Degree25HighKeys
