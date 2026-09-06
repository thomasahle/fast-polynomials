import FastPoly.Examples.Char2Degree25TailCoordinates
import FastPoly.Examples.Char2Degree25LateKeys
import FastPoly.Examples.Char2Degree25TwentyOneBounds
import FastPoly.Examples.Char2Degree25TwentyBounds
import FastPoly.Examples.Char2CoefficientDegreePeel

/-! Seven literal coefficient corrections lower a supplied degree-eleven
late-coordinate difference to degree four. This is the existing descending
decoder, with each correction retained as a named circuit coefficient. -/
namespace FastPoly.Char2Degree25LatePeel

open Polynomial Char2CoefficientShearTransport
open Char2Degree25LowerCoordinates (Vector before13 before14 before15)
open Char2Degree25TailCoordinates (before16 before17 before18 before19 output)
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

-- Keep recursive circuit families opaque to degree-bound unification.
-- Each transition below opens only its explicitly named branch equation.
attribute [local irreducible] before13 before14 before15 before16 before17 before18 before19 output

theorem peel13 (i : Fin 25) (hi : (13 : Fin 25) < i)
    (h : ∀ (q : Vector R) (d : R), (before13 (increment q i d) + before13 q).natDegree ≤ 11)
    (q : Vector R) (d : R) : (before14 (increment q i d) + before14 q).natDegree ≤ 10 := by
  simp only [before14, Char2Degree25LowerCoordinates.step13]
  exact Char2CoefficientDegreePeel.degree_after (before13 (R := R)) 13 i 11 hi
    Char2Degree25LowerCoordinates.unit13_before h q d

theorem peel14 (i : Fin 25) (hi : (14 : Fin 25) < i)
    (h : ∀ (q : Vector R) (d : R), (before14 (increment q i d) + before14 q).natDegree ≤ 10)
    (q : Vector R) (d : R) : (before15 (increment q i d) + before15 q).natDegree ≤ 9 := by
  simp only [before15, Char2Degree25LowerCoordinates.step14]
  exact Char2CoefficientDegreePeel.degree_after (before14 (R := R)) 14 i 10 hi
    Char2Degree25LowerCoordinates.unit14_after13 h q d

theorem peel15 (i : Fin 25) (hi : (15 : Fin 25) < i)
    (h : ∀ (q : Vector R) (d : R), (before15 (increment q i d) + before15 q).natDegree ≤ 9)
    (q : Vector R) (d : R) : (before16 (increment q i d) + before16 q).natDegree ≤ 8 := by
  simp only [before16, Char2Degree25LowerCoordinates.output, Char2Degree25LowerCoordinates.step15]
  exact Char2CoefficientDegreePeel.degree_after (before15 (R := R)) 15 i 9 hi
    Char2Degree25LowerCoordinates.unit15_after14 h q d

theorem peel16 (i : Fin 25) (hi : (16 : Fin 25) < i)
    (h : ∀ (q : Vector R) (d : R), (before16 (increment q i d) + before16 q).natDegree ≤ 8)
    (q : Vector R) (d : R) : (before17 (increment q i d) + before17 q).natDegree ≤ 7 := by
  simp only [before17, Char2Degree25TailCoordinates.step16]
  exact Char2CoefficientDegreePeel.degree_after (before16 (R := R)) 16 i 8 hi
    Char2Degree25TailCoordinates.unit16_before h q d

theorem peel17 (i : Fin 25) (hi : (17 : Fin 25) < i)
    (h : ∀ (q : Vector R) (d : R), (before17 (increment q i d) + before17 q).natDegree ≤ 7)
    (q : Vector R) (d : R) : (before18 (increment q i d) + before18 q).natDegree ≤ 6 := by
  simp only [before18, Char2Degree25TailCoordinates.step17]
  exact Char2CoefficientDegreePeel.degree_after (before17 (R := R)) 17 i 7 hi
    Char2Degree25TailCoordinates.unit17_before h q d

theorem peel18 (i : Fin 25) (hi : (18 : Fin 25) < i)
    (h : ∀ (q : Vector R) (d : R), (before18 (increment q i d) + before18 q).natDegree ≤ 6)
    (q : Vector R) (d : R) : (before19 (increment q i d) + before19 q).natDegree ≤ 5 := by
  simp only [before19, Char2Degree25TailCoordinates.step18]
  exact Char2CoefficientDegreePeel.degree_after (before18 (R := R)) 18 i 6 hi
    Char2Degree25TailCoordinates.unit18_before h q d

theorem peel19 (i : Fin 25) (hi : (19 : Fin 25) < i)
    (h : ∀ (q : Vector R) (d : R), (before19 (increment q i d) + before19 q).natDegree ≤ 5)
    (q : Vector R) (d : R) : (output (increment q i d) + output q).natDegree ≤ 4 := by
  simp only [output, Char2Degree25TailCoordinates.step19]
  exact Char2CoefficientDegreePeel.degree_after (before19 (R := R)) 19 i 5 hi
    Char2Degree25TailCoordinates.unit19_before h q d

theorem degree_through19 (i : Fin 25) (hi : (19 : Fin 25) < i)
    (h11 : ∀ (q : Vector R) (d : R), (before13 (increment q i d) + before13 q).natDegree ≤ 11)
    (q : Vector R) (d : R) : (output (increment q i d) + output q).natDegree ≤ 4 :=
  peel19 i hi (peel18 i (by omega) (peel17 i (by omega)
    (peel16 i (by omega) (peel15 i (by omega) (peel14 i (by omega)
      (peel13 i (by omega) h11)))))) q d

theorem middle_degree20 (q : Vector R) (d : R) :
    (before13 (increment q 20 d) + before13 q).natDegree ≤ 11 := by
  have h := Char2Degree25TwentyBounds.output_difference_degree
    (Char2Degree25MiddleCoordinates.keys q) d
  rw [← Char2Degree25LateKeys.keys_increment20 q d] at h
  simpa only [before13] using h

theorem middle_degree21 (q : Vector R) (d : R) :
    (before13 (increment q 21 d) + before13 q).natDegree ≤ 11 := by
  have h := Char2Degree25TwentyOneBounds.output_difference_degree
    (Char2Degree25MiddleCoordinates.keys q) d
  rw [← Char2Degree25LateKeys.keys_increment21 q d] at h
  simpa only [before13] using h
theorem middle_degree22 (q : Vector R) (d : R) :
    (before13 (increment q 22 d) + before13 q).natDegree ≤ 11 := by
  have h := Char2Degree25TwentyTwoBounds.output_difference_degree
    (Char2Degree25MiddleCoordinates.keys q) d
  rw [← Char2Degree25LateKeys.keys_increment22 q d] at h
  simpa only [before13] using h
theorem middle_degree23 (q : Vector R) (d : R) :
    (before13 (increment q 23 d) + before13 q).natDegree ≤ 11 := by
  have h := Char2Degree25TwentyTwoBounds.output_difference_degree23
    (Char2Degree25MiddleCoordinates.keys q) d
  rw [← Char2Degree25LateKeys.keys_increment23 q d] at h
  simpa only [before13] using h

theorem degree20 (q : Vector R) (d : R) :
    (output (increment q 20 d) + output q).natDegree ≤ 4 :=
  degree_through19 20 (by omega) middle_degree20 q d

theorem degree21 (q : Vector R) (d : R) :
    (output (increment q 21 d) + output q).natDegree ≤ 4 :=
  degree_through19 21 (by omega) middle_degree21 q d
theorem degree22 (q : Vector R) (d : R) :
    (output (increment q 22 d) + output q).natDegree ≤ 4 :=
  degree_through19 22 (by omega) middle_degree22 q d
theorem degree23 (q : Vector R) (d : R) :
    (output (increment q 23 d) + output q).natDegree ≤ 4 :=
  degree_through19 23 (by omega) middle_degree23 q d

end FastPoly.Char2Degree25LatePeel
