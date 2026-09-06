import FastPoly.Examples.Char2Degree25TailCoordinates

/-! Exact raw-slot preservation for the seven actual coefficient shears
13 through 19. Their coefficient corrections stay opaque. In the raw
circuit only slots 10/11/15/17/19/21/22 can change; in particular the
quintic modulus and every head input except a17 are preserved. -/
namespace FastPoly.Char2Degree25TailSlots

open Char2Degree25MiddleCoordinates Char2Degree25MiddleKeys
  Char2CoefficientShear
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def middleInput (q : Fin 25 → R) : Fin 25 → R :=
  Char2Degree25LowerCoordinates.lowerEquiv (Char2Degree25TailCoordinates.tailEquiv q)

theorem keys_eq_middleInput (q : Fin 25 → R) :
    Char2Degree25TailCoordinates.keys q = Char2Degree25MiddleCoordinates.keys (middleInput q) := rfl

theorem middleInput_other (q : Fin 25 → R) (i : Fin 25)
    (hi : i.val < 13 ∨ 19 < i.val) : middleInput q i = q i := by
  have h13 : i ≠ 13 := by omega
  have h14 : i ≠ 14 := by omega
  have h15 : i ≠ 15 := by omega
  have h16 : i ≠ 16 := by omega
  have h17 : i ≠ 17 := by omega
  have h18 : i ≠ 18 := by omega
  have h19 : i ≠ 19 := by omega
  simp only [middleInput, Char2Degree25LowerCoordinates.lowerEquiv,
    Char2Degree25TailCoordinates.tailEquiv, Equiv.trans_apply,
    Char2Degree25LowerCoordinates.step13, Char2Degree25LowerCoordinates.step14,
    Char2Degree25LowerCoordinates.step15, Char2Degree25TailCoordinates.step16,
    Char2Degree25TailCoordinates.step17, Char2Degree25TailCoordinates.step18,
    Char2Degree25TailCoordinates.step19, coordinateShear_apply,
    Function.update_of_ne h13, Function.update_of_ne h14, Function.update_of_ne h15,
    Function.update_of_ne h16, Function.update_of_ne h17, Function.update_of_ne h18,
    Function.update_of_ne h19]

theorem a13_middleInput (q : Fin 25 → R) : a13 (middleInput q) = a13 q := by
  have h0 := middleInput_other q 0 (by omega)
  have h4 := middleInput_other q 4 (by omega)
  have h5 := middleInput_other q 5 (by omega)
  have h6 := middleInput_other q 6 (by omega)
  have h7 := middleInput_other q 7 (by omega)
  have h11 := middleInput_other q 11 (by omega)
  have h20 := middleInput_other q 20 (by omega)
  have h21 := middleInput_other q 21 (by omega)
  have h22 := middleInput_other q 22 (by omega)
  simp only [a13, tail11, B, h0, h4, h5, h6, h7, h11, h20, h21, h22]

theorem a7_middleInput (q : Fin 25 → R) : a7 (middleInput q) = a7 q := by
  have h9 := middleInput_other q 9 (by omega)
  have h12 := middleInput_other q 12 (by omega)
  simp only [a7, a13_middleInput, h9, h12]

theorem a8_middleInput (q : Fin 25 → R) : a8 (middleInput q) = a8 q := by
  have h4 := middleInput_other q 4 (by omega)
  have h5 := middleInput_other q 5 (by omega)
  have h7 := middleInput_other q 7 (by omega)
  have h12 := middleInput_other q 12 (by omega)
  have h20 := middleInput_other q 20 (by omega)
  have h21 := middleInput_other q 21 (by omega)
  have h22 := middleInput_other q 22 (by omega)
  simp only [a8, tail12, shared, h4, h5, h7, h12, h20, h21, h22]

theorem a9_middleInput (q : Fin 25 → R) : a9 (middleInput q) = a9 q := by
  have h0 := middleInput_other q 0 (by omega)
  have h4 := middleInput_other q 4 (by omega)
  have h5 := middleInput_other q 5 (by omega)
  have h6 := middleInput_other q 6 (by omega)
  have h7 := middleInput_other q 7 (by omega)
  have h10 := middleInput_other q 10 (by omega)
  have h11 := middleInput_other q 11 (by omega)
  have h20 := middleInput_other q 20 (by omega)
  have h21 := middleInput_other q 21 (by omega)
  have h22 := middleInput_other q 22 (by omega)
  simp only [a9, tail10, tail11, B, shared, h0, h4, h5, h6, h7, h10, h11, h20, h21, h22]

/-- Only these seven raw slots can be altered by the actual earlier peel. -/
theorem keys_other (q : Fin 25 → R) (i : ℕ)
    (h10 : i ≠ 10) (h11 : i ≠ 11) (h15 : i ≠ 15) (h17 : i ≠ 17)
    (h19 : i ≠ 19) (h21 : i ≠ 21) (h22 : i ≠ 22) :
    Char2Degree25TailCoordinates.keys q i = Char2Degree25MiddleCoordinates.keys q i := by
  have hq0 := middleInput_other q 0 (by omega)
  have hq1 := middleInput_other q 1 (by omega)
  have hq2 := middleInput_other q 2 (by omega)
  have hq3 := middleInput_other q 3 (by omega)
  have hq4 := middleInput_other q 4 (by omega)
  have hq5 := middleInput_other q 5 (by omega)
  have hq6 := middleInput_other q 6 (by omega)
  have hq7 := middleInput_other q 7 (by omega)
  have hq8 := middleInput_other q 8 (by omega)
  have hq20 := middleInput_other q 20 (by omega)
  have hq21 := middleInput_other q 21 (by omega)
  have hq22 := middleInput_other q 22 (by omega)
  have hq23 := middleInput_other q 23 (by omega)
  have hq24 := middleInput_other q 24 (by omega)
  rw [keys_eq_middleInput, keys_formula, keys_formula]
  by_cases hi : i < 25
  · interval_cases i <;> first
      | omega
      | simp only [factoredKeys, a7_middleInput, a8_middleInput, a9_middleInput, a13_middleInput,
          hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq20, hq21, hq22, hq23, hq24]
  · have hn : i = (i - 25) + 25 := by omega
    rw [hn]
    rfl

theorem raw0 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 0 = keys q 0 :=
  keys_other q 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw1 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 1 = keys q 1 :=
  keys_other q 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw2 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 2 = keys q 2 :=
  keys_other q 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw3 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 3 = keys q 3 :=
  keys_other q 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw4 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 4 = keys q 4 :=
  keys_other q 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw5 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 5 = keys q 5 :=
  keys_other q 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw6 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 6 = keys q 6 :=
  keys_other q 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw7 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 7 = keys q 7 :=
  keys_other q 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw8 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 8 = keys q 8 :=
  keys_other q 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw9 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 9 = keys q 9 :=
  keys_other q 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw12 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 12 = keys q 12 :=
  keys_other q 12 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw13 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 13 = keys q 13 :=
  keys_other q 13 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw14 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 14 = keys q 14 :=
  keys_other q 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw16 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 16 = keys q 16 :=
  keys_other q 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw18 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 18 = keys q 18 :=
  keys_other q 18 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw20 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 20 = keys q 20 :=
  keys_other q 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw23 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 23 = keys q 23 :=
  keys_other q 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
theorem raw24 (q : Fin 25 → R) : Char2Degree25TailCoordinates.keys q 24 = keys q 24 :=
  keys_other q 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

end FastPoly.Char2Degree25TailSlots
