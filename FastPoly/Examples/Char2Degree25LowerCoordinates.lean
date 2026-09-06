import FastPoly.Examples.Char2Degree25HighKeys
import FastPoly.Examples.Char2Degree25LowerRawKeys
import FastPoly.Examples.Char2CoefficientShearTransport

/-! Three more steps of the supplied coefficient decoder. Each correction is
the coefficient of the original named circuit with its current pivot zeroed,
minus (in characteristic two, plus) the already-known prefix coefficient.
No expanded correction expression is generated. This is still a partial map. -/
namespace FastPoly.Char2Degree25LowerCoordinates

open Polynomial Char2Degree19InnerTail Char2CoefficientShear
open Char2CoefficientShearTransport (increment)
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

abbrev Vector (R : Type*) := Fin 25 → R
noncomputable def before13 (q : Vector R) : R[X] :=
  Char2Degree25Frame.output (Char2Degree25MiddleCoordinates.keys q)
noncomputable def step13 : Vector R ≃ Vector R := coordinateShear before13 13 11
noncomputable def before14 (q : Vector R) : R[X] := before13 (step13 q)
noncomputable def step14 : Vector R ≃ Vector R := coordinateShear before14 14 10
noncomputable def before15 (q : Vector R) : R[X] := before14 (step14 q)
noncomputable def step15 : Vector R ≃ Vector R := coordinateShear before15 15 9
noncomputable def output (q : Vector R) : R[X] := before15 (step15 q)

noncomputable def lowerEquiv : Vector R ≃ Vector R :=
  (step15.trans step14).trans step13
noncomputable def keyEquiv : Vector R ≃ Vector R :=
  lowerEquiv.trans Char2Degree25MiddleCoordinates.keyEquiv
noncomputable def keys (q : Vector R) : ℕ → R :=
  Char2Degree25MiddleCoordinates.keys (lowerEquiv q)

theorem output_eq (q : Vector R) : output q = Char2Degree25Frame.output (keys q) := rfl
theorem decode_encode (q : Vector R) : keyEquiv.symm (keyEquiv q) = q :=
  keyEquiv.symm_apply_apply q
theorem encode_decode (a : Vector R) : keyEquiv (keyEquiv.symm a) = a :=
  keyEquiv.apply_symm_apply a

theorem unit13_before (q : Vector R) (d : R) :
    UnitDifference (before13 q) (before13 (increment q 13 d)) 11 d :=
  Char2Degree25LowerRawKeys.increment13_unit q d
theorem unit14_before (q : Vector R) (d : R) :
    UnitDifference (before13 q) (before13 (increment q 14 d)) 10 d :=
  Char2Degree25LowerRawKeys.increment14_unit q d
theorem unit15_before (q : Vector R) (d : R) :
    UnitDifference (before13 q) (before13 (increment q 15 d)) 9 d :=
  Char2Degree25LowerRawKeys.increment15_unit q d
theorem unit24_before (q : Vector R) (d : R) :
    UnitDifference (before13 q) (before13 (increment q 24 d)) 0 d :=
  Char2Degree25LowerRawKeys.increment24_unit q d

theorem unit14_after13 (q : Vector R) (d : R) :
    UnitDifference (before14 q) (before14 (increment q 14 d)) 10 d :=
  Char2CoefficientShearTransport.low_unit before13 13 11 14 (by omega) 10 (by omega)
    unit14_before q d
theorem unit15_after13 (q : Vector R) (d : R) :
    UnitDifference (before14 q) (before14 (increment q 15 d)) 9 d :=
  Char2CoefficientShearTransport.low_unit before13 13 11 15 (by omega) 9 (by omega)
    unit15_before q d
theorem unit15_after14 (q : Vector R) (d : R) :
    UnitDifference (before15 q) (before15 (increment q 15 d)) 9 d :=
  Char2CoefficientShearTransport.low_unit before14 14 10 15 (by omega) 9 (by omega)
    unit15_after13 q d

theorem row13 (q : Vector R) : (before14 q).coeff 11 = q 13 + baseline before13 13 11 q :=
  coefficient_normalized before13 13 11 (fun q d => (unit13_before q d).row) q
theorem row14 (q : Vector R) : (before15 q).coeff 10 = q 14 + baseline before14 14 10 q :=
  coefficient_normalized before14 14 10 (fun q d => (unit14_after13 q d).row) q
theorem row15 (q : Vector R) : (output q).coeff 9 = q 15 + baseline before15 15 9 q :=
  coefficient_normalized before15 15 9 (fun q d => (unit15_after14 q d).row) q

theorem row13_final (q : Vector R) : (output q).coeff 11 = q 13 + baseline before13 13 11 q := by
  change (before14 (step14 (step15 q))).coeff 11 = _
  rw [row13]
  simp only [step14, step15, coordinateShear_apply,
    Function.update_of_ne (show (13 : Fin 25) ≠ 14 by omega),
    Function.update_of_ne (show (13 : Fin 25) ≠ 15 by omega),
    baseline_update before13 13 11 14 (by omega),
    baseline_update before13 13 11 15 (by omega)]

theorem row14_final (q : Vector R) : (output q).coeff 10 = q 14 + baseline before14 14 10 q := by
  change (before15 (step15 q)).coeff 10 = _
  rw [row14]
  simp only [step15, coordinateShear_apply,
    Function.update_of_ne (show (14 : Fin 25) ≠ 15 by omega),
    baseline_update before14 14 10 15 (by omega)]

theorem high_before (q : Vector R) (i : Fin 13) (d : R) :
    UnitDifference (before13 q) (before13 (increment q ⟨i.val, by omega⟩ d)) (24-i.val) d := by
  rcases i with ⟨i, hi13⟩
  by_cases hi : i < 9
  · exact Char2Degree25HighKeys.increment_high_unit q ⟨i, hi⟩ d
  · interval_cases i
    · exact Char2Degree25MiddleKeys.increment9_unit q d
    · exact Char2Degree25MiddleKeys.increment10_unit q d
    · exact Char2Degree25MiddleKeys.increment11_unit q d
    · exact Char2Degree25MiddleKeys.increment12_unit q d

theorem high_after13 (i : Fin 13) (q : Vector R) (d : R) :
    UnitDifference (before14 q) (before14 (increment q ⟨i.val, by omega⟩ d)) (24-i.val) d := by
  have hi := i.isLt
  exact Char2CoefficientShearTransport.high_unit before13 13 11 unit13_before
    ⟨i.val, by omega⟩ (24-i.val) (by omega) (fun q d => high_before q i d) q d
theorem high_after14 (i : Fin 13) (q : Vector R) (d : R) :
    UnitDifference (before15 q) (before15 (increment q ⟨i.val, by omega⟩ d)) (24-i.val) d := by
  have hi := i.isLt
  exact Char2CoefficientShearTransport.high_unit before14 14 10 unit14_after13
    ⟨i.val, by omega⟩ (24-i.val) (by omega) (high_after13 i) q d
theorem high_unit (i : Fin 13) (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q ⟨i.val, by omega⟩ d)) (24-i.val) d := by
  have hi := i.isLt
  exact Char2CoefficientShearTransport.high_unit before15 15 9 unit15_after14
    ⟨i.val, by omega⟩ (24-i.val) (by omega) (high_after14 i) q d

theorem unit13_after13 (q : Vector R) (d : R) :
    UnitDifference (before14 q) (before14 (increment q 13 d)) 11 d :=
  Char2CoefficientShearTransport.own_unit before13 13 11 unit13_before q d
theorem unit13_after14 (q : Vector R) (d : R) :
    UnitDifference (before15 q) (before15 (increment q 13 d)) 11 d :=
  Char2CoefficientShearTransport.high_unit before14 14 10 unit14_after13
    13 11 (by omega) unit13_after13 q d
theorem unit13 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 13 d)) 11 d :=
  Char2CoefficientShearTransport.high_unit before15 15 9 unit15_after14
    13 11 (by omega) unit13_after14 q d
theorem unit14_after14 (q : Vector R) (d : R) :
    UnitDifference (before15 q) (before15 (increment q 14 d)) 10 d :=
  Char2CoefficientShearTransport.own_unit before14 14 10 unit14_after13 q d
theorem unit14 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 14 d)) 10 d :=
  Char2CoefficientShearTransport.high_unit before15 15 9 unit15_after14
    14 10 (by omega) unit14_after14 q d
theorem unit15 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 15 d)) 9 d :=
  Char2CoefficientShearTransport.own_unit before15 15 9 unit15_after14 q d

theorem unit24_after13 (q : Vector R) (d : R) :
    UnitDifference (before14 q) (before14 (increment q 24 d)) 0 d :=
  Char2CoefficientShearTransport.low_unit before13 13 11 24 (by omega) 0 (by omega)
    unit24_before q d
theorem unit24_after14 (q : Vector R) (d : R) :
    UnitDifference (before15 q) (before15 (increment q 24 d)) 0 d :=
  Char2CoefficientShearTransport.low_unit before14 14 10 24 (by omega) 0 (by omega)
    unit24_after13 q d
theorem unit24 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 24 d)) 0 d :=
  Char2CoefficientShearTransport.low_unit before15 15 9 24 (by omega) 0 (by omega)
    unit24_after14 q d

end FastPoly.Char2Degree25LowerCoordinates
