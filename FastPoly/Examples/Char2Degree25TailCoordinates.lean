import FastPoly.Examples.Char2Degree25LowerActions

/-! Four further explicit coefficient shears, using the supplied coupled
actions after their earlier corrections have been removed. This gives the
first twenty coordinate unit columns of the existing degree-25 circuit.
The last four nonconstant columns are not asserted here. -/
namespace FastPoly.Char2Degree25TailCoordinates

open Polynomial Char2Degree19InnerTail Char2CoefficientShear Char2PivotAction
open Char2CoefficientShearTransport (increment)
open Char2Degree25LowerCoordinates (Vector)
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def before16 (q : Vector R) : R[X] := Char2Degree25LowerCoordinates.output q
noncomputable def step16 : Vector R ≃ Vector R := coordinateShear before16 16 8
noncomputable def before17 (q : Vector R) : R[X] := before16 (step16 q)
theorem unit16_before (q : Vector R) (d : R) :
    UnitDifference (before16 q) (before16 (increment q 16 d)) 8 d :=
  Char2Degree25LowerActions.unit16 q d

noncomputable def action17 : Action (before17 (R := R)) 17 17 7 :=
  Char2Degree25LowerActions.action17.normalize 16 8 (by omega) (by omega) (by omega) unit16_before
noncomputable def action18_after16 : Action (before17 (R := R)) 17 18 6 :=
  Char2Degree25LowerActions.action18.normalize 16 8 (by omega) (by omega) (by omega) unit16_before
noncomputable def action19_after16 : Action (before17 (R := R)) 17 19 5 :=
  Char2Degree25LowerActions.action19.normalize 16 8 (by omega) (by omega) (by omega) unit16_before
theorem unit17_before (q : Vector R) (d : R) :
    UnitDifference (before17 q) (before17 (increment q 17 d)) 7 d :=
  action17.unit_increment (by omega) q d

noncomputable def step17 : Vector R ≃ Vector R := coordinateShear before17 17 7
noncomputable def before18 (q : Vector R) : R[X] := before17 (step17 q)
noncomputable def action18 : Action (before18 (R := R)) 18 18 6 :=
  action18_after16.normalize 17 7 (by omega) (by omega) (by omega) unit17_before
noncomputable def action19_after17 : Action (before18 (R := R)) 18 19 5 :=
  action19_after16.normalize 17 7 (by omega) (by omega) (by omega) unit17_before
theorem unit18_before (q : Vector R) (d : R) :
    UnitDifference (before18 q) (before18 (increment q 18 d)) 6 d :=
  action18.unit_increment (by omega) q d

noncomputable def step18 : Vector R ≃ Vector R := coordinateShear before18 18 6
noncomputable def before19 (q : Vector R) : R[X] := before18 (step18 q)
noncomputable def action19 : Action (before19 (R := R)) 19 19 5 :=
  action19_after17.normalize 18 6 (by omega) (by omega) (by omega) unit18_before
theorem unit19_before (q : Vector R) (d : R) :
    UnitDifference (before19 q) (before19 (increment q 19 d)) 5 d :=
  action19.unit_increment (by omega) q d

noncomputable def step19 : Vector R ≃ Vector R := coordinateShear before19 19 5
noncomputable def output (q : Vector R) : R[X] := before19 (step19 q)
noncomputable def tailEquiv : Vector R ≃ Vector R :=
  ((step19.trans step18).trans step17).trans step16
noncomputable def keyEquiv : Vector R ≃ Vector R :=
  tailEquiv.trans Char2Degree25LowerCoordinates.keyEquiv
noncomputable def keys (q : Vector R) : ℕ → R :=
  Char2Degree25LowerCoordinates.keys (tailEquiv q)

theorem output_eq (q : Vector R) : output q = Char2Degree25Frame.output (keys q) := rfl
theorem keyEquiv_apply (q : Vector R) (i : Fin 25) : keyEquiv q i = keys q i.val := rfl
theorem decode_encode (q : Vector R) : keyEquiv.symm (keyEquiv q) = q :=
  keyEquiv.symm_apply_apply q
theorem encode_decode (a : Vector R) : keyEquiv (keyEquiv.symm a) = a :=
  keyEquiv.apply_symm_apply a

theorem row16 (q : Vector R) : (before17 q).coeff 8 = q 16 + baseline before16 16 8 q :=
  coefficient_normalized before16 16 8 (fun q d => (unit16_before q d).row) q
theorem row17 (q : Vector R) : (before18 q).coeff 7 = q 17 + baseline before17 17 7 q :=
  coefficient_normalized before17 17 7 (fun q d => (unit17_before q d).row) q
theorem row18 (q : Vector R) : (before19 q).coeff 6 = q 18 + baseline before18 18 6 q :=
  coefficient_normalized before18 18 6 (fun q d => (unit18_before q d).row) q
theorem row19 (q : Vector R) : (output q).coeff 5 = q 19 + baseline before19 19 5 q :=
  coefficient_normalized before19 19 5 (fun q d => (unit19_before q d).row) q

theorem high_through19 (p : Fin 25) (r : ℕ) (hr : 8 < r)
    (hu : ∀ (q : Vector R) (d : R), UnitDifference (before16 q) (before16 (increment q p d)) r d)
    (q : Vector R) (d : R) : UnitDifference (output q) (output (increment q p d)) r d := by
  have h16 : ∀ (q : Vector R) (d : R), UnitDifference (before17 q) (before17 (increment q p d)) r d :=
    Char2CoefficientShearTransport.high_unit before16 16 8 unit16_before p r hr hu
  have h17 : ∀ (q : Vector R) (d : R), UnitDifference (before18 q) (before18 (increment q p d)) r d :=
    Char2CoefficientShearTransport.high_unit before17 17 7 unit17_before p r (by omega) h16
  have h18 : ∀ (q : Vector R) (d : R), UnitDifference (before19 q) (before19 (increment q p d)) r d :=
    Char2CoefficientShearTransport.high_unit before18 18 6 unit18_before p r (by omega) h17
  exact Char2CoefficientShearTransport.high_unit before19 19 5 unit19_before p r (by omega) h18 q d

theorem high_unit (i : Fin 16) (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q ⟨i.val, by omega⟩ d)) (24-i.val) d := by
  have hi := i.isLt
  apply high_through19 _ _ (by omega) _ q d
  intro q d
  rcases i with ⟨i, hi⟩
  by_cases hi13 : i < 13
  · exact Char2Degree25LowerCoordinates.high_unit ⟨i, hi13⟩ q d
  · interval_cases i
    · exact Char2Degree25LowerCoordinates.unit13 q d
    · exact Char2Degree25LowerCoordinates.unit14 q d
    · exact Char2Degree25LowerCoordinates.unit15 q d

theorem unit16 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 16 d)) 8 d := by
  have h16 : ∀ (q : Vector R) (d : R), UnitDifference (before17 q) (before17 (increment q 16 d)) 8 d :=
    Char2CoefficientShearTransport.own_unit before16 16 8 unit16_before
  have h17 : ∀ (q : Vector R) (d : R), UnitDifference (before18 q) (before18 (increment q 16 d)) 8 d :=
    Char2CoefficientShearTransport.high_unit before17 17 7 unit17_before 16 8 (by omega) h16
  have h18 : ∀ (q : Vector R) (d : R), UnitDifference (before19 q) (before19 (increment q 16 d)) 8 d :=
    Char2CoefficientShearTransport.high_unit before18 18 6 unit18_before 16 8 (by omega) h17
  exact Char2CoefficientShearTransport.high_unit before19 19 5 unit19_before 16 8 (by omega) h18 q d
theorem unit17 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 17 d)) 7 d := by
  have h17 : ∀ (q : Vector R) (d : R), UnitDifference (before18 q) (before18 (increment q 17 d)) 7 d :=
    Char2CoefficientShearTransport.own_unit before17 17 7 unit17_before
  have h18 : ∀ (q : Vector R) (d : R), UnitDifference (before19 q) (before19 (increment q 17 d)) 7 d :=
    Char2CoefficientShearTransport.high_unit before18 18 6 unit18_before 17 7 (by omega) h17
  exact Char2CoefficientShearTransport.high_unit before19 19 5 unit19_before 17 7 (by omega) h18 q d
theorem unit18 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 18 d)) 6 d :=
  Char2CoefficientShearTransport.high_unit before19 19 5 unit19_before 18 6 (by omega)
    (Char2CoefficientShearTransport.own_unit before18 18 6 unit18_before) q d
theorem unit19 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 19 d)) 5 d :=
  Char2CoefficientShearTransport.own_unit before19 19 5 unit19_before q d

/-- All twenty supplied nonconstant unit columns after these twenty steps. -/
theorem increment_unit (i : Fin 20) (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q ⟨i.val, by omega⟩ d)) (24-i.val) d := by
  rcases i with ⟨i, hi⟩
  by_cases hi16 : i < 16
  · exact high_unit ⟨i, hi16⟩ q d
  · interval_cases i
    · exact unit16 q d
    · exact unit17 q d
    · exact unit18 q d
    · exact unit19 q d

theorem unit24 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 24 d)) 0 d := by
  have h16 : ∀ (q : Vector R) (d : R), UnitDifference (before17 q) (before17 (increment q 24 d)) 0 d :=
    Char2CoefficientShearTransport.low_unit before16 16 8 24 (by omega) 0 (by omega)
      Char2Degree25LowerCoordinates.unit24
  have h17 : ∀ (q : Vector R) (d : R), UnitDifference (before18 q) (before18 (increment q 24 d)) 0 d :=
    Char2CoefficientShearTransport.low_unit before17 17 7 24 (by omega) 0 (by omega) h16
  have h18 : ∀ (q : Vector R) (d : R), UnitDifference (before19 q) (before19 (increment q 24 d)) 0 d :=
    Char2CoefficientShearTransport.low_unit before18 18 6 24 (by omega) 0 (by omega) h17
  exact Char2CoefficientShearTransport.low_unit before19 19 5 24 (by omega) 0 (by omega) h18 q d

end FastPoly.Char2Degree25TailCoordinates
