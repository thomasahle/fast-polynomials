import FastPoly.Examples.Char2Degree25TerminalUnits
import FastPoly.Examples.Char2Degree25TerminalOne
import FastPoly.Examples.Char2PivotAction

/-! The last nontrivial coordinate shear of the supplied degree-25 inverse.
Its explicit row-four correction removes the q20 part of the supplied
coupled q21 direction. The original raw offsets are recovered by reversing
the displayed shear composition. All twenty-five unit columns are certified
against the actual circuit, including the recovered row-one correction. -/
namespace FastPoly.Char2Degree25Coordinates

open Polynomial Char2CoefficientShear Char2CoefficientShearTransport
  Char2Degree19InnerTail Char2PivotAction
open Char2Degree25LowerCoordinates (Vector)
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def step20 : Vector R ≃ Vector R :=
  coordinateShear Char2Degree25TailCoordinates.output 20 4
noncomputable def output (q : Vector R) : R[X] := Char2Degree25TailCoordinates.output (step20 q)
noncomputable def keyEquiv : Vector R ≃ Vector R :=
  step20.trans Char2Degree25TailCoordinates.keyEquiv
noncomputable def keys (q : Vector R) : ℕ → R := Char2Degree25TailCoordinates.keys (step20 q)

theorem output_eq (q : Vector R) : output q = Char2Degree25Frame.output (keys q) := rfl
theorem keyEquiv_apply (q : Vector R) (i : Fin 25) : keyEquiv q i = keys q i.val := rfl
theorem decode_encode (q : Vector R) : keyEquiv.symm (keyEquiv q) = q := keyEquiv.symm_apply_apply q
theorem encode_decode (a : Vector R) : keyEquiv (keyEquiv.symm a) = a := keyEquiv.apply_symm_apply a

def raw (a : Vector R) (i : ℕ) : R := if h : i < 25 then a ⟨i, h⟩ else 0

theorem raw_inverse (a : Vector R) : keys (keyEquiv.symm a) = raw a := by
  funext i
  by_cases hi : i < 25
  · have h := congrFun (keyEquiv.apply_symm_apply a) (⟨i, hi⟩ : Fin 25)
    rw [keyEquiv_apply] at h
    simpa only [raw, dif_pos hi] using h
  · have hn : i = (i - 25) + 25 := by omega
    rw [raw, dif_neg hi, hn]
    rfl

theorem output_monic (q : Vector R) : IsMonicOfDegree (output q) 25 := by
  rw [output_eq]
  exact Char2Degree25Frame.output_monic _

-- Proofs below use the named input family, never its nested circuit body.
attribute [local irreducible] Char2Degree25TailCoordinates.output

theorem high_unit (q : Vector R) (i : Fin 20) (d : R) :
    UnitDifference (output q) (output (increment q ⟨i.val, by omega⟩ d)) (24-i.val) d := by
  have hi := i.isLt
  simp only [output, step20]
  exact Char2CoefficientShearTransport.high_unit
    (Char2Degree25TailCoordinates.output (R := R)) 20 4 Char2Degree25TerminalUnits.unit20
    ⟨i.val, by omega⟩ (24-i.val) (by omega)
    (fun q d => Char2Degree25TailCoordinates.increment_unit i q d) q d

theorem unit20 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 20 d)) 4 d := by
  simp only [output, step20]
  exact Char2CoefficientShearTransport.own_unit
    (Char2Degree25TailCoordinates.output (R := R)) 20 4 Char2Degree25TerminalUnits.unit20 q d

noncomputable def action21 : Action (Char2Degree25TailCoordinates.output (R := R)) 20 21 3 where
  shift := Char2Degree25TerminalSlots.step21
  unit := Char2Degree25TerminalUnits.unit_step21
  before := by
    intro q d k hk
    simp only [Char2Degree25TerminalSlots.step21, increment,
      Function.update_of_ne (show k ≠ 20 by omega), Function.update_of_ne (show k ≠ 21 by omega)]
  after := by
    intro q d k hk
    simp only [Char2Degree25TerminalSlots.step21, increment,
      Function.update_of_ne (show k ≠ 20 by omega), Function.update_of_ne (show k ≠ 21 by omega)]
  pivot := by
    intro q d
    rfl

noncomputable def normalizedAction21 : Action (output (R := R)) 21 21 3 :=
  action21.normalize 20 4 (by omega) (by omega) (by omega) Char2Degree25TerminalUnits.unit20

theorem unit21 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 21 d)) 3 d :=
  normalizedAction21.unit_increment (by omega) q d

theorem unit22 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 22 d)) 2 d := by
  simp only [output, step20]
  exact Char2CoefficientShearTransport.low_unit
    (Char2Degree25TailCoordinates.output (R := R)) 20 4 22 (by omega) 2 (by omega)
    Char2Degree25TerminalUnits.unit22 q d

theorem unit23 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 23 d)) 1 d := by
  simp only [output, step20]
  exact Char2CoefficientShearTransport.low_unit
    (Char2Degree25TailCoordinates.output (R := R)) 20 4 23 (by omega) 1 (by omega)
    Char2Degree25TerminalOne.unit23 q d

theorem unit24 (q : Vector R) (d : R) :
    UnitDifference (output q) (output (increment q 24 d)) 0 d := by
  simp only [output, step20]
  exact Char2CoefficientShearTransport.low_unit
    (Char2Degree25TailCoordinates.output (R := R)) 20 4 24 (by omega) 0 (by omega)
    Char2Degree25TailCoordinates.unit24 q d

end FastPoly.Char2Degree25Coordinates
