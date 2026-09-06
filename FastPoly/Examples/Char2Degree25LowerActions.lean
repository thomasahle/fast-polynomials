import FastPoly.Examples.Char2Degree25CoupledLowerKeys
import FastPoly.Examples.Char2Degree25LowerCoordinates
import FastPoly.Examples.Char2PivotAction

/-! The four supplied coupled directions conjugated by the three checked
coefficient shears at coordinates 13, 14, and 15. The generic action
construction supplies each explicit conjugate and removes its corrections
at normalized earlier coordinates; it performs no coefficient expansion. -/

namespace FastPoly.Char2Degree25LowerActions

open Char2Degree25CoupledLowerKeys Char2Degree25LowerCoordinates
  Char2PivotAction Char2Degree19InnerTail
open Char2CoefficientShearTransport (increment)

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def base16 : Action (before13 (R := R)) 13 16 8 where
  shift := step16
  unit := step16_unit
  before := by
    intro q d k hk
    apply step16_other <;> omega
  after := step16_later
  pivot := step16_pivot

noncomputable def base17 : Action (before13 (R := R)) 13 17 7 where
  shift := step17
  unit := step17_unit
  before := by
    intro q d k hk
    apply step17_other <;> omega
  after := step17_later
  pivot := step17_pivot

noncomputable def base18 : Action (before13 (R := R)) 13 18 6 where
  shift := step18
  unit := step18_unit
  before := by
    intro q d k hk
    apply step18_other <;> omega
  after := step18_later
  pivot := step18_pivot

noncomputable def base19 : Action (before13 (R := R)) 13 19 5 where
  shift := step19
  unit := step19_unit
  before := by
    intro q d k hk
    apply step19_other
    omega
  after := step19_later
  pivot := step19_pivot

/-- Three explicit conjugates, retaining the displayed lower raw action. -/
noncomputable def normalizeThrough15 {p : Fin 25} {r : ℕ}
    (a : Action (before13 (R := R)) 13 p r)
    (hp : (15 : Fin 25) < p) (hr : r < 9) :
    Action (output (R := R)) 16 p r := by
  let a13 : Action (before14 (R := R)) 14 p r :=
    a.normalize 13 11 (by omega) (by omega) (by omega) unit13_before
  let a14 : Action (before15 (R := R)) 15 p r :=
    a13.normalize 14 10 (by omega) (by omega) (by omega) unit14_after13
  exact a14.normalize 15 9 (by omega) hp hr unit15_after14

noncomputable def action16 : Action (output (R := R)) 16 16 8 :=
  normalizeThrough15 base16 (by omega) (by omega)
noncomputable def action17 : Action (output (R := R)) 16 17 7 :=
  normalizeThrough15 base17 (by omega) (by omega)
noncomputable def action18 : Action (output (R := R)) 16 18 6 :=
  normalizeThrough15 base18 (by omega) (by omega)
noncomputable def action19 : Action (output (R := R)) 16 19 5 :=
  normalizeThrough15 base19 (by omega) (by omega)

/-- The first conjugated action has singleton support, hence is the literal
coordinate-16 translation and provides its elementary unit pivot. -/
theorem unit16 (q : Fin 25 → R) (d : R) :
    UnitDifference (output q) (output (increment q 16 d)) 8 d :=
  action16.unit_increment (by omega) q d

end FastPoly.Char2Degree25LowerActions
