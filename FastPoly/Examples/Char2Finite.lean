import FastPoly.Examples.Char2Construction
import FastPoly.Examples.Char2Degree5
import FastPoly.Examples.Char2Degree7
import FastPoly.Examples.Char2Degree9
import FastPoly.Examples.Char2Degree11FastRealization
import FastPoly.Examples.Char2Degree13FastRealization
import FastPoly.Examples.Char2Degree15FastRealization
import FastPoly.Examples.Char2Degree17Realization
import FastPoly.Examples.Char2Degree19Realization
import FastPoly.Examples.Char2Degree21Realization
import FastPoly.Examples.Char2Degree23Realization
import FastPoly.Examples.Char2Degree25Realization

/-!
# Verified finite characteristic-two constructions

These are the website's literal fixed circuits, not the older search candidates.
The odd circuits include explicit coefficient decoders; each even degree uses
the one-product lift. This module imports only completed certificates.
-/

namespace FastPoly.Char2Finite

open Char2Certificate Polynomial
variable {F : Type*} [Field F] [CharP F 2]

noncomputable def degree5 : Construction F 5 3 :=
  ⟨Char2Degree5.program, Char2Degree5.decode, Char2Degree5.program_decode_correct⟩

noncomputable def degree7 [PerfectRing F 2] : Construction F 7 4 :=
  ⟨Char2Degree7.program, Char2Degree7.decode, Char2Degree7.program_decode_correct⟩

noncomputable def degree9 : Construction F 9 5 :=
  ⟨Char2Degree9.program, Char2Degree9.decode, Char2Degree9.program_decode_correct⟩

noncomputable def degree11 : Construction F 11 6 :=
  Char2Degree11Fast.construction

noncomputable def degree13 : Construction F 13 7 :=
  Char2Degree13Fast.construction

noncomputable def degree15 : Construction F 15 8 :=
  Char2Degree15Fast.construction

/-- The supplied degree-17 circuit with explicit square/fourth-power pivots. -/
noncomputable def degree17 [PerfectRing F 2] : Construction F 17 9 :=
  Char2Degree17Realization.construction

/-- The one-product lift of the completed degree-17 decoder. -/
noncomputable def degree18 [PerfectRing F 2] : Construction F 18 10 := degree17.evenLift

/-- The existing degree-19 circuit, decoded by monic division and explicit
thirteen-row back-substitution; no perfect-field assumption is needed. -/
noncomputable def degree19 : Construction F 19 10 :=
  Char2Degree19Realization.construction

/-- The one-product lift of the completed degree-19 decoder. -/
noncomputable def degree20 : Construction F 20 11 := degree19.evenLift

/-- The supplied degree-21 circuit with its two-sided raw-key inverse. -/
noncomputable def degree21 : Construction F 21 11 :=
  Char2Degree21Realization.construction

/-- The one-product lift of the completed degree-21 decoder. -/
noncomputable def degree22 : Construction F 22 12 := degree21.evenLift

/-- The supplied degree-23 circuit with its two-sided raw-key inverse. -/
noncomputable def degree23 : Construction F 23 12 :=
  Char2Degree23Realization.construction

/-- The one-product lift of the completed degree-23 decoder. -/
noncomputable def degree24 : Construction F 24 13 := degree23.evenLift

/-- The supplied degree-25 circuit with its explicit two-sided raw-key inverse.
No perfect-field assumption is needed by this degree. -/
noncomputable def degree25 : Construction F 25 13 :=
  Char2Degree25Realization.construction

/-- A fixed program with exactly `⌊n/2⌋+1` products and its explicit decoder.
The perfect-field assumption is needed by the degree-7 and degree-17 bases
and their even lifts; the degree-25 inverse uses only unit pivots. -/
noncomputable def construction [PerfectRing F 2] (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 25) :
    Construction F n (n / 2 + 1) := by
  interval_cases n
  · exact degree5
  · exact degree5.evenLift
  · exact degree7
  · exact degree7.evenLift
  · exact degree9
  · exact degree9.evenLift
  · exact degree11
  · exact degree11.evenLift
  · exact degree13
  · exact degree13.evenLift
  · exact degree15
  · exact degree15.evenLift
  · exact degree17
  · exact degree18
  · exact degree19
  · exact degree20
  · exact degree21
  · exact degree22
  · exact degree23
  · exact degree24
  · exact degree25

/-- The counted program really computes any requested monic polynomial. -/
theorem monic_evaluation [PerfectRing F 2] (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 25)
    (P : F[X]) (hP : P.Monic) (hn : P.natDegree = n) :
    (construction (F := F) n hlo hhi).program.circuit.eval
      (inputEnv ((construction n hlo hhi).decoder (fun i => P.coeff i))) 0 = P :=
  (construction n hlo hhi).correct_polynomial P hP hn

end FastPoly.Char2Finite
