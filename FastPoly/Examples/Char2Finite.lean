import FastPoly.Examples.Char2Construction
import FastPoly.Examples.Char2Degree5
import FastPoly.Examples.Char2Degree7
import FastPoly.Examples.Char2Degree9
import FastPoly.Examples.Char2Degree11
import FastPoly.Examples.Char2Degree13
import FastPoly.Examples.Char2Degree15

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
  ⟨Char2Degree11.program, Char2Degree11.decode, Char2Degree11.program_decode_correct⟩

noncomputable def degree13 : Construction F 13 7 :=
  ⟨Char2Degree13.program, Char2Degree13.decode, Char2Degree13.program_decode_correct⟩

noncomputable def degree15 : Construction F 15 8 :=
  ⟨Char2Degree15.program, Char2Degree15.decode, Char2Degree15.program_decode_correct⟩

/-- A fixed program with exactly `⌊n/2⌋+1` products and its explicit decoder.
The perfect-field assumption is needed only by the degree-7 base and its lift. -/
noncomputable def construction [PerfectRing F 2] (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 16) :
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

/-- The counted program really computes any requested monic polynomial. -/
theorem monic_evaluation [PerfectRing F 2] (n : ℕ) (hlo : 5 ≤ n) (hhi : n ≤ 16)
    (P : F[X]) (hP : P.Monic) (hn : P.natDegree = n) :
    (construction (F := F) n hlo hhi).program.circuit.eval
      (inputEnv ((construction n hlo hhi).decoder (fun i => P.coeff i))) 0 = P :=
  (construction n hlo hhi).correct_polynomial P hP hn

end FastPoly.Char2Finite
