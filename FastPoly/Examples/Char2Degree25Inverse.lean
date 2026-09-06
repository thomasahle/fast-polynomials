import FastPoly.Examples.Char2Degree25Coordinates
import FastPoly.Examples.Char2CoefficientInverse

/-! Two-sided inversion of the supplied thirteen-product degree-25 circuit.
The decoder reads descending coefficients at each recovered prefix, then
reverses the explicit raw-key coordinate changes. No coefficient baseline
or recursive circuit is expanded. -/
namespace FastPoly.Char2Degree25Inverse

open Polynomial Char2Degree19InnerTail Char2CoefficientShearTransport
open Char2Degree25Coordinates
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- Dispatch only the supplied column identities, not possible field values. -/
theorem all_unit (q : Fin 25 → R) (i : Fin 25) (d : R) :
    UnitDifference (output q) (output (Char2CoefficientInverse.increment q i d))
      (25 - 1 - i.val) d := by
  by_cases hi : i.val < 20
  · exact high_unit q ⟨i.val, hi⟩ d
  have hin := i.isLt
  have hc : i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact unit20 q d
  · exact unit21 q d
  · exact unit22 q d
  · exact unit23 q d
  · exact unit24 q d

/-- The literal recursive prefix decoder on reversed coefficient rows. -/
noncomputable def decodeRows (c : Fin 25 → R) : Fin 25 → R :=
  Char2CoefficientInverse.decodeRows output c

theorem decodeRows_eq (c : Fin 25 → R) (i : Fin 25) :
    decodeRows c i = c i +
      (output (Char2UpdateTriangular.knownPrefix i (decodeRows c))).coeff (24 - i.val) :=
  Char2CoefficientInverse.decodeRows_eq output c i

noncomputable def normalizedCoefficientEquiv : (Fin 25 → R) ≃ (Fin 25 → R) :=
  Char2CoefficientInverse.coefficientEquiv output all_unit

theorem normalizedCoefficientEquiv_apply (q : Fin 25 → R) (i : Fin 25) :
    normalizedCoefficientEquiv q i = (output q).coeff i.val :=
  Char2CoefficientInverse.coefficientEquiv_apply output all_unit q i

/-- In raw coordinates, undo the key changes before reading ordinary coefficients. -/
noncomputable def coefficientEquiv : (Fin 25 → R) ≃ (Fin 25 → R) :=
  keyEquiv.symm.trans normalizedCoefficientEquiv

theorem coefficientEquiv_apply (a : Fin 25 → R) (i : Fin 25) :
    coefficientEquiv a i = (Char2Degree25Frame.output (raw a)).coeff i.val := by
  change normalizedCoefficientEquiv (keyEquiv.symm a) i = _
  rw [normalizedCoefficientEquiv_apply, output_eq, raw_inverse]

theorem coefficientEquiv_symm_apply (c : Fin 25 → R) :
    coefficientEquiv.symm c =
      keyEquiv (decodeRows (Char2CoefficientInverse.reverseRows c)) := rfl

theorem decode_encode (a : Fin 25 → R) :
    keyEquiv (decodeRows (Char2CoefficientInverse.reverseRows (coefficientEquiv a))) = a := by
  rw [← coefficientEquiv_symm_apply, Equiv.symm_apply_apply]

theorem encode_decode (c : Fin 25 → R) :
    coefficientEquiv (keyEquiv (decodeRows (Char2CoefficientInverse.reverseRows c))) = c := by
  rw [← coefficientEquiv_symm_apply, Equiv.apply_symm_apply]

end FastPoly.Char2Degree25Inverse
