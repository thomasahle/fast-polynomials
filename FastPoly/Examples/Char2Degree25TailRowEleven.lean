import FastPoly.Examples.Char2Degree25TailCoordinates

/-! The already normalized row eleven survives the four later coefficient
shears. Only the pivot coordinate and its known prefix are read; no named
coefficient correction or circuit polynomial is expanded. -/
namespace FastPoly.Char2Degree25TailRowEleven

open Polynomial Char2CoefficientShear
open Char2CoefficientShearTransport (increment)
open Char2Degree25LowerCoordinates (Vector before13)
open Char2Degree25TailCoordinates (before16 before17 before18 before19
  step16 step17 step18 step19 tailEquiv output)

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem output_lower (q : Vector R) :
    output q = Char2Degree25LowerCoordinates.output (tailEquiv q) := rfl

attribute [local irreducible] before13 before16 before17 before18 before19 output

/-- The explicit row-eleven readout fixed after the thirteenth shear. -/
noncomputable def read (q : Vector R) : R :=
  q 13 + baseline before13 13 11 q

theorem read_update (q : Vector R) (j : Fin 25) (hj : (13 : Fin 25) < j)
    (value : R) : read (Function.update q j value) = read q := by
  simp only [read, Function.update_of_ne (ne_of_lt hj),
    baseline_update before13 13 11 j hj.le]

theorem read_shear (f : Vector R → R[X]) (j : Fin 25) (m : ℕ)
    (hj : (13 : Fin 25) < j) (q : Vector R) :
    read (coordinateShear f j m q) = read q := by
  rw [coordinateShear_apply]
  exact read_update q j hj _

theorem read_step16 (q : Vector R) : read (step16 q) = read q :=
  read_shear before16 16 8 (by omega) q
theorem read_step17 (q : Vector R) : read (step17 q) = read q :=
  read_shear before17 17 7 (by omega) q
theorem read_step18 (q : Vector R) : read (step18 q) = read q :=
  read_shear before18 18 6 (by omega) q
theorem read_step19 (q : Vector R) : read (step19 q) = read q :=
  read_shear before19 19 5 (by omega) q

theorem read_tailEquiv (q : Vector R) : read (tailEquiv q) = read q := by
  change read (step16 (step17 (step18 (step19 q)))) = read q
  rw [read_step16, read_step17, read_step18, read_step19]

/-- Actual tail output, not a formal or proposed normalized coefficient map. -/
theorem row11 (q : Vector R) :
    (output q).coeff 11 = q 13 + baseline before13 13 11 q := by
  rw [output_lower, Char2Degree25LowerCoordinates.row13_final]
  exact read_tailEquiv q

theorem increment_row11 (q : Vector R) (j : Fin 25)
    (hj : (13 : Fin 25) < j) (d : R) :
    (output (increment q j d)).coeff 11 = (output q).coeff 11 := by
  rw [row11, row11]
  exact read_update q j hj (q j + d)

theorem late_increment_row11 (q : Vector R) (j : Fin 25)
    (hj : (19 : Fin 25) < j) (d : R) :
    (output (increment q j d)).coeff 11 = (output q).coeff 11 :=
  increment_row11 q j (lt_trans (by omega) hj) d

theorem late_difference_row11 (q : Vector R) (j : Fin 25)
    (hj : (19 : Fin 25) < j) (d : R) :
    (output (increment q j d) + output q).coeff 11 = 0 := by
  rw [coeff_add, late_increment_row11 q j hj d, CharTwo.add_self_eq_zero]

end FastPoly.Char2Degree25TailRowEleven
