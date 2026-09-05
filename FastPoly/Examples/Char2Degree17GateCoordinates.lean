import FastPoly.Examples.Char2Degree17Wires
import Mathlib.Tactic.FinCases

/-!
# Gate-by-gate coordinate inverse for the existing degree-17 circuit

This is the supplied verifier's map between the seventeen raw offsets and
the selected internal gate rows Q0,...,Q16. Each pair is inverted before
constructing its gate, and all previously constructed gates remain named.
The final output-row decoder and the S/R/E coordinate changes are separate.
-/

namespace FastPoly.Char2Degree17GateCoordinates

set_option maxHeartbeats 20000

open Polynomial
open Char2Degree17Wires

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The scalar rows Q0 and Q9 are their original offsets, by the named
`y_coeff_one` and `h_coeff_one` lemmas. Q16 is the final offset itself. -/
noncomputable def coordinates (a : Vector R) (i : Fin 17) : R :=
  match i.val with
  | 0 => a 0
  | 1 => (z a).coeff 2
  | 2 => (z a).coeff 1
  | 3 => (t a).coeff 2
  | 4 => (t a).coeff 1
  | 5 => (u a).coeff 4
  | 6 => (u a).coeff 3
  | 7 => (v a).coeff 7
  | 8 => (v a).coeff 3
  | 9 => a 9
  | 10 => (j a).coeff 2
  | 11 => (j a).coeff 1
  | 12 => (ell a).coeff 4
  | 13 => (ell a).coeff 3
  | 14 => (w a).coeff 10
  | 15 => (w a).coeff 7
  | _ => a 16

noncomputable def dy (q : Vector R) : R[X] := Char2Degree17QuadraticOffsets.y (q 0)
noncomputable def az (q : Vector R) : R × R :=
  Char2UnequalOffsets.recover X (X + dy q) 1 2 (q 1, q 2)
noncomputable def dz (q : Vector R) : R[X] :=
  Char2UnequalOffsets.gate X (X + dy q) (az q)
def aT (q : Vector R) : R × R :=
  Char2Degree17QuadraticOffsets.recover (q 0) (q 3, q 4)
noncomputable def dt (q : Vector R) : R[X] :=
  Char2Degree17QuadraticOffsets.gate (q 0) (aT q)
noncomputable def au (q : Vector R) : R × R :=
  Char2UnequalOffsets.recover (dy q + dz q) (dz q + dt q) 3 4 (q 5, q 6)
noncomputable def du (q : Vector R) : R[X] :=
  Char2UnequalOffsets.gate (dy q + dz q) (dz q + dt q) (au q)
noncomputable def av (q : Vector R) : R × R :=
  Char2UnequalOffsets.recover (X + dz q) (X + dz q + dt q + du q) 3 7 (q 7, q 8)
noncomputable def dv (q : Vector R) : R[X] :=
  Char2UnequalOffsets.gate (X + dz q) (X + dz q + dt q + du q) (av q)
noncomputable def dh (q : Vector R) : R[X] := (dy q + C (q 9)) * X
noncomputable def aj (q : Vector R) : R × R :=
  Char2UnequalOffsets.recover X (dy q) 1 2 (q 10, q 11)
noncomputable def dj (q : Vector R) : R[X] := Char2UnequalOffsets.gate X (dy q) (aj q)
noncomputable def al (q : Vector R) : R × R :=
  Char2UnequalOffsets.recover (dh q) (dt q) 3 4 (q 12, q 13)
noncomputable def dell (q : Vector R) : R[X] :=
  Char2UnequalOffsets.gate (dh q) (dt q) (al q)
noncomputable def aw (q : Vector R) : R × R :=
  Char2UnequalOffsets.recover (X + du q) (du q + dv q) 7 10 (q 14, q 15)
noncomputable def dw (q : Vector R) : R[X] :=
  Char2UnequalOffsets.gate (X + du q) (du q + dv q) (aw q)

/-- Original raw order; `j` and `ell` use the helper with their factors reversed. -/
noncomputable def keys (q : Vector R) (i : Fin 17) : R :=
  match i.val with
  | 0 => q 0
  | 1 => (az q).1
  | 2 => (az q).2
  | 3 => (aT q).1
  | 4 => (aT q).2
  | 5 => (au q).1
  | 6 => (au q).2
  | 7 => (av q).1
  | 8 => (av q).2
  | 9 => q 9
  | 10 => (aj q).2
  | 11 => (aj q).1
  | 12 => (al q).2
  | 13 => (al q).1
  | 14 => (aw q).1
  | 15 => (aw q).2
  | _ => q 16

theorem y_keys (q : Vector R) : y (keys q) = dy q := rfl
theorem z_keys (q : Vector R) : z (keys q) = dz q := rfl
theorem t_keys (q : Vector R) : t (keys q) = dt q := rfl
theorem u_keys (q : Vector R) : u (keys q) = du q := rfl
theorem v_keys (q : Vector R) : v (keys q) = dv q := rfl
theorem h_keys (q : Vector R) : h (keys q) = dh q := rfl
theorem j_keys (q : Vector R) : j (keys q) = dj q := rfl
theorem ell_keys (q : Vector R) : ell (keys q) = dell q := rfl
theorem w_keys (q : Vector R) : w (keys q) = dw q := rfl

variable [Nontrivial R]

theorem z_rows (q : Vector R) : ((dz q).coeff 2, (dz q).coeff 1) = (q 1, q 2) := by
  have hm : IsMonicOfDegree (X + dy q) 2 := by
    simpa only [y_keys] using higherZ_monic (keys q)
  exact Char2UnequalOffsets.rows_recover X (X + dy q) 1 2
    (isMonicOfDegree_X R) hm (by omega) (by omega) _

theorem t_rows (q : Vector R) : ((dt q).coeff 2, (dt q).coeff 1) = (q 3, q 4) :=
  Char2Degree17QuadraticOffsets.rows_recover (q 0) _

theorem u_rows (q : Vector R) : ((du q).coeff 4, (du q).coeff 3) = (q 5, q 6) := by
  have hl : IsMonicOfDegree (dy q + dz q) 3 := by
    simpa only [y_keys, z_keys] using lowerU_monic (keys q)
  have hh : IsMonicOfDegree (dz q + dt q) 4 := by
    simpa only [z_keys, t_keys] using higherU_monic (keys q)
  exact Char2UnequalOffsets.rows_recover _ _ 3 4 hl hh (by omega) (by omega) _

theorem v_rows (q : Vector R) : ((dv q).coeff 7, (dv q).coeff 3) = (q 7, q 8) := by
  have hl : IsMonicOfDegree (X + dz q) 3 := by
    simpa only [z_keys] using lowerV_monic (keys q)
  have hh : IsMonicOfDegree (X + dz q + dt q + du q) 7 := by
    simpa only [z_keys, t_keys, u_keys] using higherV_monic (keys q)
  exact Char2UnequalOffsets.rows_recover _ _ 3 7 hl hh (by omega) (by omega) _

theorem j_rows (q : Vector R) : ((dj q).coeff 2, (dj q).coeff 1) = (q 10, q 11) := by
  have hm : IsMonicOfDegree (dy q) 2 := by simpa only [y_keys] using y_monic (keys q)
  exact Char2UnequalOffsets.rows_recover X (dy q) 1 2
    (isMonicOfDegree_X R) hm (by omega) (by omega) _

theorem ell_rows (q : Vector R) : ((dell q).coeff 4, (dell q).coeff 3) = (q 12, q 13) := by
  have hl : IsMonicOfDegree (dh q) 3 := by simpa only [h_keys] using h_monic (keys q)
  have hh : IsMonicOfDegree (dt q) 4 := by simpa only [t_keys] using t_monic (keys q)
  exact Char2UnequalOffsets.rows_recover _ _ 3 4 hl hh (by omega) (by omega) _

theorem w_rows (q : Vector R) : ((dw q).coeff 10, (dw q).coeff 7) = (q 14, q 15) := by
  have hl : IsMonicOfDegree (X + du q) 7 := by
    simpa only [u_keys] using lowerW_monic (keys q)
  have hh : IsMonicOfDegree (du q + dv q) 10 := by
    simpa only [u_keys, v_keys] using higherW_monic (keys q)
  exact Char2UnequalOffsets.rows_recover _ _ 7 10 hl hh (by omega) (by omega) _

theorem coordinates_keys (q : Vector R) : coordinates (keys q) = q := by
  funext i
  fin_cases i
  · rfl
  · exact congrArg Prod.fst (z_rows q)
  · exact congrArg Prod.snd (z_rows q)
  · exact congrArg Prod.fst (t_rows q)
  · exact congrArg Prod.snd (t_rows q)
  · exact congrArg Prod.fst (u_rows q)
  · exact congrArg Prod.snd (u_rows q)
  · exact congrArg Prod.fst (v_rows q)
  · exact congrArg Prod.snd (v_rows q)
  · rfl
  · exact congrArg Prod.fst (j_rows q)
  · exact congrArg Prod.snd (j_rows q)
  · exact congrArg Prod.fst (ell_rows q)
  · exact congrArg Prod.snd (ell_rows q)
  · exact congrArg Prod.fst (w_rows q)
  · exact congrArg Prod.snd (w_rows q)
  · rfl

theorem dy_coordinates (a : Vector R) : dy (coordinates a) = y a := rfl

theorem az_coordinates (a : Vector R) : az (coordinates a) = (a 1, a 2) :=
  Char2UnequalOffsets.recover_rows X (X + y a) 1 2
    (isMonicOfDegree_X R) (higherZ_monic a) (by omega) (by omega) _

theorem dz_coordinates (a : Vector R) : dz (coordinates a) = z a := by
  rw [dz, dy_coordinates, az_coordinates]; rfl

theorem aT_coordinates (a : Vector R) : aT (coordinates a) = (a 3, a 4) :=
  Char2Degree17QuadraticOffsets.recover_rows (a 0) _

theorem dt_coordinates (a : Vector R) : dt (coordinates a) = t a := by
  rw [dt, aT_coordinates]; rfl

theorem au_coordinates (a : Vector R) : au (coordinates a) = (a 5, a 6) := by
  rw [au, dy_coordinates, dz_coordinates, dt_coordinates]
  exact Char2UnequalOffsets.recover_rows _ _ 3 4 (lowerU_monic a) (higherU_monic a)
    (by omega) (by omega) _

theorem du_coordinates (a : Vector R) : du (coordinates a) = u a := by
  rw [du, dy_coordinates, dz_coordinates, dt_coordinates, au_coordinates]; rfl

theorem av_coordinates (a : Vector R) : av (coordinates a) = (a 7, a 8) := by
  rw [av, dz_coordinates, dt_coordinates, du_coordinates]
  exact Char2UnequalOffsets.recover_rows _ _ 3 7 (lowerV_monic a) (higherV_monic a)
    (by omega) (by omega) _

theorem dv_coordinates (a : Vector R) : dv (coordinates a) = v a := by
  rw [dv, dz_coordinates, dt_coordinates, du_coordinates, av_coordinates]; rfl

theorem dh_coordinates (a : Vector R) : dh (coordinates a) = h a := by
  rw [dh, dy_coordinates]; rfl

theorem aj_coordinates (a : Vector R) : aj (coordinates a) = (a 11, a 10) := by
  rw [aj, dy_coordinates]
  exact Char2UnequalOffsets.recover_rows X (y a) 1 2 (isMonicOfDegree_X R) (y_monic a)
    (by omega) (by omega) _

theorem al_coordinates (a : Vector R) : al (coordinates a) = (a 13, a 12) := by
  rw [al, dh_coordinates, dt_coordinates]
  exact Char2UnequalOffsets.recover_rows _ _ 3 4 (h_monic a) (t_monic a)
    (by omega) (by omega) _

theorem aw_coordinates (a : Vector R) : aw (coordinates a) = (a 14, a 15) := by
  rw [aw, du_coordinates, dv_coordinates]
  exact Char2UnequalOffsets.recover_rows _ _ 7 10 (lowerW_monic a) (higherW_monic a)
    (by omega) (by omega) _

theorem keys_coordinates (a : Vector R) : keys (coordinates a) = a := by
  funext i
  fin_cases i
  · rfl
  · exact congrArg Prod.fst (az_coordinates a)
  · exact congrArg Prod.snd (az_coordinates a)
  · exact congrArg Prod.fst (aT_coordinates a)
  · exact congrArg Prod.snd (aT_coordinates a)
  · exact congrArg Prod.fst (au_coordinates a)
  · exact congrArg Prod.snd (au_coordinates a)
  · exact congrArg Prod.fst (av_coordinates a)
  · exact congrArg Prod.snd (av_coordinates a)
  · rfl
  · exact congrArg Prod.snd (aj_coordinates a)
  · exact congrArg Prod.fst (aj_coordinates a)
  · exact congrArg Prod.snd (al_coordinates a)
  · exact congrArg Prod.fst (al_coordinates a)
  · exact congrArg Prod.fst (aw_coordinates a)
  · exact congrArg Prod.snd (aw_coordinates a)
  · rfl

/-- The selected internal gate rows, not yet the output's coefficient map. -/
noncomputable def coordinateEquiv : Vector R ≃ Vector R where
  toFun := coordinates
  invFun := keys
  left_inv := keys_coordinates
  right_inv := coordinates_keys

end FastPoly.Char2Degree17GateCoordinates
