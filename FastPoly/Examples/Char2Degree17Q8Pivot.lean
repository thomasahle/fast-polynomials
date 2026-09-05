import FastPoly.Examples.Char2Degree17SexticCancellation

/-!
# Q8, the normalized z10 / row-six pivot of the actual degree-17 circuit

The v gate's low-row inverse changes v by a multiple of its known cubic
factor. The shared-factor sextic identity then supplies the exact update
of the final reconstructed product, with no expansion through its inputs.
-/

namespace FastPoly.Char2Degree17Q8Pivot

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TriangularCoordinates Char2Degree17TerminalFrame
open Char2Degree17TerminalPivots Char2RecoveredProductUpdates
open Char2Degree17Q9Pivot

variable {R : Type*} [CommRing R] [CharP R 2]

structure BeforeV (q r : Vector R) : Prop where
  y : dy q = dy r
  z : dz q = dz r
  t : dt q = dt r
  u : du q = du r

theorem beforeV_congr (q r : Vector R)
    (he : ∀ i : Fin 17, i.val < 7 → q i = r i) : BeforeV q r := by
  have h0 := he 0 (by omega)
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  have h3 := he 3 (by omega)
  have h4 := he 4 (by omega)
  have h5 := he 5 (by omega)
  have h6 := he 6 (by omega)
  have hy : dy q = dy r := by rw [dy, dy, h0]
  have haz : az q = az r := by rw [az, az, hy, h1, h2]
  have hz : dz q = dz r := by rw [dz, dz, hy, haz]
  have haT : aT q = aT r := by rw [aT, aT, h0, h3, h4]
  have ht : dt q = dt r := by rw [dt, dt, h0, haT]
  have hau : au q = au r := by rw [au, au, hy, hz, ht, h5, h6]
  have hu : du q = du r := by rw [du, du, hy, hz, ht, hau]
  exact ⟨hy, hz, ht, hu⟩

theorem beforeV_shift8 (q : Vector R) (δ : R) : BeforeV (shift q 8 δ) q := by
  apply beforeV_congr
  intro i hi
  have hne : i ≠ (8 : Fin 17) := by
    intro h
    have hv := congrArg Fin.val h
    omega
  exact shift_other q 8 i δ hne

noncomputable def B (q : Vector R) : R[X] := X + dz q + C (av q).1

noncomputable def S6 (q : Vector R) : R[X] :=
  Char2Degree17SexticCancellation.sextic (dy q) (dz q) (dt q)
    (au q).1 (au q).2 (av q).1 (av q).2

theorem v_shift8 (q : Vector R) (δ : R) : dv (shift q 8 δ) = dv q + C δ * B q := by
  change recoveredGate (X + dz (shift q 8 δ))
    (X + dz (shift q 8 δ) + dt (shift q 8 δ) + du (shift q 8 δ)) 3 7
    (shift q 8 δ 7, shift q 8 δ 8) = _
  rw [(beforeV_shift8 q δ).z, (beforeV_shift8 q δ).t, (beforeV_shift8 q δ).u,
    shift_other q 8 7 δ (by omega), shift_self]
  exact low_update (X + dz q) (X + dz q + dt q + du q) 3 7 (q 7, q 8) δ

theorem h_shift8 (q : Vector R) (δ : R) : dh (shift q 8 δ) = dh q := by
  rw [dh, dh, (beforeV_shift8 q δ).y, shift_other q 8 9 δ (by omega)]

theorem j_shift8 (q : Vector R) (δ : R) : dj (shift q 8 δ) = dj q := by
  rw [dj, dj, aj, aj, (beforeV_shift8 q δ).y,
    shift_other q 8 10 δ (by omega), shift_other q 8 11 δ (by omega)]

theorem ell_shift8 (q : Vector R) (δ : R) : dell (shift q 8 δ) = dell q := by
  rw [dell, dell, al, al, h_shift8, (beforeV_shift8 q δ).t,
    shift_other q 8 12 δ (by omega), shift_other q 8 13 δ (by omega)]

theorem w_shift8 (q : Vector R) (δ : R) :
    dw (shift q 8 δ) =
      recoveredGate (X + du q) ((du q + dv q) + C δ * B q) 7 10 (q 14, q 15) := by
  change recoveredGate (X + du (shift q 8 δ))
    (du (shift q 8 δ) + dv (shift q 8 δ)) 7 10
    (shift q 8 δ 14, shift q 8 δ 15) = _
  rw [(beforeV_shift8 q δ).u, v_shift8,
    shift_other q 8 14 δ (by omega), shift_other q 8 15 δ (by omega), ← add_assoc]

theorem sextic_identity (q : Vector R) :
    (X + du q) * B q + (du q + dv q) = S6 q :=
  Char2Degree17SexticCancellation.crown_cancel (dy q) (dz q) (dt q) (du q) (dv q)
    (au q).1 (au q).2 (av q).1 (av q).2 rfl rfl

variable [Nontrivial R]

theorem frame_z_monic (q : Vector R) : IsMonicOfDegree (dz q) 3 := by
  simpa only [z_keys] using z_monic (keys q)

theorem B_monic (q : Vector R) : IsMonicOfDegree (B q) 3 :=
  shifted_monic (add_monic (isMonicOfDegree_X R) (frame_z_monic q) (by omega))
    (by omega) (av q).1

theorem S6_monic (q : Vector R) : IsMonicOfDegree (S6 q) 6 :=
  Char2Degree17SexticCancellation.sextic_monic (dy q) (dz q) (dt q)
    (au q).1 (au q).2 (av q).1 (av q).2
    (frame_y_monic q) (frame_z_monic q) (frame_t_monic q)

theorem outputQ_change8 (q : Vector R) (δ : R) :
    TopChange (outputQ q) (outputQ (shift q 8 δ)) 6 δ := by
  have hp := Char2Degree17SexticCancellation.reconstructed_change
    (X + du q) (du q + dv q) (B q) (S6 q) (q 14, q 15) δ
    (frame_lowerW_monic q) (B_monic q) (S6_monic q) (sextic_identity q)
  have hsum := (hp.add_left (dj q + dell q)).add_right (C (q 16))
  rw [outputQ_as_wires, outputQ_as_wires, j_shift8, ell_shift8, w_shift8,
    shift_other q 8 16 δ (by omega)]
  exact hsum

theorem qOfZ_shift10 (z : Vector R) (δ : R) :
    qOfZ (shift z 10 δ) = shift (qOfZ z) 8 δ := by
  funext j
  fin_cases j <;> rfl

/-- The ninth checked normalized output pivot: row six, coordinate z10. -/
theorem outputZ_change10 (z : Vector R) (δ : R) :
    TopChange (outputZ z) (outputZ (shift z 10 δ)) 6 δ := by
  change TopChange (outputQ (qOfZ z)) (outputQ (qOfZ (shift z 10 δ))) 6 δ
  rw [qOfZ_shift10]
  exact outputQ_change8 (qOfZ z) δ

end FastPoly.Char2Degree17Q8Pivot
