import FastPoly.Examples.Char2Degree17EllPerturbation

/-!
# The Q9 (normalized z11) unit pivot of the actual degree-17 output

Changing Q9 affects only the cubic h and the terminal ell gate. The earlier
wires are preserved by named congruences. The ell gate uses the supplied
two-row inverse with its explicit compensating offset shifts.
-/

namespace FastPoly.Char2Degree17Q9Pivot

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TriangularCoordinates Char2Degree17TerminalFrame
open Char2Degree17TerminalPivots Char2RecoveredProductUpdates

variable {R : Type*} [CommRing R] [CharP R 2]

structure SameUpper (q r : Vector R) : Prop where
  y : dy q = dy r
  z : dz q = dz r
  t : dt q = dt r
  u : du q = du r
  v : dv q = dv r

theorem upper_congr (q r : Vector R)
    (he : ∀ i : Fin 17, i.val < 9 → q i = r i) : SameUpper q r := by
  have h0 := he 0 (by omega)
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  have h3 := he 3 (by omega)
  have h4 := he 4 (by omega)
  have h5 := he 5 (by omega)
  have h6 := he 6 (by omega)
  have h7 := he 7 (by omega)
  have h8 := he 8 (by omega)
  have hy : dy q = dy r := by rw [dy, dy, h0]
  have haz : az q = az r := by rw [az, az, hy, h1, h2]
  have hz : dz q = dz r := by rw [dz, dz, hy, haz]
  have haT : aT q = aT r := by rw [aT, aT, h0, h3, h4]
  have ht : dt q = dt r := by rw [dt, dt, h0, haT]
  have hau : au q = au r := by rw [au, au, hy, hz, ht, h5, h6]
  have hu : du q = du r := by rw [du, du, hy, hz, ht, hau]
  have hav : av q = av r := by rw [av, av, hz, ht, hu, h7, h8]
  have hv : dv q = dv r := by rw [dv, dv, hz, ht, hu, hav]
  exact ⟨hy, hz, ht, hu, hv⟩

theorem upper_shift9 (q : Vector R) (δ : R) : SameUpper (shift q 9 δ) q := by
  apply upper_congr
  intro i hi
  have hne : i ≠ (9 : Fin 17) := by
    intro h
    have hv := congrArg Fin.val h
    omega
  exact shift_other q 9 i δ hne

theorem h_shift9 (q : Vector R) (δ : R) :
    dh (shift q 9 δ) = dh q + C δ * X := by
  rw [dh, dh, (upper_shift9 q δ).y, shift_self]
  simp only [map_add]
  ring

theorem j_shift9 (q : Vector R) (δ : R) : dj (shift q 9 δ) = dj q := by
  rw [dj, dj, aj, aj, (upper_shift9 q δ).y,
    shift_other q 9 10 δ (by omega), shift_other q 9 11 δ (by omega)]

theorem ell_shift9 (q : Vector R) (δ : R) :
    dell (shift q 9 δ) =
      recoveredGate (dh q + C δ * X) (dt q) 3 4 (q 12, q 13) := by
  change recoveredGate (dh (shift q 9 δ)) (dt (shift q 9 δ)) 3 4
    (shift q 9 δ 12, shift q 9 δ 13) = _
  rw [h_shift9, (upper_shift9 q δ).t,
    shift_other q 9 12 δ (by omega), shift_other q 9 13 δ (by omega)]

theorem w_shift9 (q : Vector R) (δ : R) : dw (shift q 9 δ) = dw q := by
  rw [dw, dw, aw, aw, (upper_shift9 q δ).u, (upper_shift9 q δ).v,
    shift_other q 9 14 δ (by omega), shift_other q 9 15 δ (by omega)]

theorem t_coeff_three (q : Vector R) : (dt q).coeff 3 = 1 := by
  have h34 : (3 : ℕ) ≠ 4 := by omega
  have h32 : (3 : ℕ) ≠ 2 := by omega
  have h31 : (3 : ℕ) ≠ 1 := by omega
  have h30 : (3 : ℕ) ≠ 0 := by omega
  simp only [dt, Char2Degree17QuadraticOffsets.gate_form, coeff_add,
    coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
    h34, h32, h31, h30, ite_true, ite_false, add_zero, zero_add,
    CharTwo.add_self_eq_zero]

theorem outputQ_as_wires (q : Vector R) :
    outputQ q = dj q + dell q + dw q + C (q 16) := rfl

variable [Nontrivial R]

theorem t_coeff_two (q : Vector R) : (dt q).coeff 2 = q 3 :=
  congrArg Prod.fst (t_rows q)

theorem outputQ_change9 (q : Vector R) (δ : R) :
    TopChange (outputQ q) (outputQ (shift q 9 δ)) 5 δ := by
  have hp := Char2Degree17EllPerturbation.gate_change (dh q) (dt q) (q 12, q 13)
    δ (q 3) (frame_h_monic q) (frame_t_monic q) (t_coeff_three q) (t_coeff_two q)
  have hsum := ((hp.add_left (dj q)).add_right (dw q)).add_right (C (q 16))
  rw [outputQ_as_wires, outputQ_as_wires, j_shift9, ell_shift9, w_shift9,
    shift_other q 9 16 δ (by omega)]
  exact hsum

theorem qOfZ_shift11 (z : Vector R) (δ : R) :
    qOfZ (shift z 11 δ) = shift (qOfZ z) 9 δ := by
  funext j
  fin_cases j <;> rfl

/-- The eighth checked normalized output pivot: row five, coordinate z11. -/
theorem outputZ_change11 (z : Vector R) (δ : R) :
    TopChange (outputZ z) (outputZ (shift z 11 δ)) 5 δ := by
  change TopChange (outputQ (qOfZ z)) (outputQ (qOfZ (shift z 11 δ))) 5 δ
  rw [qOfZ_shift11]
  exact outputQ_change9 (qOfZ z) δ

end FastPoly.Char2Degree17Q9Pivot
