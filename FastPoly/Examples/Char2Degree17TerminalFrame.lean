import FastPoly.Examples.Char2Degree17TriangularCoordinates
import FastPoly.Examples.Char2RecoveredProductUpdates

/-!
# The fixed frame of the seven terminal degree-17 coordinates

The earlier ten Q-coordinates determine every input to the three terminal
products. Their seven remaining inputs are isolated in `terminal`. This
factorization permits local output updates without unfolding the core DAG.
-/

namespace FastPoly.Char2Degree17TerminalFrame

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2RecoveredProductUpdates

variable {R : Type*} [CommRing R] [CharP R 2]

def CoreEq (q r : Vector R) : Prop := ∀ i : Fin 17, i.val < 10 → q i = r i

structure SameFrame (q r : Vector R) : Prop where
  y : dy q = dy r
  z : dz q = dz r
  t : dt q = dt r
  u : du q = du r
  v : dv q = dv r
  h : dh q = dh r

theorem core_congr (q r : Vector R) (he : CoreEq q r) : SameFrame q r := by
  have h0 := he 0 (by omega)
  have h1 := he 1 (by omega)
  have h2 := he 2 (by omega)
  have h3 := he 3 (by omega)
  have h4 := he 4 (by omega)
  have h5 := he 5 (by omega)
  have h6 := he 6 (by omega)
  have h7 := he 7 (by omega)
  have h8 := he 8 (by omega)
  have h9 := he 9 (by omega)
  have hy : dy q = dy r := by rw [dy, dy, h0]
  have haz : az q = az r := by rw [az, az, hy, h1, h2]
  have hz : dz q = dz r := by rw [dz, dz, hy, haz]
  have haT : aT q = aT r := by rw [aT, aT, h0, h3, h4]
  have ht : dt q = dt r := by rw [dt, dt, h0, haT]
  have hau : au q = au r := by rw [au, au, hy, hz, ht, h5, h6]
  have hu : du q = du r := by rw [du, du, hy, hz, ht, hau]
  have hav : av q = av r := by rw [av, av, hz, ht, hu, h7, h8]
  have hv : dv q = dv r := by rw [dv, dv, hz, ht, hu, hav]
  have hh : dh q = dh r := by rw [dh, dh, hy, h9]
  exact ⟨hy, hz, ht, hu, hv, hh⟩

abbrev Tail (R : Type*) := Fin 7 → R

def tailIndex (i : Fin 7) : Fin 17 := ⟨i.val + 10, by omega⟩

def readTail (q : Vector R) : Tail R := fun i => q (tailIndex i)

noncomputable def terminal (q : Vector R) (c : Tail R) : R[X] :=
  recoveredGate X (dy q) 1 2 (c 0, c 1) +
    recoveredGate (dh q) (dt q) 3 4 (c 2, c 3) +
    recoveredGate (X + du q) (du q + dv q) 7 10 (c 4, c 5) + C (c 6)

theorem terminal_congr (q r : Vector R) (he : SameFrame q r) (c : Tail R) :
    terminal q c = terminal r c := by
  rw [terminal, terminal, he.y, he.h, he.t, he.u, he.v]

noncomputable def outputQ (q : Vector R) : R[X] := Char2Degree17Wires.output (keys q)

theorem outputQ_eq (q : Vector R) : outputQ q = terminal q (readTail q) := rfl

def shift {n : ℕ} (q : Fin n → R) (i : Fin n) (δ : R) : Fin n → R :=
  Function.update q i (q i + δ)

theorem shift_self {n : ℕ} (q : Fin n → R) (i : Fin n) (δ : R) :
    shift q i δ i = q i + δ := Function.update_self ..

theorem shift_other {n : ℕ} (q : Fin n → R) (i j : Fin n) (δ : R) (hji : j ≠ i) :
    shift q i δ j = q j := Function.update_of_ne hji ..

theorem shift_core (q : Vector R) (i : Fin 7) (δ : R) :
    CoreEq (shift q (tailIndex i) δ) q := by
  intro j hj
  have hji : j ≠ tailIndex i := by
    intro h
    have hv := congrArg Fin.val h
    simp only [tailIndex] at hv
    omega
  exact shift_other q (tailIndex i) j δ hji

theorem readTail_shift (q : Vector R) (i : Fin 7) (δ : R) :
    readTail (shift q (tailIndex i) δ) = shift (readTail q) i δ := by
  funext j
  by_cases hji : j = i
  · subst j
    exact (shift_self q (tailIndex i) δ).trans (shift_self (readTail q) i δ).symm
  · have ht : tailIndex j ≠ tailIndex i := by
      intro h
      apply hji
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [tailIndex] at hv
      omega
    exact (shift_other q (tailIndex i) (tailIndex j) δ ht).trans
      (shift_other (readTail q) i j δ hji).symm

/-- A terminal-coordinate update freezes the whole preceding circuit frame. -/
theorem outputQ_shift (q : Vector R) (i : Fin 7) (δ : R) :
    outputQ (shift q (tailIndex i) δ) = terminal q (shift (readTail q) i δ) := by
  rw [outputQ_eq, terminal_congr _ q (core_congr _ q (shift_core q i δ)), readTail_shift]

end FastPoly.Char2Degree17TerminalFrame
