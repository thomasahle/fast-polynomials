import FastPoly.Examples.Char2Degree17TerminalFrame

/-!
# Seven terminal pivots of the actual normalized degree-17 output

Only one of the final three products (or the final scalar) changes. Each
proof uses its supplied two-row inverse and an opaque-factor degree bound.
`outputZ_change` covers Q10,Q11,Q12,Q13,Q14,Q15,Q16, in the actual S/R/E order.
The ten preceding coefficient pivots remain separate obligations.
-/

namespace FastPoly.Char2Degree17TerminalPivots

set_option maxHeartbeats 20000

open Polynomial Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TriangularCoordinates Char2Degree17TerminalFrame
open Char2RecoveredProductUpdates

variable {R : Type*} [CommRing R] [CharP R 2]

/-- A specified coefficient changes by delta; every higher row is preserved. -/
structure TopChange (p p' : R[X]) (d : ℕ) (δ : R) : Prop where
  row : p'.coeff d = p.coeff d + δ
  above : ∀ j, d < j → p'.coeff j = p.coeff j

theorem TopChange.add_left {p p' : R[X]} {d : ℕ} {δ : R}
    (h : TopChange p p' d δ) (r : R[X]) : TopChange (r + p) (r + p') d δ := by
  constructor
  · rw [coeff_add, coeff_add, h.row, add_assoc]
  · intro j hj
    rw [coeff_add, coeff_add, h.above j hj]

theorem TopChange.add_right {p p' : R[X]} {d : ℕ} {δ : R}
    (h : TopChange p p' d δ) (r : R[X]) : TopChange (p + r) (p' + r) d δ := by
  constructor
  · rw [coeff_add, coeff_add, h.row, add_right_comm]
  · intro j hj
    rw [coeff_add, coeff_add, h.above j hj]

theorem constant_change (a δ : R) : TopChange (C a) (C (a + δ)) 0 δ := by
  constructor
  · rw [coeff_C_zero, coeff_C_zero]
  · intro j hj
    have h0 : j ≠ 0 := by omega
    simp only [coeff_C, h0, ite_false]

theorem product_high_change (lower higher : R[X]) (dl dh : ℕ) (q : R × R) (δ : R)
    (hl : IsMonicOfDegree lower dl) (hh : IsMonicOfDegree higher dh)
    (hpos : 0 < dl) (hlt : dl < dh) :
    TopChange (recoveredGate lower higher dl dh q)
      (recoveredGate lower higher dl dh (q.1 + δ, q.2)) dh δ := by
  constructor
  · rw [high_row lower higher dl dh _ hl hh hpos hlt,
      high_row lower higher dl dh q hl hh hpos hlt]
  · intro j hj
    have hjpos : 0 < j := by omega
    have hlj : lower.natDegree < j := by rw [hl.natDegree_eq]; omega
    have hhj : higher.natDegree < j := by rw [hh.natDegree_eq]; exact hj
    exact high_update_above lower higher dl dh q δ j hjpos hlj hhj

theorem product_low_change (lower higher : R[X]) (dl dh : ℕ) (q : R × R) (δ : R)
    (hl : IsMonicOfDegree lower dl) (hh : IsMonicOfDegree higher dh)
    (hpos : 0 < dl) (hlt : dl < dh) :
    TopChange (recoveredGate lower higher dl dh q)
      (recoveredGate lower higher dl dh (q.1, q.2 + δ)) dl δ := by
  constructor
  · rw [low_row lower higher dl dh _ hl hh hpos hlt,
      low_row lower higher dl dh q hl hh hpos hlt]
  · intro j hj
    have hjpos : 0 < j := by omega
    have hlj : lower.natDegree < j := by rw [hl.natDegree_eq]; exact hj
    exact low_update_above lower higher dl dh q δ j hjpos hlj

/-- Q10,...,Q16 are read at these output rows. -/
def pivotDegree (i : Fin 7) : ℕ :=
  match i.val with
  | 0 => 2
  | 1 => 1
  | 2 => 4
  | 3 => 3
  | 4 => 10
  | 5 => 7
  | _ => 0

variable [Nontrivial R]

noncomputable def terminalJ (q : Vector R) (c : Tail R) : R[X] :=
  recoveredGate X (dy q) 1 2 (c 0, c 1)

noncomputable def terminalL (q : Vector R) (c : Tail R) : R[X] :=
  recoveredGate (dh q) (dt q) 3 4 (c 2, c 3)

noncomputable def terminalW (q : Vector R) (c : Tail R) : R[X] :=
  recoveredGate (X + du q) (du q + dv q) 7 10 (c 4, c 5)

theorem frame_y_monic (q : Vector R) : IsMonicOfDegree (dy q) 2 := by
  simpa only [y_keys] using y_monic (keys q)

theorem frame_h_monic (q : Vector R) : IsMonicOfDegree (dh q) 3 := by
  simpa only [h_keys] using h_monic (keys q)

theorem frame_t_monic (q : Vector R) : IsMonicOfDegree (dt q) 4 := by
  simpa only [t_keys] using t_monic (keys q)

theorem frame_lowerW_monic (q : Vector R) : IsMonicOfDegree (X + du q) 7 := by
  simpa only [u_keys] using lowerW_monic (keys q)

theorem frame_higherW_monic (q : Vector R) : IsMonicOfDegree (du q + dv q) 10 := by
  simpa only [u_keys, v_keys] using higherW_monic (keys q)

theorem terminal_change0 (q : Vector R) (c : Tail R) (δ : R) :
    TopChange (terminal q c) (terminal q (shift c 0 δ)) 2 δ := by
  exact (((product_high_change X (dy q) 1 2 (c 0, c 1) δ
    (isMonicOfDegree_X R) (frame_y_monic q) (by omega) (by omega)).add_right
      (terminalL q c)).add_right (terminalW q c)).add_right (C (c 6))

theorem terminal_change1 (q : Vector R) (c : Tail R) (δ : R) :
    TopChange (terminal q c) (terminal q (shift c 1 δ)) 1 δ := by
  exact (((product_low_change X (dy q) 1 2 (c 0, c 1) δ
    (isMonicOfDegree_X R) (frame_y_monic q) (by omega) (by omega)).add_right
      (terminalL q c)).add_right (terminalW q c)).add_right (C (c 6))

theorem terminal_change2 (q : Vector R) (c : Tail R) (δ : R) :
    TopChange (terminal q c) (terminal q (shift c 2 δ)) 4 δ := by
  exact (((product_high_change (dh q) (dt q) 3 4 (c 2, c 3) δ
    (frame_h_monic q) (frame_t_monic q) (by omega) (by omega)).add_left
      (terminalJ q c)).add_right (terminalW q c)).add_right (C (c 6))

theorem terminal_change3 (q : Vector R) (c : Tail R) (δ : R) :
    TopChange (terminal q c) (terminal q (shift c 3 δ)) 3 δ := by
  exact (((product_low_change (dh q) (dt q) 3 4 (c 2, c 3) δ
    (frame_h_monic q) (frame_t_monic q) (by omega) (by omega)).add_left
      (terminalJ q c)).add_right (terminalW q c)).add_right (C (c 6))

theorem terminal_change4 (q : Vector R) (c : Tail R) (δ : R) :
    TopChange (terminal q c) (terminal q (shift c 4 δ)) 10 δ := by
  exact ((product_high_change (X + du q) (du q + dv q) 7 10 (c 4, c 5) δ
    (frame_lowerW_monic q) (frame_higherW_monic q) (by omega) (by omega)).add_left
      (terminalJ q c + terminalL q c)).add_right (C (c 6))

theorem terminal_change5 (q : Vector R) (c : Tail R) (δ : R) :
    TopChange (terminal q c) (terminal q (shift c 5 δ)) 7 δ := by
  exact ((product_low_change (X + du q) (du q + dv q) 7 10 (c 4, c 5) δ
    (frame_lowerW_monic q) (frame_higherW_monic q) (by omega) (by omega)).add_left
      (terminalJ q c + terminalL q c)).add_right (C (c 6))

theorem terminal_change6 (q : Vector R) (c : Tail R) (δ : R) :
    TopChange (terminal q c) (terminal q (shift c 6 δ)) 0 δ := by
  exact (constant_change (c 6) δ).add_left (terminalJ q c + terminalL q c + terminalW q c)

theorem terminal_change (q : Vector R) (c : Tail R) (i : Fin 7) (δ : R) :
    TopChange (terminal q c) (terminal q (shift c i δ)) (pivotDegree i) δ := by
  fin_cases i
  · exact terminal_change0 q c δ
  · exact terminal_change1 q c δ
  · exact terminal_change2 q c δ
  · exact terminal_change3 q c δ
  · exact terminal_change4 q c δ
  · exact terminal_change5 q c δ
  · exact terminal_change6 q c δ

/-- Positions of Q10,...,Q16 in the supplied S/R/E decoder order. -/
def zIndex (i : Fin 7) : Fin 17 :=
  match i.val with
  | 0 => 14
  | 1 => 15
  | 2 => 12
  | 3 => 13
  | 4 => 6
  | 5 => 9
  | _ => 16

theorem qOfZ_shift0 (z : Vector R) (δ : R) :
    qOfZ (shift z 14 δ) = shift (qOfZ z) 10 δ := by
  funext j
  fin_cases j <;> rfl

theorem qOfZ_shift1 (z : Vector R) (δ : R) :
    qOfZ (shift z 15 δ) = shift (qOfZ z) 11 δ := by
  funext j
  fin_cases j <;> rfl

theorem qOfZ_shift2 (z : Vector R) (δ : R) :
    qOfZ (shift z 12 δ) = shift (qOfZ z) 12 δ := by
  funext j
  fin_cases j <;> rfl

theorem qOfZ_shift3 (z : Vector R) (δ : R) :
    qOfZ (shift z 13 δ) = shift (qOfZ z) 13 δ := by
  funext j
  fin_cases j <;> rfl

theorem qOfZ_shift4 (z : Vector R) (δ : R) :
    qOfZ (shift z 6 δ) = shift (qOfZ z) 14 δ := by
  funext j
  fin_cases j <;> rfl

theorem qOfZ_shift5 (z : Vector R) (δ : R) :
    qOfZ (shift z 9 δ) = shift (qOfZ z) 15 δ := by
  funext j
  fin_cases j <;> rfl

theorem qOfZ_shift6 (z : Vector R) (δ : R) :
    qOfZ (shift z 16 δ) = shift (qOfZ z) 16 δ := by
  funext j
  fin_cases j <;> rfl

theorem qOfZ_shift (z : Vector R) (i : Fin 7) (δ : R) :
    qOfZ (shift z (zIndex i) δ) = shift (qOfZ z) (tailIndex i) δ := by
  fin_cases i
  · exact qOfZ_shift0 z δ
  · exact qOfZ_shift1 z δ
  · exact qOfZ_shift2 z δ
  · exact qOfZ_shift3 z δ
  · exact qOfZ_shift4 z δ
  · exact qOfZ_shift5 z δ
  · exact qOfZ_shift6 z δ

/-- The actual circuit, with its explicitly decoded raw offsets installed. -/
noncomputable def outputZ (z : Vector R) : R[X] :=
  Char2Degree17Wires.output (keys (qOfZ z))

/-- Seven local output unit pivots, including all corresponding higher-row
invariance statements, after the supplied S/R/E coordinate normalization. -/
theorem outputZ_change (z : Vector R) (i : Fin 7) (δ : R) :
    TopChange (outputZ z) (outputZ (shift z (zIndex i) δ)) (pivotDegree i) δ := by
  change TopChange (outputQ (qOfZ z))
    (outputQ (qOfZ (shift z (zIndex i) δ))) (pivotDegree i) δ
  rw [qOfZ_shift, outputQ_shift, outputQ_eq]
  exact terminal_change (qOfZ z) (readTail (qOfZ z)) i δ

end FastPoly.Char2Degree17TerminalPivots
