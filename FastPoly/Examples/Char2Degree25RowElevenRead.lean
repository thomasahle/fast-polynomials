import FastPoly.Examples.Char2Degree25HeadChange
import FastPoly.Examples.Char2Degree25MiddleFrame

/-! Read only row eleven under the supplied final-coordinate corrections.
All shared gates stay fixed and named. Only the two degree-six terms in the
j difference contribute: the raw a20 change and the raw a17 change. -/

namespace FastPoly.Char2Degree25RowElevenRead

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
open Char2Degree25MiddleFrame (DifferenceBound constant_bound same_bound)
open Char2Degree25TwentyTwoWires (E)

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

structure SameFixed (a b : ℕ → R) : Prop where
  h0 : b 0 = a 0
  h1 : b 1 = a 1
  h2 : b 2 = a 2
  h3 : b 3 = a 3
  h4 : b 4 = a 4
  h5 : b 5 = a 5
  h6 : b 6 = a 6
  h7 : b 7 = a 7
  h8 : b 8 = a 8
  h9 : b 9 = a 9
  h12 : b 12 = a 12
  h13 : b 13 = a 13
  h14 : b 14 = a 14
  h16 : b 16 = a 16
  h18 : b 18 = a 18
  h23 : b 23 = a 23
  h24 : b 24 = a 24

variable {a b : ℕ → R}

theorem SameFixed.z_eq (he : SameFixed a b) : z b = z a := by
  simp only [z, he.h0, he.h1]
theorem SameFixed.t_eq (he : SameFixed a b) : t b = t a := by
  simp only [t, he.z_eq, he.h2, he.h3]
theorem SameFixed.u_eq (he : SameFixed a b) : u b = u a := by
  simp only [u, he.z_eq, he.t_eq, he.h4, he.h5]
theorem SameFixed.v_eq (he : SameFixed a b) : v b = v a := by
  simp only [v, he.z_eq, he.h6, he.h7]
theorem SameFixed.w_eq (he : SameFixed a b) : w b = w a := by
  simp only [w, he.z_eq, he.v_eq, he.h8, he.h9]
theorem SameFixed.r_eq (he : SameFixed a b) : r b = r a := by
  simp only [r, he.t_eq, he.u_eq, he.h12, he.h13]
theorem SameFixed.hLeft_eq (he : SameFixed a b) : hLeft b = hLeft a := by
  simp only [hLeft, he.z_eq, he.t_eq, he.h18]
theorem SameFixed.nRight_eq (he : SameFixed a b) : nRight b = nRight a := by
  simp only [nRight, he.t_eq, he.h23]

private theorem common_add (p x y : R[X]) : (p + x) + (p + y) = x + y := by
  rw [add_add_add_comm, CharTwo.add_self_eq_zero, zero_add]

theorem SameFixed.ell_difference (he : SameFixed a b) :
    ell b + ell a = C (b 17 + a 17) * E a := by
  unfold ell
  rw [he.h16, he.z_eq, he.v_eq, ← mul_add, common_add, ← map_add, mul_comm]
  rfl

theorem SameFixed.head_change (he : SameFixed a b) :
    Char2Degree25Frame.head b + Char2Degree25Frame.head a =
      C (b 17 + a 17) * (X + C (a 16)) := by
  unfold Char2Degree25Frame.head
  rw [he.z_eq, he.u_eq, common_add, he.ell_difference]
  rfl

private theorem Cmul_degree (c : R) {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    (C c * p).natDegree ≤ n := by
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add]
  exact hp

theorem SameFixed.ell_bound (he : SameFixed a b) : DifferenceBound (ell a) (ell b) 1 := by
  change (ell b + ell a).natDegree ≤ 1
  rw [he.ell_difference]
  exact Cmul_degree _ (Char2Degree25TerminalHead.E_monic a).natDegree_eq.le

theorem SameFixed.s_bound (he : SameFixed a b) : DifferenceBound (s a) (s b) 5 := by
  unfold s
  rw [he.z_eq, he.v_eq]
  have hl : DifferenceBound (z a + C (a 10)) (z a + C (b 10)) 0 :=
    (constant_bound (a 10) (b 10) 0).add_left (z a)
  have hr : DifferenceBound (v a + C (a 11)) (v a + C (b 11)) 0 :=
    (constant_bound (a 11) (b 11) 0).add_left (v a)
  have hld : (z a + C (a 10)).natDegree ≤ 4 :=
    natDegree_add_le_of_degree_le (z_monic a).natDegree_eq.le (by rw [natDegree_C]; omega)
  have hrd : (v a + C (b 11)).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le (v_monic a).natDegree_eq.le (by rw [natDegree_C]; omega)
  exact hl.mul hr hld hrd

theorem SameFixed.g_bound (he : SameFixed a b) : DifferenceBound (g a) (g b) 5 := by
  unfold g
  rw [he.z_eq, he.t_eq, he.u_eq, he.h14]
  have hr : DifferenceBound (X + u a + C (a 15)) (X + u a + C (b 15)) 0 :=
    (constant_bound (a 15) (b 15) 0).add_left (X + u a)
  have hd : (z a + t a + C (a 14)).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le (z_add_t_monic a).natDegree_eq.le
      (by rw [natDegree_C]; omega)
  exact hr.mul_left _ hd

theorem SameFixed.h_bound (he : SameFixed a b) : DifferenceBound (h a) (h b) 5 := by
  unfold Char2Degree25Frame.h
  rw [he.hLeft_eq]
  have hr : DifferenceBound (hRight a) (hRight b) 0 := by
    unfold hRight
    rw [he.z_eq, he.u_eq, he.v_eq, he.w_eq, he.r_eq]
    exact (constant_bound (a 19) (b 19) 0).add_left _
  exact hr.mul_left _ (hLeft_monic a).natDegree_eq.le

private theorem products_difference (p p' q q' : R[X]) :
    p' * q' + p * q = (p' + p) * q' + p * (q' + q) := by
  rw [add_mul, mul_add]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem SameFixed.jLeft_difference (he : SameFixed a b) :
    jLeft b + jLeft a = C (b 20 + a 20) := by
  unfold jLeft
  rw [he.t_eq, common_add, map_add]

noncomputable def rightDifference (a b : ℕ → R) : R[X] :=
  C (b 17 + a 17) * E a + C (b 21 + a 21)

theorem SameFixed.j_difference (he : SameFixed a b) :
    j b + j a = C (b 20 + a 20) * (ell b + C (b 21)) +
      jLeft a * rightDifference a b := by
  unfold j
  rw [products_difference, he.jLeft_difference, add_add_add_comm (ell b),
    he.ell_difference, ← map_add]
  rfl

theorem rightDifference_bound (a b : ℕ → R) : (rightDifference a b).natDegree ≤ 1 :=
  natDegree_add_le_of_degree_le
    (Cmul_degree _ (Char2Degree25TerminalHead.E_monic a).natDegree_eq.le)
    (by rw [natDegree_C]; omega)

theorem rightDifference_one (a b : ℕ → R) : (rightDifference a b).coeff 1 = b 17 + a 17 := by
  have hc : (E a).coeff 1 = 1 := by
    rw [← (Char2Degree25TerminalHead.E_monic a).natDegree_eq]
    exact (Char2Degree25TerminalHead.E_monic a).monic.coeff_natDegree
  simp only [rightDifference, coeff_add, coeff_C_mul, coeff_C_succ, hc, mul_one, add_zero]

theorem SameFixed.j_bound (he : SameFixed a b) : DifferenceBound (j a) (j b) 6 := by
  change (j b + j a).natDegree ≤ 6
  rw [he.j_difference]
  have hright : (ell b + C (b 21)).natDegree ≤ 6 :=
    natDegree_add_le_of_degree_le (ell_monic b).natDegree_eq.le (by rw [natDegree_C]; omega)
  have hprod : (jLeft a * rightDifference a b).natDegree ≤ 6 :=
    natDegree_mul_le.trans (Nat.add_le_add (jLeft_monic a).natDegree_eq.le (rightDifference_bound a b))
  exact natDegree_add_le_of_degree_le (Cmul_degree _ hright) hprod

theorem SameFixed.j_six (he : SameFixed a b) :
    (j b + j a).coeff 6 = (b 20 + a 20) + (b 17 + a 17) := by
  have hel : (ell b + C (b 21)).coeff 6 = 1 := by
    have hc : (ell b).coeff 6 = 1 := by
      rw [← (ell_monic b).natDegree_eq]
      exact (ell_monic b).monic.coeff_natDegree
    rw [coeff_add, hc, coeff_C_succ, add_zero]
  have hj : (jLeft a).coeff 5 = 1 := by
    rw [← (jLeft_monic a).natDegree_eq]
    exact (jLeft_monic a).monic.coeff_natDegree
  rw [he.j_difference, coeff_add, coeff_C_mul, hel, mul_one,
    coeff_mul_add_eq_of_natDegree_le (jLeft_monic a).natDegree_eq.le (rightDifference_bound a b),
    hj, rightDifference_one, one_mul]

noncomputable def beforeJ (a : ℕ → R) : R[X] :=
  X + t a + u a + s a + r a + g a + ell a + h a

theorem SameFixed.beforeJ_bound (he : SameFixed a b) : DifferenceBound (beforeJ a) (beforeJ b) 5 := by
  unfold beforeJ
  rw [he.t_eq, he.u_eq, he.r_eq]
  exact ((((he.s_bound.add_left (X + t a + u a)).add_right (r a)).add he.g_bound).add
    (he.ell_bound.mono (by omega))).add he.h_bound

theorem SameFixed.nLeft_bound (he : SameFixed a b) : DifferenceBound (nLeft a) (nLeft b) 6 :=
  ((he.beforeJ_bound.mono (by omega)).add he.j_bound).add (constant_bound _ _ 6)

theorem SameFixed.nLeft_six (he : SameFixed a b) :
    (nLeft b + nLeft a).coeff 6 = (b 20 + a 20) + (b 17 + a 17) := by
  have hz : (beforeJ b + beforeJ a).coeff 6 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.beforeJ_bound.trans_lt (by omega))
  change ((beforeJ b + j b + C (b 22)) + (beforeJ a + j a + C (a 22))).coeff 6 = _
  rw [add_add_add_comm (beforeJ b + j b), add_add_add_comm (beforeJ b),
    coeff_add, coeff_add, hz, he.j_six, coeff_add, coeff_C_succ, coeff_C_succ,
    zero_add, zero_add, add_zero]

theorem SameFixed.output_row11 (he : SameFixed a b) :
    (Char2Degree25Frame.output b + Char2Degree25Frame.output a).coeff 11 =
      (b 20 + a 20) + (b 17 + a 17) := by
  have hh : (Char2Degree25Frame.head b + Char2Degree25Frame.head a).natDegree ≤ 1 := by
    rw [he.head_change]
    exact Cmul_degree _ (isMonicOfDegree_X_add_one (a 16)).natDegree_eq.le
  have hz : (Char2Degree25Frame.head b + Char2Degree25Frame.head a).coeff 11 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hh.trans_lt (by omega))
  have hn : (nRight a).coeff 5 = 1 := by
    rw [← (nRight_monic a).natDegree_eq]
    exact (nRight_monic a).monic.coeff_natDegree
  rw [Char2Degree25HeadChange.output_difference he.nRight_eq he.h24,
    coeff_add, hz, zero_add,
    coeff_mul_add_eq_of_natDegree_le (nRight_monic a).natDegree_eq.le he.nLeft_bound,
    hn, one_mul, he.nLeft_six]

theorem SameFixed.offset17_eq (he : SameFixed a b) (d : R)
    (h20 : b 20 = a 20 + d)
    (hrow : (Char2Degree25Frame.output b + Char2Degree25Frame.output a).coeff 11 = 0) :
    b 17 = a 17 + d := by
  rw [he.output_row11, h20, Char2Decoder.cancel_tail] at hrow
  have hp : d = b 17 + a 17 := CharTwo.add_eq_zero.mp hrow
  rw [hp, add_comm (b 17) (a 17), CharTwo.add_cancel_left]

end FastPoly.Char2Degree25RowElevenRead
