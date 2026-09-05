import FastPoly.Examples.Char2Degree15FastCore

/-! Named wires of the existing seven-product degree-thirteen circuit.
The normalized keys preserve the active generated/website choice a4=q8+q9;
the appendix verifier's alternative a4=q9 is not substituted. The final
R*v+S*w expression remains a sum of opaque named products. -/

namespace FastPoly.Char2Degree13Fast

set_option maxHeartbeats 20000

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

abbrev Keys (R : Type*) := Fin 13 → R

/-- The active coordinate map, in the original raw-offset order. -/
def keys (q : Keys R) : ℕ → R
  | 0 => q 12
  | 1 => q 6
  | 2 => q 11
  | 3 => q 8
  | 4 => q 8 + q 9
  | 5 => q 0
  | 6 => q 10
  | 7 => q 7
  | 8 => q 4
  | 9 => q 3
  | 10 => q 5
  | 11 => q 1 + q 2
  | 12 => q 2
  | _ => 0

noncomputable def y : R[X] := X ^ 2
noncomputable def z (q : Keys R) : R[X] :=
  (X + y + C (q 2)) * (y + C (q 1 + q 2))
noncomputable def aFactor (q : Keys R) : R[X] := y + z q
noncomputable def bFactor (q : Keys R) : R[X] := z q + C (q 3)
noncomputable def w (q : Keys R) : R[X] := (aFactor q + C (q 5)) * bFactor q
noncomputable def v (q : Keys R) : R[X] :=
  (aFactor q + C (q 4)) * (w q + C (q 7))
noncomputable def u (q : Keys R) : R[X] :=
  (z q + v q + C (q 10)) * (X + C (q 0))
noncomputable def t (q : Keys R) : R[X] :=
  (X + y + C (q 8 + q 9)) * (X + C (q 8))
noncomputable def sFactor (q : Keys R) : R[X] := y + C (q 6)
noncomputable def s (q : Keys R) : R[X] :=
  (w q + t q + C (q 11)) * sFactor q
noncomputable def output (q : Keys R) : R[X] := u q + v q + s q + C (q 12)

/-- The linear coefficient of the degree-twelve branch after combining u+v. -/
noncomputable def rFactor (q : Keys R) : R[X] := X + C (q 0 + 1)
noncomputable def low (q : Keys R) : R[X] :=
  (X + C (q 0)) * (z q + C (q 10)) +
    sFactor q * (t q + C (q 11)) + C (q 12)

/-- The common factor in the q3 and q5 changes. -/
noncomputable def cFactor (q : Keys R) : R[X] :=
  rFactor q * (aFactor q + C (q 4)) + sFactor q

private theorem frame_identity (x y z w v t a b c d e : R[X]) :
    (z + v + c) * (x + a) + v + (w + t + d) * (y + b) + e =
      (x + (a + 1)) * v + (y + b) * w +
        ((x + a) * (z + c) + (y + b) * (t + d) + e) := by ring

theorem output_split (q : Keys R) :
    output q = rFactor q * v q + sFactor q * w q + low q := by
  unfold output u s rFactor sFactor low
  rw [map_add, map_one]
  exact frame_identity X y (z q) (w q) (v q) (t q)
    (C (q 0)) (C (q 6)) (C (q 10)) (C (q 11)) (C (q 12))

variable [Nontrivial R]

theorem y_monic : IsMonicOfDegree (y : R[X]) 2 := isMonicOfDegree_X_pow R 2

theorem z_monic (q : Keys R) : IsMonicOfDegree (z q) 4 :=
  ((y_monic.add_left (natDegree_X_le.trans_lt (by omega))).add_right
    (Char2Degree15Fast.const_lt (q 2) 2 (by omega))).mul
    (y_monic.add_right (Char2Degree15Fast.const_lt (q 1 + q 2) 2 (by omega)))

theorem aFactor_monic (q : Keys R) : IsMonicOfDegree (aFactor q) 4 :=
  (z_monic q).add_left ((y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 4))

theorem bFactor_monic (q : Keys R) : IsMonicOfDegree (bFactor q) 4 :=
  (z_monic q).add_right (Char2Degree15Fast.const_lt (q 3) 4 (by omega))

theorem w_monic (q : Keys R) : IsMonicOfDegree (w q) 8 :=
  ((aFactor_monic q).add_right (Char2Degree15Fast.const_lt (q 5) 4 (by omega))).mul
    (bFactor_monic q)

theorem v_monic (q : Keys R) : IsMonicOfDegree (v q) 12 :=
  ((aFactor_monic q).add_right (Char2Degree15Fast.const_lt (q 4) 4 (by omega))).mul
    ((w_monic q).add_right (Char2Degree15Fast.const_lt (q 7) 8 (by omega)))

theorem u_monic (q : Keys R) : IsMonicOfDegree (u q) 13 :=
  (((v_monic q).add_left ((z_monic q).natDegree_eq ▸ (by omega : 4 < 12))).add_right
    (Char2Degree15Fast.const_lt (q 10) 12 (by omega))).mul
    (isMonicOfDegree_X_add_one (q 0))

theorem t_monic (q : Keys R) : IsMonicOfDegree (t q) 3 :=
  ((y_monic.add_left (natDegree_X_le.trans_lt (by omega))).add_right
    (Char2Degree15Fast.const_lt (q 8 + q 9) 2 (by omega))).mul
    (isMonicOfDegree_X_add_one (q 8))

theorem rFactor_monic (q : Keys R) : IsMonicOfDegree (rFactor q) 1 :=
  isMonicOfDegree_X_add_one (q 0 + 1)

theorem sFactor_monic (q : Keys R) : IsMonicOfDegree (sFactor q) 2 :=
  y_monic.add_right (Char2Degree15Fast.const_lt (q 6) 2 (by omega))

theorem s_monic (q : Keys R) : IsMonicOfDegree (s q) 10 :=
  (((w_monic q).add_right ((t_monic q).natDegree_eq ▸ (by omega : 3 < 8))).add_right
    (Char2Degree15Fast.const_lt (q 11) 8 (by omega))).mul (sFactor_monic q)

theorem cFactor_monic (q : Keys R) : IsMonicOfDegree (cFactor q) 5 :=
  ((rFactor_monic q).mul
    ((aFactor_monic q).add_right (Char2Degree15Fast.const_lt (q 4) 4 (by omega)))).add_right
      ((sFactor_monic q).natDegree_eq ▸ (by omega : 2 < 5))

theorem low_degree (q : Keys R) : (low q).natDegree ≤ 5 := by
  have hz : IsMonicOfDegree (z q + C (q 10)) 4 :=
    (z_monic q).add_right (Char2Degree15Fast.const_lt (q 10) 4 (by omega))
  have ht : IsMonicOfDegree (t q + C (q 11)) 3 :=
    (t_monic q).add_right (Char2Degree15Fast.const_lt (q 11) 3 (by omega))
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (Char2Degree15Fast.mul_bound (isMonicOfDegree_X_add_one (q 0)).natDegree_eq.le
        hz.natDegree_eq.le)
      (Char2Degree15Fast.mul_bound (sFactor_monic q).natDegree_eq.le ht.natDegree_eq.le))
    ((natDegree_C (q 12)).le.trans (by omega))

theorem output_monic (q : Keys R) : IsMonicOfDegree (output q) 13 :=
  (((u_monic q).add_right ((v_monic q).natDegree_eq ▸ (by omega : 12 < 13))).add_right
    ((s_monic q).natDegree_eq ▸ (by omega : 10 < 13))).add_right
      (Char2Degree15Fast.const_lt (q 12) 13 (by omega))

end FastPoly.Char2Degree13Fast

