import FastPoly.Examples.Char2Degree15FastCore

/-!
# Named wires of the active square-first degree-11 circuit

This is the six-product circuit in `website/js/char2.js`, NOT the different
Frobenius circuit certified by `char2/verify_n11.py`.  Its supplied normalized
coordinates are retained. The larger raw-offset expressions are kept as the
actual scalar inverse steps for the named wire `J = t + v + a9`.

The final product `B * J` is never expanded. Coefficient work belongs to the
separate signature module and stops at the small named wire `J`.
-/

namespace FastPoly.Char2Degree11Fast

set_option maxHeartbeats 20000

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

abbrev Keys (R : Type*) := Fin 11 → R

/-- The only five unfixed coefficients of the degree-eight wire. -/
def k4 (q : Keys R) : R := 1 + q 0 + q 3 + q 0 ^ 2
def k3 (q : Keys R) : R := q 1 + q 4
def k2 (q : Keys R) : R :=
  q 3 + q 4 + q 5 + q 0 * q 1 + q 0 * (q 3 + q 4) + q 1 ^ 2
def k1 (q : Keys R) : R := q 6 + q 1 * (q 3 + q 4)
def k0 (q : Keys R) : R :=
  q 7 + (q 3 + q 4) * q 5 + q 4 * q 6 + q 5 ^ 2 +
    q 0 * q 1 * (q 3 + q 4) + (q 0 * q 1) ^ 2

def z0 (q : Keys R) : R := q 9 * (q 8 + q 9)
def h2 (q : Keys R) : R := q 8 + q 0
def h1 (q : Keys R) : R := q 9 + q 1
def h0 (q : Keys R) : R := z0 q + q 0 * q 1

def a2 (q : Keys R) : R := q 4 + q 8 + q 9
def sigma (q : Keys R) : R := q 3 + q 4 + q 9 + q 8 ^ 2

/-- Read row two of `J` after its higher rows have been installed. -/
def a6 (q : Keys R) : R :=
  k2 q + (q 9 + a2 q * q 8 + h1 q ^ 2 + h0 q + sigma q * h2 q)
def a7 (q : Keys R) : R := a6 q + sigma q

/-- Read row one of `J` with unit slope in the offset of `t`. -/
def a3 (q : Keys R) : R :=
  k1 q + (z0 q + a2 q * q 9 + sigma q * h1 q)

/-- Read row zero of `J`; neither baseline wire contains this offset. -/
def a9 (q : Keys R) : R :=
  k0 q + (a2 q * (z0 q + a3 q) + (h0 q + a6 q) * (h0 q + a7 q))

def keys (q : Keys R) : ℕ → R
  | 0 => q 9
  | 1 => q 8 + q 9
  | 2 => a2 q
  | 3 => a3 q
  | 4 => q 0
  | 5 => q 1
  | 6 => a6 q
  | 7 => a7 q
  | 8 => q 2
  | 9 => a9 q
  | 10 => q 10
  | _ => 0

noncomputable def y : R[X] := X ^ 2
noncomputable def z (q : Keys R) : R[X] :=
  (y + C (q 9)) * (X + y + C (q 8 + q 9))
noncomputable def t (q : Keys R) : R[X] :=
  (X + C (a2 q)) * (z q + C (a3 q))
noncomputable def u (q : Keys R) : R[X] :=
  (X + C (q 0)) * (y + C (q 1))

/-- The equal cubic terms in `z+u` cancel before squaring. -/
noncomputable def H (q : Keys R) : R[X] := z q + u q
noncomputable def v (q : Keys R) : R[X] :=
  (H q + C (a6 q)) * (y + H q + C (a7 q))
noncomputable def B (q : Keys R) : R[X] := u q + C (q 2)
noncomputable def J (q : Keys R) : R[X] := t q + v q + C (a9 q)
noncomputable def w (q : Keys R) : R[X] := B q * J q
noncomputable def output (q : Keys R) : R[X] := z q + w q + C (q 10)

theorem output_split (q : Keys R) :
    output q = z q + B q * J q + C (q 10) := rfl

theorem offsets_sum (q : Keys R) : a6 q + a7 q = sigma q := by
  rw [a7, CharTwo.add_cancel_left]

variable [Nontrivial R]

theorem y_monic : IsMonicOfDegree (y : R[X]) 2 := isMonicOfDegree_X_pow R 2

theorem z_monic (q : Keys R) : IsMonicOfDegree (z q) 4 :=
  (y_monic.add_right (Char2Degree15Fast.const_lt (q 9) 2 (by omega))).mul
    ((y_monic.add_left (natDegree_X_le.trans_lt (by omega))).add_right
      (Char2Degree15Fast.const_lt (q 8 + q 9) 2 (by omega)))

theorem t_monic (q : Keys R) : IsMonicOfDegree (t q) 5 :=
  (isMonicOfDegree_X_add_one (a2 q)).mul
    ((z_monic q).add_right (Char2Degree15Fast.const_lt (a3 q) 4 (by omega)))

theorem u_monic (q : Keys R) : IsMonicOfDegree (u q) 3 :=
  (isMonicOfDegree_X_add_one (q 0)).mul
    (y_monic.add_right (Char2Degree15Fast.const_lt (q 1) 2 (by omega)))

theorem H_monic (q : Keys R) : IsMonicOfDegree (H q) 4 :=
  (z_monic q).add_right ((u_monic q).natDegree_eq ▸ (by omega : 3 < 4))

theorem v_monic (q : Keys R) : IsMonicOfDegree (v q) 8 :=
  ((H_monic q).add_right (Char2Degree15Fast.const_lt (a6 q) 4 (by omega))).mul
    (((H_monic q).add_left ((y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 4))).add_right
      (Char2Degree15Fast.const_lt (a7 q) 4 (by omega)))

theorem B_monic (q : Keys R) : IsMonicOfDegree (B q) 3 :=
  (u_monic q).add_right (Char2Degree15Fast.const_lt (q 2) 3 (by omega))

theorem J_monic (q : Keys R) : IsMonicOfDegree (J q) 8 :=
  ((v_monic q).add_left ((t_monic q).natDegree_eq ▸ (by omega : 5 < 8))).add_right
    (Char2Degree15Fast.const_lt (a9 q) 8 (by omega))

theorem output_monic (q : Keys R) : IsMonicOfDegree (output q) 11 :=
  (((B_monic q).mul (J_monic q)).add_left
    ((z_monic q).natDegree_eq ▸ (by omega : 4 < 11))).add_right
      (Char2Degree15Fast.const_lt (q 10) 11 (by omega))

end FastPoly.Char2Degree11Fast
