import FastPoly.Examples.Char2Degree23Frame

/-!
# The two shared-wire cancellations in the degree-23 circuit

The two degree-nine wires `w,s` add to a monic degree-seven polynomial;
the two degree-fifteen wires `r,g` add to a monic degree-fourteen polynomial.
These are local distributive identities, with the shared wires kept named.
They provide degree bounds for subsequent explicit pivot proofs, not an
independent recovery claim.
-/

namespace FastPoly.Char2Degree23Cancellations

open Polynomial Char2Degree23RowEight Char2Degree23Frame

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def W (a : ℕ → R) : R[X] := w a + s a
noncomputable def wLeft (a : ℕ → R) : R[X] := X + y + z a + C (a 8)
noncomputable def wSlope (a : ℕ → R) : R[X] := X + y + C (a 8) + C (a 10)

omit [CharP R 2] [Nontrivial R] in
private theorem shared_product (b c y v d e : R[X]) :
    b * (y + v + d) + c * (v + e) =
      (b + c) * v + y * b + d * b + e * c := by
  simp only [mul_add, add_mul]
  rw [mul_comm b y, mul_comm b d, mul_comm c e]
  simp only [add_assoc, add_comm, add_left_comm]

omit [Nontrivial R] in
private theorem w_factor_sum (a : ℕ → R) :
    wLeft a + (z a + C (a 10)) = wSlope a := by
  change (X + y + z a + C (a 8)) + (z a + C (a 10)) =
    X + y + C (a 8) + C (a 10)
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

omit [Nontrivial R] in
/-- The common `z*v` term cancels before any coefficients are read. -/
theorem W_eq (a : ℕ → R) :
    W a = wSlope a * v a + y * wLeft a + C (a 9) * wLeft a +
      C (a 11) * (z a + C (a 10)) := by
  change wLeft a * (y + v a + C (a 9)) +
    (z a + C (a 10)) * (v a + C (a 11)) = _
  rw [shared_product, w_factor_sum]

omit [CharP R 2] [Nontrivial R] in
private theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) :
    (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

omit [CharP R 2] [Nontrivial R] in
private theorem scaled_degree (c : R) {p : R[X]} {n : ℕ}
    (hp : p.natDegree ≤ n) : (C c * p).natDegree ≤ n := by
  apply natDegree_mul_le.trans
  rw [natDegree_C, Nat.zero_add]
  exact hp

omit [CharP R 2] in
theorem wLeft_monic (a : ℕ → R) : IsMonicOfDegree (wLeft a) 4 :=
  ((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt
    (by omega))).add_right (C_lt _ 4 (by omega))

omit [CharP R 2] in
theorem wSlope_monic (a : ℕ → R) : IsMonicOfDegree (wSlope a) 2 :=
  (x_add_y_monic.add_right (C_lt _ 2 (by omega))).add_right (C_lt _ 2 (by omega))

theorem W_monic (a : ℕ → R) : IsMonicOfDegree (W a) 7 := by
  have hy : (y * wLeft a).natDegree < 7 :=
    (y_monic.mul (wLeft_monic a)).natDegree_eq.trans_lt (by omega)
  have hb : (C (a 9) * wLeft a).natDegree < 7 :=
    (scaled_degree _ (wLeft_monic a).natDegree_eq.le).trans_lt (by omega)
  have hz : IsMonicOfDegree (z a + C (a 10)) 4 :=
    (z_monic a).add_right (C_lt _ 4 (by omega))
  have hc : (C (a 11) * (z a + C (a 10))).natDegree < 7 :=
    (scaled_degree _ hz.natDegree_eq.le).trans_lt (by omega)
  rw [W_eq]
  exact ((((wSlope_monic a).mul (v_monic a)).add_right hy).add_right hb).add_right hc

noncomputable def RG (a : ℕ → R) : R[X] := r a + g a
noncomputable def rLeft (a : ℕ → R) : R[X] := X + t a + C (a 12)
noncomputable def gLeft (a : ℕ → R) : R[X] := z a + t a + C (a 14)
noncomputable def rgSlope (a : ℕ → R) : R[X] := X + z a + C (a 12) + C (a 14)

omit [CharP R 2] [Nontrivial R] in
private theorem paired_product (a b u c x d : R[X]) :
    a * (u + c) + b * (x + u + d) =
      (a + b) * u + c * a + (x + d) * b := by
  simp only [mul_add, add_mul]
  rw [mul_comm a c, mul_comm b x, mul_comm b d]
  simp only [add_assoc, add_comm, add_left_comm]

omit [Nontrivial R] in
private theorem rg_factor_sum (a : ℕ → R) : rLeft a + gLeft a = rgSlope a := by
  change (X + t a + C (a 12)) + (z a + t a + C (a 14)) =
    X + z a + C (a 12) + C (a 14)
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

omit [Nontrivial R] in
/-- The shared degree-fifteen `t*u` term cancels as a named product. -/
theorem RG_eq (a : ℕ → R) :
    RG a = rgSlope a * u a + C (a 13) * rLeft a + (X + C (a 15)) * gLeft a := by
  change rLeft a * (u a + C (a 13)) + gLeft a * (X + u a + C (a 15)) = _
  rw [paired_product, rg_factor_sum]

omit [CharP R 2] in
theorem rLeft_monic (a : ℕ → R) : IsMonicOfDegree (rLeft a) 5 :=
  ((t_monic a).add_left (natDegree_X_le.trans_lt (by omega))).add_right
    (C_lt _ 5 (by omega))

omit [CharP R 2] in
theorem gLeft_monic (a : ℕ → R) : IsMonicOfDegree (gLeft a) 5 :=
  (z_add_t_monic a).add_right (C_lt _ 5 (by omega))

omit [CharP R 2] in
theorem rgSlope_monic (a : ℕ → R) : IsMonicOfDegree (rgSlope a) 4 :=
  (((z_monic a).add_left (natDegree_X_le.trans_lt (by omega))).add_right
    (C_lt _ 4 (by omega))).add_right (C_lt _ 4 (by omega))

theorem RG_monic (a : ℕ → R) : IsMonicOfDegree (RG a) 14 := by
  have hr : (C (a 13) * rLeft a).natDegree < 14 :=
    (scaled_degree _ (rLeft_monic a).natDegree_eq.le).trans_lt (by omega)
  have hg : ((X + C (a 15)) * gLeft a).natDegree < 14 :=
    ((isMonicOfDegree_X_add_one (a 15)).mul (gLeft_monic a)).natDegree_eq.trans_lt
      (by omega)
  rw [RG_eq]
  exact (((rgSlope_monic a).mul (u_monic a)).add_right hr).add_right hg

end FastPoly.Char2Degree23Cancellations
