import FastPoly.Examples.Char2Degree23Cancellations

/-!
# A five-factor top frame for the supplied degree-23 circuit

The only terms above degree fifteen are the product of the two quartic
frame factors and three quintic factors. All other terms remain named,
including the final `a21` wire. This is a supporting identity and degree
bound for the explicit decoder, not a recovery argument on its own.
-/

namespace FastPoly.Char2Degree23HighFrame

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree23Cancellations

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def h (a : ℕ → R) : R[X] := z a + t a
noncomputable def D (a : ℕ → R) : R[X] := lastFactor a * crownLeft a
noncomputable def E (a : ℕ → R) : R[X] := h a + C (a 14)
noncomputable def H (a : ℕ → R) : R[X] := h a + C (a 5)
noncomputable def G (a : ℕ → R) : R[X] := h a + y + C (a 4)

noncomputable def high (a : ℕ → R) : R[X] := D a * (E a * (G a * H a))
noncomputable def lowCrown (a : ℕ → R) : R[X] :=
  X + y + z a + W a + ell a + C (a 19)
noncomputable def lowG (a : ℕ → R) : R[X] := E a * (X + C (a 15))
noncomputable def remainder (a : ℕ → R) : R[X] :=
  D a * lowCrown a + D a * lowG a + lastFactor a * u a + head a +
    lastFactor a * C (a 21) + C (a 22)

omit [CharP R 2] [Nontrivial R] in
theorem u_eq (a : ℕ → R) : u a = G a * H a := by
  have he : y + z a + t a + C (a 4) = (z a + t a) + y + C (a 4) := by
    simp only [add_assoc, add_comm, add_left_comm]
  change (y + z a + t a + C (a 4)) * (z a + t a + C (a 5)) = _
  rw [he]
  rfl

omit [CharP R 2] [Nontrivial R] in
theorem g_eq (a : ℕ → R) : g a = E a * u a + lowG a := by
  change E a * (X + u a + C (a 15)) = E a * u a + E a * (X + C (a 15))
  have he : (X : R[X]) + u a + C (a 15) = u a + (X + C (a 15)) := by
    simp only [add_assoc, add_comm, add_left_comm]
  rw [he, mul_add]

omit [CharP R 2] [Nontrivial R] in
theorem crown_eq (a : ℕ → R) : crownRight a + C (a 19) = g a + lowCrown a := by
  change (X + y + z a + w a + s a + g a + ell a) + C (a 19) =
    g a + (X + y + z a + (w a + s a) + ell a + C (a 19))
  simp only [add_assoc, add_comm, add_left_comm]

omit [CharP R 2] [Nontrivial R] in
private theorem assemble (head last left u e low tail c o : R[X]) :
    head + last * (u + left * ((e * u + low) + tail) + c) + o =
      (last * left) * (e * u) +
        ((last * left) * tail + (last * left) * low + last * u + head + last * c + o) := by
  simp only [mul_add, mul_assoc]
  simp only [add_assoc, add_comm, add_left_comm]

omit [CharP R 2] [Nontrivial R] in
/-- The five-factor identity, without flattening any recursive gate. -/
theorem output_eq (a : ℕ → R) : output a = high a + remainder a := by
  change head a + lastFactor a *
    (u a + crownLeft a * (crownRight a + C (a 19)) + C (a 21)) + C (a 22) = _
  rw [crown_eq, g_eq, assemble]
  change D a * (E a * u a) + remainder a = _
  rw [u_eq]
  rfl

omit [CharP R 2] [Nontrivial R] in
private theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) :
    (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

omit [CharP R 2] in
theorem D_monic (a : ℕ → R) : IsMonicOfDegree (D a) 8 := slope_monic a

omit [CharP R 2] in
theorem E_monic (a : ℕ → R) : IsMonicOfDegree (E a) 5 :=
  (z_add_t_monic a).add_right (C_lt _ 5 (by omega))

omit [CharP R 2] in
theorem H_monic (a : ℕ → R) : IsMonicOfDegree (H a) 5 :=
  (z_add_t_monic a).add_right (C_lt _ 5 (by omega))

omit [CharP R 2] in
theorem G_monic (a : ℕ → R) : IsMonicOfDegree (G a) 5 :=
  ((z_add_t_monic a).add_right (y_monic.natDegree_eq.trans_lt
    (by omega))).add_right (C_lt _ 5 (by omega))

omit [CharP R 2] in
theorem high_monic (a : ℕ → R) : IsMonicOfDegree (high a) 23 :=
  (D_monic a).mul ((E_monic a).mul ((G_monic a).mul (H_monic a)))

theorem lowCrown_monic (a : ℕ → R) : IsMonicOfDegree (lowCrown a) 7 := by
  have hx : ((X : R[X]) + y + z a).natDegree < 7 :=
    ((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt
      (by omega))).natDegree_eq.trans_lt (by omega)
  exact (((W_monic a).add_left hx).add_right
    ((ell_monic a).natDegree_eq.trans_lt (by omega))).add_right (C_lt _ 7 (by omega))

omit [CharP R 2] in
theorem lowG_monic (a : ℕ → R) : IsMonicOfDegree (lowG a) 6 :=
  (E_monic a).mul (isMonicOfDegree_X_add_one (a 15))

theorem head_degree14 (a : ℕ → R) : (head a).natDegree ≤ 14 := by
  have he : head a = RG a + (y + v a + W a) := by
    change y + v a + w a + s a + r a + g a = (r a + g a) + (y + v a + (w a + s a))
    simp only [add_assoc, add_comm, add_left_comm]
  have hl : (y + v a + W a).natDegree ≤ 14 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (y_monic.natDegree_eq.le.trans (by omega))
        ((v_monic a).natDegree_eq.le.trans (by omega)))
      ((W_monic a).natDegree_eq.le.trans (by omega))
  rw [he]
  exact natDegree_add_le_of_degree_le (RG_monic a).natDegree_eq.le hl

/-- The remainder's leading coefficient is fixed too: only `D * lowCrown`
reaches degree fifteen. This will control differences without expansion. -/
theorem remainder_monic (a : ℕ → R) : IsMonicOfDegree (remainder a) 15 := by
  have h1 : IsMonicOfDegree (D a * lowCrown a) 15 :=
    (D_monic a).mul (lowCrown_monic a)
  have h2 : (D a * lowG a).natDegree < 15 :=
    ((D_monic a).mul (lowG_monic a)).natDegree_eq.trans_lt (by omega)
  have h3 : (lastFactor a * u a).natDegree < 15 :=
    ((lastFactor_monic a).mul (u_monic a)).natDegree_eq.trans_lt (by omega)
  have h4 : (head a).natDegree < 15 := (head_degree14 a).trans_lt (by omega)
  have hb : (lastFactor a * C (a 21)).natDegree ≤ 4 := by
    apply natDegree_mul_le.trans
    rw [(lastFactor_monic a).natDegree_eq, natDegree_C]
  have h5 : (lastFactor a * C (a 21)).natDegree < 15 := hb.trans_lt (by omega)
  have h6 : (C (a 22)).natDegree < 15 := C_lt _ 15 (by omega)
  exact ((((h1.add_right h2).add_right h3).add_right h4).add_right h5).add_right h6

/-- All discarded terms, including `lastFactor * a21`, have degree at most fifteen. -/
theorem remainder_degree (a : ℕ → R) : (remainder a).natDegree ≤ 15 :=
  (remainder_monic a).natDegree_eq.le

end FastPoly.Char2Degree23HighFrame
