import FastPoly.Examples.Char2Degree23HighPivots

/-!
# The compensated common increment in the degree-23 top frame

The change is organized by powers of the one scalar increment. Its linear
coefficient is reduced by a supplied factor identity; all higher powers
have degree at most fifteen. Only opaque frame wires occur in the small
commutative-ring identity below.
-/

namespace FastPoly.Char2Degree23SeamDifference

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23HighFrame Char2Degree23HighDifference Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def linear (a : ℕ → R) : R[X] := X + C (a 2)
noncomputable def gap (a : ℕ → R) : R[X] := C (a 14 + a 5)
noncomputable def pair (a : ℕ → R) : R[X] := E a * H a
noncomputable def firstChange (a : ℕ → R) : R[X] :=
  (linear a + 1) * pair a + linear a * gap a * G a
noncomputable def secondChange (a : ℕ → R) : R[X] :=
  linear a ^ 2 * G a + linear a * gap a * (linear a + 1)
noncomputable def thirdChange (a : ℕ → R) : R[X] := linear a ^ 2 * (linear a + 1)

noncomputable def seamSlope (a : ℕ → R) (f j : R[X]) : R[X] :=
  (f * j) * pair a + D a * linear a * gap a * G a
noncomputable def seamTail (a : ℕ → R) (f : R[X]) (delta : R) : R[X] :=
  C (delta ^ 2) * (D a * secondChange a + f * firstChange a) +
    C (delta ^ 3) * (D a * thirdChange a + f * secondChange a) +
    C (delta ^ 4) * (f * thirdChange a)

omit [CharP R 2] [Nontrivial R] in
private theorem four_increment (d f e g h l c : R[X]) :
    (d + c * f) * ((e + c * l) * ((g + c * (l + 1)) * (h + c * l))) =
      d * (e * (g * h)) +
        c * ((d * (l + 1) + f * g) * (e * h) + d * l * (e + h) * g) +
        c ^ 2 * (d * (l ^ 2 * g + l * (e + h) * (l + 1)) +
          f * ((l + 1) * (e * h) + l * (e + h) * g)) +
        c ^ 3 * (d * (l ^ 2 * (l + 1)) + f * (l ^ 2 * g + l * (e + h) * (l + 1))) +
        c ^ 4 * (f * (l ^ 2 * (l + 1))) := by
  ring

omit [CharP R 2] in
theorem linear_monic (a : ℕ → R) : IsMonicOfDegree (linear a) 1 :=
  isMonicOfDegree_X_add_one (a 2)

omit [CharP R 2] in
theorem linear_one_monic (a : ℕ → R) : IsMonicOfDegree (linear a + 1) 1 := by
  have ho : ((1 : R[X])).natDegree < 1 := by rw [natDegree_one]; omega
  exact (linear_monic a).add_right ho

omit [CharP R 2] in
theorem pair_monic (a : ℕ → R) : IsMonicOfDegree (pair a) 10 :=
  (E_monic a).mul (H_monic a)

omit [CharP R 2] [Nontrivial R] in
private theorem mul_bound {p q : R[X]} {n m : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ m) :
    (p * q).natDegree ≤ n + m := natDegree_mul_le.trans (Nat.add_le_add hp hq)

omit [CharP R 2] [Nontrivial R] in
private theorem scale_bound (c : R) {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    (C c * p).natDegree ≤ n := by
  apply natDegree_mul_le.trans
  rw [natDegree_C, Nat.zero_add]
  exact hp

omit [CharP R 2] [Nontrivial R] in
theorem gap_degree (a : ℕ → R) : (gap a).natDegree = 0 := natDegree_C _

omit [CharP R 2] in
theorem firstChange_degree (a : ℕ → R) : (firstChange a).natDegree ≤ 11 := by
  have h1 : ((linear a + 1) * pair a).natDegree ≤ 11 :=
    ((linear_one_monic a).mul (pair_monic a)).natDegree_eq.le
  have h2 : (linear a * gap a * G a).natDegree ≤ 6 :=
    mul_bound (mul_bound (linear_monic a).natDegree_eq.le (gap_degree a).le)
      (G_monic a).natDegree_eq.le
  exact natDegree_add_le_of_degree_le h1 (h2.trans (by omega))

omit [CharP R 2] in
theorem secondChange_degree (a : ℕ → R) : (secondChange a).natDegree ≤ 7 := by
  have hl : (linear a ^ 2).natDegree ≤ 2 :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 (linear_monic a).natDegree_eq.le)
  have h1 : (linear a ^ 2 * G a).natDegree ≤ 7 := mul_bound hl (G_monic a).natDegree_eq.le
  have h2 : (linear a * gap a * (linear a + 1)).natDegree ≤ 2 :=
    mul_bound (mul_bound (linear_monic a).natDegree_eq.le (gap_degree a).le)
      (linear_one_monic a).natDegree_eq.le
  exact natDegree_add_le_of_degree_le h1 (h2.trans (by omega))

omit [CharP R 2] in
theorem thirdChange_degree (a : ℕ → R) : (thirdChange a).natDegree ≤ 3 := by
  have hl : (linear a ^ 2).natDegree ≤ 2 :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 (linear_monic a).natDegree_eq.le)
  exact mul_bound hl (linear_one_monic a).natDegree_eq.le

omit [CharP R 2] in
theorem seamSlope_monic (a : ℕ → R) (f j : R[X]) (k : ℕ)
    (hf : IsMonicOfDegree f 4) (hj : IsMonicOfDegree j k) (hk : 0 < k) :
    IsMonicOfDegree (seamSlope a f j) (14 + k) := by
  have h1 := (hf.mul hj).mul (pair_monic a)
  have hn : 4 + k + 10 = 14 + k := by omega
  rw [hn] at h1
  have h2 : (D a * linear a * gap a * G a).natDegree ≤ 14 :=
    mul_bound
      (mul_bound (mul_bound (D_monic a).natDegree_eq.le (linear_monic a).natDegree_eq.le)
        (gap_degree a).le) (G_monic a).natDegree_eq.le
  exact h1.add_right (h2.trans_lt (by omega))

omit [CharP R 2] in
theorem seamTail_degree (a : ℕ → R) (f : R[X]) (delta : R)
    (hf : IsMonicOfDegree f 4) : (seamTail a f delta).natDegree ≤ 15 := by
  have h2 : (D a * secondChange a + f * firstChange a).natDegree ≤ 15 :=
    natDegree_add_le_of_degree_le
      (mul_bound (D_monic a).natDegree_eq.le (secondChange_degree a))
      (mul_bound hf.natDegree_eq.le (firstChange_degree a))
  have h3 : (D a * thirdChange a + f * secondChange a).natDegree ≤ 11 :=
    natDegree_add_le_of_degree_le
      (mul_bound (D_monic a).natDegree_eq.le (thirdChange_degree a))
      (mul_bound hf.natDegree_eq.le (secondChange_degree a))
  have h4 : (f * thirdChange a).natDegree ≤ 7 := mul_bound hf.natDegree_eq.le (thirdChange_degree a)
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (scale_bound _ h2) ((scale_bound _ h3).trans (by omega)))
    ((scale_bound _ h4).trans (by omega))

/-- The factor identity supplied by the particular seam exposes its monic slope. -/
theorem seam_high_unit (a b : ℕ → R) (f j : R[X]) (k : ℕ) (delta : R)
    (hf : IsMonicOfDegree f 4) (hj : IsMonicOfDegree j k) (hk : 2 ≤ k)
    (hd : D b = D a + C delta * f)
    (he : E b = E a + C delta * linear a)
    (hg : G b = G a + C delta * (linear a + 1))
    (hh : H b = H a + C delta * linear a)
    (hframe : D a * (linear a + 1) + f * G a = f * j) :
    UnitDifference (high a) (high b) (14 + k) delta := by
  apply Char2Degree19InnerChanges.unit_difference_of_lower
    _ _ (seamSlope a f j) (seamTail a f delta) (14 + k) delta
    (seamSlope_monic a f j k hf hj (by omega))
    ((seamTail_degree a f delta hf).trans_lt (by omega))
  change D b * (E b * (G b * H b)) = _
  rw [hd, he, hg, hh, four_increment, hframe]
  simp only [E_add_H]
  change high a + C delta * seamSlope a f j +
      (C delta) ^ 2 * (D a * secondChange a + f * firstChange a) +
      (C delta) ^ 3 * (D a * thirdChange a + f * secondChange a) +
      (C delta) ^ 4 * (f * thirdChange a) =
    high a + (C delta * seamSlope a f j + seamTail a f delta)
  simp only [seamTail, map_pow, add_assoc]

/-- Recover the three shifted quintic factors from the named `h` change. -/
theorem shifted_factors (a b : ℕ → R) (delta : R)
    (hh : h b = h a + C delta * linear a)
    (h4 : b 4 = a 4 + delta) (h5 : b 5 = a 5) (h14 : b 14 = a 14) :
    E b = E a + C delta * linear a ∧
      G b = G a + C delta * (linear a + 1) ∧
      H b = H a + C delta * linear a := by
  refine ⟨?_, ?_, ?_⟩
  · change h b + C (b 14) = (h a + C (a 14)) + C delta * linear a
    rw [hh, h14]
    simp only [add_assoc, add_comm, add_left_comm]
  · change h b + y + C (b 4) = (h a + y + C (a 4)) + C delta * (linear a + 1)
    rw [hh, h4, map_add, mul_add, mul_one]
    simp only [add_assoc, add_comm, add_left_comm]
  · change h b + C (b 5) = (h a + C (a 5)) + C delta * linear a
    rw [hh, h5]
    simp only [add_assoc, add_comm, add_left_comm]

theorem seam_output_unit (a b : ℕ → R) (f j : R[X]) (k : ℕ) (delta : R)
    (hf : IsMonicOfDegree f 4) (hj : IsMonicOfDegree j k) (hk : 2 ≤ k)
    (hd : D b = D a + C delta * f)
    (hh : h b = h a + C delta * linear a)
    (h4 : b 4 = a 4 + delta) (h5 : b 5 = a 5) (h14 : b 14 = a 14)
    (hframe : D a * (linear a + 1) + f * G a = f * j) :
    UnitDifference (output a) (output b) (14 + k) delta := by
  obtain ⟨he, hg, hh'⟩ := shifted_factors a b delta hh h4 h5 h14
  exact output_unit (seam_high_unit a b f j k delta hf hj hk hd he hg hh' hframe) (by omega)

end FastPoly.Char2Degree23SeamDifference
