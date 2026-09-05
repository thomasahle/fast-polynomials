import FastPoly.Examples.Char2Degree23HighKeys
import FastPoly.Examples.Char2MonicPivotPeel

/-!
# A named low frame for three terminal degree-23 updates

Only raw slots 13, 19, 21 and 22 remain variable in this frame. Their
four columns are displayed explicitly. The monic row-eight column is
removed by its already decoded coefficient, not by expanding its baseline.
-/

namespace FastPoly.Char2Degree23LowFrame

open Polynomial Char2Degree23RowEight Char2Degree23HighFrame
  Char2Degree23HighKeys Char2Degree19InnerTail

set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

structure SameSlots (a b : ℕ → R) : Prop where
  h0 : a 0 = b 0
  h1 : a 1 = b 1
  h2 : a 2 = b 2
  h3 : a 3 = b 3
  h4 : a 4 = b 4
  h5 : a 5 = b 5
  h6 : a 6 = b 6
  h7 : a 7 = b 7
  h8 : a 8 = b 8
  h9 : a 9 = b 9
  h10 : a 10 = b 10
  h11 : a 11 = b 11
  h12 : a 12 = b 12
  h14 : a 14 = b 14
  h15 : a 15 = b 15
  h16 : a 16 = b 16
  h17 : a 17 = b 17
  h18 : a 18 = b 18
  h20 : a 20 = b 20

noncomputable def linear (a : ℕ → R) : R[X] := X + t a + C (a 12)
noncomputable def constant (a : ℕ → R) : R[X] :=
  y + v a + w a + s a + g a + linear a * u a +
    lastFactor a * (u a + crownLeft a * crownRight a)

theorem linear_monic (a : ℕ → R) : IsMonicOfDegree (linear a) 5 := by
  have hx : (X : R[X]).natDegree < 5 := natDegree_X_le.trans_lt (by omega)
  have hc : (C (a 12)).natDegree < 5 := by rw [natDegree_C]; omega
  exact ((Char2Degree23Frame.t_monic a).add_left hx).add_right hc

private theorem collect (y v w s g l u f c b j k t o : R[X]) :
    (y + v + w + s + l * (u + j) + g) +
      f * (u + c * (b + k) + t) + o =
    (y + v + w + s + g + l * u + f * (u + c * b)) +
      l * j + (f * c) * k + f * t + o := by
  ring

theorem output_eq (a : ℕ → R) :
    output a = constant a + linear a * C (a 13) +
      D a * C (a 19) + lastFactor a * C (a 21) + C (a 22) := by
  change (y + v a + w a + s a + linear a * (u a + C (a 13)) + g a) +
    lastFactor a * (u a + crownLeft a * (crownRight a + C (a 19)) + C (a 21)) +
      C (a 22) = _
  exact collect _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem SameSlots.frames {a b : ℕ → R} (he : SameSlots a b) :
    constant a = constant b ∧ linear a = linear b ∧
      D a = D b ∧ lastFactor a = lastFactor b := by
  have hz : z a = z b := by rw [z, he.h0, he.h1]; rfl
  have ht : t a = t b := by rw [t, he.h2, hz, he.h3]; rfl
  have hu : u a = u b := by rw [u, hz, ht, he.h4, he.h5]; rfl
  have hv : v a = v b := by rw [v, he.h6, hz, he.h7]; rfl
  have hw : w a = w b := by rw [w, hz, he.h8, hv, he.h9]; rfl
  have hs : s a = s b := by rw [s, hz, he.h10, hv, he.h11]; rfl
  have hg : g a = g b := by rw [g, hz, ht, he.h14, hu, he.h15]; rfl
  have hl : ell a = ell b := by rw [ell, he.h16, hz, hv, he.h17]; rfl
  have hcl : crownLeft a = crownLeft b := by rw [crownLeft, hz, he.h18]; rfl
  have hcr : crownRight a = crownRight b := by
    rw [crownRight, hz, hw, hs, hg, hl]; rfl
  have hf : lastFactor a = lastFactor b := by rw [lastFactor, hz, he.h20]; rfl
  have hn : linear a = linear b := by rw [linear, ht, he.h12]; rfl
  refine ⟨?_, hn, ?_, hf⟩
  · rw [constant, hv, hw, hs, hg, hn, hu, hf, hcl, hcr]; rfl
  · rw [D, hf, hcl]; rfl

private theorem collect_difference (c l d f : R[X]) (j j' k k' t t' o o' : R) :
    (c + l * C j' + d * C k' + f * C t' + C o') +
      (c + l * C j + d * C k + f * C t + C o) =
    d * C (k' + k) + (l * C (j' + j) + f * C (t' + t) + C (o' + o)) := by
  simp only [map_add]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem SameSlots.output_difference {a b : ℕ → R} (he : SameSlots a b) :
    output b + output a = D a * C (b 19 + a 19) +
      (linear a * C (b 13 + a 13) + lastFactor a * C (b 21 + a 21) +
        C (b 22 + a 22)) := by
  obtain ⟨hc, hl, hd, hf⟩ := he.frames
  rw [output_eq b, output_eq a, ← hc, ← hl, ← hd, ← hf, collect_difference]

/-- The three residual columns have degree at most five. -/
theorem residual_degree (a : ℕ → R) (j t o : R) :
    (linear a * C j + lastFactor a * C t + C o).natDegree < 8 := by
  have hj : (linear a * C j).natDegree ≤ 5 := by
    apply natDegree_mul_le.trans
    rw [(linear_monic a).natDegree_eq, natDegree_C]
  have ht : (lastFactor a * C t).natDegree ≤ 5 := by
    apply natDegree_mul_le.trans
    rw [(lastFactor_monic a).natDegree_eq, natDegree_C]; omega
  have ho : (C o).natDegree ≤ 5 := by rw [natDegree_C]; exact Nat.zero_le _
  exact (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le hj ht) ho).trans_lt (by omega)

/-- Explicit row-eight decoding removes the only column above these updates. -/
theorem SameSlots.peel {a b : ℕ → R} (he : SameSlots a b)
    (hrow : (output b).coeff 8 = (output a).coeff 8) :
    output b = output a +
      (linear a * C (b 13 + a 13) + lastFactor a * C (b 21 + a 21) +
        C (b 22 + a 22)) :=
  Char2MonicPivotPeel.peel_difference (D_monic a)
    (residual_degree a _ _ _) he.output_difference hrow

end FastPoly.Char2Degree23LowFrame
