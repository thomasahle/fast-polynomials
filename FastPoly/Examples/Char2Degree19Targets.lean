import FastPoly.Examples.Char2Degree19Shell

/-!
# The degree-19 shell decoder lands in the prescribed crown family

For an arbitrary monic degree-19 target, the explicit shell inverse divides
`P + X^3` by the cubic read from rows 18, 17, and 16. Monic division gives a
monic degree-16 quotient. The same three observed rows, read in descending
order, force its coefficients 15, 14, and 13 to be 0, 0, and 1.

This is a target-side property of the existing explicit inverse, not a new
decoder or an assertion of abstract invertibility. The crown stays opaque:
only four-term convolution with the known cubic and local cancellation are
used. No gate circuit or recursive baseline is expanded.
-/

namespace FastPoly.Char2Degree19Shell

set_option maxHeartbeats 20000

open Polynomial Char2Decoder

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- The crown component of the supplied inverse, kept behind a named quotient. -/
noncomputable def decodedCrown (p : R[X]) : R[X] :=
  (p + X ^ 3) /ₘ cubic (readShell p)

omit [CharP R 2] in
/-- Adding the known boundary correction does not change the leading row. -/
theorem correctedTarget_monic (p : R[X]) (hp : IsMonicOfDegree p 19) :
    IsMonicOfDegree (p + X ^ 3) 19 := by
  apply hp.add_right
  rw [natDegree_X_pow]
  omega

omit [CharP R 2] in
/-- Monic division by the recovered cubic leaves a monic degree-16 crown. -/
theorem decodedCrown_monic (p : R[X]) (hp : IsMonicOfDegree p 19) :
    IsMonicOfDegree (decodedCrown p) 16 := by
  have htarget := correctedTarget_monic p hp
  have hshell := cubic_monic (readShell p)
  have hdegree : (cubic (readShell p)).degree ≤ (p + X ^ 3).degree := by
    rw [degree_eq_natDegree hshell.ne_zero, degree_eq_natDegree htarget.ne_zero,
      hshell.natDegree_eq, htarget.natDegree_eq]
    exact WithBot.coe_le_coe.mpr (by omega : (3 : ℕ) ≤ 19)
  refine ⟨?_, ?_⟩
  · change ((p + X ^ 3) /ₘ cubic (readShell p)).natDegree = 16
    rw [natDegree_divByMonic _ hshell.monic, htarget.natDegree_eq,
      hshell.natDegree_eq]
  · change ((p + X ^ 3) /ₘ cubic (readShell p)).leadingCoeff = 1
    rw [leadingCoeff_divByMonic_of_monic hshell.monic hdegree]
    exact htarget.leadingCoeff_eq

omit [CharP R 2] in
theorem decodedCrown_coeff16 (p : R[X]) (hp : IsMonicOfDegree p 19) :
    (decodedCrown p).coeff 16 = 1 := by
  have hc := decodedCrown_monic p hp
  rw [← hc.natDegree_eq]
  exact hc.monic.coeff_natDegree

omit [CharP R 2] in
theorem decodedCrown_coeff_above (p : R[X]) (hp : IsMonicOfDegree p 19)
    (j : ℕ) (hj : 16 < j) : (decodedCrown p).coeff j = 0 := by
  have hdegree : (decodedCrown p).natDegree < j := by
    rw [(decodedCrown_monic p hp).natDegree_eq]
    exact hj
  exact coeff_eq_zero_of_natDegree_lt hdegree

/-- Above the other cubic, reconstruction equates the quotient product's row
with the corresponding target row. This uses the already checked inverse. -/
theorem decodedCrown_product_coeff (p : R[X]) (j : ℕ) (hj : 3 < j) :
    (cubic (readShell p) * decodedCrown p).coeff j = p.coeff j := by
  calc
    _ = (join (readShell p) (split (readShell p) p)).coeff j :=
      (join_coeff_high (readShell p) (split (readShell p) p) j hj).symm
    _ = p.coeff j := congrArg (fun q : R[X] => q.coeff j) (join_split (readShell p) p)

/-- The first shell read makes the quotient's row 15 vanish. -/
theorem decodedCrown_coeff15 (p : R[X]) (hp : IsMonicOfDegree p 19) :
    (decodedCrown p).coeff 15 = 0 := by
  have h16 := decodedCrown_coeff16 p hp
  have h17 := decodedCrown_coeff_above p hp 17 (by omega)
  have h18 := decodedCrown_coeff_above p hp 18 (by omega)
  have hrow := decodedCrown_product_coeff p 18 (by omega)
  rw [cubic_mul_coeff (readShell p) (decodedCrown p) 15,
    h16, h17, h18, mul_one, mul_zero, mul_zero, add_zero, add_zero] at hrow
  change (decodedCrown p).coeff 15 + p.coeff 18 = p.coeff 18 at hrow
  exact add_right_cancel (hrow.trans (zero_add _).symm)

/-- After row 15, the second shell read makes row 14 vanish. -/
theorem decodedCrown_coeff14 (p : R[X]) (hp : IsMonicOfDegree p 19) :
    (decodedCrown p).coeff 14 = 0 := by
  have h15 := decodedCrown_coeff15 p hp
  have h16 := decodedCrown_coeff16 p hp
  have h17 := decodedCrown_coeff_above p hp 17 (by omega)
  have hrow := decodedCrown_product_coeff p 17 (by omega)
  rw [cubic_mul_coeff (readShell p) (decodedCrown p) 14,
    h15, h16, h17, mul_zero, mul_one, mul_zero, add_zero, add_zero] at hrow
  change (decodedCrown p).coeff 14 + p.coeff 17 = p.coeff 17 at hrow
  exact add_right_cancel (hrow.trans (zero_add _).symm)

/-- The third shell read includes the fixed one in the crown's row 13. -/
theorem decodedCrown_coeff13 (p : R[X]) (hp : IsMonicOfDegree p 19) :
    (decodedCrown p).coeff 13 = 1 := by
  have h14 := decodedCrown_coeff14 p hp
  have h15 := decodedCrown_coeff15 p hp
  have h16 := decodedCrown_coeff16 p hp
  have hrow := decodedCrown_product_coeff p 16 (by omega)
  rw [cubic_mul_coeff (readShell p) (decodedCrown p) 13,
    h14, h15, h16, mul_zero, mul_zero, mul_one, add_zero, add_zero] at hrow
  change (decodedCrown p).coeff 13 +
    (p.coeff 18 * p.coeff 17 + ((p.coeff 16 + 1) + p.coeff 18 * p.coeff 17)) =
      p.coeff 16 at hrow
  rw [← add_assoc (p.coeff 18 * p.coeff 17), cancel_tail] at hrow
  have hcancel : (1 : R) + (p.coeff 16 + 1) = p.coeff 16 := by
    rw [← add_assoc, cancel_tail]
  exact add_right_cancel (hrow.trans hcancel.symm)

/-- Every monic degree-19 target is sent to a crown satisfying the exact
four-row precondition of the inner decoder. -/
theorem decode_signature (p : R[X]) (hp : IsMonicOfDegree p 19) :
    Signature (decode p).2.1 := by
  change Signature (decodedCrown p)
  exact ⟨decodedCrown_monic p hp, decodedCrown_coeff15 p hp,
    decodedCrown_coeff14 p hp, decodedCrown_coeff13 p hp⟩

end FastPoly.Char2Degree19Shell
