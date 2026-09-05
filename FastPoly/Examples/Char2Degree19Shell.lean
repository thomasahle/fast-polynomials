import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Explicit cubic-shell inverse for the existing degree-19 circuit

This is the division step in (A.17)--(A.25), as certified by
`char2/verify_n19_unitriangular_symbolic.py`. The crown is kept opaque. The
inverse first reads the shell's three top coefficients, then divides
`P + X^3` by that monic cubic, then reads the three remaining low rows.
The correction `+ X^3` is essential at the boundary: the circuit's other
cubic contributes one in row three.

All proofs are small, local identities. No inner gate or crown is expanded.
This module certifies the outer inverse; the inner crown's thirteen supplied
unit-pivot identities are a separate obligation.
-/

namespace FastPoly.Char2Degree19Shell

set_option maxHeartbeats 20000

open Polynomial Char2Decoder

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The three slots `(q0,q1,q2)` or `(q16,q17,q18)`. -/
abbrev Triple (R : Type*) := R × R × R

/-- The lower part of `(X + a) * (X^2 + b) + d`. -/
noncomputable def low (t : Triple R) : R[X] :=
  C t.1 * X ^ 2 + C t.2.1 * X + C (t.1 * t.2.1 + t.2.2)

noncomputable def cubic (t : Triple R) : R[X] := X ^ 3 + low t

/-- Read the two unit pivots, then cancel their known product. -/
def readLow (p : R[X]) : Triple R :=
  (p.coeff 2, p.coeff 1, p.coeff 0 + p.coeff 2 * p.coeff 1)

omit [CharP R 2] in
theorem low_coeff_two (t : Triple R) : (low t).coeff 2 = t.1 := by
  simp only [low, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
    ite_true, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, ite_false, add_zero]

omit [CharP R 2] in
theorem low_coeff_one (t : Triple R) : (low t).coeff 1 = t.2.1 := by
  have h : (1 : ℕ) ≠ 2 := by omega
  simp only [low, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
    ite_true, h, one_ne_zero, ite_false, zero_add, add_zero]

omit [CharP R 2] in
theorem low_coeff_zero (t : Triple R) : (low t).coeff 0 = t.1 * t.2.1 + t.2.2 := by
  have h : (0 : ℕ) ≠ 2 := by omega
  simp only [low, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
    ite_true, h, zero_ne_one, ite_false, zero_add]

omit [CharP R 2] in
theorem low_degree (t : Triple R) : (low t).degree < 3 := by
  apply (degree_lt_iff_coeff_zero _ 3).mpr
  intro j hj
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have h2 : j ≠ 2 := by omega
  simp only [low, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C,
    h0, h1, h2, ite_false, add_zero]

theorem readLow_low (t : Triple R) : readLow (low t) = t := by
  simp only [readLow, low_coeff_two, low_coeff_one, low_coeff_zero, cancel_tail]

/-- Three coefficient reads reconstruct a polynomial below degree three. -/
theorem low_readLow (p : R[X]) (hp : p.degree < 3) : low (readLow p) = p := by
  ext j
  by_cases h0 : j = 0
  · subst j
    rw [low_coeff_zero]
    change p.coeff 2 * p.coeff 1 + (p.coeff 0 + p.coeff 2 * p.coeff 1) = p.coeff 0
    rw [← add_assoc, cancel_tail]
  by_cases h1 : j = 1
  · subst j
    exact low_coeff_one _
  by_cases h2 : j = 2
  · subst j
    exact low_coeff_two _
  have hj : 3 ≤ j := by omega
  have hz : p.coeff j = 0 := (degree_lt_iff_coeff_zero _ 3).mp hp j hj
  have hz' : (low (readLow p)).coeff j = 0 :=
    (degree_lt_iff_coeff_zero _ 3).mp (low_degree _) j hj
  exact hz'.trans hz.symm

section Nontrivial

variable [Nontrivial R]

omit [CharP R 2] in
theorem cubic_monic (t : Triple R) : IsMonicOfDegree (cubic t) 3 := by
  apply (isMonicOfDegree_X_pow R 3).add_right
  by_cases hz : low t = 0
  · rw [hz, natDegree_zero]; omega
  · exact (natDegree_lt_iff_degree_lt hz).mpr (low_degree t)

/-- Encode the outer shell, leaving the already computed crown opaque. -/
noncomputable def join (s : Triple R) (data : R[X] × Triple R) : R[X] :=
  cubic s * data.1 + cubic data.2

/-- Literal monic division followed by the three displayed low-row reads. -/
noncomputable def split (s : Triple R) (p : R[X]) : R[X] × Triple R :=
  ((p + X ^ 3) /ₘ cubic s, readLow ((p + X ^ 3) %ₘ cubic s))

omit [Nontrivial R] in
theorem join_boundary (s : Triple R) (data : R[X] × Triple R) :
    join s data + X ^ 3 = low data.2 + cubic s * data.1 := by
  change (cubic s * data.1 + (X ^ 3 + low data.2)) + X ^ 3 = _
  rw [add_right_comm, ← add_assoc, CharTwo.add_cancel_right, add_comm]

theorem split_join (s : Triple R) (data : R[X] × Triple R) :
    split s (join s data) = data := by
  have hdeg : (low data.2).degree < (cubic s).degree := by
    rw [degree_eq_natDegree (cubic_monic s).ne_zero, (cubic_monic s).natDegree_eq]
    exact low_degree data.2
  have h := div_modByMonic_unique data.1 (low data.2) (cubic_monic s).monic
    ⟨(join_boundary s data).symm, hdeg⟩
  change ((join s data + X ^ 3) /ₘ cubic s,
    readLow ((join s data + X ^ 3) %ₘ cubic s)) = data
  rw [h.1, h.2, readLow_low]

theorem join_split (s : Triple R) (p : R[X]) : join s (split s p) = p := by
  have hdeg : ((p + X ^ 3) %ₘ cubic s).degree < 3 := by
    have h := degree_modByMonic_lt (p + X ^ 3) (cubic_monic s).monic
    rwa [degree_eq_natDegree (cubic_monic s).ne_zero, (cubic_monic s).natDegree_eq] at h
  change cubic s * ((p + X ^ 3) /ₘ cubic s) +
    (X ^ 3 + low (readLow ((p + X ^ 3) %ₘ cubic s))) = p
  rw [low_readLow _ hdeg, add_left_comm, add_comm (cubic s * _),
    modByMonic_add_div (p + X ^ 3) (cubic_monic s).monic, ← add_assoc, cancel_tail]

/-- A genuine equivalence with its supplied, executable inverse. -/
noncomputable def outerEquiv (s : Triple R) : (R[X] × Triple R) ≃ R[X] where
  toFun := join s
  invFun := split s
  left_inv := split_join s
  right_inv := join_split s

/-- The fixed four-row signature of the degree-16 inner crown. -/
structure Signature (c : R[X]) : Prop where
  monic : IsMonicOfDegree c 16
  row15 : c.coeff 15 = 0
  row14 : c.coeff 14 = 0
  row13 : c.coeff 13 = 1

omit [CharP R 2] [Nontrivial R] in
/-- Four-term convolution with the known cubic, independent of the crown's
internal representation. -/
theorem cubic_mul_coeff (s : Triple R) (c : R[X]) (j : ℕ) :
    (cubic s * c).coeff (j + 3) =
      c.coeff j + s.1 * c.coeff (j + 1) + s.2.1 * c.coeff (j + 2) +
        (s.1 * s.2.1 + s.2.2) * c.coeff (j + 3) := by
  have h2 : 2 ≤ j + 3 := by omega
  have h3 : 3 ≤ j + 3 := by omega
  have e2 : j + 3 - 2 = j + 1 := by omega
  have e3 : j + 3 - 3 = j := by omega
  simp only [cubic, low, add_mul, coeff_add, mul_assoc, coeff_C_mul,
    coeff_X_mul, coeff_X_pow_mul', h2, h3, ite_true, e2, e3, add_assoc]

omit [CharP R 2] in
theorem join_coeff_high (s : Triple R) (data : R[X] × Triple R)
    (j : ℕ) (hj : 3 < j) :
    (join s data).coeff j = (cubic s * data.1).coeff j := by
  have hz : (cubic data.2).coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt ((cubic_monic data.2).natDegree_eq ▸ hj)
  rw [join, coeff_add, hz, add_zero]

omit [CharP R 2] in
theorem join_coeff18 (s : Triple R) (data : R[X] × Triple R)
    (hc : Signature data.1) : (join s data).coeff 18 = s.1 := by
  have hc16 : data.1.coeff 16 = 1 := by
    rw [← hc.monic.natDegree_eq]
    exact hc.monic.monic.coeff_natDegree
  have hc17 : data.1.coeff 17 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.monic.natDegree_eq ▸ (by omega : 16 < 17))
  have hc18 : data.1.coeff 18 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.monic.natDegree_eq ▸ (by omega : 16 < 18))
  rw [join_coeff_high s data 18 (by omega), cubic_mul_coeff s data.1 15,
    hc.row15, hc16, hc17, hc18, mul_one, mul_zero, mul_zero, zero_add, add_zero, add_zero]

omit [CharP R 2] in
theorem join_coeff17 (s : Triple R) (data : R[X] × Triple R)
    (hc : Signature data.1) : (join s data).coeff 17 = s.2.1 := by
  have hc16 : data.1.coeff 16 = 1 := by
    rw [← hc.monic.natDegree_eq]
    exact hc.monic.monic.coeff_natDegree
  have hc17 : data.1.coeff 17 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.monic.natDegree_eq ▸ (by omega : 16 < 17))
  rw [join_coeff_high s data 17 (by omega), cubic_mul_coeff s data.1 14,
    hc.row14, hc.row15, hc16, hc17, mul_zero, mul_one, mul_zero,
    zero_add, zero_add, add_zero]

omit [CharP R 2] in
theorem join_coeff16 (s : Triple R) (data : R[X] × Triple R)
    (hc : Signature data.1) : (join s data).coeff 16 = 1 + (s.1 * s.2.1 + s.2.2) := by
  have hc16 : data.1.coeff 16 = 1 := by
    rw [← hc.monic.natDegree_eq]
    exact hc.monic.monic.coeff_natDegree
  rw [join_coeff_high s data 16 (by omega), cubic_mul_coeff s data.1 13,
    hc.row13, hc.row14, hc.row15, hc16, mul_zero, mul_zero, mul_one, add_zero, add_zero]

/-- The first three displayed decoder formulas (A.20). -/
def readShell (p : R[X]) : Triple R :=
  (p.coeff 18, p.coeff 17, (p.coeff 16 + 1) + p.coeff 18 * p.coeff 17)

theorem readShell_join (s : Triple R) (data : R[X] × Triple R)
    (hc : Signature data.1) : readShell (join s data) = s := by
  simp only [readShell, join_coeff18 s data hc, join_coeff17 s data hc,
    join_coeff16 s data hc, cancel_tail]

/-- The whole outer decoder, including recovery of the formerly unknown
shell. The crown's thirteen inner keys are not yet decoded here. -/
noncomputable def decode (p : R[X]) : Triple R × (R[X] × Triple R) :=
  (readShell p, split (readShell p) p)

noncomputable def encode (data : Triple R × (R[X] × Triple R)) : R[X] :=
  join data.1 data.2

theorem decode_encode (data : Triple R × (R[X] × Triple R))
    (hc : Signature data.2.1) : decode (encode data) = data := by
  simp only [decode, encode, readShell_join data.1 data.2 hc, split_join]

theorem encode_decode (p : R[X]) : encode (decode p) = p := join_split (readShell p) p

end Nontrivial

end FastPoly.Char2Degree19Shell
