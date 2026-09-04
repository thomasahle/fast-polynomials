import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Tactic.Ring

/-!
# Low-jet congruence and coefficient closure

Two small bookkeeping calculi shared by the barred-gadget decoders:

* `JetEq n p q` — equality of the first `n` coefficients, encoded as congruence
  modulo `X^n` (divisibility keeps all closure arguments exact and avoids ever
  expanding a large circuit);
* `CoeffsIn S p` — every coefficient of `p` lies in the subalgebra `S`.

Both are deliberately narrow: plain Mathlib imports, no dependence on the rest
of the library.
-/

namespace FastPoly

open Polynomial

section JetEq

variable {A : Type*} [CommRing A]

/-- Equality through row `n-1` of two coefficient jets: congruence modulo `X^n`. -/
def JetEq (n : ℕ) (p q : A[X]) : Prop := X ^ n ∣ p - q

namespace JetEq

theorem refl (n : ℕ) (p : A[X]) : JetEq n p p := by
  rw [JetEq, sub_self]
  exact dvd_zero _

theorem of_eq {n : ℕ} {p q : A[X]} (h : p = q) : JetEq n p q := by
  subst q
  exact refl n p

theorem coeff_eq {n i : ℕ} {p q : A[X]} (h : JetEq n p q) (hi : i < n) :
    p.coeff i = q.coeff i := by
  have hz : (p - q).coeff i = 0 := (Polynomial.X_pow_dvd_iff.mp h) i hi
  rw [coeff_sub] at hz
  exact sub_eq_zero.mp hz

theorem trans {n : ℕ} {p q r : A[X]} (hpq : JetEq n p q) (hqr : JetEq n q r) :
    JetEq n p r := by
  rw [JetEq] at hpq hqr ⊢
  have hsum : X ^ n ∣ (p - q) + (q - r) := dvd_add hpq hqr
  convert hsum using 1
  all_goals ring

theorem add {n : ℕ} {p q r s : A[X]} (hpq : JetEq n p q) (hrs : JetEq n r s) :
    JetEq n (p + r) (q + s) := by
  rw [JetEq] at hpq hrs ⊢
  have hsum : X ^ n ∣ (p - q) + (r - s) := dvd_add hpq hrs
  convert hsum using 1
  all_goals ring

theorem mul {n : ℕ} {p q r s : A[X]} (hpq : JetEq n p q) (hrs : JetEq n r s) :
    JetEq n (p * r) (q * s) := by
  rw [JetEq] at hpq hrs ⊢
  have h₁ : X ^ n ∣ (p - q) * r := dvd_mul_of_dvd_left hpq r
  have h₂ : X ^ n ∣ q * (r - s) := dvd_mul_of_dvd_right hrs q
  have hsum : X ^ n ∣ (p - q) * r + q * (r - s) := dvd_add h₁ h₂
  convert hsum using 1
  all_goals ring

theorem pow {n : ℕ} {p q : A[X]} (h : JetEq n p q) :
    ∀ m, JetEq n (p ^ m) (q ^ m)
  | 0 => of_eq (by simp)
  | m + 1 => by
      rw [pow_succ, pow_succ]
      exact (pow h m).mul h

theorem add_right {n : ℕ} {p q : A[X]} (r : A[X]) (h : JetEq n p q) :
    JetEq n (p + r) (q + r) := h.add (refl n r)

theorem mul_left {n : ℕ} (p : A[X]) {q r : A[X]} (h : JetEq n q r) :
    JetEq n (p * q) (p * r) := (refl n p).mul h

theorem mul_right {n : ℕ} {p q : A[X]} (r : A[X]) (h : JetEq n p q) :
    JetEq n (p * r) (q * r) := h.mul (refl n r)

theorem mono {n m : ℕ} (hnm : n ≤ m) {p q : A[X]} (h : JetEq m p q) :
    JetEq n p q := by
  rw [JetEq] at h ⊢
  exact dvd_trans (pow_dvd_pow X hnm) h

theorem zero_X_pow_mul (n : ℕ) (p : A[X]) : JetEq n (X ^ n * p) 0 := by
  rw [JetEq, sub_zero]
  exact dvd_mul_right _ _

theorem zero_of_X_pow_dvd {n : ℕ} {p : A[X]} (h : X ^ n ∣ p) : JetEq n p 0 := by
  simpa only [JetEq, sub_zero]

/-- A term starting in row `e` vanishes from every shorter jet. -/
theorem zero_X_pow_mul_of_le {n e : ℕ} (hne : n ≤ e) (p : A[X]) :
    JetEq n (X ^ e * p) 0 := by
  rw [JetEq, sub_zero]
  exact dvd_mul_of_dvd_left (pow_dvd_pow X hne) p

/-- `zero_X_pow_mul_of_le` under its original degree-15 name. -/
theorem zero_of_le {n m : ℕ} (h : n ≤ m) (p : A[X]) : JetEq n (X ^ m * p) 0 :=
  zero_X_pow_mul_of_le h p

/-- Adding a term that starts beyond the visible precision changes no visible row. -/
theorem add_high {n e : ℕ} (hne : n ≤ e) (p q : A[X]) :
    JetEq n (p + X ^ e * q) p := by
  rw [JetEq]
  have h : X ^ n ∣ X ^ e * q := dvd_mul_of_dvd_left (pow_dvd_pow X hne) q
  convert h using 1
  ring

end JetEq

end JetEq

section CoeffsIn

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- All coefficients of `p` belong to the subalgebra `S`. -/
def CoeffsIn (S : Subalgebra R A) (p : A[X]) : Prop := ∀ i, p.coeff i ∈ S

namespace CoeffsIn

theorem zero (S : Subalgebra R A) : CoeffsIn S (0 : A[X]) := by
  intro i
  rw [coeff_zero]
  exact Subalgebra.zero_mem _

theorem one (S : Subalgebra R A) : CoeffsIn S (1 : A[X]) := by
  intro i
  rw [coeff_one]
  split <;> simp

theorem X (S : Subalgebra R A) : CoeffsIn S (X : A[X]) := by
  intro i
  rw [coeff_X]
  split <;> simp

theorem C {S : Subalgebra R A} {z : A} (hz : z ∈ S) : CoeffsIn S (C z) := by
  intro i
  rw [coeff_C]
  split
  · exact hz
  · exact Subalgebra.zero_mem _

theorem add {S : Subalgebra R A} {p q : A[X]}
    (hp : CoeffsIn S p) (hq : CoeffsIn S q) : CoeffsIn S (p + q) := by
  intro i
  rw [coeff_add]
  exact Subalgebra.add_mem _ (hp i) (hq i)

theorem sub {S : Subalgebra R A} {p q : A[X]}
    (hp : CoeffsIn S p) (hq : CoeffsIn S q) : CoeffsIn S (p - q) := by
  intro i
  rw [coeff_sub]
  exact Subalgebra.sub_mem _ (hp i) (hq i)

theorem mul {S : Subalgebra R A} {p q : A[X]}
    (hp : CoeffsIn S p) (hq : CoeffsIn S q) : CoeffsIn S (p * q) := by
  intro i
  rw [coeff_mul]
  exact Subalgebra.sum_mem _ fun x _ => Subalgebra.mul_mem _ (hp x.1) (hq x.2)

theorem pow {S : Subalgebra R A} {p : A[X]} (hp : CoeffsIn S p) (n : ℕ) :
    CoeffsIn S (p ^ n) := by
  induction n with
  | zero => simpa using one S
  | succ n ih => simpa [pow_succ] using ih.mul hp

theorem nsmul {S : Subalgebra R A} {p : A[X]} (hp : CoeffsIn S p) (n : ℕ) :
    CoeffsIn S (n • p) := by
  intro i
  rw [coeff_smul, nsmul_eq_mul]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ n) (hp i)

end CoeffsIn

end CoeffsIn

end FastPoly
