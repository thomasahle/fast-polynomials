import FastPoly.Section4.FillRec

/-!
# Appendix `A`: optimized polynomial circuits — well-formedness

Definitions of the displayed circuits of `sections/appendix_polynomials.tex`
(characteristic-2 and large-prime families), each with its monic/degree lemma.
The section's blanket claim — a circuit with `m` products outputs a monic
polynomial of degree `2m-1` — holds over every nontrivial commutative ring.
-/

namespace FastPoly

open Polynomial

variable {A : Type*} [CommRing A]

namespace Circuit

/-! A small monic-degree calculus for straight-line circuits. -/

theorem md_mul {P Q : A[X]} {m n : ℕ} (hP : P.Monic ∧ P.natDegree = m)
    (hQ : Q.Monic ∧ Q.natDegree = n) :
    (P * Q).Monic ∧ (P * Q).natDegree = m + n :=
  ⟨hP.1.mul hQ.1, by rw [hP.1.natDegree_mul hQ.1, hP.2, hQ.2]⟩

theorem md_X [Nontrivial A] : (X : A[X]).Monic ∧ (X : A[X]).natDegree = 1 :=
  ⟨monic_X, natDegree_X⟩

theorem md_linear [Nontrivial A] (b : A) :
    (X + C b).Monic ∧ (X + C b).natDegree = 1 :=
  ⟨monic_X_add_C b, natDegree_X_add_C b⟩

theorem md_add_low [Nontrivial A] {P Q : A[X]} {m k : ℕ}
    (hP : P.Monic ∧ P.natDegree = m) (hQ : Q.natDegree ≤ k) (hk : k < m) :
    (P + Q).Monic ∧ (P + Q).natDegree = m := by
  obtain ⟨hm, hd⟩ := monic_add_low (e := Q) hP.1 (Or.inr (by omega))
  exact ⟨hm, hd.trans hP.2⟩

theorem ndb_add {P Q : A[X]} {n : ℕ} (hP : P.natDegree ≤ n)
    (hQ : Q.natDegree ≤ n) : (P + Q).natDegree ≤ n :=
  le_trans (natDegree_add_le _ _) (max_le hP hQ)

theorem ndb_sub {P Q : A[X]} {n : ℕ} (hP : P.natDegree ≤ n)
    (hQ : Q.natDegree ≤ n) : (P - Q).natDegree ≤ n :=
  le_trans (natDegree_sub_le _ _) (max_le hP hQ)

theorem ndb_neg {P : A[X]} {n : ℕ} (hP : P.natDegree ≤ n) :
    (-P).natDegree ≤ n := by rwa [natDegree_neg]

theorem ndb_X {n : ℕ} (hn : 1 ≤ n) : (X : A[X]).natDegree ≤ n :=
  le_trans natDegree_X_le hn

theorem ndb_C {b : A} {n : ℕ} : (C b).natDegree ≤ n :=
  le_trans (natDegree_C b).le (Nat.zero_le n)

theorem ndb_of_md {P : A[X]} {m n : ℕ} (hP : P.Monic ∧ P.natDegree = m)
    (h : m ≤ n) : P.natDegree ≤ n := hP.2.le.trans h

theorem ndb_mul {P Q : A[X]} {m n : ℕ} (hP : P.natDegree ≤ m)
    (hQ : Q.natDegree ≤ n) : (P * Q).natDegree ≤ m + n :=
  le_trans natDegree_mul_le (Nat.add_le_add hP hQ)

end Circuit

open Circuit

/-! ## Characteristic-2 family, first circuit: 4 products, degree 7 -/

namespace Char2Four

variable (a : ℕ → A)

noncomputable def yW : A[X] := X * (X + C (a 0))
noncomputable def zW : A[X] := (X + C (a 1)) * (yW a + C (a 2))
noncomputable def tW : A[X] :=
  (X + yW a + zW a + C (a 3)) * (X + yW a + zW a)
noncomputable def uW : A[X] := (X + C (a 4)) * (yW a + tW a + C (a 5))
noncomputable def P : A[X] := uW a + C (a 6)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 7 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X (md_linear _)
  have hz : (zW a).Monic ∧ (zW a).natDegree = 3 :=
    md_mul (md_linear _) (md_add_low (k := 0) hy ndb_C (by norm_num))
  have hcore : (X + yW a + zW a).Monic ∧ (X + yW a + zW a).natDegree = 3 := by
    rw [show X + yW a + zW a = zW a + (X + yW a) from by ring]
    exact md_add_low (k := 2) hz
      (ndb_add (ndb_X (by norm_num)) (ndb_of_md hy (by norm_num))) (by norm_num)
  have hcore' : (X + yW a + zW a + C (a 3)).Monic ∧
      (X + yW a + zW a + C (a 3)).natDegree = 3 :=
    md_add_low (k := 0) hcore ndb_C (by norm_num)
  have ht : (tW a).Monic ∧ (tW a).natDegree = 6 := md_mul hcore' hcore
  have hin : (yW a + tW a + C (a 5)).Monic ∧
      (yW a + tW a + C (a 5)).natDegree = 6 := by
    rw [show yW a + tW a + C (a 5) = tW a + (yW a + C (a 5)) from by ring]
    exact md_add_low (k := 2) ht
      (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 7 := md_mul (md_linear _) hin
  exact md_add_low (k := 0) hu ndb_C (by norm_num)

end Char2Four

/-! ## Characteristic-2 family: 5 products, degree 9 -/

namespace Char2Five

variable (a : ℕ → A)

noncomputable def yW (_ : ℕ → A) : A[X] := X * X
noncomputable def zW : A[X] := (X + yW a + C (a 0)) * (X + C (a 1))
noncomputable def tW : A[X] := (zW a + C (a 2)) * (yW a + zW a + C (a 3))
noncomputable def uW : A[X] :=
  (X + zW a + tW a + C (a 4)) * (X + yW a + zW a + C (a 5))
noncomputable def vW : A[X] := (X + C (a 6)) * (yW a + C (a 7))
noncomputable def P : A[X] := uW a + vW a + C (a 8)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 9 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X md_X
  have hz : (zW a).Monic ∧ (zW a).natDegree = 3 := by
    refine md_mul (m := 2) ?_ (md_linear _)
    rw [show X + yW a + C (a 0) = yW a + (X + C (a 0)) from by ring]
    exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have ht : (tW a).Monic ∧ (tW a).natDegree = 6 := by
    refine md_mul (n := 3) (md_add_low (k := 0) hz ndb_C (by norm_num)) ?_
    rw [show yW a + zW a + C (a 3) = zW a + (yW a + C (a 3)) from by ring]
    exact md_add_low (k := 2) hz (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C)
      (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 9 := by
    refine md_mul (m := 6) (n := 3) ?_ ?_
    · rw [show X + zW a + tW a + C (a 4)
          = tW a + (X + zW a + C (a 4)) from by ring]
      exact md_add_low (k := 3) ht
        (ndb_add (ndb_add (ndb_X (by norm_num)) (ndb_of_md hz (le_refl 3)))
          ndb_C) (by norm_num)
    · rw [show X + yW a + zW a + C (a 5)
          = zW a + (X + yW a + C (a 5)) from by ring]
      exact md_add_low (k := 2) hz
        (ndb_add (ndb_add (ndb_X (by norm_num)) (ndb_of_md hy (le_refl 2)))
          ndb_C) (by norm_num)
  have hv : (vW a).Monic ∧ (vW a).natDegree = 3 :=
    md_mul (md_linear _) (md_add_low (k := 0) hy ndb_C (by norm_num))
  rw [show P a = uW a + (vW a + C (a 8)) from by rw [P]; ring]
  exact md_add_low (k := 3) hu (ndb_add (ndb_of_md hv (le_refl 3)) ndb_C)
    (by norm_num)

end Char2Five

/-! ## Characteristic-2 family: 6 products, degree 11 -/

namespace Char2Six

variable (a : ℕ → A)

noncomputable def yW : A[X] := X * (X + C (a 0))
noncomputable def zW : A[X] := (X + yW a + C (a 1)) * (X + yW a)
noncomputable def tW : A[X] := (X + zW a + C (a 2)) * (zW a + C (a 3))
noncomputable def uW : A[X] := (tW a + C (a 4)) * (X + C (a 5))
noncomputable def vW : A[X] :=
  (X + yW a + zW a + tW a + uW a + C (a 6)) * (yW a + C (a 7))
noncomputable def wW : A[X] := (X + C (a 8)) * (yW a + zW a + tW a + C (a 9))
noncomputable def P : A[X] := zW a + vW a + wW a + C (a 10)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 11 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X (md_linear _)
  have hz : (zW a).Monic ∧ (zW a).natDegree = 4 := by
    refine md_mul (m := 2) (n := 2) ?_ ?_
    · rw [show X + yW a + C (a 1) = yW a + (X + C (a 1)) from by ring]
      exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
        (by norm_num)
    · rw [show X + yW a = yW a + X from by ring]
      exact md_add_low (k := 1) hy (ndb_X (by norm_num)) (by norm_num)
  have ht : (tW a).Monic ∧ (tW a).natDegree = 8 := by
    refine md_mul (m := 4) (n := 4) ?_
      (md_add_low (k := 0) hz ndb_C (by norm_num))
    rw [show X + zW a + C (a 2) = zW a + (X + C (a 2)) from by ring]
    exact md_add_low (k := 1) hz (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 9 :=
    md_mul (md_add_low (k := 0) ht ndb_C (by norm_num)) (md_linear _)
  have hv : (vW a).Monic ∧ (vW a).natDegree = 11 := by
    refine md_mul (m := 9) (n := 2) ?_
      (md_add_low (k := 0) hy ndb_C (by norm_num))
    rw [show X + yW a + zW a + tW a + uW a + C (a 6)
        = uW a + (X + yW a + zW a + tW a + C (a 6)) from by ring]
    exact md_add_low (k := 8) hu
      (ndb_add (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
        (ndb_of_md hy (by norm_num))) (ndb_of_md hz (by norm_num)))
        (ndb_of_md ht (le_refl 8))) ndb_C) (by norm_num)
  have hw : (wW a).Monic ∧ (wW a).natDegree = 9 := by
    refine md_mul (md_linear _) (m := 1) (n := 8) ?_
    rw [show yW a + zW a + tW a + C (a 9)
        = tW a + (yW a + zW a + C (a 9)) from by ring]
    exact md_add_low (k := 4) ht
      (ndb_add (ndb_add (ndb_of_md hy (by norm_num)) (ndb_of_md hz (le_refl 4)))
        ndb_C) (by norm_num)
  rw [show P a = vW a + (zW a + wW a + C (a 10)) from by rw [P]; ring]
  exact md_add_low (k := 9) hv
    (ndb_add (ndb_add (ndb_of_md hz (by norm_num)) (ndb_of_md hw (le_refl 9)))
      ndb_C) (by norm_num)

end Char2Six

/-! ## Characteristic-2 family: 7 products, degree 13 -/

namespace Char2Seven

variable (a : ℕ → A)

noncomputable def yW (_ : ℕ → A) : A[X] := X * X
noncomputable def zW : A[X] := (yW a + C (a 0)) * (X + yW a + C (a 1))
noncomputable def tW : A[X] := (X + zW a + C (a 2)) * (X + C (a 3))
noncomputable def uW : A[X] := (X + yW a + C (a 4)) * (X + tW a + C (a 5))
noncomputable def vW : A[X] := (yW a + zW a + C (a 6)) * (uW a + C (a 7))
noncomputable def wW : A[X] :=
  (yW a + zW a + tW a + C (a 8)) * (X + uW a + C (a 9))
noncomputable def sW : A[X] :=
  (X + zW a + uW a + vW a + wW a + C (a 10)) * (X + C (a 11))
noncomputable def P : A[X] := tW a + sW a + C (a 12)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 13 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X md_X
  have hz : (zW a).Monic ∧ (zW a).natDegree = 4 := by
    refine md_mul (m := 2) (n := 2) (md_add_low (k := 0) hy ndb_C (by norm_num)) ?_
    rw [show X + yW a + C (a 1) = yW a + (X + C (a 1)) from by ring]
    exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have ht : (tW a).Monic ∧ (tW a).natDegree = 5 := by
    refine md_mul (m := 4) ?_ (md_linear _)
    rw [show X + zW a + C (a 2) = zW a + (X + C (a 2)) from by ring]
    exact md_add_low (k := 1) hz (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 7 := by
    refine md_mul (m := 2) (n := 5) ?_ ?_
    · rw [show X + yW a + C (a 4) = yW a + (X + C (a 4)) from by ring]
      exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
        (by norm_num)
    · rw [show X + tW a + C (a 5) = tW a + (X + C (a 5)) from by ring]
      exact md_add_low (k := 1) ht (ndb_add (ndb_X (by norm_num)) ndb_C)
        (by norm_num)
  have hv : (vW a).Monic ∧ (vW a).natDegree = 11 := by
    refine md_mul (m := 4) (n := 7) ?_
      (md_add_low (k := 0) hu ndb_C (by norm_num))
    rw [show yW a + zW a + C (a 6) = zW a + (yW a + C (a 6)) from by ring]
    exact md_add_low (k := 2) hz
      (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
  have hw : (wW a).Monic ∧ (wW a).natDegree = 12 := by
    refine md_mul (m := 5) (n := 7) ?_ ?_
    · rw [show yW a + zW a + tW a + C (a 8)
          = tW a + (yW a + zW a + C (a 8)) from by ring]
      exact md_add_low (k := 4) ht
        (ndb_add (ndb_add (ndb_of_md hy (by norm_num))
          (ndb_of_md hz (le_refl 4))) ndb_C) (by norm_num)
    · rw [show X + uW a + C (a 9) = uW a + (X + C (a 9)) from by ring]
      exact md_add_low (k := 1) hu (ndb_add (ndb_X (by norm_num)) ndb_C)
        (by norm_num)
  have hs : (sW a).Monic ∧ (sW a).natDegree = 13 := by
    refine md_mul (m := 12) ?_ (md_linear _)
    rw [show X + zW a + uW a + vW a + wW a + C (a 10)
        = wW a + (X + zW a + uW a + vW a + C (a 10)) from by ring]
    exact md_add_low (k := 11) hw
      (ndb_add (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
        (ndb_of_md hz (by norm_num))) (ndb_of_md hu (by norm_num)))
        (ndb_of_md hv (le_refl 11))) ndb_C) (by norm_num)
  rw [show P a = sW a + (tW a + C (a 12)) from by rw [P]; ring]
  exact md_add_low (k := 5) hs
    (ndb_add (ndb_of_md ht (le_refl 5)) ndb_C) (by norm_num)

end Char2Seven

/-! ## Characteristic-2 family: 8 products, degree 15 -/

namespace Char2Eight

variable (a : ℕ → A)

noncomputable def yW : A[X] := X * (X + C (a 0))
noncomputable def zW : A[X] := (X + C (a 1)) * (X + yW a + C (a 2))
noncomputable def tW : A[X] := (yW a + zW a + C (a 3)) * (X + zW a + C (a 4))
noncomputable def uW : A[X] :=
  (X + tW a + C (a 5)) * (yW a + zW a + tW a + C (a 6))
noncomputable def vW : A[X] :=
  (X + yW a + zW a + uW a + C (a 7)) * (yW a + C (a 8))
noncomputable def wW : A[X] := (yW a + C (a 9)) * (zW a + C (a 10))
noncomputable def sW : A[X] :=
  (X + yW a + zW a + tW a + uW a + wW a + C (a 11)) * (X + yW a + C (a 12))
noncomputable def rW : A[X] := X * (X + yW a + vW a + wW a + C (a 13))
noncomputable def P : A[X] := sW a + rW a + C (a 14)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 15 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X (md_linear _)
  have hz : (zW a).Monic ∧ (zW a).natDegree = 3 := by
    refine md_mul (m := 1) (n := 2) (md_linear _) ?_
    rw [show X + yW a + C (a 2) = yW a + (X + C (a 2)) from by ring]
    exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have ht : (tW a).Monic ∧ (tW a).natDegree = 6 := by
    refine md_mul (m := 3) (n := 3) ?_ ?_
    · rw [show yW a + zW a + C (a 3) = zW a + (yW a + C (a 3)) from by ring]
      exact md_add_low (k := 2) hz
        (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
    · rw [show X + zW a + C (a 4) = zW a + (X + C (a 4)) from by ring]
      exact md_add_low (k := 1) hz (ndb_add (ndb_X (by norm_num)) ndb_C)
        (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 12 := by
    refine md_mul (m := 6) (n := 6) ?_ ?_
    · rw [show X + tW a + C (a 5) = tW a + (X + C (a 5)) from by ring]
      exact md_add_low (k := 1) ht (ndb_add (ndb_X (by norm_num)) ndb_C)
        (by norm_num)
    · rw [show yW a + zW a + tW a + C (a 6)
          = tW a + (yW a + zW a + C (a 6)) from by ring]
      exact md_add_low (k := 3) ht
        (ndb_add (ndb_add (ndb_of_md hy (by norm_num))
          (ndb_of_md hz (le_refl 3))) ndb_C) (by norm_num)
  have hv : (vW a).Monic ∧ (vW a).natDegree = 14 := by
    refine md_mul (m := 12) (n := 2) ?_
      (md_add_low (k := 0) hy ndb_C (by norm_num))
    rw [show X + yW a + zW a + uW a + C (a 7)
        = uW a + (X + yW a + zW a + C (a 7)) from by ring]
    exact md_add_low (k := 3) hu
      (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
        (ndb_of_md hy (by norm_num))) (ndb_of_md hz (le_refl 3))) ndb_C)
      (by norm_num)
  have hw : (wW a).Monic ∧ (wW a).natDegree = 5 :=
    md_mul (md_add_low (k := 0) hy ndb_C (by norm_num))
      (md_add_low (k := 0) hz ndb_C (by norm_num))
  have hs : (sW a).Monic ∧ (sW a).natDegree = 14 := by
    refine md_mul (m := 12) (n := 2) ?_ ?_
    · rw [show X + yW a + zW a + tW a + uW a + wW a + C (a 11)
          = uW a + (X + yW a + zW a + tW a + wW a + C (a 11)) from by ring]
      exact md_add_low (k := 6) hu
        (ndb_add (ndb_add (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
          (ndb_of_md hy (by norm_num))) (ndb_of_md hz (by norm_num)))
          (ndb_of_md ht (le_refl 6))) (ndb_of_md hw (by norm_num))) ndb_C)
        (by norm_num)
    · rw [show X + yW a + C (a 12) = yW a + (X + C (a 12)) from by ring]
      exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
        (by norm_num)
  have hr : (rW a).Monic ∧ (rW a).natDegree = 15 := by
    refine md_mul (m := 1) (n := 14) md_X ?_
    rw [show X + yW a + vW a + wW a + C (a 13)
        = vW a + (X + yW a + wW a + C (a 13)) from by ring]
    exact md_add_low (k := 5) hv
      (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
        (ndb_of_md hy (by norm_num))) (ndb_of_md hw (le_refl 5))) ndb_C)
      (by norm_num)
  rw [show P a = rW a + (sW a + C (a 14)) from by rw [P]; ring]
  exact md_add_low (k := 14) hr
    (ndb_add (ndb_of_md hs (le_refl 14)) ndb_C) (by norm_num)

end Char2Eight

/-! ## Characteristic-2 family: 9 products, degree 17 -/

namespace Char2Nine

variable (a : ℕ → A)

noncomputable def yW : A[X] := X * (X + C (a 0))
noncomputable def zW : A[X] := (X + yW a + C (a 1)) * (yW a + C (a 2))
noncomputable def tW : A[X] := (yW a + C (a 3)) * (X + C (a 4))
noncomputable def uW : A[X] :=
  (X + yW a + zW a + tW a + C (a 5)) * (X + yW a + tW a + C (a 6))
noncomputable def vW : A[X] :=
  (tW a + C (a 7)) * (X + yW a + zW a + tW a + uW a + C (a 8))
noncomputable def wW : A[X] := (tW a + C (a 9)) * (X + yW a + C (a 10))
noncomputable def sW : A[X] := (yW a + uW a + C (a 11)) * (X + zW a + uW a)
noncomputable def rW : A[X] :=
  (X + tW a + wW a + sW a + C (a 12)) * (X + tW a + C (a 13))
noncomputable def qW : A[X] := (tW a + uW a + C (a 14)) * (zW a + tW a + C (a 15))
noncomputable def P : A[X] := yW a + vW a + rW a + qW a + C (a 16)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 17 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X (md_linear _)
  have hz : (zW a).Monic ∧ (zW a).natDegree = 4 := by
    refine md_mul (m := 2) (n := 2) ?_
      (md_add_low (k := 0) hy ndb_C (by norm_num))
    rw [show X + yW a + C (a 1) = yW a + (X + C (a 1)) from by ring]
    exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have ht : (tW a).Monic ∧ (tW a).natDegree = 3 :=
    md_mul (md_add_low (k := 0) hy ndb_C (by norm_num)) (md_linear _)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 7 := by
    refine md_mul (m := 4) (n := 3) ?_ ?_
    · rw [show X + yW a + zW a + tW a + C (a 5)
          = zW a + (X + yW a + tW a + C (a 5)) from by ring]
      exact md_add_low (k := 3) hz
        (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
          (ndb_of_md hy (by norm_num))) (ndb_of_md ht (le_refl 3))) ndb_C)
        (by norm_num)
    · rw [show X + yW a + tW a + C (a 6)
          = tW a + (X + yW a + C (a 6)) from by ring]
      exact md_add_low (k := 2) ht
        (ndb_add (ndb_add (ndb_X (by norm_num)) (ndb_of_md hy (le_refl 2)))
          ndb_C) (by norm_num)
  have hv : (vW a).Monic ∧ (vW a).natDegree = 10 := by
    refine md_mul (m := 3) (n := 7)
      (md_add_low (k := 0) ht ndb_C (by norm_num)) ?_
    rw [show X + yW a + zW a + tW a + uW a + C (a 8)
        = uW a + (X + yW a + zW a + tW a + C (a 8)) from by ring]
    exact md_add_low (k := 4) hu
      (ndb_add (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
        (ndb_of_md hy (by norm_num))) (ndb_of_md hz (le_refl 4)))
        (ndb_of_md ht (by norm_num))) ndb_C) (by norm_num)
  have hw : (wW a).Monic ∧ (wW a).natDegree = 5 := by
    refine md_mul (m := 3) (n := 2)
      (md_add_low (k := 0) ht ndb_C (by norm_num)) ?_
    rw [show X + yW a + C (a 10) = yW a + (X + C (a 10)) from by ring]
    exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have hs : (sW a).Monic ∧ (sW a).natDegree = 14 := by
    refine md_mul (m := 7) (n := 7) ?_ ?_
    · rw [show yW a + uW a + C (a 11) = uW a + (yW a + C (a 11)) from by ring]
      exact md_add_low (k := 2) hu
        (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
    · rw [show X + zW a + uW a = uW a + (X + zW a) from by ring]
      exact md_add_low (k := 4) hu
        (ndb_add (ndb_X (by norm_num)) (ndb_of_md hz (le_refl 4)))
        (by norm_num)
  have hr : (rW a).Monic ∧ (rW a).natDegree = 17 := by
    refine md_mul (m := 14) (n := 3) ?_ ?_
    · rw [show X + tW a + wW a + sW a + C (a 12)
          = sW a + (X + tW a + wW a + C (a 12)) from by ring]
      exact md_add_low (k := 5) hs
        (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
          (ndb_of_md ht (by norm_num))) (ndb_of_md hw (le_refl 5))) ndb_C)
        (by norm_num)
    · rw [show X + tW a + C (a 13) = tW a + (X + C (a 13)) from by ring]
      exact md_add_low (k := 1) ht (ndb_add (ndb_X (by norm_num)) ndb_C)
        (by norm_num)
  have hq : (qW a).Monic ∧ (qW a).natDegree = 11 := by
    refine md_mul (m := 7) (n := 4) ?_ ?_
    · rw [show tW a + uW a + C (a 14) = uW a + (tW a + C (a 14)) from by ring]
      exact md_add_low (k := 3) hu
        (ndb_add (ndb_of_md ht (le_refl 3)) ndb_C) (by norm_num)
    · rw [show zW a + tW a + C (a 15) = zW a + (tW a + C (a 15)) from by ring]
      exact md_add_low (k := 3) hz
        (ndb_add (ndb_of_md ht (le_refl 3)) ndb_C) (by norm_num)
  rw [show P a = rW a + (yW a + vW a + qW a + C (a 16)) from by rw [P]; ring]
  exact md_add_low (k := 11) hr
    (ndb_add (ndb_add (ndb_add (ndb_of_md hy (by norm_num))
      (ndb_of_md hv (by norm_num))) (ndb_of_md hq (le_refl 11))) ndb_C)
    (by norm_num)

end Char2Nine

/-! ## Large-prime family: 4 products, degree 7 -/

namespace PrimeFour

variable (a : ℕ → A)

noncomputable def yW : A[X] := X * (X + C (a 0))
noncomputable def zW : A[X] := (X + C (a 1)) * (yW a + C (a 2))
noncomputable def tW : A[X] := (X + zW a + C (a 3)) * X
noncomputable def uW : A[X] := (tW a + C (a 4)) * (zW a + C (a 5))
noncomputable def P : A[X] := yW a + uW a + C (a 6)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 7 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X (md_linear _)
  have hz : (zW a).Monic ∧ (zW a).natDegree = 3 :=
    md_mul (md_linear _) (md_add_low (k := 0) hy ndb_C (by norm_num))
  have ht : (tW a).Monic ∧ (tW a).natDegree = 4 := by
    refine md_mul (m := 3) (n := 1) ?_ md_X
    rw [show X + zW a + C (a 3) = zW a + (X + C (a 3)) from by ring]
    exact md_add_low (k := 1) hz (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 7 :=
    md_mul (md_add_low (k := 0) ht ndb_C (by norm_num))
      (md_add_low (k := 0) hz ndb_C (by norm_num))
  rw [show P a = uW a + (yW a + C (a 6)) from by rw [P]; ring]
  exact md_add_low (k := 2) hu
    (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)

end PrimeFour

/-! ## Large-prime family: 5 products, degree 9 -/

namespace PrimeFive

variable (a : ℕ → A)

noncomputable def yW (_ : ℕ → A) : A[X] := X * X
noncomputable def zW : A[X] := (X + yW a + C (a 0)) * (yW a + C (a 1))
noncomputable def tW : A[X] := (yW a + zW a + C (a 2)) * (X + C (a 3))
noncomputable def uW : A[X] := (zW a + C (a 4)) * (tW a + C (a 5))
noncomputable def vW : A[X] := (X + C (a 6)) * (yW a + C (a 7))
noncomputable def P : A[X] := uW a + vW a + C (a 8)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 9 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X md_X
  have hz : (zW a).Monic ∧ (zW a).natDegree = 4 := by
    refine md_mul (m := 2) (n := 2) ?_
      (md_add_low (k := 0) hy ndb_C (by norm_num))
    rw [show X + yW a + C (a 0) = yW a + (X + C (a 0)) from by ring]
    exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have ht : (tW a).Monic ∧ (tW a).natDegree = 5 := by
    refine md_mul (m := 4) (n := 1) ?_ (md_linear _)
    rw [show yW a + zW a + C (a 2) = zW a + (yW a + C (a 2)) from by ring]
    exact md_add_low (k := 2) hz
      (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 9 :=
    md_mul (md_add_low (k := 0) hz ndb_C (by norm_num))
      (md_add_low (k := 0) ht ndb_C (by norm_num))
  have hv : (vW a).Monic ∧ (vW a).natDegree = 3 :=
    md_mul (md_linear _) (md_add_low (k := 0) hy ndb_C (by norm_num))
  rw [show P a = uW a + (vW a + C (a 8)) from by rw [P]; ring]
  exact md_add_low (k := 3) hu
    (ndb_add (ndb_of_md hv (le_refl 3)) ndb_C) (by norm_num)

end PrimeFive

/-! ## Large-prime family: 6 products, degree 11 -/

namespace PrimeSix

variable (a : ℕ → A)

noncomputable def yW : A[X] := X * (X + C (a 0))
noncomputable def zW : A[X] := (yW a + C (a 1)) * (X + yW a + C (a 2))
noncomputable def tW : A[X] := (yW a + zW a + C (a 3)) * (X + C (a 4))
noncomputable def uW : A[X] := (yW a + tW a + C (a 5)) * (tW a + C (a 6))
noncomputable def vW : A[X] := (yW a + C (a 7)) * (zW a + C (a 8))
noncomputable def wW : A[X] := (uW a + C (a 9)) * X
noncomputable def P : A[X] := vW a + wW a + C (a 10)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 11 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X (md_linear _)
  have hz : (zW a).Monic ∧ (zW a).natDegree = 4 := by
    refine md_mul (m := 2) (n := 2)
      (md_add_low (k := 0) hy ndb_C (by norm_num)) ?_
    rw [show X + yW a + C (a 2) = yW a + (X + C (a 2)) from by ring]
    exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have ht : (tW a).Monic ∧ (tW a).natDegree = 5 := by
    refine md_mul (m := 4) (n := 1) ?_ (md_linear _)
    rw [show yW a + zW a + C (a 3) = zW a + (yW a + C (a 3)) from by ring]
    exact md_add_low (k := 2) hz
      (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 10 := by
    refine md_mul (m := 5) (n := 5) ?_
      (md_add_low (k := 0) ht ndb_C (by norm_num))
    rw [show yW a + tW a + C (a 5) = tW a + (yW a + C (a 5)) from by ring]
    exact md_add_low (k := 2) ht
      (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
  have hv : (vW a).Monic ∧ (vW a).natDegree = 6 :=
    md_mul (md_add_low (k := 0) hy ndb_C (by norm_num))
      (md_add_low (k := 0) hz ndb_C (by norm_num))
  have hw : (wW a).Monic ∧ (wW a).natDegree = 11 :=
    md_mul (md_add_low (k := 0) hu ndb_C (by norm_num)) md_X
  rw [show P a = wW a + (vW a + C (a 10)) from by rw [P]; ring]
  exact md_add_low (k := 6) hw
    (ndb_add (ndb_of_md hv (le_refl 6)) ndb_C) (by norm_num)

end PrimeSix

/-! ## Large-prime family: 7 products, degree 13 -/

namespace PrimeSeven

variable (a : ℕ → A)

noncomputable def yW (_ : ℕ → A) : A[X] := X * X
noncomputable def zW : A[X] := (yW a + C (a 0)) * (X + yW a + C (a 1))
noncomputable def tW : A[X] := (yW a + zW a + C (a 2)) * (X + C (a 3))
noncomputable def uW : A[X] := (yW a + zW a + C (a 4)) * (zW a + C (a 5))
noncomputable def vW : A[X] := (zW a + tW a + C (a 6)) * (zW a + uW a + C (a 7))
noncomputable def wW : A[X] := (yW a + C (a 8)) * (X + C (a 9))
noncomputable def sW : A[X] :=
  (X + yW a + zW a + tW a + uW a + wW a + C (a 10)) * (X + C (a 11))
noncomputable def P : A[X] := vW a + sW a + C (a 12)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 13 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X md_X
  have hz : (zW a).Monic ∧ (zW a).natDegree = 4 := by
    refine md_mul (m := 2) (n := 2)
      (md_add_low (k := 0) hy ndb_C (by norm_num)) ?_
    rw [show X + yW a + C (a 1) = yW a + (X + C (a 1)) from by ring]
    exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have ht : (tW a).Monic ∧ (tW a).natDegree = 5 := by
    refine md_mul (m := 4) (n := 1) ?_ (md_linear _)
    rw [show yW a + zW a + C (a 2) = zW a + (yW a + C (a 2)) from by ring]
    exact md_add_low (k := 2) hz
      (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 8 := by
    refine md_mul (m := 4) (n := 4) ?_
      (md_add_low (k := 0) hz ndb_C (by norm_num))
    rw [show yW a + zW a + C (a 4) = zW a + (yW a + C (a 4)) from by ring]
    exact md_add_low (k := 2) hz
      (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
  have hv : (vW a).Monic ∧ (vW a).natDegree = 13 := by
    refine md_mul (m := 5) (n := 8) ?_ ?_
    · rw [show zW a + tW a + C (a 6) = tW a + (zW a + C (a 6)) from by ring]
      exact md_add_low (k := 4) ht
        (ndb_add (ndb_of_md hz (le_refl 4)) ndb_C) (by norm_num)
    · rw [show zW a + uW a + C (a 7) = uW a + (zW a + C (a 7)) from by ring]
      exact md_add_low (k := 4) hu
        (ndb_add (ndb_of_md hz (le_refl 4)) ndb_C) (by norm_num)
  have hw : (wW a).Monic ∧ (wW a).natDegree = 3 :=
    md_mul (md_add_low (k := 0) hy ndb_C (by norm_num)) (md_linear _)
  have hs : (sW a).Monic ∧ (sW a).natDegree = 9 := by
    refine md_mul (m := 8) (n := 1) ?_ (md_linear _)
    rw [show X + yW a + zW a + tW a + uW a + wW a + C (a 10)
        = uW a + (X + yW a + zW a + tW a + wW a + C (a 10)) from by ring]
    exact md_add_low (k := 5) hu
      (ndb_add (ndb_add (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
        (ndb_of_md hy (by norm_num))) (ndb_of_md hz (by norm_num)))
        (ndb_of_md ht (le_refl 5))) (ndb_of_md hw (by norm_num))) ndb_C)
      (by norm_num)
  rw [show P a = vW a + (sW a + C (a 12)) from by rw [P]; ring]
  exact md_add_low (k := 9) hv
    (ndb_add (ndb_of_md hs (le_refl 9)) ndb_C) (by norm_num)

end PrimeSeven

/-! ## Large-prime family: 8 products, degree 15 -/

namespace PrimeEight

variable (a : ℕ → A)

noncomputable def yW : A[X] := X * (X + C (a 0))
noncomputable def zW : A[X] := (yW a + C (a 1)) * X
noncomputable def tW : A[X] := (zW a + C (a 2)) * (X + yW a + zW a + C (a 3))
noncomputable def uW : A[X] := (yW a + tW a + C (a 4)) * (zW a + tW a + C (a 5))
noncomputable def vW : A[X] := (tW a + C (a 6)) * (X + tW a + C (a 7))
noncomputable def wW : A[X] := (tW a + C (a 8)) * (X + C (a 9))
noncomputable def sW : A[X] := (zW a + C (a 10)) * (X + yW a + vW a + C (a 11))
noncomputable def rW : A[X] := (yW a + C (a 12)) * (uW a + vW a + C (a 13))
noncomputable def P : A[X] := wW a + sW a + rW a + C (a 14)

variable [Nontrivial A]

theorem good : (P a).Monic ∧ (P a).natDegree = 15 := by
  have hy : (yW a).Monic ∧ (yW a).natDegree = 2 := md_mul md_X (md_linear _)
  have hz : (zW a).Monic ∧ (zW a).natDegree = 3 :=
    md_mul (md_add_low (k := 0) hy ndb_C (by norm_num)) md_X
  have ht : (tW a).Monic ∧ (tW a).natDegree = 6 := by
    refine md_mul (m := 3) (n := 3)
      (md_add_low (k := 0) hz ndb_C (by norm_num)) ?_
    rw [show X + yW a + zW a + C (a 3)
        = zW a + (X + yW a + C (a 3)) from by ring]
    exact md_add_low (k := 2) hz
      (ndb_add (ndb_add (ndb_X (by norm_num)) (ndb_of_md hy (le_refl 2)))
        ndb_C) (by norm_num)
  have hu : (uW a).Monic ∧ (uW a).natDegree = 12 := by
    refine md_mul (m := 6) (n := 6) ?_ ?_
    · rw [show yW a + tW a + C (a 4) = tW a + (yW a + C (a 4)) from by ring]
      exact md_add_low (k := 2) ht
        (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
    · rw [show zW a + tW a + C (a 5) = tW a + (zW a + C (a 5)) from by ring]
      exact md_add_low (k := 3) ht
        (ndb_add (ndb_of_md hz (le_refl 3)) ndb_C) (by norm_num)
  have hv : (vW a).Monic ∧ (vW a).natDegree = 12 := by
    refine md_mul (m := 6) (n := 6)
      (md_add_low (k := 0) ht ndb_C (by norm_num)) ?_
    rw [show X + tW a + C (a 7) = tW a + (X + C (a 7)) from by ring]
    exact md_add_low (k := 1) ht (ndb_add (ndb_X (by norm_num)) ndb_C)
      (by norm_num)
  have hw : (wW a).Monic ∧ (wW a).natDegree = 7 :=
    md_mul (md_add_low (k := 0) ht ndb_C (by norm_num)) (md_linear _)
  have hs : (sW a).Monic ∧ (sW a).natDegree = 15 := by
    refine md_mul (m := 3) (n := 12)
      (md_add_low (k := 0) hz ndb_C (by norm_num)) ?_
    rw [show X + yW a + vW a + C (a 11)
        = vW a + (X + yW a + C (a 11)) from by ring]
    exact md_add_low (k := 2) hv
      (ndb_add (ndb_add (ndb_X (by norm_num)) (ndb_of_md hy (le_refl 2)))
        ndb_C) (by norm_num)
  have hrb : (rW a).natDegree ≤ 14 := by
    refine le_trans (natDegree_mul_le (p := yW a + C (a 12))) ?_
    have h1 : (yW a + C (a 12)).natDegree ≤ 2 :=
      ndb_add (ndb_of_md hy (le_refl 2)) ndb_C
    have h2 : (uW a + vW a + C (a 13)).natDegree ≤ 12 :=
      ndb_add (ndb_add (ndb_of_md hu (le_refl 12))
        (ndb_of_md hv (le_refl 12))) ndb_C
    omega
  rw [show P a = sW a + (wW a + rW a + C (a 14)) from by rw [P]; ring]
  exact md_add_low (k := 14) hs
    (ndb_add (ndb_add (ndb_of_md hw (by norm_num)) hrb) ndb_C) (by norm_num)

end PrimeEight

/-! ## The proved general construction at degree 17 (9 products), reduced keys -/

namespace Chain17

variable (b : ℕ → A)

noncomputable def yW : A[X] := (X + C (b 16)) * X
noncomputable def zW : A[X] :=
  (X + yW b + C (b 13)) * (-X + yW b + C (b 15))
noncomputable def tW : A[X] :=
  (X + yW b + zW b + C (b 11)) * (-X - yW b + zW b + C (b 12))
noncomputable def uW : A[X] :=
  (yW b + zW b + C (b 10)) * (-(yW b) + zW b + C (b 14))
noncomputable def vW : A[X] := (X + C (b 7)) * (yW b + C (b 6))
noncomputable def wW : A[X] := (X + C (b 3)) * (yW b + C (b 2))
noncomputable def sW : A[X] :=
  (X + zW b + tW b + vW b + C (b 5)) * (X - zW b + tW b - vW b + C (b 9))
noncomputable def rW : A[X] :=
  (zW b + uW b + C (b 4)) * (-(zW b) + uW b + C (b 8))
noncomputable def qW : A[X] := (wW b + sW b + C (b 1)) * X
noncomputable def P : A[X] := rW b + qW b + C (b 0)

variable [Nontrivial A]

theorem good : (P b).Monic ∧ (P b).natDegree = 17 := by
  have hy : (yW b).Monic ∧ (yW b).natDegree = 2 := md_mul (md_linear _) md_X
  have hz : (zW b).Monic ∧ (zW b).natDegree = 4 := by
    refine md_mul (m := 2) (n := 2) ?_ ?_
    · rw [show X + yW b + C (b 13) = yW b + (X + C (b 13)) from by ring]
      exact md_add_low (k := 1) hy (ndb_add (ndb_X (by norm_num)) ndb_C)
        (by norm_num)
    · rw [show -X + yW b + C (b 15) = yW b + (-X + C (b 15)) from by ring]
      exact md_add_low (k := 1) hy
        (ndb_add (ndb_neg (ndb_X (by norm_num))) ndb_C) (by norm_num)
  have ht : (tW b).Monic ∧ (tW b).natDegree = 8 := by
    refine md_mul (m := 4) (n := 4) ?_ ?_
    · rw [show X + yW b + zW b + C (b 11)
          = zW b + (X + yW b + C (b 11)) from by ring]
      exact md_add_low (k := 2) hz
        (ndb_add (ndb_add (ndb_X (by norm_num)) (ndb_of_md hy (le_refl 2)))
          ndb_C) (by norm_num)
    · rw [show -X - yW b + zW b + C (b 12)
          = zW b + (-X - yW b + C (b 12)) from by ring]
      exact md_add_low (k := 2) hz
        (ndb_add (ndb_sub (ndb_neg (ndb_X (by norm_num)))
          (ndb_of_md hy (le_refl 2))) ndb_C) (by norm_num)
  have hu : (uW b).Monic ∧ (uW b).natDegree = 8 := by
    refine md_mul (m := 4) (n := 4) ?_ ?_
    · rw [show yW b + zW b + C (b 10) = zW b + (yW b + C (b 10)) from by ring]
      exact md_add_low (k := 2) hz
        (ndb_add (ndb_of_md hy (le_refl 2)) ndb_C) (by norm_num)
    · rw [show -(yW b) + zW b + C (b 14)
          = zW b + (-(yW b) + C (b 14)) from by ring]
      exact md_add_low (k := 2) hz
        (ndb_add (ndb_neg (ndb_of_md hy (le_refl 2))) ndb_C) (by norm_num)
  have hv : (vW b).Monic ∧ (vW b).natDegree = 3 :=
    md_mul (md_linear _) (md_add_low (k := 0) hy ndb_C (by norm_num))
  have hw : (wW b).Monic ∧ (wW b).natDegree = 3 :=
    md_mul (md_linear _) (md_add_low (k := 0) hy ndb_C (by norm_num))
  have hs : (sW b).Monic ∧ (sW b).natDegree = 16 := by
    refine md_mul (m := 8) (n := 8) ?_ ?_
    · rw [show X + zW b + tW b + vW b + C (b 5)
          = tW b + (X + zW b + vW b + C (b 5)) from by ring]
      exact md_add_low (k := 4) ht
        (ndb_add (ndb_add (ndb_add (ndb_X (by norm_num))
          (ndb_of_md hz (le_refl 4))) (ndb_of_md hv (by norm_num))) ndb_C)
        (by norm_num)
    · rw [show X - zW b + tW b - vW b + C (b 9)
          = tW b + (X - zW b - vW b + C (b 9)) from by ring]
      exact md_add_low (k := 4) ht
        (ndb_add (ndb_sub (ndb_sub (ndb_X (by norm_num))
          (ndb_of_md hz (le_refl 4))) (ndb_of_md hv (by norm_num))) ndb_C)
        (by norm_num)
  have hr : (rW b).Monic ∧ (rW b).natDegree = 16 := by
    refine md_mul (m := 8) (n := 8) ?_ ?_
    · rw [show zW b + uW b + C (b 4) = uW b + (zW b + C (b 4)) from by ring]
      exact md_add_low (k := 4) hu
        (ndb_add (ndb_of_md hz (le_refl 4)) ndb_C) (by norm_num)
    · rw [show -(zW b) + uW b + C (b 8)
          = uW b + (-(zW b) + C (b 8)) from by ring]
      exact md_add_low (k := 4) hu
        (ndb_add (ndb_neg (ndb_of_md hz (le_refl 4))) ndb_C) (by norm_num)
  have hq : (qW b).Monic ∧ (qW b).natDegree = 17 := by
    refine md_mul (m := 16) (n := 1) ?_ md_X
    rw [show wW b + sW b + C (b 1) = sW b + (wW b + C (b 1)) from by ring]
    exact md_add_low (k := 3) hs
      (ndb_add (ndb_of_md hw (le_refl 3)) ndb_C) (by norm_num)
  rw [show P b = qW b + (rW b + C (b 0)) from by rw [P]; ring]
  exact md_add_low (k := 16) hq
    (ndb_add (ndb_of_md hr (le_refl 16)) ndb_C) (by norm_num)

end Chain17

end FastPoly
