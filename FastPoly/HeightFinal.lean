import FastPoly.Main
import FastPoly.Admissible
import FastPoly.Cost.PolynomialProgram
import FastPoly.Cost.SepticProgram
import FastPoly.Height.Depth

/-!
# Height of the complete polynomial (`thm:construction-height`, final clause)

`odd_realizable_pairs` carries, for every odd `n ≥ 3`, `n ≠ 7`, one fixed
`Cost.JointPairProgram` of `(n-1)/2` products whose two pair outputs sit at
multiplicative depth at most `2⌈log₂ n⌉ + 3`.  The complete polynomial
`P_n = x·T⁽¹⁾ + T⁽²⁾` is one further product on top of that pair
(`Cost.PolynomialProgram.ofJointPair`), and the even degrees are one further product
again (`Cost.PolynomialProgram.evenLift`, `P = x·Q_{n-1} + c₀`).  This file threads
monicity, degree, the explicit decoder, the fixed program, its exact multiplication
count, and the height bound through those two combiners:

* `odd_polynomial_height`: odd `n ≥ 3`, `n ≠ 7` — `(n-1)/2 + 1` products, height
  `≤ 2⌈log₂ n⌉ + 4`;
* `septic_polynomial_height`: the direct septic — `4` products, height `≤ 4`;
* `polynomial_height`: every `n ≥ 3` — `⌊n/2⌋ + 1` products, height
  `≤ 2⌈log₂ n⌉ + 4` for odd `n` and `≤ 2⌈log₂ n⌉ + 5` for even `n` (the even lift's
  product sits on the critical path above the odd polynomial, and
  `⌈log₂(n-1)⌉ = ⌈log₂ n⌉` for even `n ≥ 4`, so the `+1` is not absorbed);
* `linear_polynomial_height`, `quadratic_polynomial_height`: the two small degrees.

The invariant is packaged as `RealizedPolynomial`: monic of the stated degree, decodable
(every subalgebra containing the coefficients contains the parameter block), realized by
one fixed base-ring program with the stated exact count, and of bounded height.  The
even lift's decoder is the coefficient shift `P.coeff (j+1) = Q.coeff j`,
`P.coeff 0 = c₀` (`evenLift_coeff_mem`), the same one `even_lift_bijective` uses.
-/

namespace FastPoly

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

namespace Cost

/-- Height budget of a one-output program: the multiplicative depth of its output over
inputs of depth zero. -/
abbrev PolynomialProgram.HeightBounded {m : ℕ} (prog : PolynomialProgram R m) (D : ℕ) :
    Prop :=
  prog.circuit.multDepth (fun _ => 0) 0 ≤ D

/-- The same syntax with a re-indexed multiplication count. -/
def MultiplicationProgram.recount {ι : Type*} {q m m' : ℕ}
    (prog : MultiplicationProgram R ι q m) (h : m = m') :
    MultiplicationProgram R ι q m' where
  circuit := prog.circuit
  multiplication_count := by rw [prog.multiplication_count, h]

@[simp] theorem MultiplicationProgram.recount_circuit {ι : Type*} {q m m' : ℕ}
    (prog : MultiplicationProgram R ι q m) (h : m = m') :
    (prog.recount h).circuit = prog.circuit := rfl

/-- Height never exceeds the multiplication count. -/
theorem PolynomialProgram.heightBounded_of_count {m : ℕ} (prog : PolynomialProgram R m) :
    prog.HeightBounded m := by
  have h := Circuit.multDepth_le_multiplications prog.circuit (env := fun _ => 0) (d := 0)
    (fun _ => le_rfl) 0
  rw [prog.multiplication_count] at h
  exact h.trans (by omega)

/-- The combiner `x·T⁽¹⁾ + T⁽²⁾` adds one product on top of the two source outputs. -/
theorem PolynomialProgram.multDepth_ofOutputs_le {q m : ℕ}
    (source : MultiplicationProgram R PolyInput q m) (first second : Fin q) :
    (PolynomialProgram.ofOutputs source first second).circuit.multDepth (fun _ => 0) 0 ≤
      max (source.circuit.multDepth (fun _ => 0) first)
        (source.circuit.multDepth (fun _ => 0) second) + 1 := by
  show (Circuit.bind source.circuit (PolynomialProgram.combineOutputsBody first second)).multDepth
    (fun _ => 0) 0 ≤ _
  simp only [PolynomialProgram.combineOutputsBody, Circuit.multDepth_bind,
    Circuit.multDepth_add, Circuit.multDepth_mul, Circuit.multDepth_liftLeft,
    Circuit.multDepth_rightInput, Circuit.polyX, Circuit.multDepth_input]
  omega

/-- The even lift `x·Q + c` adds one product on top of the source output. -/
theorem PolynomialProgram.multDepth_evenLift_le {m : ℕ} (source : PolynomialProgram R m)
    (fresh : ℕ) :
    (PolynomialProgram.evenLift source fresh).circuit.multDepth (fun _ => 0) 0 ≤
      source.circuit.multDepth (fun _ => 0) 0 + 1 := by
  show (Circuit.bind source.circuit (PolynomialProgram.evenLiftBody fresh)).multDepth
    (fun _ => 0) 0 ≤ _
  simp only [PolynomialProgram.evenLiftBody, Circuit.multDepth_bind,
    Circuit.multDepth_add, Circuit.multDepth_mul, Circuit.multDepth_liftLeft,
    Circuit.multDepth_rightInput, Circuit.polyX, Circuit.polyParameter,
    Circuit.multDepth_input]
  omega

end Cost

/-! ## The complete-polynomial invariant -/

/-- **A realized complete polynomial**: a monic degree-`n` polynomial over `A`, decodable
to the parameter block `θ 0, …, θ (n-1)` (every subalgebra containing its coefficients
contains the block), computed by one fixed base-ring program of exactly `m` nonscalar
multiplications and multiplicative depth at most `D`. -/
def RealizedPolynomial (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    (θ : ℕ → A) (n m D : ℕ) : Prop :=
  ∃ (P : A[X]) (prog : Cost.PolynomialProgram R m),
    P.Monic ∧ P.natDegree = n ∧
    (∀ V : Subalgebra R A, (∀ j, P.coeff j ∈ V) → ∀ t, t < n → θ t ∈ V) ∧
    prog.RealizesAt θ P ∧ prog.HeightBounded D

namespace RealizedPolynomial

theorem recount {θ : ℕ → A} {n m m' D : ℕ} (h : RealizedPolynomial R θ n m D)
    (hm : m = m') : RealizedPolynomial R θ n m' D := by
  obtain ⟨P, prog, hPm, hPd, hdec, hpr, hh⟩ := h
  exact ⟨P, prog.recount hm, hPm, hPd, hdec, hpr, hh⟩

theorem mono {θ : ℕ → A} {n m D D' : ℕ} (h : RealizedPolynomial R θ n m D)
    (hD : D ≤ D') : RealizedPolynomial R θ n m D' := by
  obtain ⟨P, prog, hPm, hPd, hdec, hpr, hh⟩ := h
  exact ⟨P, prog, hPm, hPd, hdec, hpr, hh.trans hD⟩

end RealizedPolynomial

/-- The even lift's decoder: the coefficients of `x·Q + C c` are `c` and those of `Q`. -/
theorem evenLift_coeff_mem {Q : A[X]} {c : A} {V : Subalgebra R A}
    (hV : ∀ j, (X * Q + C c).coeff j ∈ V) : (∀ j, Q.coeff j ∈ V) ∧ c ∈ V := by
  refine ⟨fun j => ?_, ?_⟩
  · have h := hV (j + 1)
    rwa [coeff_add, coeff_X_mul, coeff_C, if_neg (by omega), add_zero] at h
  · have h := hV 0
    rwa [coeff_add, mul_coeff_zero, coeff_X_zero, zero_mul, coeff_C, if_pos rfl,
      zero_add] at h

section Lift

variable [Nontrivial A]

/-- **The even lift** (`P = x·Q_{n} + θ n`): one more product, one more unit of height,
the fresh coordinate `θ n` read off the constant term. -/
theorem RealizedPolynomial.evenLift {θ : ℕ → A} {n m D : ℕ}
    (h : RealizedPolynomial R θ n m D) :
    RealizedPolynomial R θ (n + 1) (m + 1) (D + 1) := by
  obtain ⟨Q, prog, hQm, hQd, hQdec, hpr, hh⟩ := h
  have hXQm : (X * Q).Monic := monic_X.mul hQm
  have hXQd : (X * Q).natDegree = n + 1 := by
    rw [monic_X.natDegree_mul hQm, natDegree_X, hQd]
    omega
  obtain ⟨hPm, hPd⟩ := monic_add_low (e := C (θ n)) hXQm
    (Or.inr (by rw [natDegree_C, hXQd]; omega))
  refine ⟨X * Q + C (θ n), Cost.PolynomialProgram.evenLift prog n, hPm, hPd.trans hXQd,
    ?_, Cost.PolynomialProgram.evenLift_realizesAt hpr n, ?_⟩
  · intro V hV t ht
    obtain ⟨hQV, hcV⟩ := evenLift_coeff_mem hV
    rcases Nat.lt_or_ge t n with hlt | hge
    · exact hQdec V hQV t hlt
    · have ht' : t = n := by omega
      rw [ht']
      exact hcV
  · exact (Cost.PolynomialProgram.multDepth_evenLift_le prog n).trans
      (Nat.succ_le_succ hh)

end Lift

/-! ## The small degrees and the direct septic -/

/-- Degree `1`: `x + θ 0`, no product, height `0`. -/
theorem linear_polynomial_height [Nontrivial A] (θ : ℕ → A) :
    RealizedPolynomial R θ 1 0 0 := by
  refine ⟨X + C (θ 0), Cost.PolynomialProgram.linear, monic_X_add_C _, natDegree_X_add_C _,
    ?_, Cost.PolynomialProgram.linear_realizesAt θ,
    Cost.PolynomialProgram.heightBounded_of_count _⟩
  intro V hV t ht
  have h := hV 0
  rw [coeff_add, coeff_X_zero, coeff_C, if_pos rfl, zero_add] at h
  have ht' : t = 0 := by omega
  rw [ht']
  exact h

/-- Degree `2`: `x(x + θ 1) + θ 0`, one product, height `1`. -/
theorem quadratic_polynomial_height [Nontrivial A] (θ : ℕ → A) :
    RealizedPolynomial R θ 2 1 1 := by
  have hm : (X * (X + C (θ 1))).Monic := monic_X.mul (monic_X_add_C _)
  have hd : (X * (X + C (θ 1))).natDegree = 2 := by
    rw [monic_X.natDegree_mul (monic_X_add_C _), natDegree_X, natDegree_X_add_C]
  obtain ⟨hPm, hPd⟩ := monic_add_low (e := C (θ 0)) hm
    (Or.inr (by rw [natDegree_C, hd]; omega))
  refine ⟨X * (X + C (θ 1)) + C (θ 0), Cost.PolynomialProgram.quadratic, hPm, hPd.trans hd,
    ?_, Cost.PolynomialProgram.quadratic_realizesAt θ,
    Cost.PolynomialProgram.heightBounded_of_count _⟩
  intro V hV t ht
  obtain ⟨hQV, h0⟩ := evenLift_coeff_mem hV
  have h1 := hQV 0
  rw [coeff_add, coeff_X_zero, coeff_C, if_pos rfl, zero_add] at h1
  rcases (show t = 0 ∨ t = 1 from by omega) with rfl | rfl
  · exact h0
  · exact h1

/-- Degree `7`: the direct four-product septic (`lem:septic-base`), height `≤ 4`. -/
theorem septic_polynomial_height [Nontrivial A] (h2 : IsUnit (2 : R)) (θ : ℕ → A) :
    RealizedPolynomial R θ 7 4 4 := by
  refine ⟨_, Cost.SepticProgram.program, (Cost.SepticProgram.good (R := R) θ).1,
    (Cost.SepticProgram.good (R := R) θ).2, ?_, Cost.SepticProgram.realizesAt (R := R) θ,
    Cost.PolynomialProgram.heightBounded_of_count _⟩
  intro V hV t ht
  have hle : optimizedSepticObs (R := R) (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6)
      (⊥ : Subalgebra R A) ≤ V := by
    refine sup_le bot_le (Algebra.adjoin_le ?_)
    rintro x ⟨j, -, rfl⟩
    exact hV j
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ :=
    optimizedSeptic_decodable (R := R) (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6)
      (⊥ : Subalgebra R A) h2
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 from by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hle p0
  · exact hle p1
  · exact hle p2
  · exact hle p3
  · exact hle p4
  · exact hle p5
  · exact hle p6

/-! ## The odd master family and the assembly -/

section Master

variable [Nontrivial A]

/-- **Height of the complete odd polynomial** (`thm:construction-height`, final
clause, odd degrees): for odd `n ≥ 3`, `n ≠ 7`, over an `n`-admissible base, the
polynomial `P_n = x·T⁽¹⁾ + T⁽²⁾` of `odd_realizable_pairs` is monic of degree `n`, decodes
the whole parameter block, and is computed by one fixed program with exactly
`(n-1)/2 + 1` products and height at most `2⌈log₂ n⌉ + 4`. -/
theorem odd_polynomial_height (n : ℕ) (hodd : n % 2 = 1) (hn3 : 3 ≤ n) (hn7 : n ≠ 7)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R)) (θ : ℕ → A) :
    RealizedPolynomial R θ n ((n - 1) / 2 + 1) (2 * Nat.clog 2 n + 4) := by
  obtain ⟨T₁, T₂, H₂, H₄, G, hcp, -, -, -, hdec, prog, hpr, hh⟩ :=
    odd_realizable_pairs' (R := R) (A := A) n hodd hn3 hn7 hadm θ
  obtain ⟨hPm, hPd⟩ := combined_good_of_monic hcp.monic₁ hcp.natDegree₁
    hcp.monic₂ hcp.natDegree₂
  refine ⟨combined T₁ T₂, Cost.PolynomialProgram.ofJointPair prog, hPm, by rw [hPd]; omega,
    fun V hV => (hdec V hV).1, Cost.PolynomialProgram.ofJointPair_realizesAt hpr, ?_⟩
  refine (Cost.PolynomialProgram.multDepth_ofOutputs_le prog 0 1).trans ?_
  have h0 := hh.1
  have h1 := hh.2.1
  omega

/-- **`thm:construction-count` + `thm:construction-height`, complete form.**  For
every `n ≥ 3` over an `n`-admissible base — the odd master family, the direct septic, or
the even lift `P = x·Q_{n-1} + θ (n-1)` of one of these — there is a monic decodable
degree-`n` polynomial computed by one fixed program with exactly `⌊n/2⌋ + 1` products and
height at most `2⌈log₂ n⌉ + 4` (odd `n`) resp. `2⌈log₂ n⌉ + 5` (even `n`). -/
theorem polynomial_height (n : ℕ) (hn3 : 3 ≤ n)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R)) (θ : ℕ → A) :
    RealizedPolynomial R θ n (n / 2 + 1) (2 * Nat.clog 2 n + 4 + (n + 1) % 2) := by
  rcases (show n = 7 ∨ n = 8 ∨ (n % 2 = 1 ∧ n ≠ 7) ∨ (n % 2 = 0 ∧ 4 ≤ n ∧ n ≠ 8)
      from by omega) with rfl | rfl | ⟨hodd, h7⟩ | ⟨heven, h4, h8⟩
  · -- the direct septic
    have h2 : IsUnit (2 : R) := isUnit_two_of_cast hadm (by omega)
    exact (septic_polynomial_height h2 θ).mono (by omega)
  · -- the lifted septic
    have h2 : IsUnit (2 : R) := isUnit_two_of_cast hadm (by omega)
    exact (septic_polynomial_height h2 θ).evenLift.mono (by omega)
  · -- the odd master family
    exact (odd_polynomial_height n hodd hn3 h7 hadm θ).recount (by omega)
      |>.mono (by omega)
  · -- the even lift of the odd master family
    have hclog : Nat.clog 2 (n - 1) ≤ Nat.clog 2 n := Nat.clog_mono_right 2 (by omega)
    have hodd' := odd_polynomial_height (R := R) (A := A) (n - 1) (by omega) (by omega)
      (by omega) (fun i h1 hi => hadm i h1 (by omega)) θ
    have hlift := hodd'.evenLift
    rw [show n - 1 + 1 = n by omega] at hlift
    exact (hlift.recount (by omega)).mono (by omega)

end Master

/-! ## The paper's `n`-admissible hypothesis -/

/-- The master's unit hypothesis is `Admissible R n` up to the integer cast. -/
theorem Admissible.intCast_units {n : ℕ} (h : Admissible R n) :
    ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R) := fun i h1 h2 => by
  rw [Int.cast_natCast]
  exact h i h1 h2

/-- `polynomial_height` over an `n`-admissible base ring. -/
theorem polynomial_height_of_admissible [Nontrivial A] (n : ℕ) (hn3 : 3 ≤ n)
    (h : Admissible R n) (θ : ℕ → A) :
    RealizedPolynomial R θ n (n / 2 + 1) (2 * Nat.clog 2 n + 4 + (n + 1) % 2) :=
  polynomial_height n hn3 h.intCast_units θ

/-- `polynomial_height` over a field of characteristic `0`: the paper's first
`n`-admissible case. -/
theorem polynomial_height_of_charZero (F : Type u) [Field F] [CharZero F]
    {A : Type v} [CommRing A] [Algebra F A] [Nontrivial A] (n : ℕ) (hn3 : 3 ≤ n)
    (θ : ℕ → A) :
    RealizedPolynomial F θ n (n / 2 + 1) (2 * Nat.clog 2 n + 4 + (n + 1) % 2) :=
  polynomial_height_of_admissible n hn3 (admissible_of_charZero F n) θ

/-- `polynomial_height` over a field of characteristic `p > n`: the paper's second
`n`-admissible case. -/
theorem polynomial_height_of_charP (F : Type u) [Field F] (p : ℕ) [CharP F p]
    {A : Type v} [CommRing A] [Algebra F A] [Nontrivial A] (n : ℕ) (hn3 : 3 ≤ n)
    (hp : n < p) (θ : ℕ → A) :
    RealizedPolynomial F θ n (n / 2 + 1) (2 * Nat.clog 2 n + 4 + (n + 1) % 2) :=
  polynomial_height_of_admissible n hn3 (admissible_of_charP F p hp) θ

end FastPoly
