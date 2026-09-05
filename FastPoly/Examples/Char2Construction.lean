import FastPoly.Examples.Char2Triangular
import FastPoly.Cost.MultiplicationProgram

/-!
# A fixed counted circuit together with its coefficient decoder

The program is chosen before the target coefficients. Its only online inputs
are x and preprocessed scalar constants. The generic even lift uses one more
literal product and one fresh constant, without changing the odd decoder.
-/

namespace FastPoly.Char2Certificate

open Polynomial Cost
variable {F : Type*} [Field F]

noncomputable def inputEnv (a : ℕ → F) (i : ℕ) : F[X] :=
  if i = 0 then X else C (a (i-1))

structure Construction (F : Type*) [Field F] (degree multiplications : ℕ) where
  program : MultiplicationProgram F ℕ 1 multiplications
  decoder : (Fin degree → F) → ℕ → F
  correct : ∀ c, program.circuit.eval (inputEnv (decoder c)) 0 = monicOfCoefficients c

/-- The coefficient-vector interface covers every monic polynomial of this degree. -/
theorem monic_eq_coefficients {n : ℕ} (P : F[X]) (hP : P.Monic)
    (hn : P.natDegree = n) :
    P = monicOfCoefficients (fun i : Fin n => P.coeff i) := by
  have htop : P.coeff n = 1 := by
    rw [← hn, coeff_natDegree]
    exact hP
  have hsum : (∑ j ∈ Finset.range n, C (P.coeff j) * X ^ j) =
      ∑ j ∈ Finset.range n,
        C (extendFin (fun i : Fin n => P.coeff i) j) * X ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [extendFin, dif_pos (Finset.mem_range.mp hj)]
  have hrepr := P.as_sum_range_C_mul_X_pow' (show P.natDegree < n+1 by omega)
  rw [Finset.sum_range_succ, htop, map_one, one_mul, hsum] at hrepr
  exact hrepr.trans (add_comm _ _)

theorem Construction.correct_polynomial {n m : ℕ} (c : Construction F n m)
    (P : F[X]) (hP : P.Monic) (hn : P.natDegree = n) :
    c.program.circuit.eval (inputEnv (c.decoder (fun i => P.coeff i))) 0 = P :=
  (c.correct _).trans (monic_eq_coefficients P hP hn).symm

theorem monic_even_lift {n : ℕ} (c : Fin (n+1) → F) :
    monicOfCoefficients c =
      X * monicOfCoefficients (fun j : Fin n => c j.succ) + C (c 0) := by
  have hshift (j : ℕ) : extendFin c (j+1) =
      extendFin (fun j : Fin n => c j.succ) j := by
    by_cases hj : j < n
    · simp only [extendFin, dif_pos hj, dif_pos (Nat.succ_lt_succ hj)]
      rfl
    · have hj' : ¬j+1 < n+1 := by omega
      simp only [extendFin, dif_neg hj, dif_neg hj']
  have hs : (∑ j ∈ Finset.range n, C (extendFin c (j+1)) * X ^ (j+1)) =
      X * ∑ j ∈ Finset.range n,
        C (extendFin (fun j : Fin n => c j.succ) j) * X ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hshift, pow_succ]
    ring
  have hz : extendFin c 0 = c 0 := rfl
  simp only [monicOfCoefficients]
  rw [Finset.sum_range_succ', hs, hz, pow_zero, mul_one, pow_succ]
  ring

/-- Keep x at input 0 and make room for the new scalar at input 1. -/
def liftInput : ℕ → ℕ
  | 0 => 0
  | i+1 => i+2

def evenCircuit (c : Circuit F ℕ 1) : Circuit F ℕ 1 :=
  .bind (c.relabel liftInput)
    (.add (.mul (.input (.inl 0)) (.input (.inr 0))) (.input (.inl 1)))

theorem evenCircuit_count (c : Circuit F ℕ 1) :
    (evenCircuit c).gates.multiplications = c.gates.multiplications + 1 := by
  simp only [evenCircuit, Circuit.gates_bind, Circuit.gates_relabel, Circuit.gates,
    Circuit.gates_input,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.muls_multiplications, GateCount.adds_multiplications]

noncomputable def Construction.evenLift {n m : ℕ} (c : Construction F n m) :
    Construction F (n+1) (m+1) where
  program := ⟨evenCircuit c.program.circuit, by
    rw [evenCircuit_count, c.program.multiplication_count]⟩
  decoder b
    | 0 => b 0
    | i+1 => c.decoder (fun j => b j.succ) i
  correct b := by
    let a : ℕ → F := fun i => match i with
      | 0 => b 0
      | j+1 => c.decoder (fun k => b k.succ) j
    have he : inputEnv a ∘ liftInput = inputEnv (c.decoder (fun j => b j.succ)) := by
      funext i
      cases i <;> rfl
    change X * ((c.program.circuit.relabel liftInput).eval (inputEnv a) 0) +
      C (b 0) = monicOfCoefficients b
    rw [Circuit.eval_relabel, he, c.correct]
    exact (monic_even_lift b).symm

end FastPoly.Char2Certificate
