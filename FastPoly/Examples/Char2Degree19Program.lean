import FastPoly.Examples.Char2Construction
import FastPoly.Examples.Char2Degree19Crown

/-!
# The existing degree-19 circuit's literal multiplication ledger

This is the same ten-product syntax as the supplied verifier and website.
Only the syntax and its evaluation bridge are reused from the archived draft;
none of its expanded coefficient proofs or enlarged heartbeat limits is used.
-/

namespace FastPoly.Char2Degree19Program

open Polynomial Char2Certificate Char2Degree19Crown

set_option maxHeartbeats 20000

variable {F : Type*} [Field F] [CharP F 2]

/-- Literal fixed circuit, independent of the target polynomial. -/
def circuit : Cost.Circuit F ℕ 1 :=
  .bind (.mul (.input (0)) (.input (0))) (
  .bind (.mul (.add (.input (Sum.inr 0)) (.input (Sum.inl (1)))) (.add (.add (.input (Sum.inl (0))) (.input (Sum.inr 0))) (.input (Sum.inl (2))))) (
  .bind (.mul (.add (.input (Sum.inl (Sum.inl (0)))) (.input (Sum.inl (Sum.inl (3))))) (.add (.input (Sum.inr 0)) (.input (Sum.inl (Sum.inl (4)))))) (
  .bind (.mul (.add (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (5)))))) (.add (.add (.input (Sum.inl (Sum.inr 0))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (6))))))) (
  .bind (.mul (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0)))))) (.input (Sum.inl (Sum.inl (Sum.inr 0))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (7))))))) (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (8)))))))) (
  .bind (.mul (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (9)))))))) (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (10))))))))) (
  .bind (.mul (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0)))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (11))))))))) (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (12)))))))))) (
  .bind (.mul (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (13)))))))))) (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (14))))))))))) (
  .bind (.mul (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (15))))))))))) (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inl (Sum.inr 0)))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (16)))))))))))) (
  .bind (.mul (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (17)))))))))))) (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (18))))))))))))) (
  (.add (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (19)))))))))))))))))))))))

theorem multiplication_count : (circuit (F := F)).gates.multiplications = 10 := by
  simp only [circuit, Cost.Circuit.gates, Cost.Circuit.gates_input,
    Cost.GateCount.add_multiplications, Cost.GateCount.zero_multiplications,
    Cost.GateCount.adds_multiplications, Cost.GateCount.muls_multiplications,
    Nat.zero_add, Nat.add_zero]

def program : Cost.MultiplicationProgram F ℕ 1 10 :=
  ⟨circuit, multiplication_count⟩


/-- The syntax computes the very same named circuit used by the decoder. -/
theorem program_eval (a : ℕ → F) :
    (program (F := F)).circuit.eval (inputEnv a) 0 = output a := by
  simp only [output, crown, q, r, s, w, v, u, t, z, y, pow_two]
  rfl

end FastPoly.Char2Degree19Program
