import FastPoly.Examples.Char2Degree11FastCore
import FastPoly.Examples.Char2Construction

/-! The original active six-product circuit, with named gate/bind equations.
The gate syntax is copied literally from the existing degree-eleven circuit;
only the bind tails and semantic environments are named separately. -/

namespace FastPoly.Char2Degree11Fast

open Polynomial Char2Certificate
set_option maxHeartbeats 20000

variable {F : Type*} [Field F] [CharP F 2]

abbrev Inputs : ℕ → Type
  | 0 => ℕ
  | k + 1 => Inputs k ⊕ Fin 1

def gate0 : Cost.Circuit F (Inputs 0) 1 :=
  .mul (.input (0)) (.input (0))

def gate1 : Cost.Circuit F (Inputs 1) 1 :=
  .mul (.add (.input (Sum.inr 0)) (.input (Sum.inl (1)))) (.add (.add (.input (Sum.inl (0))) (.input (Sum.inr 0))) (.input (Sum.inl (2))))

def gate2 : Cost.Circuit F (Inputs 2) 1 :=
  .mul (.add (.input (Sum.inl (Sum.inl (0)))) (.input (Sum.inl (Sum.inl (3))))) (.add (.input (Sum.inr 0)) (.input (Sum.inl (Sum.inl (4)))))

def gate3 : Cost.Circuit F (Inputs 3) 1 :=
  .mul (.add (.input (Sum.inl (Sum.inl (Sum.inl (0))))) (.input (Sum.inl (Sum.inl (Sum.inl (5)))))) (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inl (Sum.inl (Sum.inl (6))))))

def gate4 : Cost.Circuit F (Inputs 4) 1 :=
  .mul (.add (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (7))))))) (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))) (.input (Sum.inl (Sum.inl (Sum.inr 0))))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (8)))))))

def gate5 : Cost.Circuit F (Inputs 5) 1 :=
  .mul (.add (.input (Sum.inl (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (9)))))))) (.add (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (10))))))))

def tail6 : Cost.Circuit F (Inputs 6) 1 :=
  (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (11)))))))))

def tail5 : Cost.Circuit F (Inputs 5) 1 := .bind gate5 tail6

def tail4 : Cost.Circuit F (Inputs 4) 1 := .bind gate4 tail5

def tail3 : Cost.Circuit F (Inputs 3) 1 := .bind gate3 tail4

def tail2 : Cost.Circuit F (Inputs 2) 1 := .bind gate2 tail3

def tail1 : Cost.Circuit F (Inputs 1) 1 := .bind gate1 tail2

def tail0 : Cost.Circuit F (Inputs 0) 1 := .bind gate0 tail1

def circuit : Cost.Circuit F ℕ 1 := tail0

theorem multiplication_count : (circuit (F := F)).gates.multiplications = 6 := by
  simp only [circuit, tail0, tail1, tail2, tail3, tail4, tail5, tail6,
    gate0, gate1, gate2, gate3, gate4, gate5, Cost.Circuit.gates, Cost.Circuit.gates_input,
    Cost.GateCount.add_multiplications, Cost.GateCount.zero_multiplications,
    Cost.GateCount.adds_multiplications, Cost.GateCount.muls_multiplications,
    Nat.zero_add, Nat.add_zero]

def program : Cost.MultiplicationProgram F ℕ 1 6 :=
  ⟨circuit, multiplication_count⟩

noncomputable def env0 (q : Keys F) : Inputs 0 → F[X] := inputEnv (keys q)

noncomputable def env1 (q : Keys F) : Inputs 1 → F[X] :=
  Sum.elim (env0 q) (fun _ => (y : F[X]))

noncomputable def env2 (q : Keys F) : Inputs 2 → F[X] :=
  Sum.elim (env1 q) (fun _ => z q)

noncomputable def env3 (q : Keys F) : Inputs 3 → F[X] :=
  Sum.elim (env2 q) (fun _ => t q)

noncomputable def env4 (q : Keys F) : Inputs 4 → F[X] :=
  Sum.elim (env3 q) (fun _ => u q)

noncomputable def env5 (q : Keys F) : Inputs 5 → F[X] :=
  Sum.elim (env4 q) (fun _ => v q)

noncomputable def env6 (q : Keys F) : Inputs 6 → F[X] :=
  Sum.elim (env5 q) (fun _ => w q)

theorem gate0_eval (q : Keys F) (i : Fin 1) :
    (gate0 (F := F)).eval (env0 q) i = (y : F[X]) := by
  simp only [gate0, Cost.Circuit.eval, Cost.Circuit.input,
    env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, keys, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    y, pow_two, add_assoc]

theorem gate1_eval (q : Keys F) (i : Fin 1) :
    (gate1 (F := F)).eval (env1 q) i = z q := by
  simp only [gate1, Cost.Circuit.eval, Cost.Circuit.input,
    env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, keys, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    z, pow_two, add_assoc]

theorem gate2_eval (q : Keys F) (i : Fin 1) :
    (gate2 (F := F)).eval (env2 q) i = t q := by
  simp only [gate2, Cost.Circuit.eval, Cost.Circuit.input,
    env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, keys, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    t, pow_two, add_assoc]

theorem gate3_eval (q : Keys F) (i : Fin 1) :
    (gate3 (F := F)).eval (env3 q) i = u q := by
  simp only [gate3, Cost.Circuit.eval, Cost.Circuit.input,
    env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, keys, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    u, pow_two, add_assoc]

theorem gate4_eval (q : Keys F) (i : Fin 1) :
    (gate4 (F := F)).eval (env4 q) i = v q := by
  simp only [gate4, Cost.Circuit.eval, Cost.Circuit.input,
    env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, keys, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    v, H, pow_two, add_assoc]

theorem gate5_eval (q : Keys F) (i : Fin 1) :
    (gate5 (F := F)).eval (env5 q) i = w q := by
  simp only [gate5, Cost.Circuit.eval, Cost.Circuit.input,
    env5, env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, keys, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    w, B, J, pow_two, add_assoc]

theorem tail6_eval (q : Keys F) :
    (tail6 (F := F)).eval (env6 q) 0 = output q := by
  simp only [tail6, Cost.Circuit.eval, Cost.Circuit.input,
    env6, env5, env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, keys, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    output, add_assoc]

theorem tail5_eval (q : Keys F) :
    (tail5 (F := F)).eval (env5 q) 0 = output q := by
  have hg : (gate5 (F := F)).eval (env5 q) = (fun _ => w q) :=
    funext (gate5_eval q)
  rw [tail5, Cost.Circuit.eval, hg]
  exact tail6_eval q

theorem tail4_eval (q : Keys F) :
    (tail4 (F := F)).eval (env4 q) 0 = output q := by
  have hg : (gate4 (F := F)).eval (env4 q) = (fun _ => v q) :=
    funext (gate4_eval q)
  rw [tail4, Cost.Circuit.eval, hg]
  exact tail5_eval q

theorem tail3_eval (q : Keys F) :
    (tail3 (F := F)).eval (env3 q) 0 = output q := by
  have hg : (gate3 (F := F)).eval (env3 q) = (fun _ => u q) :=
    funext (gate3_eval q)
  rw [tail3, Cost.Circuit.eval, hg]
  exact tail4_eval q

theorem tail2_eval (q : Keys F) :
    (tail2 (F := F)).eval (env2 q) 0 = output q := by
  have hg : (gate2 (F := F)).eval (env2 q) = (fun _ => t q) :=
    funext (gate2_eval q)
  rw [tail2, Cost.Circuit.eval, hg]
  exact tail3_eval q

theorem tail1_eval (q : Keys F) :
    (tail1 (F := F)).eval (env1 q) 0 = output q := by
  have hg : (gate1 (F := F)).eval (env1 q) = (fun _ => z q) :=
    funext (gate1_eval q)
  rw [tail1, Cost.Circuit.eval, hg]
  exact tail2_eval q

theorem tail0_eval (q : Keys F) :
    (tail0 (F := F)).eval (env0 q) 0 = output q := by
  have hg : (gate0 (F := F)).eval (env0 q) = (fun _ => (y : F[X])) :=
    funext (gate0_eval q)
  rw [tail0, Cost.Circuit.eval, hg]
  exact tail1_eval q

/-- The counted online program computes the exact named decoder polynomial. -/
theorem program_eval (q : Keys F) :
    (program (F := F)).circuit.eval (inputEnv (keys q)) 0 = output q :=
  tail0_eval q

end FastPoly.Char2Degree11Fast

