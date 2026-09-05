import FastPoly.Examples.Char2Construction
import FastPoly.Examples.Char2Degree21Frame

/-!
# The supplied degree-21 circuit's literal multiplication ledger

Each bind tail and each evaluated wire has its own name. The evaluation bridge
checks one gate at a time and then follows eleven small branch equations.
It never unfolds the whole shared polynomial into one proof term.
-/

namespace FastPoly.Char2Degree21Program

open Polynomial Char2Certificate Char2Degree19Crown
set_option maxHeartbeats 20000

variable {F : Type*} [Field F] [CharP F 2]

/-- The input labels after each literal bind, without changing their order. -/
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
  .mul (.add (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (5)))))) (.add (.add (.input (Sum.inl (Sum.inr 0))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (6))))))

def gate4 : Cost.Circuit F (Inputs 4) 1 :=
  .mul (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0)))))) (.input (Sum.inl (Sum.inl (Sum.inr 0))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (7))))))) (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (8)))))))

def gate5 : Cost.Circuit F (Inputs 5) 1 :=
  .mul (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (9)))))))) (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (10))))))))

def gate6 : Cost.Circuit F (Inputs 6) 1 :=
  .mul (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0)))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (11))))))))) (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (12)))))))))

def gate7 : Cost.Circuit F (Inputs 7) 1 :=
  .mul (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (13)))))))))) (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (14))))))))))

def gate8 : Cost.Circuit F (Inputs 8) 1 :=
  .mul (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (15))))))))))) (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inl (Sum.inr 0)))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (16)))))))))))

def gate9 : Cost.Circuit F (Inputs 9) 1 :=
  .mul (.add (.input (Sum.inl (Sum.inl (Sum.inr 0)))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (17)))))))))))) (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (18))))))))))))

def gate10 : Cost.Circuit F (Inputs 10) 1 :=
  .mul (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (19))))))))))))) (.add (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inr 0)))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (20)))))))))))))

def tail11 : Cost.Circuit F (Inputs 11) 1 :=
  (.add (.add (.add (.add (.input (Sum.inr 0)) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inl (Sum.inr 0)))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (21))))))))))))))

def tail10 : Cost.Circuit F (Inputs 10) 1 := .bind gate10 tail11

def tail9 : Cost.Circuit F (Inputs 9) 1 := .bind gate9 tail10

def tail8 : Cost.Circuit F (Inputs 8) 1 := .bind gate8 tail9

def tail7 : Cost.Circuit F (Inputs 7) 1 := .bind gate7 tail8

def tail6 : Cost.Circuit F (Inputs 6) 1 := .bind gate6 tail7

def tail5 : Cost.Circuit F (Inputs 5) 1 := .bind gate5 tail6

def tail4 : Cost.Circuit F (Inputs 4) 1 := .bind gate4 tail5

def tail3 : Cost.Circuit F (Inputs 3) 1 := .bind gate3 tail4

def tail2 : Cost.Circuit F (Inputs 2) 1 := .bind gate2 tail3

def tail1 : Cost.Circuit F (Inputs 1) 1 := .bind gate1 tail2

def tail0 : Cost.Circuit F (Inputs 0) 1 := .bind gate0 tail1

def circuit : Cost.Circuit F ℕ 1 := tail0

omit [Field F] [CharP F 2] in
theorem multiplication_count : (circuit (F := F)).gates.multiplications = 11 := by
  simp only [circuit, tail0, tail1, tail2, tail3, tail4, tail5, tail6, tail7, tail8, tail9, tail10, tail11,
    gate0, gate1, gate2, gate3, gate4, gate5, gate6, gate7, gate8, gate9, gate10, Cost.Circuit.gates, Cost.Circuit.gates_input,
    Cost.GateCount.add_multiplications, Cost.GateCount.zero_multiplications,
    Cost.GateCount.adds_multiplications, Cost.GateCount.muls_multiplications,
    Nat.zero_add, Nat.add_zero]

def program : Cost.MultiplicationProgram F ℕ 1 11 :=
  ⟨circuit, multiplication_count⟩

noncomputable def env0 (a : ℕ → F) : Inputs 0 → F[X] := inputEnv a

noncomputable def env1 (a : ℕ → F) : Inputs 1 → F[X] :=
  Sum.elim (env0 a) (fun _ => (y : F[X]))

noncomputable def env2 (a : ℕ → F) : Inputs 2 → F[X] :=
  Sum.elim (env1 a) (fun _ => z a)

noncomputable def env3 (a : ℕ → F) : Inputs 3 → F[X] :=
  Sum.elim (env2 a) (fun _ => t a)

noncomputable def env4 (a : ℕ → F) : Inputs 4 → F[X] :=
  Sum.elim (env3 a) (fun _ => u a)

noncomputable def env5 (a : ℕ → F) : Inputs 5 → F[X] :=
  Sum.elim (env4 a) (fun _ => v a)

noncomputable def env6 (a : ℕ → F) : Inputs 6 → F[X] :=
  Sum.elim (env5 a) (fun _ => w a)

noncomputable def env7 (a : ℕ → F) : Inputs 7 → F[X] :=
  Sum.elim (env6 a) (fun _ => s a)

noncomputable def env8 (a : ℕ → F) : Inputs 8 → F[X] :=
  Sum.elim (env7 a) (fun _ => r a)

noncomputable def env9 (a : ℕ → F) : Inputs 9 → F[X] :=
  Sum.elim (env8 a) (fun _ => q a)

noncomputable def env10 (a : ℕ → F) : Inputs 10 → F[X] :=
  Sum.elim (env9 a) (fun _ => Char2Degree21Frame.ell a)

noncomputable def env11 (a : ℕ → F) : Inputs 11 → F[X] :=
  Sum.elim (env10 a) (fun _ => Char2Degree21Frame.m a)

theorem gate0_eval (a : ℕ → F) (i : Fin 1) :
    (gate0 (F := F)).eval (env0 a) i = (y : F[X]) := by
  simp only [gate0, Cost.Circuit.eval, Cost.Circuit.input,
    env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    y, pow_two, add_assoc]

theorem gate1_eval (a : ℕ → F) (i : Fin 1) :
    (gate1 (F := F)).eval (env1 a) i = z a := by
  simp only [gate1, Cost.Circuit.eval, Cost.Circuit.input,
    env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    z, pow_two, add_assoc]

theorem gate2_eval (a : ℕ → F) (i : Fin 1) :
    (gate2 (F := F)).eval (env2 a) i = t a := by
  simp only [gate2, Cost.Circuit.eval, Cost.Circuit.input,
    env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    t, pow_two, add_assoc]

theorem gate3_eval (a : ℕ → F) (i : Fin 1) :
    (gate3 (F := F)).eval (env3 a) i = u a := by
  simp only [gate3, Cost.Circuit.eval, Cost.Circuit.input,
    env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    u, pow_two, add_assoc]

theorem gate4_eval (a : ℕ → F) (i : Fin 1) :
    (gate4 (F := F)).eval (env4 a) i = v a := by
  simp only [gate4, Cost.Circuit.eval, Cost.Circuit.input,
    env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    v, pow_two, add_assoc]

theorem gate5_eval (a : ℕ → F) (i : Fin 1) :
    (gate5 (F := F)).eval (env5 a) i = w a := by
  simp only [gate5, Cost.Circuit.eval, Cost.Circuit.input,
    env5, env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    w, pow_two, add_assoc]

theorem gate6_eval (a : ℕ → F) (i : Fin 1) :
    (gate6 (F := F)).eval (env6 a) i = s a := by
  simp only [gate6, Cost.Circuit.eval, Cost.Circuit.input,
    env6, env5, env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    s, pow_two, add_assoc]

theorem gate7_eval (a : ℕ → F) (i : Fin 1) :
    (gate7 (F := F)).eval (env7 a) i = r a := by
  simp only [gate7, Cost.Circuit.eval, Cost.Circuit.input,
    env7, env6, env5, env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    r, pow_two, add_assoc]

theorem gate8_eval (a : ℕ → F) (i : Fin 1) :
    (gate8 (F := F)).eval (env8 a) i = q a := by
  simp only [gate8, Cost.Circuit.eval, Cost.Circuit.input,
    env8, env7, env6, env5, env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    q, pow_two, add_assoc]

theorem gate9_eval (a : ℕ → F) (i : Fin 1) :
    (gate9 (F := F)).eval (env9 a) i = Char2Degree21Frame.ell a := by
  simp only [gate9, Cost.Circuit.eval, Cost.Circuit.input,
    env9, env8, env7, env6, env5, env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    Char2Degree21Frame.ell, Char2Degree21Frame.core, pow_two, add_assoc]

theorem gate10_eval (a : ℕ → F) (i : Fin 1) :
    (gate10 (F := F)).eval (env10 a) i = Char2Degree21Frame.m a := by
  simp only [gate10, Cost.Circuit.eval, Cost.Circuit.input,
    env10, env9, env8, env7, env6, env5, env4, env3, env2, env1, env0, Sum.elim_inl, Sum.elim_inr,
    inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    Char2Degree21Frame.m, Char2Degree21Frame.core, pow_two, add_assoc]

theorem tail11_eval (a : ℕ → F) :
    (tail11 (F := F)).eval (env11 a) 0 = Char2Degree21Frame.output a := by
  simp only [tail11, Cost.Circuit.eval, Cost.Circuit.input,
    env11, env10, env9, env8, env7, env6, env5, env4, env3, env2, env1, env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub,
    OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    Char2Degree21Frame.output, add_assoc]

theorem tail10_eval (a : ℕ → F) :
    (tail10 (F := F)).eval (env10 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate10 (F := F)).eval (env10 a) = (fun _ => Char2Degree21Frame.m a) :=
    funext (gate10_eval a)
  rw [tail10, Cost.Circuit.eval, hg]
  exact tail11_eval a

theorem tail9_eval (a : ℕ → F) :
    (tail9 (F := F)).eval (env9 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate9 (F := F)).eval (env9 a) = (fun _ => Char2Degree21Frame.ell a) :=
    funext (gate9_eval a)
  rw [tail9, Cost.Circuit.eval, hg]
  exact tail10_eval a

theorem tail8_eval (a : ℕ → F) :
    (tail8 (F := F)).eval (env8 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate8 (F := F)).eval (env8 a) = (fun _ => q a) :=
    funext (gate8_eval a)
  rw [tail8, Cost.Circuit.eval, hg]
  exact tail9_eval a

theorem tail7_eval (a : ℕ → F) :
    (tail7 (F := F)).eval (env7 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate7 (F := F)).eval (env7 a) = (fun _ => r a) :=
    funext (gate7_eval a)
  rw [tail7, Cost.Circuit.eval, hg]
  exact tail8_eval a

theorem tail6_eval (a : ℕ → F) :
    (tail6 (F := F)).eval (env6 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate6 (F := F)).eval (env6 a) = (fun _ => s a) :=
    funext (gate6_eval a)
  rw [tail6, Cost.Circuit.eval, hg]
  exact tail7_eval a

theorem tail5_eval (a : ℕ → F) :
    (tail5 (F := F)).eval (env5 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate5 (F := F)).eval (env5 a) = (fun _ => w a) :=
    funext (gate5_eval a)
  rw [tail5, Cost.Circuit.eval, hg]
  exact tail6_eval a

theorem tail4_eval (a : ℕ → F) :
    (tail4 (F := F)).eval (env4 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate4 (F := F)).eval (env4 a) = (fun _ => v a) :=
    funext (gate4_eval a)
  rw [tail4, Cost.Circuit.eval, hg]
  exact tail5_eval a

theorem tail3_eval (a : ℕ → F) :
    (tail3 (F := F)).eval (env3 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate3 (F := F)).eval (env3 a) = (fun _ => u a) :=
    funext (gate3_eval a)
  rw [tail3, Cost.Circuit.eval, hg]
  exact tail4_eval a

theorem tail2_eval (a : ℕ → F) :
    (tail2 (F := F)).eval (env2 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate2 (F := F)).eval (env2 a) = (fun _ => t a) :=
    funext (gate2_eval a)
  rw [tail2, Cost.Circuit.eval, hg]
  exact tail3_eval a

theorem tail1_eval (a : ℕ → F) :
    (tail1 (F := F)).eval (env1 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate1 (F := F)).eval (env1 a) = (fun _ => z a) :=
    funext (gate1_eval a)
  rw [tail1, Cost.Circuit.eval, hg]
  exact tail2_eval a

theorem tail0_eval (a : ℕ → F) :
    (tail0 (F := F)).eval (env0 a) 0 = Char2Degree21Frame.output a := by
  have hg : (gate0 (F := F)).eval (env0 a) = (fun _ => (y : F[X])) :=
    funext (gate0_eval a)
  rw [tail0, Cost.Circuit.eval, hg]
  exact tail1_eval a

/-- The literal counted syntax computes the inverse's named polynomial. -/
theorem program_eval (a : ℕ → F) :
    (program (F := F)).circuit.eval (inputEnv a) 0 = Char2Degree21Frame.output a :=
  tail0_eval a

end FastPoly.Char2Degree21Program
