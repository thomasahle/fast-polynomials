import FastPoly.Examples.Char2Degree23Program
import FastPoly.Examples.Char2Degree25Frame

/-!
# The supplied degree-25 circuit: thirteen literal multiplications

The checked first ten gates and semantic environments are reused verbatim
from the degree-23 program. Only the three existing terminal products differ.
Each new gate and bind tail has a separate evaluation equation; no recursive
circuit is expanded into a polynomial.
-/

namespace FastPoly.Char2Degree25Program

open Polynomial Char2Certificate Char2Degree25Frame
set_option maxHeartbeats 20000

variable {F : Type*} [Field F] [CharP F 2]

abbrev Inputs (k : ℕ) := Char2Degree23Program.Inputs k

def gate10 : Cost.Circuit F (Inputs 10) 1 :=
  .mul (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (19))))))))))))) (.add (.add (.add (.add (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0)))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inr 0))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (20)))))))))))))

def gate11 : Cost.Circuit F (Inputs 11) 1 :=
  .mul (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0))))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (21)))))))))))))) (.add (.input (Sum.inl (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (22))))))))))))))

def gate12 : Cost.Circuit F (Inputs 12) 1 :=
  .mul (.add (.add (.add (.add (.add (.add (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (0)))))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inl (Sum.inl (Sum.inr 0))))) (.input (Sum.inl (Sum.inr 0)))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (23))))))))))))))) (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (24)))))))))))))))

def tail13 : Cost.Circuit F (Inputs 13) 1 :=
  (.add (.add (.add (.add (.add (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))))))))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))) (.input (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (25))))))))))))))))

def tail12 : Cost.Circuit F (Inputs 12) 1 := .bind gate12 tail13

def tail11 : Cost.Circuit F (Inputs 11) 1 := .bind gate11 tail12

def tail10 : Cost.Circuit F (Inputs 10) 1 := .bind gate10 tail11

def tail9 : Cost.Circuit F (Inputs 9) 1 := .bind Char2Degree23Program.gate9 tail10

def tail8 : Cost.Circuit F (Inputs 8) 1 := .bind Char2Degree23Program.gate8 tail9

def tail7 : Cost.Circuit F (Inputs 7) 1 := .bind Char2Degree23Program.gate7 tail8

def tail6 : Cost.Circuit F (Inputs 6) 1 := .bind Char2Degree23Program.gate6 tail7

def tail5 : Cost.Circuit F (Inputs 5) 1 := .bind Char2Degree23Program.gate5 tail6

def tail4 : Cost.Circuit F (Inputs 4) 1 := .bind Char2Degree23Program.gate4 tail5

def tail3 : Cost.Circuit F (Inputs 3) 1 := .bind Char2Degree23Program.gate3 tail4

def tail2 : Cost.Circuit F (Inputs 2) 1 := .bind Char2Degree23Program.gate2 tail3

def tail1 : Cost.Circuit F (Inputs 1) 1 := .bind Char2Degree23Program.gate1 tail2

def tail0 : Cost.Circuit F (Inputs 0) 1 := .bind Char2Degree23Program.gate0 tail1

def circuit : Cost.Circuit F ℕ 1 := tail0

theorem multiplication_count : (circuit (F := F)).gates.multiplications = 13 := by
  simp only [circuit, tail0, tail1, tail2, tail3, tail4, tail5, tail6, tail7, tail8, tail9, tail10, tail11, tail12, tail13,
    Char2Degree23Program.gate0, Char2Degree23Program.gate1, Char2Degree23Program.gate2, Char2Degree23Program.gate3, Char2Degree23Program.gate4, Char2Degree23Program.gate5, Char2Degree23Program.gate6, Char2Degree23Program.gate7, Char2Degree23Program.gate8, Char2Degree23Program.gate9, gate10, gate11, gate12,
    Cost.Circuit.gates, Cost.Circuit.gates_input,
    Cost.GateCount.add_multiplications, Cost.GateCount.zero_multiplications,
    Cost.GateCount.adds_multiplications, Cost.GateCount.muls_multiplications,
    Nat.zero_add, Nat.add_zero]

def program : Cost.MultiplicationProgram F ℕ 1 13 := ⟨circuit, multiplication_count⟩

noncomputable def env11 (a : ℕ → F) : Inputs 11 → F[X] :=
  Sum.elim (Char2Degree23Program.env10 a) (fun _ => h a)

noncomputable def env12 (a : ℕ → F) : Inputs 12 → F[X] :=
  Sum.elim (env11 a) (fun _ => j a)

noncomputable def env13 (a : ℕ → F) : Inputs 13 → F[X] :=
  Sum.elim (env12 a) (fun _ => n a)

theorem gate10_eval (a : ℕ → F) (i : Fin 1) :
    (gate10 (F := F)).eval (Char2Degree23Program.env10 a) i = h a := by
  simp only [gate10, Cost.Circuit.eval, Cost.Circuit.input,
    Char2Degree23Program.env10, Char2Degree23Program.env9, Char2Degree23Program.env8, Char2Degree23Program.env7, Char2Degree23Program.env6, Char2Degree23Program.env5, Char2Degree23Program.env4, Char2Degree23Program.env3, Char2Degree23Program.env2, Char2Degree23Program.env1, Char2Degree23Program.env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub,
    OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, h, hLeft, hRight, add_assoc]

theorem gate11_eval (a : ℕ → F) (i : Fin 1) :
    (gate11 (F := F)).eval (env11 a) i = j a := by
  simp only [gate11, Cost.Circuit.eval, Cost.Circuit.input,
    env11, Char2Degree23Program.env10, Char2Degree23Program.env9, Char2Degree23Program.env8, Char2Degree23Program.env7, Char2Degree23Program.env6, Char2Degree23Program.env5, Char2Degree23Program.env4, Char2Degree23Program.env3, Char2Degree23Program.env2, Char2Degree23Program.env1, Char2Degree23Program.env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub,
    OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, j, jLeft, add_assoc]

theorem gate12_eval (a : ℕ → F) (i : Fin 1) :
    (gate12 (F := F)).eval (env12 a) i = n a := by
  simp only [gate12, Cost.Circuit.eval, Cost.Circuit.input,
    env12, env11, Char2Degree23Program.env10, Char2Degree23Program.env9, Char2Degree23Program.env8, Char2Degree23Program.env7, Char2Degree23Program.env6, Char2Degree23Program.env5, Char2Degree23Program.env4, Char2Degree23Program.env3, Char2Degree23Program.env2, Char2Degree23Program.env1, Char2Degree23Program.env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub,
    OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, n, nLeft, nRight, add_assoc]

theorem tail13_eval (a : ℕ → F) :
    (tail13 (F := F)).eval (env13 a) 0 = output a := by
  simp only [tail13, Cost.Circuit.eval, Cost.Circuit.input,
    env13, env12, env11, Char2Degree23Program.env10, Char2Degree23Program.env9, Char2Degree23Program.env8, Char2Degree23Program.env7, Char2Degree23Program.env6, Char2Degree23Program.env5, Char2Degree23Program.env4, Char2Degree23Program.env3, Char2Degree23Program.env2, Char2Degree23Program.env1, Char2Degree23Program.env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub,
    OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true,
    output, Char2Degree25Frame.head, add_assoc]

theorem tail12_eval (a : ℕ → F) :
    (tail12 (F := F)).eval (env12 a) 0 = output a := by
  have hg : (gate12 (F := F)).eval (env12 a) = (fun _ => n a) :=
    funext (gate12_eval a)
  rw [tail12, Cost.Circuit.eval, hg]
  exact tail13_eval a

theorem tail11_eval (a : ℕ → F) :
    (tail11 (F := F)).eval (env11 a) 0 = output a := by
  have hg : (gate11 (F := F)).eval (env11 a) = (fun _ => j a) :=
    funext (gate11_eval a)
  rw [tail11, Cost.Circuit.eval, hg]
  exact tail12_eval a

theorem tail10_eval (a : ℕ → F) :
    (tail10 (F := F)).eval (Char2Degree23Program.env10 a) 0 = output a := by
  have hg : (gate10 (F := F)).eval (Char2Degree23Program.env10 a) = (fun _ => h a) :=
    funext (gate10_eval a)
  rw [tail10, Cost.Circuit.eval, hg]
  exact tail11_eval a

theorem tail9_eval (a : ℕ → F) :
    (tail9 (F := F)).eval (Char2Degree23Program.env9 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate9 (F := F)).eval (Char2Degree23Program.env9 a) = (fun _ => Char2Degree23RowEight.ell a) :=
    funext (Char2Degree23Program.gate9_eval a)
  rw [tail9, Cost.Circuit.eval, hg]
  exact tail10_eval a

theorem tail8_eval (a : ℕ → F) :
    (tail8 (F := F)).eval (Char2Degree23Program.env8 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate8 (F := F)).eval (Char2Degree23Program.env8 a) = (fun _ => Char2Degree23RowEight.g a) :=
    funext (Char2Degree23Program.gate8_eval a)
  rw [tail8, Cost.Circuit.eval, hg]
  exact tail9_eval a

theorem tail7_eval (a : ℕ → F) :
    (tail7 (F := F)).eval (Char2Degree23Program.env7 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate7 (F := F)).eval (Char2Degree23Program.env7 a) = (fun _ => Char2Degree23RowEight.r a) :=
    funext (Char2Degree23Program.gate7_eval a)
  rw [tail7, Cost.Circuit.eval, hg]
  exact tail8_eval a

theorem tail6_eval (a : ℕ → F) :
    (tail6 (F := F)).eval (Char2Degree23Program.env6 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate6 (F := F)).eval (Char2Degree23Program.env6 a) = (fun _ => Char2Degree23RowEight.s a) :=
    funext (Char2Degree23Program.gate6_eval a)
  rw [tail6, Cost.Circuit.eval, hg]
  exact tail7_eval a

theorem tail5_eval (a : ℕ → F) :
    (tail5 (F := F)).eval (Char2Degree23Program.env5 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate5 (F := F)).eval (Char2Degree23Program.env5 a) = (fun _ => Char2Degree23RowEight.w a) :=
    funext (Char2Degree23Program.gate5_eval a)
  rw [tail5, Cost.Circuit.eval, hg]
  exact tail6_eval a

theorem tail4_eval (a : ℕ → F) :
    (tail4 (F := F)).eval (Char2Degree23Program.env4 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate4 (F := F)).eval (Char2Degree23Program.env4 a) = (fun _ => Char2Degree23RowEight.v a) :=
    funext (Char2Degree23Program.gate4_eval a)
  rw [tail4, Cost.Circuit.eval, hg]
  exact tail5_eval a

theorem tail3_eval (a : ℕ → F) :
    (tail3 (F := F)).eval (Char2Degree23Program.env3 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate3 (F := F)).eval (Char2Degree23Program.env3 a) = (fun _ => Char2Degree23RowEight.u a) :=
    funext (Char2Degree23Program.gate3_eval a)
  rw [tail3, Cost.Circuit.eval, hg]
  exact tail4_eval a

theorem tail2_eval (a : ℕ → F) :
    (tail2 (F := F)).eval (Char2Degree23Program.env2 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate2 (F := F)).eval (Char2Degree23Program.env2 a) = (fun _ => Char2Degree23RowEight.t a) :=
    funext (Char2Degree23Program.gate2_eval a)
  rw [tail2, Cost.Circuit.eval, hg]
  exact tail3_eval a

theorem tail1_eval (a : ℕ → F) :
    (tail1 (F := F)).eval (Char2Degree23Program.env1 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate1 (F := F)).eval (Char2Degree23Program.env1 a) = (fun _ => Char2Degree23RowEight.z a) :=
    funext (Char2Degree23Program.gate1_eval a)
  rw [tail1, Cost.Circuit.eval, hg]
  exact tail2_eval a

theorem tail0_eval (a : ℕ → F) :
    (tail0 (F := F)).eval (Char2Degree23Program.env0 a) 0 = output a := by
  have hg : (Char2Degree23Program.gate0 (F := F)).eval (Char2Degree23Program.env0 a) = (fun _ => (Char2Degree23RowEight.y : F[X])) :=
    funext (Char2Degree23Program.gate0_eval a)
  rw [tail0, Cost.Circuit.eval, hg]
  exact tail1_eval a

theorem program_eval (a : ℕ → F) :
    (program (F := F)).circuit.eval (inputEnv a) 0 = output a := tail0_eval a

end FastPoly.Char2Degree25Program

