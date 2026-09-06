import FastPoly.Examples.Char2PaperDegree11Core
import FastPoly.Examples.Char2Construction

/-! The six literal products of the current appendix's degree-eleven circuit.
Every gate and bind tail has a separate evaluation equation. No inverse or
perfect-field assumption is needed for the multiplication ledger. -/

namespace FastPoly.Char2PaperDegree11Program

open Polynomial Char2Certificate Char2PaperDegree11
set_option maxHeartbeats 20000

variable {F : Type*} [Field F] [CharP F 2]

abbrev Inputs : ℕ → Type
  | 0 => ℕ
  | k + 1 => Inputs k ⊕ Fin 1

def gate0 : Cost.Circuit F (Inputs 0) 1 :=
  .mul (.input 0) (.add (.input 0) (.input 1))

def gate1 : Cost.Circuit F (Inputs 1) 1 :=
  let x : Cost.Circuit F (Inputs 1) 1 := .input (Sum.inl 0)
  let y : Cost.Circuit F (Inputs 1) 1 := .input (Sum.inr 0)
  .mul (.add y (.input (Sum.inl 2))) (.add (.add x y) (.input (Sum.inl 3)))

def gate2 : Cost.Circuit F (Inputs 2) 1 :=
  .mul (.input (Sum.inl (Sum.inl 0)))
    (.add (.input (Sum.inl (Sum.inr 0))) (.input (Sum.inl (Sum.inl 4))))

def gate3 : Cost.Circuit F (Inputs 3) 1 :=
  .mul (.add (.input (Sum.inr 0)) (.input (Sum.inl (Sum.inl (Sum.inl 5)))))
    (.add (.input (Sum.inl (Sum.inr 0))) (.input (Sum.inl (Sum.inl (Sum.inl 6)))))

def gate4 : Cost.Circuit F (Inputs 4) 1 :=
  let x : Cost.Circuit F (Inputs 4) 1 := .input (Sum.inl (Sum.inl (Sum.inl (Sum.inl 0))))
  let y : Cost.Circuit F (Inputs 4) 1 := .input (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0))))
  let z : Cost.Circuit F (Inputs 4) 1 := .input (Sum.inl (Sum.inl (Sum.inr 0)))
  let t : Cost.Circuit F (Inputs 4) 1 := .input (Sum.inl (Sum.inr 0))
  let u : Cost.Circuit F (Inputs 4) 1 := .input (Sum.inr 0)
  .mul (.add (.add (.add (.add x y) t) u) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl 7))))))
    (.add (.add z t) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl 8))))))

def gate5 : Cost.Circuit F (Inputs 5) 1 :=
  let y : Cost.Circuit F (Inputs 5) 1 := .input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr 0)))))
  let t : Cost.Circuit F (Inputs 5) 1 := .input (Sum.inl (Sum.inl (Sum.inr 0)))
  let u : Cost.Circuit F (Inputs 5) 1 := .input (Sum.inl (Sum.inr 0))
  .mul (.add t (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl 9)))))))
    (.add (.add y u) (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl 10)))))))

def tail6 : Cost.Circuit F (Inputs 6) 1 :=
  .add (.add (.input (Sum.inl (Sum.inr 0))) (.input (Sum.inr 0)))
    (.input (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl 11)))))))

def tail5 : Cost.Circuit F (Inputs 5) 1 := .bind gate5 tail6
def tail4 : Cost.Circuit F (Inputs 4) 1 := .bind gate4 tail5
def tail3 : Cost.Circuit F (Inputs 3) 1 := .bind gate3 tail4
def tail2 : Cost.Circuit F (Inputs 2) 1 := .bind gate2 tail3
def tail1 : Cost.Circuit F (Inputs 1) 1 := .bind gate1 tail2
def tail0 : Cost.Circuit F (Inputs 0) 1 := .bind gate0 tail1
def circuit : Cost.Circuit F ℕ 1 := tail0

theorem multiplication_count : (circuit (F := F)).gates.multiplications = 6 := by
  simp only [circuit, tail0, tail1, tail2, tail3, tail4, tail5, tail6,
    gate0, gate1, gate2, gate3, gate4, gate5,
    Cost.Circuit.gates, Cost.Circuit.gates_input,
    Cost.GateCount.add_multiplications, Cost.GateCount.zero_multiplications,
    Cost.GateCount.adds_multiplications, Cost.GateCount.muls_multiplications,
    Nat.zero_add, Nat.add_zero]

def program : Cost.MultiplicationProgram F ℕ 1 6 := ⟨circuit, multiplication_count⟩

noncomputable def env0 (a : ℕ → F) : Inputs 0 → F[X] := inputEnv a
noncomputable def env1 (a : ℕ → F) : Inputs 1 → F[X] := Sum.elim (env0 a) (fun _ => y a)
noncomputable def env2 (a : ℕ → F) : Inputs 2 → F[X] := Sum.elim (env1 a) (fun _ => z a)
noncomputable def env3 (a : ℕ → F) : Inputs 3 → F[X] := Sum.elim (env2 a) (fun _ => t a)
noncomputable def env4 (a : ℕ → F) : Inputs 4 → F[X] := Sum.elim (env3 a) (fun _ => u a)
noncomputable def env5 (a : ℕ → F) : Inputs 5 → F[X] := Sum.elim (env4 a) (fun _ => v a)
noncomputable def env6 (a : ℕ → F) : Inputs 6 → F[X] := Sum.elim (env5 a) (fun _ => w a)

theorem gate0_eval (a : ℕ → F) (i : Fin 1) : (gate0 (F := F)).eval (env0 a) i = y a := by
  simp only [gate0, Cost.Circuit.eval, Cost.Circuit.input, env0, inputEnv,
    Nat.reduceSub, one_ne_zero, ite_false, ite_true, y]

theorem gate1_eval (a : ℕ → F) (i : Fin 1) : (gate1 (F := F)).eval (env1 a) i = z a := by
  simp only [gate1, Cost.Circuit.eval, Cost.Circuit.input, env1, env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero,
    one_ne_zero, ite_false, ite_true, z]

theorem gate2_eval (a : ℕ → F) (i : Fin 1) : (gate2 (F := F)).eval (env2 a) i = t a := by
  simp only [gate2, Cost.Circuit.eval, Cost.Circuit.input, env2, env1, env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero,
    one_ne_zero, ite_false, ite_true, t]

theorem gate3_eval (a : ℕ → F) (i : Fin 1) : (gate3 (F := F)).eval (env3 a) i = u a := by
  simp only [gate3, Cost.Circuit.eval, Cost.Circuit.input, env3, env2, env1, env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero,
    one_ne_zero, ite_false, ite_true, u]

theorem gate4_eval (a : ℕ → F) (i : Fin 1) : (gate4 (F := F)).eval (env4 a) i = v a := by
  simp only [gate4, Cost.Circuit.eval, Cost.Circuit.input, env4, env3, env2, env1, env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero,
    one_ne_zero, ite_false, ite_true, v, vLeft, vRight]

theorem gate5_eval (a : ℕ → F) (i : Fin 1) : (gate5 (F := F)).eval (env5 a) i = w a := by
  simp only [gate5, Cost.Circuit.eval, Cost.Circuit.input, env5, env4, env3, env2, env1, env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero,
    one_ne_zero, ite_false, ite_true, w, wLeft, wRight]

theorem tail6_eval (a : ℕ → F) : (tail6 (F := F)).eval (env6 a) 0 = output a := by
  simp only [tail6, Cost.Circuit.eval, Cost.Circuit.input, env6, env5, env4, env3, env2, env1, env0,
    Sum.elim_inl, Sum.elim_inr, inputEnv, Nat.reduceSub, OfNat.ofNat_ne_zero,
    one_ne_zero, ite_false, ite_true, output]

theorem tail5_eval (a : ℕ → F) : (tail5 (F := F)).eval (env5 a) 0 = output a := by
  have hg : (gate5 (F := F)).eval (env5 a) = fun _ => w a := funext (gate5_eval a)
  rw [tail5, Cost.Circuit.eval, hg]
  exact tail6_eval a

theorem tail4_eval (a : ℕ → F) : (tail4 (F := F)).eval (env4 a) 0 = output a := by
  have hg : (gate4 (F := F)).eval (env4 a) = fun _ => v a := funext (gate4_eval a)
  rw [tail4, Cost.Circuit.eval, hg]
  exact tail5_eval a

theorem tail3_eval (a : ℕ → F) : (tail3 (F := F)).eval (env3 a) 0 = output a := by
  have hg : (gate3 (F := F)).eval (env3 a) = fun _ => u a := funext (gate3_eval a)
  rw [tail3, Cost.Circuit.eval, hg]
  exact tail4_eval a

theorem tail2_eval (a : ℕ → F) : (tail2 (F := F)).eval (env2 a) 0 = output a := by
  have hg : (gate2 (F := F)).eval (env2 a) = fun _ => t a := funext (gate2_eval a)
  rw [tail2, Cost.Circuit.eval, hg]
  exact tail3_eval a

theorem tail1_eval (a : ℕ → F) : (tail1 (F := F)).eval (env1 a) 0 = output a := by
  have hg : (gate1 (F := F)).eval (env1 a) = fun _ => z a := funext (gate1_eval a)
  rw [tail1, Cost.Circuit.eval, hg]
  exact tail2_eval a

theorem tail0_eval (a : ℕ → F) : (tail0 (F := F)).eval (env0 a) 0 = output a := by
  have hg : (gate0 (F := F)).eval (env0 a) = fun _ => y a := funext (gate0_eval a)
  rw [tail0, Cost.Circuit.eval, hg]
  exact tail1_eval a

theorem program_eval (a : ℕ → F) :
    (program (F := F)).circuit.eval (inputEnv a) 0 = Char2PaperDegree11.output a :=
  tail0_eval a

end FastPoly.Char2PaperDegree11Program
