import FastPoly.Cost.TCircuit
import FastPoly.Cost.RealizationComposition

/-!
# Shared quadratic/quartic tower circuit

Several construction branches begin with the same two-product prefix

`H₂ = (x+b)x+c`, `H₄ = H₂²-(x+a)²+e`.

This module packages that prefix once, retaining `H₂`, `H₄`, an optional scalar-shifted
quartic, and a zero wire for local compilers whose source labels are formally present
but unused.  The identities are ring identities and hence characteristic independent.
-/

namespace FastPoly.Cost

universe u v w

namespace Circuit

/-- Output order: `(H₂,H₄,H₄+ρ,0)`. -/
def quadraticQuartic {R : Type u} [CommRing R] {ι : Type v}
    (x b c a e rho : Circuit R ι 1) : Circuit R ι 4 :=
  let H₂ : Circuit R ι 1 := .add (.mul (.add x b) x) c
  .bind H₂ <|
    let h₂ := Circuit.rightInput (R := R) (ι := ι) (0 : Fin 1)
    let old (p : Circuit R ι 1) := p.liftLeft
    let H₄ := Circuit.diffSquareAdd h₂ (.add (old x) (old a)) (old e)
    .bind H₄ <|
      let h₂' := Circuit.priorOutput (R := R) (n := 1) (0 : Fin 1)
      let h₄ := Circuit.rightInput (R := R) (ι := Sum ι (Fin 1)) (0 : Fin 1)
      .fork h₂' (.fork h₄ (.fork (.add h₄ rho.liftLeft.liftLeft) (.const 0)))

/-- Output order `(H₂,H₄,H₄,0)` when no shifted quartic is required.

This is not defined as `quadraticQuartic ... 0`: the third output is a copy of the
already-bound `H₄` wire, so the syntax contains no spurious addition by zero. -/
def quadraticQuarticUnshifted {R : Type u} [CommRing R] {ι : Type v}
    (x b c a e : Circuit R ι 1) : Circuit R ι 4 :=
  let H₂ : Circuit R ι 1 := .add (.mul (.add x b) x) c
  .bind H₂ <|
    let h₂ := Circuit.rightInput (R := R) (ι := ι) (0 : Fin 1)
    let old (p : Circuit R ι 1) := p.liftLeft
    let H₄ := Circuit.diffSquareAdd h₂ (.add (old x) (old a)) (old e)
    .bind H₄ <|
      let h₂' := Circuit.priorOutput (R := R) (n := 1) (0 : Fin 1)
      let h₄ := Circuit.rightInput (R := R) (ι := Sum ι (Fin 1)) (0 : Fin 1)
      .fork h₂' (.fork h₄ (.fork h₄ (.const 0)))

@[simp] theorem eval_quadraticQuarticUnshifted_zero {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type v}
    (x b c a e : Circuit R ι 1) (env : ι → A) :
    (quadraticQuarticUnshifted x b c a e).eval env 0 =
      (x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0 := by
  rfl

@[simp] theorem eval_quadraticQuarticUnshifted_one {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type v}
    (x b c a e : Circuit R ι 1) (env : ι → A) :
    (quadraticQuarticUnshifted x b c a e).eval env 1 =
      ((x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0) ^ 2 -
        (x.eval env 0 + a.eval env 0) ^ 2 + e.eval env 0 := by
  simp only [quadraticQuarticUnshifted, Circuit.eval_bind, Circuit.eval_fork,
    Circuit.eval_add, Circuit.eval_mul]
  rw [show (1 : Fin 4) = Fin.natAdd 1 (0 : Fin 3) from rfl,
    Fin.addCases_right]
  rw [show (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) from rfl,
    Fin.addCases_left]
  rw [Circuit.eval_rightInput, Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  ring

@[simp] theorem eval_quadraticQuarticUnshifted_two {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type v}
    (x b c a e : Circuit R ι 1) (env : ι → A) :
    (quadraticQuarticUnshifted x b c a e).eval env 2 =
      ((x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0) ^ 2 -
        (x.eval env 0 + a.eval env 0) ^ 2 + e.eval env 0 := by
  simp only [quadraticQuarticUnshifted, Circuit.eval_bind, Circuit.eval_fork,
    Circuit.eval_add, Circuit.eval_mul]
  rw [show (2 : Fin 4) = Fin.natAdd 1 (1 : Fin 3) from rfl,
    Fin.addCases_right]
  rw [show (1 : Fin 3) = Fin.natAdd 1 (0 : Fin 2) from rfl,
    Fin.addCases_right]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_left]
  rw [Circuit.eval_rightInput, Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  ring

@[simp] theorem eval_quadraticQuarticUnshifted_three {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type v}
    (x b c a e : Circuit R ι 1) (env : ι → A) :
    (quadraticQuarticUnshifted x b c a e).eval env 3 = 0 := by
  simp only [quadraticQuarticUnshifted, Circuit.eval_bind, Circuit.eval_fork,
    Circuit.eval_const]
  rw [show (3 : Fin 4) = Fin.natAdd 1 (2 : Fin 3) from rfl,
    Fin.addCases_right]
  rw [show (2 : Fin 3) = Fin.natAdd 1 (1 : Fin 2) from rfl,
    Fin.addCases_right]
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_right]
  exact map_zero (algebraMap R A)

/-- Exact addition cost of one difference-of-squares shell. -/
theorem gates_diffSquareAdd_additions {R : Type u} {ι : Type v}
    (center shift tail : Circuit R ι 1) :
    (Circuit.diffSquareAdd center shift tail).gates.additions =
      center.gates.additions + shift.gates.additions + tail.gates.additions + 3 := by
  simp only [Circuit.diffSquareAdd, Circuit.gates_bind, Circuit.gates,
    GateCount.add_additions, GateCount.zero_additions,
    GateCount.adds_additions, GateCount.muls_additions,
    Circuit.gates_rightInput, Circuit.gates_liftLeft]
  omega

/-- Exact nonscalar-multiplication count of the unshifted tower. -/
theorem gates_quadraticQuarticUnshifted_multiplications {R : Type u}
    [CommRing R] {ι : Type v} (x b c a e : Circuit R ι 1) :
    (quadraticQuarticUnshifted x b c a e).gates.multiplications =
      3 * x.gates.multiplications + b.gates.multiplications +
        c.gates.multiplications + a.gates.multiplications +
        e.gates.multiplications + 2 := by
  simp only [quadraticQuarticUnshifted, Circuit.gates_bind, Circuit.gates,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    Circuit.gates_diffSquareAdd_multiplications, Circuit.gates_liftLeft,
    Circuit.gates_rightInput, Circuit.gates_priorOutput]
  omega

/-- Exact addition count of the unshifted tower.  The coefficient `3` records the
three syntactic uses of `x`; at the intended call sites all five arguments are wires. -/
theorem gates_quadraticQuarticUnshifted_additions {R : Type u}
    [CommRing R] {ι : Type v} (x b c a e : Circuit R ι 1) :
    (quadraticQuarticUnshifted x b c a e).gates.additions =
      3 * x.gates.additions + b.gates.additions + c.gates.additions +
        a.gates.additions + e.gates.additions + 6 := by
  simp only [quadraticQuarticUnshifted, Circuit.gates_bind, Circuit.gates,
    GateCount.add_additions, GateCount.zero_additions, GateCount.adds_additions,
    GateCount.muls_additions, gates_diffSquareAdd_additions,
    Circuit.gates_liftLeft, Circuit.gates_rightInput, Circuit.gates_priorOutput]
  omega

@[simp] theorem eval_quadraticQuartic_zero {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type v}
    (x b c a e rho : Circuit R ι 1) (env : ι → A) :
    (quadraticQuartic x b c a e rho).eval env 0 =
      (x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0 := by
  rfl

@[simp] theorem eval_quadraticQuartic_one {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type v}
    (x b c a e rho : Circuit R ι 1) (env : ι → A) :
    (quadraticQuartic x b c a e rho).eval env 1 =
      ((x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0) ^ 2 -
        (x.eval env 0 + a.eval env 0) ^ 2 + e.eval env 0 := by
  simp only [quadraticQuartic, Circuit.eval_bind, Circuit.eval_fork,
    Circuit.eval_diffSquareAdd, Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  rw [show (1 : Fin 4) = Fin.natAdd 1 (0 : Fin 3) from rfl,
    Fin.addCases_right]
  rw [show (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) from rfl,
    Fin.addCases_left]
  rw [Circuit.eval_rightInput, Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  ring

@[simp] theorem eval_quadraticQuartic_two {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type v}
    (x b c a e rho : Circuit R ι 1) (env : ι → A) :
    (quadraticQuartic x b c a e rho).eval env 2 =
      ((x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0) ^ 2 -
        (x.eval env 0 + a.eval env 0) ^ 2 + e.eval env 0 + rho.eval env 0 := by
  simp only [quadraticQuartic, Circuit.eval_bind, Circuit.eval_fork,
    Circuit.eval_diffSquareAdd, Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  rw [show (2 : Fin 4) = Fin.natAdd 1 (1 : Fin 3) from rfl,
    Fin.addCases_right]
  rw [show (1 : Fin 3) = Fin.natAdd 1 (0 : Fin 2) from rfl,
    Fin.addCases_right]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_left]
  ring

@[simp] theorem eval_quadraticQuartic_three {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type v}
    (x b c a e rho : Circuit R ι 1) (env : ι → A) :
    (quadraticQuartic x b c a e rho).eval env 3 = 0 := by
  simp only [quadraticQuartic, Circuit.eval_bind, Circuit.eval_fork,
    Circuit.eval_const]
  rw [show (3 : Fin 4) = Fin.natAdd 1 (2 : Fin 3) from rfl,
    Fin.addCases_right]
  rw [show (2 : Fin 3) = Fin.natAdd 1 (1 : Fin 2) from rfl,
    Fin.addCases_right]
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_right]
  exact map_zero (algebraMap R A)

/-- Gate equation for the generic prefix.  Call sites normally instantiate all six
arguments by wires, reducing this to exactly two multiplications. -/
theorem gates_quadraticQuartic_multiplications {R : Type u} [CommRing R] {ι : Type v}
    (x b c a e rho : Circuit R ι 1) :
    (quadraticQuartic x b c a e rho).gates.multiplications =
      3 * x.gates.multiplications + b.gates.multiplications +
        c.gates.multiplications + a.gates.multiplications +
        e.gates.multiplications + rho.gates.multiplications + 2 := by
  simp only [quadraticQuartic, Circuit.gates_bind,
    Circuit.gates, GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    Circuit.gates_diffSquareAdd_multiplications, Circuit.gates_liftLeft,
    Circuit.gates_rightInput, Circuit.gates_priorOutput]
  omega

end Circuit

end FastPoly.Cost
