import FastPoly.Cost.PowerTowerCircuit

/-!
# Quadratic tower with a retained scalar shift

This is the share-aware prefix used by the degree-27 cost base.  It constructs the
unshifted quadratic first, retains its scalar translate, and builds the quartic from
that translated wire.  Output order is `(H₂,H₂+σ,H₄,H₄+ρ,0)`.
-/

namespace FastPoly.Cost

universe u v w

namespace Circuit

def quadraticShiftQuartic {R : Type u} [CommRing R] {iota : Type v}
    (x b c sigma a e rho : Circuit R iota 1) : Circuit R iota 5 :=
  let H₂ : Circuit R iota 1 := .add (.mul (.add x b) x) c
  .bind H₂ <|
    let h₂ := Circuit.rightInput (R := R) (i := (0 : Fin 1))
    let old (p : Circuit R iota 1) := p.liftLeft
    let H₂s := .add h₂ (old sigma)
    .bind H₂s <|
      let h₂s := Circuit.rightInput (R := R) (i := (0 : Fin 1))
      let old (p : Circuit R iota 1) := p.liftLeft.liftLeft
      let H₄ := Circuit.diffSquareAdd h₂s (.add (old x) (old a)) (old e)
      .bind H₄ <|
        let h₂ := Circuit.grandOutput (R := R) (m := 1) (n := 1) (o := 1)
          (0 : Fin 1)
        let h₂s := Circuit.priorOutput (R := R) (m := 1) (n := 1) (0 : Fin 1)
        let h₄ := Circuit.rightInput (R := R) (i := (0 : Fin 1))
        let old (p : Circuit R iota 1) := p.liftLeft.liftLeft.liftLeft
        .fork h₂ (.fork h₂s (.fork h₄
          (.fork (.add h₄ (old rho)) (.const 0))))

private theorem eval_fork5_one {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {iota : Type v}
    (p₀ p₁ p₂ p₃ p₄ : Circuit R iota 1) (env : iota → A) :
    (Circuit.fork p₀ (Circuit.fork p₁
      (Circuit.fork p₂ (Circuit.fork p₃ p₄)))).eval env 1 =
      p₁.eval env 0 := by
  rfl

private theorem eval_fork5_two {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {iota : Type v}
    (p₀ p₁ p₂ p₃ p₄ : Circuit R iota 1) (env : iota → A) :
    (Circuit.fork p₀ (Circuit.fork p₁
      (Circuit.fork p₂ (Circuit.fork p₃ p₄)))).eval env 2 =
      p₂.eval env 0 := by
  rfl

private theorem eval_fork5_three {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {iota : Type v}
    (p₀ p₁ p₂ p₃ p₄ : Circuit R iota 1) (env : iota → A) :
    (Circuit.fork p₀ (Circuit.fork p₁
      (Circuit.fork p₂ (Circuit.fork p₃ p₄)))).eval env 3 =
      p₃.eval env 0 := by
  rfl

@[simp] theorem eval_quadraticShiftQuartic_zero {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {iota : Type v}
    (x b c sigma a e rho : Circuit R iota 1) (env : iota → A) :
    (quadraticShiftQuartic x b c sigma a e rho).eval env 0 =
      (x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0 := by
  rfl

@[simp] theorem eval_quadraticShiftQuartic_one {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {iota : Type v}
    (x b c sigma a e rho : Circuit R iota 1) (env : iota → A) :
    (quadraticShiftQuartic x b c sigma a e rho).eval env 1 =
      (x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0 +
        sigma.eval env 0 := by
  rw [quadraticShiftQuartic, Circuit.eval_bind, Circuit.eval_bind,
    Circuit.eval_bind, eval_fork5_one]
  simp only [Circuit.eval_rightInput, Circuit.eval_priorOutput,
    Circuit.eval_liftLeft, Circuit.eval_add, Circuit.eval_mul]

@[simp] theorem eval_quadraticShiftQuartic_two {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {iota : Type v}
    (x b c sigma a e rho : Circuit R iota 1) (env : iota → A) :
    (quadraticShiftQuartic x b c sigma a e rho).eval env 2 =
      ((x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0 +
          sigma.eval env 0) ^ 2 -
        (x.eval env 0 + a.eval env 0) ^ 2 + e.eval env 0 := by
  rw [quadraticShiftQuartic, Circuit.eval_bind, Circuit.eval_bind,
    Circuit.eval_bind, eval_fork5_two, Circuit.eval_rightInput,
    Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  ring

@[simp] theorem eval_quadraticShiftQuartic_three {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {iota : Type v}
    (x b c sigma a e rho : Circuit R iota 1) (env : iota → A) :
    (quadraticShiftQuartic x b c sigma a e rho).eval env 3 =
      ((x.eval env 0 + b.eval env 0) * x.eval env 0 + c.eval env 0 +
          sigma.eval env 0) ^ 2 -
        (x.eval env 0 + a.eval env 0) ^ 2 + e.eval env 0 + rho.eval env 0 := by
  rw [quadraticShiftQuartic, Circuit.eval_bind, Circuit.eval_bind,
    Circuit.eval_bind, eval_fork5_three, Circuit.eval_add,
    Circuit.eval_rightInput, Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  ring

@[simp] theorem eval_quadraticShiftQuartic_four {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {iota : Type v}
    (x b c sigma a e rho : Circuit R iota 1) (env : iota → A) :
    (quadraticShiftQuartic x b c sigma a e rho).eval env 4 = 0 := by
  simp only [quadraticShiftQuartic, Circuit.eval_bind, Circuit.eval_fork,
    Circuit.eval_const]
  exact map_zero (algebraMap R A)

theorem gates_quadraticShiftQuartic_multiplications {R : Type u} [CommRing R]
    {iota : Type v} (x b c sigma a e rho : Circuit R iota 1) :
    (quadraticShiftQuartic x b c sigma a e rho).gates.multiplications =
      3 * x.gates.multiplications + b.gates.multiplications +
        c.gates.multiplications + sigma.gates.multiplications +
        a.gates.multiplications + e.gates.multiplications +
        rho.gates.multiplications + 2 := by
  simp only [quadraticShiftQuartic, Circuit.gates_bind, Circuit.gates,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    Circuit.gates_diffSquareAdd_multiplications, Circuit.gates_liftLeft,
    Circuit.gates_rightInput, Circuit.gates_priorOutput, Circuit.gates_grandOutput]
  omega

theorem gates_quadraticShiftQuartic_additions {R : Type u} [CommRing R]
    {iota : Type v} (x b c sigma a e rho : Circuit R iota 1) :
    (quadraticShiftQuartic x b c sigma a e rho).gates.additions =
      3 * x.gates.additions + b.gates.additions + c.gates.additions +
        sigma.gates.additions + a.gates.additions + e.gates.additions +
        rho.gates.additions + 8 := by
  simp only [quadraticShiftQuartic, Circuit.gates_bind, Circuit.gates,
    GateCount.add_additions, GateCount.zero_additions, GateCount.adds_additions,
    GateCount.muls_additions, Circuit.gates_diffSquareAdd_additions,
    Circuit.gates_liftLeft, Circuit.gates_rightInput, Circuit.gates_priorOutput,
    Circuit.gates_grandOutput]
  omega

end Circuit

end FastPoly.Cost
