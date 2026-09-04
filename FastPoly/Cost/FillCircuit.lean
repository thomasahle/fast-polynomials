import FastPoly.Cost.Circuit

/-!
# Semantic circuits for fill steps and chains

This module is deliberately generic in both the input-label type and the evaluation
ring. Heads, low gadgets, and source-pair components are themselves scalar circuits; a
fill step binds the source pair once and emits its two new components. The same compiler
can therefore be reused by the current Mersenne construction and by a later
characteristic-two family.
-/

namespace FastPoly.Cost

universe u v w

/-- Circuit-valued data for one fill level. Here `b` and `ah` already denote the
constant-polynomial wires used by the polynomial construction. -/
structure FillCircuitData (R : Type u) (ι : Type v) where
  q : Circuit R ι 1
  qh : Circuit R ι 1
  b : Circuit R ι 1
  ah : Circuit R ι 1

/-- Values obtained by evaluating one level's circuit data. -/
structure FillValues (B : Type w) where
  q : B
  qh : B
  b : B
  ah : B

@[ext] theorem FillValues.ext {B : Type w} {left right : FillValues B}
    (hq : left.q = right.q) (hqh : left.qh = right.qh)
    (hb : left.b = right.b) (hah : left.ah = right.ah) : left = right := by
  cases left
  cases right
  cases hq
  cases hqh
  cases hb
  cases hah
  rfl

def FillCircuitData.eval {R : Type u} {ι : Type v} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B] (d : FillCircuitData R ι) (env : ι → B) :
    FillValues B :=
  { q := d.q.eval env 0
    qh := d.qh.eval env 0
    b := d.b.eval env 0
    ah := d.ah.eval env 0 }

/-- Semantic form of one fill step. -/
def fillStepValue {B : Type w} [Ring B] (H : B) (d : FillValues B)
    (source : B × B) : B × B :=
  ((H + d.q) * source.1 + d.qh, (H + d.b) * source.2 + d.ah)

/-- Semantic form of the descending fill chain. -/
def fillChainValue {B : Type w} [Ring B] (H : ℕ → B) (D : ℕ → FillValues B) :
    (l : ℕ) → B × B → B × B
  | 0, source => source
  | 1, source => source
  | i + 2, source => fillChainValue H D (i + 1) (fillStepValue (H (i + 2)) (D (i + 2)) source)

/-- One shared fill step. -/
def Circuit.fillStep {R : Type u} {ι : Type v} (H : Circuit R ι 1)
    (d : FillCircuitData R ι) (source : Circuit R ι 2) : Circuit R ι 2 :=
  .bind source <|
    .fork
      (.add
        (.mul (.add H.liftLeft d.q.liftLeft)
          (Circuit.rightInput (ι := ι) (0 : Fin 2)))
        d.qh.liftLeft)
      (.add
        (.mul (.add H.liftLeft d.b.liftLeft)
          (Circuit.rightInput (ι := ι) (1 : Fin 2)))
        d.ah.liftLeft)

/-- Apply levels `l,l-1,…,2`. -/
def Circuit.fillChain {R : Type u} {ι : Type v}
    (H : ℕ → Circuit R ι 1) (D : ℕ → FillCircuitData R ι) :
    (l : ℕ) → Circuit R ι 2 → Circuit R ι 2
  | 0, source => source
  | 1, source => source
  | i + 2, source => fillChain H D (i + 1) (fillStep (H (i + 2)) (D (i + 2)) source)

/-- The level-one heads and final affine head of a full fill. All seven scalar
arguments are circuits so callers may supply wires from any ambient input layout. -/
def Circuit.finishFill {R : Type u} {ι : Type v}
    (x H₂ β₀ β₁ β₂ α₀ α₁ : Circuit R ι 1) (source : Circuit R ι 2) :
    Circuit R ι 1 :=
  .bind source <|
    .add
      (.mul (.add x.liftLeft β₀.liftLeft)
        (.add
          (.mul (.add H₂.liftLeft β₁.liftLeft)
            (Circuit.rightInput (ι := ι) (0 : Fin 2)))
          α₁.liftLeft))
      (.add
        (.mul (.add H₂.liftLeft β₂.liftLeft)
          (Circuit.rightInput (ι := ι) (1 : Fin 2)))
        α₀.liftLeft)

@[simp] theorem Circuit.eval_fillStep_zero {R : Type u} {ι : Type v} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B] (H : Circuit R ι 1)
    (d : FillCircuitData R ι) (source : Circuit R ι 2) (env : ι → B) :
    (fillStep H d source).eval env 0 =
      (H.eval env 0 + d.q.eval env 0) * source.eval env 0 + d.qh.eval env 0 := by
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  simp only [fillStep, Circuit.eval_bind, Circuit.eval_fork, Fin.addCases_left,
    Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  rfl

@[simp] theorem Circuit.eval_fillStep_one {R : Type u} {ι : Type v} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B] (H : Circuit R ι 1)
    (d : FillCircuitData R ι) (source : Circuit R ι 2) (env : ι → B) :
    (fillStep H d source).eval env 1 =
      (H.eval env 0 + d.b.eval env 0) * source.eval env 1 + d.ah.eval env 0 := by
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  simp only [fillStep, Circuit.eval_bind, Circuit.eval_fork, Fin.addCases_right,
    Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  rfl

/-- Evaluation commutes with the whole fill chain. -/
theorem Circuit.eval_fillChain {R : Type u} {ι : Type v} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (H : ℕ → Circuit R ι 1) (D : ℕ → FillCircuitData R ι) (env : ι → B) :
    ∀ l source,
      ((fillChain H D l source).eval env 0, (fillChain H D l source).eval env 1) =
        fillChainValue (fun i => (H i).eval env 0) (fun i => (D i).eval env) l
          (source.eval env 0, source.eval env 1) := by
  intro l
  induction l with
  | zero => intro source; rfl
  | succ l ih =>
      intro source
      rcases l with _ | l
      · rfl
      · change
          ((fillChain H D (l + 1) (fillStep (H (l + 2)) (D (l + 2)) source)).eval env 0,
            (fillChain H D (l + 1) (fillStep (H (l + 2)) (D (l + 2)) source)).eval env 1) = _
        rw [ih]
        change fillChainValue _ _ (l + 1)
            (((fillStep (H (l + 2)) (D (l + 2)) source).eval env 0),
              ((fillStep (H (l + 2)) (D (l + 2)) source).eval env 1)) =
          fillChainValue _ _ (l + 1)
            (fillStepValue ((H (l + 2)).eval env 0) ((D (l + 2)).eval env)
              (source.eval env 0, source.eval env 1))
        rw [eval_fillStep_zero, eval_fillStep_one]
        rfl

@[simp] theorem Circuit.eval_finishFill {R : Type u} {ι : Type v} {B : Type w}
    [CommRing R] [Ring B] [Algebra R B]
    (x H₂ β₀ β₁ β₂ α₀ α₁ : Circuit R ι 1) (source : Circuit R ι 2)
    (env : ι → B) :
    (finishFill x H₂ β₀ β₁ β₂ α₀ α₁ source).eval env 0 =
      (x.eval env 0 + β₀.eval env 0) *
          ((H₂.eval env 0 + β₁.eval env 0) * source.eval env 0 + α₁.eval env 0) +
        ((H₂.eval env 0 + β₂.eval env 0) * source.eval env 1 + α₀.eval env 0) := by
  simp only [finishFill, Circuit.eval_bind, Circuit.eval_add, Circuit.eval_mul,
    Circuit.eval_liftLeft, Circuit.eval_rightInput]

end FastPoly.Cost
