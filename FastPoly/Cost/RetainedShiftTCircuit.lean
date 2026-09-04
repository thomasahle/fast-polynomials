import FastPoly.Cost.TCircuitCount
import FastPoly.Cost.PowerTowerCircuit

/-!
# Shared `T` bases with a retained scalar shift

The manuscript carries the scalar difference between the two supplied powers as a
wire.  The older semantic compiler reconstructed that difference inside each shared
base.  The circuits below expose the retained wire explicitly and prove both semantic
equivalence and literal gate counts.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace RetainedShiftT

private abbrev x {R : Type u} : Circuit R ConstructionInput 1 :=
  Circuit.constructionX

private abbrev h {R : Type u} (i : ℕ) : Circuit R ConstructionInput 1 :=
  Circuit.constructionPower i

private abbrev ht {R : Type u} : Circuit R ConstructionInput 1 :=
  Circuit.constructionShiftedPower

private abbrev a {R : Type u} (i : ℕ) : Circuit R ConstructionInput 1 :=
  Circuit.constructionParameter i

private abbrev q3 {R : Type u} : Circuit R ConstructionInput 1 :=
  (mersCircuit 2).reindexConstructionParameters (fun j => 1 + j)

/-! ## Shared even base -/

/-- The power pair of the shared even base, using the already-retained scalar shift.
Output order is `(H₄,H̃₄)`. -/
def evenBasePowerPair {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) : Circuit R ConstructionInput 2 :=
  let linear := .add x (a (2 * k - 3))
  let H₄ := Circuit.diffSquareAdd (h 1) linear (a (2 * k - 4))
  .bind H₄ <|
    let h₄ := Circuit.rightInput (R := R) (i := (0 : Fin 1))
    .fork h₄ (.add h₄ rho.liftLeft)

/-- Shared even base followed by its recursive call. -/
def evenBaseCircuit {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) (inner : Circuit R ConstructionInput 2) :
    Circuit R ConstructionInput 2 :=
  .bind (evenBasePowerPair k rho) <| recurseWithPowerPair 2 id 0 1 inner

/-- Complete level-one call with the same fuel and recursive body as `tCircuit`. -/
def evenBaseTCircuit {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) : Circuit R ConstructionInput 2 :=
  evenBaseCircuit k rho (tCircuitF (k - 1) (k / 2) 2)

theorem evenBasePowerPair_additions {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) :
    (evenBasePowerPair k rho).gates.additions = rho.gates.additions + 5 := by
  simp only [evenBasePowerPair, Circuit.gates_bind, Circuit.gates,
    Circuit.gates_diffSquareAdd_additions, Circuit.gates_rightInput,
    Circuit.gates_liftLeft, Circuit.gates_constructionPower,
    Circuit.gates_constructionX, Circuit.gates_constructionParameter,
    GateCount.add_additions, GateCount.zero_additions, GateCount.adds_additions]
  omega

theorem evenBasePowerPair_multiplications {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) :
    (evenBasePowerPair k rho).gates.multiplications =
      rho.gates.multiplications + 1 := by
  simp only [evenBasePowerPair, Circuit.gates_bind, Circuit.gates,
    Circuit.gates_diffSquareAdd_multiplications, Circuit.gates_rightInput,
    Circuit.gates_liftLeft, Circuit.gates_constructionPower,
    Circuit.gates_constructionX, Circuit.gates_constructionParameter,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications]
  omega

theorem evenBaseCircuit_additions {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) (inner : Circuit R ConstructionInput 2) :
    (evenBaseCircuit k rho inner).gates.additions =
      rho.gates.additions + inner.gates.additions + 5 := by
  simp only [evenBaseCircuit, Circuit.gates_bind, gates_recurseWithPowerPair,
    GateCount.add_additions, evenBasePowerPair_additions]
  omega

theorem evenBaseCircuit_multiplications {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) (inner : Circuit R ConstructionInput 2) :
    (evenBaseCircuit k rho inner).gates.multiplications =
      rho.gates.multiplications + inner.gates.multiplications + 1 := by
  simp only [evenBaseCircuit, Circuit.gates_bind, gates_recurseWithPowerPair,
    GateCount.add_multiplications, evenBasePowerPair_multiplications]
  omega

theorem evenBaseTCircuit_additions {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) :
    (evenBaseTCircuit k rho).gates.additions =
      rho.gates.additions + (tCircuitF (R := R) (k - 1) (k / 2) 2).gates.additions +
        5 := by
  exact evenBaseCircuit_additions k rho _

theorem evenBaseTCircuit_multiplications {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) :
    (evenBaseTCircuit k rho).gates.multiplications =
      rho.gates.multiplications +
        (tCircuitF (R := R) (k - 1) (k / 2) 2).gates.multiplications + 1 := by
  exact evenBaseCircuit_multiplications k rho _

/-! ## Shared odd base -/

/-- The six retained auxiliaries of the shared odd base, with the scalar shift supplied
as a circuit.  Binding `F₁` makes `F₂ = F₁ + kρ` a single affine gate. -/
def oddBaseAux {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) : Circuit R ConstructionInput 6 :=
  let b := 4 * (k - 2)
  let s₁ : Circuit R ConstructionInput 1 := .add (h 1) (.add x (a (b + 3)))
  .bind s₁ <|
    let s := Circuit.rightInput (R := R) (i := (0 : Fin 1))
    let old (c : Circuit R ConstructionInput 1) := c.liftLeft
    let h₈ := Circuit.diffSquareAdd
      (.add (old (h 2)) s)
      (.add (old x) (old (a (b + 2))))
      (old (a (b + 1)))
    .bind h₈ <|
      let s' : Circuit R (Sum (Sum ConstructionInput (Fin 1)) (Fin 1)) 1 :=
        Circuit.input (.inl (.inr (0 : Fin 1)))
      let old (c : Circuit R ConstructionInput 1) := c.liftLeft.liftLeft
      let f₁ := .sub (old (h 2)) (.scale ((k - 1 : ℕ) : R) s')
      .bind f₁ <|
        let h₈' : Circuit R
            (Sum (Sum (Sum ConstructionInput (Fin 1)) (Fin 1)) (Fin 1)) 1 :=
          Circuit.input (.inl (.inr (0 : Fin 1)))
        let f₁' := Circuit.rightInput (R := R) (i := (0 : Fin 1))
        let old (c : Circuit R ConstructionInput 1) := c.liftLeft.liftLeft.liftLeft
        .fork
          (.fork h₈' (.add h₈' (old (a b))))
          (.fork
            (.fork f₁' (.add f₁' (.scale (k : R) (old rho))))
            (.fork (old q3) (old (a 0))))

/-- Shared odd base using the retained scalar shift. -/
def oddBaseCircuit {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) (inner : Circuit R ConstructionInput 2) :
    Circuit R ConstructionInput 2 :=
  finishOdd 3 (fun j => 4 + j) (oddBaseAux k rho) inner

/-- Complete level-two odd call with the same fuel and recursive body as `tCircuit`. -/
def oddBaseTCircuit {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) : Circuit R ConstructionInput 2 :=
  oddBaseCircuit k rho (tCircuitF (k - 1) ((k - 1) / 2) 3)

theorem oddBaseAux_additions {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) :
    (oddBaseAux k rho).gates.additions = rho.gates.additions + 13 := by
  simp only [oddBaseAux, Circuit.diffSquareAdd, Circuit.gates_bind, Circuit.gates,
    Circuit.gates_rightInput,
    Circuit.gates_input, Circuit.gates_liftLeft,
    Circuit.gates_constructionPower, Circuit.gates_constructionX,
    Circuit.gates_constructionParameter, Circuit.gates_reindexConstructionParameters,
    GateCount.add_additions, GateCount.zero_additions, GateCount.adds_additions,
    GateCount.muls_additions, q3]
  have hq₃ : (mersCircuit (R := R) 2).gates.additions = 3 := by rfl
  rw [hq₃]
  omega

theorem oddBaseAux_multiplications {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) :
    (oddBaseAux k rho).gates.multiplications =
      rho.gates.multiplications + 2 := by
  simp only [oddBaseAux, Circuit.gates_bind, Circuit.gates,
    Circuit.gates_diffSquareAdd_multiplications, Circuit.gates_rightInput,
    Circuit.gates_input, Circuit.gates_liftLeft,
    Circuit.gates_constructionPower, Circuit.gates_constructionX,
    Circuit.gates_constructionParameter, Circuit.gates_reindexConstructionParameters,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, q3]
  rw [gates_mersCircuit_multiplications (R := R) 2 (by omega)]
  omega

theorem oddBaseCircuit_additions {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) (inner : Circuit R ConstructionInput 2) :
    (oddBaseCircuit k rho inner).gates.additions =
      rho.gates.additions + inner.gates.additions + 15 := by
  rw [oddBaseCircuit]
  simp only [finishOdd, Circuit.gates_bind, gates_recurseWithPowerPair,
    Circuit.gates, priorBound, Circuit.gates_input, Circuit.gates_rightInput,
    GateCount.add_additions, GateCount.zero_additions, GateCount.adds_additions,
    GateCount.muls_additions]
  rw [oddBaseAux_additions]
  omega

theorem oddBaseCircuit_multiplications {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) (inner : Circuit R ConstructionInput 2) :
    (oddBaseCircuit k rho inner).gates.multiplications =
      rho.gates.multiplications + inner.gates.multiplications + 4 := by
  rw [oddBaseCircuit, gates_finishOdd_multiplications,
    oddBaseAux_multiplications]
  omega

theorem oddBaseTCircuit_additions {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) :
    (oddBaseTCircuit k rho).gates.additions =
      rho.gates.additions +
        (tCircuitF (R := R) (k - 1) ((k - 1) / 2) 3).gates.additions + 15 := by
  exact oddBaseCircuit_additions k rho _

theorem oddBaseTCircuit_multiplications {R : Type u} [CommRing R] (k : ℕ)
    (rho : Circuit R ConstructionInput 1) :
    (oddBaseTCircuit k rho).gates.multiplications =
      rho.gates.multiplications +
        (tCircuitF (R := R) (k - 1) ((k - 1) / 2) 3).gates.multiplications + 4 := by
  exact oddBaseCircuit_multiplications k rho _

section Semantics

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

theorem eval_evenBasePowerPair_eq (k : ℕ)
    (rho : Circuit R ConstructionInput 1) (env : ConstructionInput → A[X])
    (hshift : env .shiftedPower = env (.power 1) + rho.eval env 0) :
    (evenBasePowerPair k rho).eval env =
      (tEvenBasePowerPair (R := R) k).eval env := by
  funext i
  refine Fin.addCases (m := 1) (n := 1) ?_ ?_ i
  · intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    simp only [evenBasePowerPair, tEvenBasePowerPair, Circuit.eval_bind,
      Circuit.eval_fork, Circuit.eval_add, Circuit.eval_diffSquareAdd,
      Circuit.eval_liftLeft, Circuit.eval_rightInput, Fin.addCases_left,
      x, h, a]
  · intro j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    simp only [evenBasePowerPair, tEvenBasePowerPair, Circuit.eval_bind,
      Circuit.eval_fork, Circuit.eval_add, Circuit.eval_sub,
      Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft,
      Circuit.eval_rightInput, Fin.addCases_right, x, h, a]
    change
      ((env (.power 1) + (env .variable + env (.parameter (2 * k - 3)))) *
            (env (.power 1) - (env .variable + env (.parameter (2 * k - 3)))) +
          env (.parameter (2 * k - 4))) + rho.eval env 0 =
        ((env (.power 1) + (env .variable + env (.parameter (2 * k - 3)))) *
            (env (.power 1) - (env .variable + env (.parameter (2 * k - 3)))) +
          env (.parameter (2 * k - 4))) +
            (env .shiftedPower - env (.power 1))
    rw [hshift]
    ring

theorem eval_evenBaseCircuit_eq (k : ℕ)
    (rho : Circuit R ConstructionInput 1) (inner : Circuit R ConstructionInput 2)
    (env : ConstructionInput → A[X])
    (hshift : env .shiftedPower = env (.power 1) + rho.eval env 0) :
    (evenBaseCircuit k rho inner).eval env =
      (tEvenBaseCircuit k inner).eval env := by
  rw [evenBaseCircuit, tEvenBaseCircuit]
  simp only [Circuit.eval_bind]
  rw [eval_evenBasePowerPair_eq k rho env hshift]

theorem eval_evenBaseTCircuit_eq_tCircuit (k : ℕ) (hk : 2 ≤ k)
    (heven : k % 2 = 0) (rho : Circuit R ConstructionInput 1)
    (env : ConstructionInput → A[X])
    (hshift : env .shiftedPower = env (.power 1) + rho.eval env 0) :
    (evenBaseTCircuit k rho).eval env = (tCircuit (R := R) k 1).eval env := by
  have hbranch : tCircuitF (R := R) k k 1 =
      tEvenBaseCircuit k (tCircuitF (k - 1) (k / 2) 2) := by
    simpa only [show k - 1 + 1 = k by omega] using
      tCircuitF_succ_even_base (R := R) (k - 1) k 1
        (by omega) heven (by omega)
  rw [evenBaseTCircuit, tCircuit, hbranch]
  exact eval_evenBaseCircuit_eq k rho _ env hshift

theorem eval_oddBaseAux_eq (k : ℕ) (hk : 1 ≤ k)
    (rho : Circuit R ConstructionInput 1) (env : ConstructionInput → A[X])
    (hshift : env .shiftedPower = env (.power 2) + rho.eval env 0) :
    (oddBaseAux k rho).eval env = (tOddBaseAux (R := R) k).eval env := by
  funext i
  refine Fin.addCases (m := 2) (n := 4) ?_ ?_ i
  · intro i
    refine Fin.addCases (m := 1) (n := 1) ?_ ?_ i
    · intro j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simp only [oddBaseAux, tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork,
        Circuit.eval_add, Circuit.eval_sub, Circuit.eval_scale,
        Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft, Circuit.eval_rightInput,
        Circuit.input, Circuit.eval_wire, Fin.addCases_left, Sum.elim_inl,
        Sum.elim_inr, x, h, a, q3]
    · intro j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simp only [oddBaseAux, tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork,
        Circuit.eval_add, Circuit.eval_sub, Circuit.eval_scale,
        Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft, Circuit.eval_rightInput,
        Circuit.input, Circuit.eval_wire, Fin.addCases_left, Fin.addCases_right,
        Sum.elim_inl, Sum.elim_inr, x, h, a, q3]
  · intro i
    refine Fin.addCases (m := 2) (n := 2) ?_ ?_ i
    · intro j
      refine Fin.addCases (m := 1) (n := 1) ?_ ?_ j
      · intro q
        have hq : q = 0 := Fin.eq_zero q
        subst q
        simp only [oddBaseAux, tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork,
          Circuit.eval_add, Circuit.eval_sub, Circuit.eval_scale,
          Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft, Circuit.eval_rightInput,
          Circuit.input, Circuit.eval_wire, Fin.addCases_left, Fin.addCases_right,
          Sum.elim_inl, Sum.elim_inr, x, h, a, q3]
      · intro q
        have hq : q = 0 := Fin.eq_zero q
        subst q
        simp only [oddBaseAux, tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork,
          Circuit.eval_add, Circuit.eval_sub, Circuit.eval_scale,
          Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft, Circuit.eval_rightInput,
          Circuit.input, Circuit.eval_wire, Fin.addCases_left, Fin.addCases_right,
          Sum.elim_inl, Sum.elim_inr, x, h, a, q3]
        change
          env (.power 2) - algebraMap R A[X] ((k - 1 : ℕ) : R) *
                (env (.power 1) + (env .variable + env (.parameter (4 * (k - 2) + 3)))) +
              algebraMap R A[X] (k : R) * rho.eval env 0 =
            env .shiftedPower - algebraMap R A[X] ((k - 1 : ℕ) : R) *
              ((env (.power 1) + (env .variable + env (.parameter (4 * (k - 2) + 3)))) -
                (env .shiftedPower - env (.power 2)))
        rw [hshift]
        have hkR : (k : R) = ((k - 1 : ℕ) : R) + 1 := by
          calc
            (k : R) = (((k - 1) + 1 : ℕ) : R) := by congr 1; omega
            _ = ((k - 1 : ℕ) : R) + 1 := by
              simp only [Nat.cast_add, Nat.cast_one]
        rw [hkR, map_add, map_one]
        ring
    · intro j
      refine Fin.addCases (m := 1) (n := 1) ?_ ?_ j
      · intro q
        have hq : q = 0 := Fin.eq_zero q
        subst q
        simp only [oddBaseAux, tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork,
          Circuit.eval_add, Circuit.eval_sub, Circuit.eval_scale,
          Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft, Circuit.eval_rightInput,
          Circuit.input, Circuit.eval_wire, Fin.addCases_left, Fin.addCases_right,
          Sum.elim_inl, Sum.elim_inr, x, h, a, q3]
        rfl
      · intro q
        have hq : q = 0 := Fin.eq_zero q
        subst q
        simp only [oddBaseAux, tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork,
          Circuit.eval_add, Circuit.eval_sub, Circuit.eval_scale,
          Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft, Circuit.eval_rightInput,
          Circuit.input, Circuit.eval_wire, Fin.addCases_right,
          Sum.elim_inl, Sum.elim_inr, x, h, a, q3]

theorem eval_oddBaseCircuit_eq (k : ℕ) (rho : Circuit R ConstructionInput 1)
    (inner : Circuit R ConstructionInput 2) (env : ConstructionInput → A[X])
    (hk : 1 ≤ k)
    (hshift : env .shiftedPower = env (.power 2) + rho.eval env 0) :
    (oddBaseCircuit k rho inner).eval env =
      (tOddBaseCircuit k inner).eval env := by
  rw [oddBaseCircuit, tOddBaseCircuit]
  conv_lhs => rw [finishOdd, Circuit.eval_bind]
  conv_rhs => rw [finishOdd, Circuit.eval_bind]
  rw [eval_oddBaseAux_eq k hk rho env hshift]

theorem eval_oddBaseTCircuit_eq_tCircuit (k : ℕ) (hk : 3 ≤ k)
    (hodd : k % 2 ≠ 0) (rho : Circuit R ConstructionInput 1)
    (env : ConstructionInput → A[X])
    (hshift : env .shiftedPower = env (.power 2) + rho.eval env 0) :
    (oddBaseTCircuit k rho).eval env = (tCircuit (R := R) k 2).eval env := by
  have hbranch : tCircuitF (R := R) k k 2 =
      tOddBaseCircuit k (tCircuitF (k - 1) ((k - 1) / 2) 3) := by
    simpa only [show k - 1 + 1 = k by omega] using
      tCircuitF_succ_odd_base (R := R) (k - 1) k 2
        (by omega) hodd (by omega)
  rw [oddBaseTCircuit, tCircuit, hbranch]
  exact eval_oddBaseCircuit_eq k rho _ env (by omega) hshift

end Semantics

end RetainedShiftT

end FastPoly.Cost
