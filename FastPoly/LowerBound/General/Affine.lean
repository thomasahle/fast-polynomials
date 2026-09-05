/-
The degree-six lower bound: affine parameter entry, the output polynomials of a general
program, and the chain rule `J_F = J ∘ Q · DQ`.
-/
import FastPoly.LowerBound.General.Gauge
import FastPoly.LowerBound.Jacobian
import FastPoly.LowerBound.Normalform

/-!
# The polynomial family of a general program and its Jacobian

A *program* is `(c, M, h₀)`: the sixteen constants `c : GCircuit F` and an affine map
`H p = M p + h₀` (`M : Matrix (Fin 7) (Fin 6) F`) sending the six parameters to the seven
constant slots.  Its six output polynomials are `outPolyGeneral c xs M h₀`, and
`polyMap (outPolyGeneral c xs M h₀)` is the evaluation map `F : F⁶ → F⁶` of the appendix.

The reduction identity `gout_eq` of `Gauge.lean` becomes, at the level of polynomial maps,
`F = E' ∘ Q` (`outPolyGeneral_eq_outPolyOf`), where `E'` is the normal form `c.toNormal`
with the slots given by the six polynomials `Qpoly b c M h₀` (`Q = ν ∘ H`, quadratic in
the parameters).  The chain rule `polyJacobian_outPolyOf` (the normal form with
*arbitrary* polynomial slots) then gives `J_F(p) = J(Q p) · DQ(p)`
(`polyJacobian_outPolyGeneral`).

The two transport lemmas `outPolyGeneral_swap` (interchange the factors of the first
gate) and `outPolyGeneral_ofNormal` (a normal-form program with affine slots is a general
program) are used by `Main.lean`.
-/

namespace FastPoly.LowerBound.General

open Matrix MvPolynomial

variable {F : Type*} [Field F]

/-! ## Affine slots -/

/-- The slots as affine functions of the parameters: `H p = M p + h₀`. -/
def affineSlots {ι : Type*} (M : Matrix ι (Fin 6) F) (h₀ : ι → F) (p : Fin 6 → F) : ι → F :=
  M *ᵥ p + h₀

/-- The slots as polynomials in the parameters. -/
noncomputable def affineSlotPoly {ι : Type*} (M : Matrix ι (Fin 6) F) (h₀ : ι → F) :
    ι → MvPolynomial (Fin 6) F :=
  fun j => (∑ i, C (M j i) * X i) + C (h₀ j)

@[simp] theorem eval_affineSlotPoly {ι : Type*} (M : Matrix ι (Fin 6) F) (h₀ : ι → F)
    (p : Fin 6 → F) (j : ι) : eval p (affineSlotPoly M h₀ j) = affineSlots M h₀ p j := by
  simp [affineSlotPoly, affineSlots, Matrix.mulVec, dotProduct]

@[simp] theorem pderiv_affineSlotPoly {ι : Type*} (M : Matrix ι (Fin 6) F) (h₀ : ι → F)
    (i : Fin 6) (j : ι) : pderiv i (affineSlotPoly M h₀ j) = C (M j i) := by
  rw [affineSlotPoly]
  simp only [map_add, pderiv_C, add_zero, map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem affineSlots_sub {ι : Type*} (M : Matrix ι (Fin 6) F) (h₀ : ι → F) (p p' : Fin 6 → F) :
    affineSlots M h₀ p - affineSlots M h₀ p' = M *ᵥ (p - p') := by
  rw [affineSlots, affineSlots, add_sub_add_right_eq_sub, Matrix.mulVec_sub]

/-! ## The output polynomials of a general program -/

/-- The six output polynomials `p ↦ f_{H p}(x_k)` of the general program `(c, M, h₀)`. -/
noncomputable def outPolyGeneral (c : GCircuit F) (xs : Fin 6 → F)
    (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) : Fin 6 → MvPolynomial (Fin 6) F :=
  fun k => gout (c.map C) (C (xs k)) (affineSlotPoly M h₀)

theorem GCircuit.mapC_map_eval (c : GCircuit F) (p : Fin 6 → F) :
    (c.map (C : F → MvPolynomial (Fin 6) F)).map (eval p) = c := by
  rw [GCircuit.map_map, GCircuit.map_congr c (g := id) (fun y => by simp), GCircuit.map_id]

theorem Circuit.mapC_map_eval' (c : Circuit F) (p : Fin 6 → F) :
    (c.map (C : F → MvPolynomial (Fin 6) F)).map (eval p) = c := by
  rw [Circuit.map_map, Circuit.map_congr c (g := id) (fun y => by simp), Circuit.map_id]

theorem eval_affineSlotPoly_fun {ι : Type*} (M : Matrix ι (Fin 6) F) (h₀ : ι → F)
    (p : Fin 6 → F) : (fun j => eval p (affineSlotPoly M h₀ j)) = affineSlots M h₀ p := by
  funext j
  exact eval_affineSlotPoly M h₀ p j

@[simp] theorem polyMap_outPolyGeneral (c : GCircuit F) (xs : Fin 6 → F)
    (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) (p : Fin 6 → F) (k : Fin 6) :
    polyMap (outPolyGeneral c xs M h₀) p k = gout c (xs k) (affineSlots M h₀ p) := by
  simp only [polyMap, outPolyGeneral]
  rw [map_gout (eval p) (c.map C) (C (xs k)) (affineSlotPoly M h₀), GCircuit.mapC_map_eval,
    eval_C, eval_affineSlotPoly_fun]

/-! ## The normal form with arbitrary polynomial slots, and the chain rule -/

/-- The normal-form program `c'` with its six slots given by arbitrary polynomials `S`. -/
noncomputable def outPolyOf (c' : Circuit F) (xs : Fin 6 → F)
    (S : Fin 6 → MvPolynomial (Fin 6) F) : Fin 6 → MvPolynomial (Fin 6) F :=
  fun k => out (c'.map C) (C (xs k)) S

theorem outPoly_eq_outPolyOf (c' : Circuit F) (xs : Fin 6 → F) :
    outPoly c' xs = outPolyOf c' xs X := rfl

theorem outPolyAffine_eq_outPolyOf (c' : Circuit F) (xs : Fin 6 → F)
    (M6 : Matrix (Fin 6) (Fin 6) F) (m₀ : Fin 6 → F) :
    outPolyAffine c' xs M6 m₀ = outPolyOf c' xs (slotPoly M6 m₀) := rfl

theorem polyMap_outPolyOf (c' : Circuit F) (xs : Fin 6 → F) (S : Fin 6 → MvPolynomial (Fin 6) F)
    (p : Fin 6 → F) (k : Fin 6) :
    polyMap (outPolyOf c' xs S) p k = out c' (xs k) (polyMap S p) := by
  have hS : polyMap S p = fun j => eval p (S j) := rfl
  simp only [polyMap, outPolyOf]
  rw [map_out (eval p) (c'.map C) (C (xs k)) S, Circuit.mapC_map_eval', eval_C, hS]

/-- **Chain rule.**  The Jacobian of the normal form with polynomial slots `S` is
`J(S p) · J_S(p)`. -/
theorem polyJacobian_outPolyOf (c' : Circuit F) (xs : Fin 6 → F)
    (S : Fin 6 → MvPolynomial (Fin 6) F) (p : Fin 6 → F) :
    polyJacobian (outPolyOf c' xs S) p = jacobian c' xs (polyMap S p) * polyJacobian S p := by
  funext k i
  have hmapC : (c'.map (algebraMap F (MvPolynomial (Fin 6) F))).map (eval p) = c' := by
    rw [Circuit.map_map, Circuit.map_congr c' (g := id) (fun y => by simp), Circuit.map_id]
  have hS : polyMap S p = fun j => eval p (S j) := rfl
  simp only [polyJacobian_apply, outPolyOf]
  rw [map_C_eq_map_algebraMap, derivation_out (pderiv i) c' (C (xs k)) (by simp) S, map_sum,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_sens (eval p) (c'.map (algebraMap F (MvPolynomial (Fin 6) F))) (C (xs k)) S j,
    hmapC, eval_C, jacobian_apply, polyJacobian_apply, hS]

/-! ## `Q = ν ∘ H` and the reduction identity for the polynomial family -/

/-- `Q = ν ∘ H` as six polynomials in the parameters (quadratic). -/
noncomputable def Qpoly (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) : Fin 6 → MvPolynomial (Fin 6) F :=
  nuSlots (C b) (c.map C) (affineSlotPoly M h₀)

/-- `Q = ν ∘ H` as a map `F⁶ → F⁶`. -/
def Qval (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F)
    (p : Fin 6 → F) : Fin 6 → F :=
  nuSlots b c (affineSlots M h₀ p)

theorem polyMap_Qpoly (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F)
    (p : Fin 6 → F) : polyMap (Qpoly b c M h₀) p = Qval b c M h₀ p := by
  funext j
  simp only [polyMap, Qpoly, Qval]
  rw [map_nuSlots (eval p) (C b) (c.map C) (affineSlotPoly M h₀) j, eval_C,
    GCircuit.mapC_map_eval, eval_affineSlotPoly_fun]

/-- **The reduction identity for the polynomial family:** `F = E' ∘ Q`. -/
theorem outPolyGeneral_eq_outPolyOf (c : GCircuit F) {b : F} (hb : c.β₁ = c.α₁ * b)
    (xs : Fin 6 → F) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) :
    outPolyGeneral c xs M h₀ = outPolyOf c.toNormal xs (Qpoly b c M h₀) := by
  funext k
  have hb' : (c.map (C : F → MvPolynomial (Fin 6) F)).β₁ = (c.map C).α₁ * C b := by
    rw [GCircuit.map_β₁, GCircuit.map_α₁, hb, C_mul]
  simp only [outPolyGeneral, outPolyOf, Qpoly]
  rw [gout_eq (c.map C) hb' (C (xs k)) (affineSlotPoly M h₀), GCircuit.toNormal_map]

/-- **`J_F(p) = J(Q p) · DQ(p)`.** -/
theorem polyJacobian_outPolyGeneral (c : GCircuit F) {b : F} (hb : c.β₁ = c.α₁ * b)
    (xs : Fin 6 → F) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) (p : Fin 6 → F) :
    polyJacobian (outPolyGeneral c xs M h₀) p
      = jacobian c.toNormal xs (Qval b c M h₀ p) * polyJacobian (Qpoly b c M h₀) p := by
  rw [outPolyGeneral_eq_outPolyOf c hb, polyJacobian_outPolyOf, polyMap_Qpoly]

/-! ## Transport: swapping the first gate, and normal-form programs -/

/-- Interchange the rows `u₁`, `v₁` of the slot matrix. -/
def swapRows (M : Matrix (Fin 7) (Fin 6) F) : Matrix (Fin 7) (Fin 6) F :=
  Matrix.of (swapSlots fun i => M i)

theorem affineSlotPoly_swap (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) :
    affineSlotPoly (swapRows M) (swapSlots h₀) = swapSlots (affineSlotPoly M h₀) := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun j => ?_) k) k
  · rfl
  · rfl
  · rfl

/-- Interchanging the factors of the first gate does not change the polynomial family. -/
theorem outPolyGeneral_swap (c : GCircuit F) (xs : Fin 6 → F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) :
    outPolyGeneral c.swap xs (swapRows M) (swapSlots h₀) = outPolyGeneral c xs M h₀ := by
  funext k
  simp only [outPolyGeneral]
  rw [affineSlotPoly_swap, ← GCircuit.swap_map, gout_swap]

/-- A `6 × 6` slot matrix of the normal form as a `7 × 6` one (zero `u₁` row). -/
def liftM (M6 : Matrix (Fin 6) (Fin 6) F) : Matrix (Fin 7) (Fin 6) F :=
  Matrix.of (Matrix.vecCons 0 fun j => M6 j)

/-- A normal-form offset vector as a seven-slot one (zero `u₁` slot). -/
def lifth (m₀ : Fin 6 → F) : Fin 7 → F := Matrix.vecCons 0 m₀

theorem affineSlotPoly_liftM_zero (M6 : Matrix (Fin 6) (Fin 6) F) (m₀ : Fin 6 → F) :
    affineSlotPoly (liftM M6) (lifth m₀) 0 = 0 := by
  simp [affineSlotPoly, liftM, lifth]

theorem tailSlots_affineSlotPoly_liftM (M6 : Matrix (Fin 6) (Fin 6) F) (m₀ : Fin 6 → F) :
    tailSlots (affineSlotPoly (liftM M6) (lifth m₀)) = slotPoly M6 m₀ := by
  funext j
  rfl

/-- A normal-form program with affine slots `M6 p + m₀` is the general program
`(ofNormal c', liftM M6, lifth m₀)`. -/
theorem outPolyGeneral_ofNormal (c' : Circuit F) (xs : Fin 6 → F) (M6 : Matrix (Fin 6) (Fin 6) F)
    (m₀ : Fin 6 → F) :
    outPolyGeneral (GCircuit.ofNormal c') xs (liftM M6) (lifth m₀) = outPolyAffine c' xs M6 m₀ := by
  funext k
  simp only [outPolyGeneral, outPolyAffine]
  rw [GCircuit.ofNormal_map, gout_ofNormal (c'.map C) (C (xs k)) _ (affineSlotPoly_liftM_zero M6 m₀),
    tailSlots_affineSlotPoly_liftM]

end FastPoly.LowerBound.General
