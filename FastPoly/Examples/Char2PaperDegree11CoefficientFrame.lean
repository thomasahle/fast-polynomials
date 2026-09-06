import FastPoly.Examples.Char2PaperDegree11Coordinates
import FastPoly.Examples.Char2PaperDegree11Top

/-! The actual circuit coefficient interfaces consumed by the displayed inverse.
The high six rows, the single a6 pivot, and the low four-row butterfly are
connected separately, with every baseline kept as a named circuit evaluation. -/
namespace FastPoly.Char2PaperDegree11CoefficientFrame

open Polynomial Char2PaperDegree11Coordinates
set_option maxHeartbeats 20000
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

noncomputable def output (p : Coordinates F) : F[X] := Char2PaperDegree11.output (keys p)
noncomputable def coefficients (p : Coordinates F) (i : Fin 11) : F := (output p).coeff i.val
noncomputable def base (p : Char2PaperDegree11HeadInverse.Head F) (a6 : F) : F[X] :=
  Char2PaperDegree11.output (baseKeys p a6)

def headRows (c : Fin 11 → F) : Char2PaperDegree11HeadInverse.Rows F :=
  ⟨c 10, c 9, c 8, c 7, c 6, c 5⟩

noncomputable def lowRows (p : Char2PaperDegree11HeadInverse.Head F) (a6 : F)
    (c : Fin 11 → F) : Char2PaperDegree11TailInverse.Rows F :=
  ⟨c 3 + (base p a6).coeff 3, c 2 + (base p a6).coeff 2,
    c 1 + (base p a6).coeff 1, c 0 + (base p a6).coeff 0⟩

theorem base_eq_B (p : Coordinates F) : base p.head p.a6 = Char2PaperDegree11.B (keys p) := by
  unfold base Char2PaperDegree11.B
  rw [baselineKeys_eq]
theorem base_eq_B0 (p : Coordinates F) : base p.head 0 = Char2PaperDegree11.B0 (keys p) := by
  unfold base Char2PaperDegree11.B0
  rw [baseline0Keys_eq]

theorem head_encode (p : Coordinates F) :
    headRows (coefficients p) = Char2PaperDegree11HeadInverse.encode p.head := by
  apply Char2PaperDegree11HeadInverse.Rows.ext
  · exact Char2PaperDegree11.output_row10 (keys p)
  · exact Char2PaperDegree11.output_row9 (keys p)
  · exact Char2PaperDegree11.output_row8 (keys p)
  · change (Char2PaperDegree11.output (keys p)).coeff 7 = _
    rw [Char2PaperDegree11.output_row7, sumKeys_keys, h_keys]
    rfl
  · change (Char2PaperDegree11.output (keys p)).coeff 6 = _
    rw [Char2PaperDegree11.output_row6, sumKeys_keys, h_keys]
    rfl
  · change (Char2PaperDegree11.output (keys p)).coeff 5 = _
    rw [Char2PaperDegree11.output_row5, sumKeys_keys, h_keys]
    rfl

theorem a6_encode (p : Coordinates F) :
    coefficients p 4 + (base p.head 0).coeff 4 = p.a6 := by
  rw [base_eq_B0]
  exact Char2PaperDegree11.baseline_pivot (keys p)

theorem residual_row (p : Coordinates F) (i : Fin 11) :
    coefficients p i + (base p.head p.a6).coeff i.val =
      (Char2PaperDegree11.residual (keys p)).coeff i.val := by
  rw [base_eq_B]
  change (Char2PaperDegree11.output (keys p)).coeff i.val +
    (Char2PaperDegree11.B (keys p)).coeff i.val = _
  rw [← coeff_add, Char2PaperDegree11.output_add_B]

theorem kappa_keys (p : Coordinates F) :
    Char2PaperDegree11.kappa (keys p) = Char2PaperDegree11TailInverse.kappa (lowCtx p) p.low := by
  rw [Char2PaperDegree11.kappa, h_keys]
  rfl

theorem low_encode (p : Coordinates F) : lowRows p.head p.a6 (coefficients p) =
    Char2PaperDegree11TailInverse.encode (lowCtx p) p.low := by
  have h3 : coefficients p 3 + (base p.head p.a6).coeff 3 =
      (Char2PaperDegree11.residual (keys p)).coeff 3 := residual_row p 3
  have h2 : coefficients p 2 + (base p.head p.a6).coeff 2 =
      (Char2PaperDegree11.residual (keys p)).coeff 2 := residual_row p 2
  have h1 : coefficients p 1 + (base p.head p.a6).coeff 1 =
      (Char2PaperDegree11.residual (keys p)).coeff 1 := residual_row p 1
  have h0 : coefficients p 0 + (base p.head p.a6).coeff 0 =
      (Char2PaperDegree11.residual (keys p)).coeff 0 := residual_row p 0
  rw [Char2PaperDegree11.residual_three, kappa_keys] at h3
  rw [Char2PaperDegree11.residual_two, kappa_keys] at h2
  rw [Char2PaperDegree11.residual_one, kappa_keys] at h1
  rw [Char2PaperDegree11.residual_zero, kappa_keys] at h0
  cases hl : lowRows p.head p.a6 (coefficients p)
  cases hr : Char2PaperDegree11TailInverse.encode (lowCtx p) p.low
  have he3 : (lowRows p.head p.a6 (coefficients p)).d3 =
      (Char2PaperDegree11TailInverse.encode (lowCtx p) p.low).d3 := h3
  have he2 : (lowRows p.head p.a6 (coefficients p)).d2 =
      (Char2PaperDegree11TailInverse.encode (lowCtx p) p.low).d2 := h2
  have he1 : (lowRows p.head p.a6 (coefficients p)).d1 =
      (Char2PaperDegree11TailInverse.encode (lowCtx p) p.low).d1 := h1
  have he0 : (lowRows p.head p.a6 (coefficients p)).d0 =
      (Char2PaperDegree11TailInverse.encode (lowCtx p) p.low).d0 := h0
  simp only [hl, hr] at he3 he2 he1 he0
  cases he3
  cases he2
  cases he1
  cases he0
  rfl

end FastPoly.Char2PaperDegree11CoefficientFrame
