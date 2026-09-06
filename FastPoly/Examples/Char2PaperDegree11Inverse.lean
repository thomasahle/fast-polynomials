import FastPoly.Examples.Char2PaperDegree11CoefficientFrame

/-! The displayed inverse of the paper's degree-eleven butterfly circuit.
Read the six high rows using two inverse-Frobenius operations, recover a6
from its named baseline, then apply the four explicit butterfly formulas.
Both compositions are checked against the actual circuit coefficient map. -/
namespace FastPoly.Char2PaperDegree11Inverse

open Char2PaperDegree11Coordinates Char2PaperDegree11CoefficientFrame
set_option maxHeartbeats 20000
variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

noncomputable def head (c : Fin 11 → F) : Char2PaperDegree11HeadInverse.Head F :=
  Char2PaperDegree11HeadInverse.decode (headRows c)
noncomputable def pivot (c : Fin 11 → F) : F := c 4 + (base (head c) 0).coeff 4
noncomputable def context (c : Fin 11 → F) : Char2PaperDegree11TailInverse.Context F :=
  ⟨(head c).a0, (head c).a3, (head c).a4, pivot c, (head c).h⟩
noncomputable def low (c : Fin 11 → F) : Char2PaperDegree11TailInverse.Keys F :=
  Char2PaperDegree11TailInverse.decode (context c) (lowRows (head c) (pivot c) c)
noncomputable def decode (c : Fin 11 → F) : Coordinates F := ⟨head c, pivot c, low c⟩

theorem head_encode (p : Coordinates F) : head (coefficients p) = p.head := by
  rw [head, Char2PaperDegree11CoefficientFrame.head_encode,
    Char2PaperDegree11HeadInverse.decode_encode]
theorem pivot_encode (p : Coordinates F) : pivot (coefficients p) = p.a6 := by
  rw [pivot, head_encode, a6_encode]
theorem context_encode (p : Coordinates F) : context (coefficients p) = lowCtx p := by
  rw [context, head_encode, pivot_encode]
  rfl
theorem low_encode (p : Coordinates F) : low (coefficients p) = p.low := by
  rw [low, head_encode, pivot_encode, context_encode,
    Char2PaperDegree11CoefficientFrame.low_encode, Char2PaperDegree11TailInverse.decode_encode]

theorem decode_encode (p : Coordinates F) : decode (coefficients p) = p := by
  apply Coordinates.ext
  · exact head_encode p
  · exact pivot_encode p
  · exact low_encode p

theorem high_decode (c : Fin 11 → F) : headRows (coefficients (decode c)) = headRows c := by
  rw [Char2PaperDegree11CoefficientFrame.head_encode]
  exact Char2PaperDegree11HeadInverse.encode_decode (headRows c)

theorem four_decode (c : Fin 11 → F) : coefficients (decode c) 4 = c 4 := by
  have he := a6_encode (decode c)
  change coefficients (decode c) 4 + (base (head c) 0).coeff 4 =
    c 4 + (base (head c) 0).coeff 4 at he
  exact add_right_cancel he

theorem low_decode (c : Fin 11 → F) :
    lowRows (head c) (pivot c) (coefficients (decode c)) = lowRows (head c) (pivot c) c := by
  have he := Char2PaperDegree11CoefficientFrame.low_encode (decode c)
  change lowRows (head c) (pivot c) (coefficients (decode c)) =
    Char2PaperDegree11TailInverse.encode (context c)
      (Char2PaperDegree11TailInverse.decode (context c) (lowRows (head c) (pivot c) c)) at he
  rw [Char2PaperDegree11TailInverse.encode_decode] at he
  exact he

theorem encode_decode (c : Fin 11 → F) : coefficients (decode c) = c := by
  have hh := high_decode c
  have hl := low_decode c
  funext i
  fin_cases i
  · exact add_right_cancel (congrArg Char2PaperDegree11TailInverse.Rows.d0 hl)
  · exact add_right_cancel (congrArg Char2PaperDegree11TailInverse.Rows.d1 hl)
  · exact add_right_cancel (congrArg Char2PaperDegree11TailInverse.Rows.d2 hl)
  · exact add_right_cancel (congrArg Char2PaperDegree11TailInverse.Rows.d3 hl)
  · exact four_decode c
  · exact congrArg Char2PaperDegree11HeadInverse.Rows.c5 hh
  · exact congrArg Char2PaperDegree11HeadInverse.Rows.c6 hh
  · exact congrArg Char2PaperDegree11HeadInverse.Rows.c7 hh
  · exact congrArg Char2PaperDegree11HeadInverse.Rows.c8 hh
  · exact congrArg Char2PaperDegree11HeadInverse.Rows.c9 hh
  · exact congrArg Char2PaperDegree11HeadInverse.Rows.c10 hh

noncomputable def coordinateEquiv : Coordinates F ≃ (Fin 11 → F) where
  toFun := coefficients
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

/-- Original raw offsets, with the explicit inverse key change applied last. -/
noncomputable def coefficientEquiv : (Fin 11 → F) ≃ (Fin 11 → F) :=
  rawEquiv.trans coordinateEquiv

theorem coefficientEquiv_apply (a : Fin 11 → F) (i : Fin 11) :
    coefficientEquiv a i = (Char2PaperDegree11.output (keys (rawInput a))).coeff i.val := rfl

theorem coefficientEquiv_symm_apply (c : Fin 11 → F) :
    coefficientEquiv.symm c = rawKeys (decode c) := rfl

theorem raw_decode_encode (a : Fin 11 → F) : rawKeys (decode (coefficientEquiv a)) = a :=
  coefficientEquiv.symm_apply_apply a
theorem raw_encode_decode (c : Fin 11 → F) : coefficientEquiv (rawKeys (decode c)) = c :=
  coefficientEquiv.apply_symm_apply c

end FastPoly.Char2PaperDegree11Inverse
