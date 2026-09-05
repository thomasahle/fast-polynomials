import FastPoly.Examples.Char2Degree23Coordinates
import FastPoly.Examples.Char2Degree23RowEight

/-!
# The complete degree-23 key-coordinate inverse

Compose the supplied polynomial key change with the row-eight correction,
which is a self-inverse coordinate shear. Independence is checked gate by
gate with the earlier wires kept named. The inverse is specified in both
directions; no existence argument or combined polynomial expansion is used.

This certifies the key-coordinate change, including its circuit-dependent
row-eight coordinate. The coefficient pivots for the other rows and the
circuit-to-terminal-block bridge are still separate obligations.
-/

namespace FastPoly.Char2Degree23Keys

open Polynomial Char2Decoder Char2Degree23Coordinates Char2Degree23RowEight
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The circuit reads only slots 0 through 22. -/
def raw (a : Vector R) (i : ℕ) : R := a ⟨i % 23, Nat.mod_lt _ (by omega)⟩

omit [CharP R 2] in
/-- The row-eight baseline and its slope do not read slot 19. The proof
reuses one equality per gate, never the recursively expanded circuit. -/
theorem frame_congr (a b : Vector R) (h : ∀ i, i ≠ 19 → a i = b i) :
    baseline (raw a) = baseline (raw b) ∧ slope (raw a) = slope (raw b) := by
  have h0 : raw a 0 = raw b 0 := h 0 (by omega)
  have h1 : raw a 1 = raw b 1 := h 1 (by omega)
  have h2 : raw a 2 = raw b 2 := h 2 (by omega)
  have h3 : raw a 3 = raw b 3 := h 3 (by omega)
  have h4 : raw a 4 = raw b 4 := h 4 (by omega)
  have h5 : raw a 5 = raw b 5 := h 5 (by omega)
  have h6 : raw a 6 = raw b 6 := h 6 (by omega)
  have h7 : raw a 7 = raw b 7 := h 7 (by omega)
  have h8 : raw a 8 = raw b 8 := h 8 (by omega)
  have h9 : raw a 9 = raw b 9 := h 9 (by omega)
  have h10 : raw a 10 = raw b 10 := h 10 (by omega)
  have h11 : raw a 11 = raw b 11 := h 11 (by omega)
  have h12 : raw a 12 = raw b 12 := h 12 (by omega)
  have h13 : raw a 13 = raw b 13 := h 13 (by omega)
  have h14 : raw a 14 = raw b 14 := h 14 (by omega)
  have h15 : raw a 15 = raw b 15 := h 15 (by omega)
  have h16 : raw a 16 = raw b 16 := h 16 (by omega)
  have h17 : raw a 17 = raw b 17 := h 17 (by omega)
  have h18 : raw a 18 = raw b 18 := h 18 (by omega)
  have h20 : raw a 20 = raw b 20 := h 20 (by omega)
  have h21 : raw a 21 = raw b 21 := h 21 (by omega)
  have hz : z (raw a) = z (raw b) := by rw [z, h0, h1]; rfl
  have ht : t (raw a) = t (raw b) := by rw [t, h2, hz, h3]; rfl
  have hu : u (raw a) = u (raw b) := by rw [u, hz, ht, h4, h5]; rfl
  have hv : v (raw a) = v (raw b) := by rw [v, h6, hz, h7]; rfl
  have hw : w (raw a) = w (raw b) := by rw [w, hz, h8, hv, h9]; rfl
  have hs : s (raw a) = s (raw b) := by rw [s, hz, h10, hv, h11]; rfl
  have hr : r (raw a) = r (raw b) := by rw [r, ht, h12, hu, h13]; rfl
  have hg : g (raw a) = g (raw b) := by rw [g, hz, ht, h14, hu, h15]; rfl
  have hl : ell (raw a) = ell (raw b) := by rw [ell, h16, hz, hv, h17]; rfl
  have hcl : crownLeft (raw a) = crownLeft (raw b) := by rw [crownLeft, hz, h18]; rfl
  have hcr : crownRight (raw a) = crownRight (raw b) := by
    rw [crownRight, hz, hw, hs, hg, hl]
    rfl
  have hf : lastFactor (raw a) = lastFactor (raw b) := by rw [lastFactor, hz, h20]; rfl
  have hh : head (raw a) = head (raw b) := by rw [head, hv, hw, hs, hr, hg]; rfl
  constructor
  · rw [baseline, hh, hf, hu, hcl, hcr, h21]
    rfl
  · rw [slope, hf, hcl]
    rfl

noncomputable def rowEightTail (a : Vector R) : R := (baseline (raw a)).coeff 8

omit [CharP R 2] in
theorem rowEightTail_independent : Independent (19 : Fin 23) (rowEightTail (R := R)) := by
  intro a c
  exact congrArg (fun P : R[X] => P.coeff 8)
    (frame_congr (Function.update a 19 c) a (fun i hi => Function.update_of_ne hi ..)).1

/-- The exact `a19 = q14 + H(a)` correction, with the same explicit inverse. -/
noncomputable def rowEightShear : Vector R ≃ Vector R :=
  coordinateShear 19 rowEightTail rowEightTail_independent

/-- All 23 supplied key coordinates, now including the output's row-eight
coordinate. The two component inverses are composed in reverse order. -/
noncomputable def keyEquiv : Vector R ≃ Vector R := coreEquiv.trans rowEightShear

theorem keyEquiv_apply (q : Vector R) :
    keyEquiv q = Function.update (keysCore q) 19 (q 14 + rowEightTail (keysCore q)) := rfl

theorem keyEquiv_symm_apply (a : Vector R) :
    keyEquiv.symm a = coordinates (Function.update a 19 (a 19 + rowEightTail a)) := rfl

theorem decode_encode (q : Vector R) : keyEquiv.symm (keyEquiv q) = q :=
  keyEquiv.symm_apply_apply q

theorem encode_decode (a : Vector R) : keyEquiv (keyEquiv.symm a) = a :=
  keyEquiv.apply_symm_apply a

/-- No inverse formula is hidden behind an existence proof. -/
theorem explicit_decode_encode (q : Vector R) :
    coordinates (Function.update (keyEquiv q) 19
      (keyEquiv q 19 + rowEightTail (keyEquiv q))) = q := decode_encode q

theorem keyEquiv_other (q : Vector R) (i : Fin 23) (hi : i ≠ 19) :
    keyEquiv q i = keysCore q i := by
  rw [keyEquiv_apply]
  exact Function.update_of_ne hi ..

variable [Nontrivial R]

/-- The inverse's coordinate 14 is the actual circuit coefficient, not just
an abstract auxiliary slot. This connects the polynomial shear to the circuit. -/
theorem inverse_fourteen (a : Vector R) :
    keyEquiv.symm a 14 = (output (raw a)).coeff 8 := by
  change Function.update a 19 (a 19 + rowEightTail a) 19 =
    (finish (raw a) (a 19) (a 22)).coeff 8
  rw [Function.update_self, coeff_eight]
  exact add_comm _ _

theorem output_fourteen (q : Vector R) : (output (raw (keyEquiv q))).coeff 8 = q 14 := by
  rw [← inverse_fourteen, decode_encode]

end FastPoly.Char2Degree23Keys
