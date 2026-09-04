// g1_emit_bases.frag.js — chain emitters I (ChainBuilder side) for the char-0
// lane port of tools/poly_schedule.py.
// Fragment: function declarations only. No imports, no exports, no top-level
// side effects. Runtime (Field, AffineForm, ChainBuilder, _affine_scale_int,
// PEELED_Q, ...) and cross-group emitters (_paper_Q_2lp1k_minus_1_with_powers)
// are supplied by other fragments at assembly time.

// py: tools/poly_schedule.py:424
// One-multiplication helper: (A+B)(A-B).
function _paper_square_diff(builder, A, B, name = null) {
  const field = builder.field;
  return builder.mul(A.add(B, field), A.sub(B, field), name);
}

// py: tools/poly_schedule.py:431
// Base known power:
//     H_2[α0,α1](x) = (x + α1)x + α0
function _paper_H2(builder, alpha0, alpha1) {
  const field = builder.field;
  const x = builder.x;
  const t = builder.withLabel('H_2 base', () =>
    builder.mul(x.add_const(field.coerce(alpha1), field), x));
  return t.add_const(field.coerce(alpha0), field);
}

// py: tools/poly_schedule.py:443
// Q_3[α0,α1,α2](x, H2) = (x + α2)(H2 + α1) + α0
//
// This uses 1 multiplication, assuming H2 is already available.
function _paper_q3(builder, alpha0, alpha1, alpha2, H2) {
  const field = builder.field;
  const x = builder.x;
  const a0 = field.coerce(alpha0);
  const a1 = field.coerce(alpha1);
  const a2 = field.coerce(alpha2);
  const t = builder.withLabel('Q_3 known-power block', () =>
    builder.mul(x.add_const(a2, field), H2.add_const(a1, field)));
  return t.add_const(a0, field);
}

// py: tools/poly_schedule.py:459
// Paper base construction for degree 5 (3 multiplications):
//
//   P5[α0..α4](x) = (x + α2) * ( (x^2 + α4) * (x^2 + x + α3) + α1 ) + α0
//
// This is the degree-5 base used by the paper family `P_n[α]` and matches the
// `n==5` chain in `_compile_paper_monic` (when the polynomial coefficients are
// interpreted as α-parameters).
function _paper_P5(builder, alpha) {
  const field = builder.field;
  if (alpha.length !== 5) {
    throw new Error(`P5 needs 5 params, got ${alpha.length}`);
  }
  const a0 = field.coerce(alpha[0]);
  const a1 = field.coerce(alpha[1]);
  const a2 = field.coerce(alpha[2]);
  const a3 = field.coerce(alpha[3]);
  const a4 = field.coerce(alpha[4]);

  const x = builder.x;
  builder.pushLabel('P_5 base');
  const x2 = builder.mul(x, x);
  const z = builder.mul(x2.add_const(a4, field), x2.add(x, field).add_const(a3, field));
  const w = builder.mul(x.add_const(a2, field), z.add_const(a1, field));
  builder.popLabel();
  return w.add_const(a0, field);
}

// py: tools/poly_schedule.py:482
// Septic base construction (degree 7, 4 multiplications).
//
// This matches the "paper-style" chain used by `_compile_paper_monic` for n=7
// (where it is shown to be decodable in characteristic != 2).
//
//     y = x * (x + α6)
//     z = (α5 + x + y) * (α4 + x)
//     w = (α3 + z) * x
//     v = (α2 + x + z) * (α1 + w)
//     P7 = α0 + y + w + v
function _paper_P7(builder, alpha) {
  if (alpha.length !== 7) {
    throw new Error(`P7 needs 7 params, got ${alpha.length}`);
  }

  const field = builder.field;
  alpha = alpha.map((a) => field.coerce(a));
  const x = builder.x;

  builder.pushLabel('P_7 base');
  const y = builder.mul(x, x.add_const(alpha[6], field));
  const z = builder.mul(x.add(y, field).add_const(alpha[5], field), x.add_const(alpha[4], field));
  const w = builder.mul(z.add_const(alpha[3], field), x);
  const v = builder.mul(x.add(z, field).add_const(alpha[2], field), w.add_const(alpha[1], field));
  builder.popLabel();
  return y.add(w, field).add(v, field).add_const(alpha[0], field);
}

// py: tools/poly_schedule.py:580
// Construct the pair (T^{(1)}_{k,2^l}, T^{(2)}_{k,2^l}) from sections/constructions.tex.
//
// This is the core subroutine used for the 4k+1 family; it also produces (as a
// byproduct) higher known powers H_{2^{l+1}} / \tilde H_{2^{l+1}} in the
// recursive cases.
//
// Args:
//     k: positive integer
//     l: >= 1 (so 2^l >= 2)
//     alpha: parameter list of length (k-1)*2^l
//     Hs: known powers list with Hs[i] = H_{2^i}, Hs[0]=x, len(Hs) >= l+1
//     tilde_H_2l: the \tilde H_{2^l} input for the second component
//
// Returns:
//     [T1, T2, Hs_out, tilde_H_out] where:
//       - T1, T2 are the constructed polynomials
//       - Hs_out extends Hs with any newly constructed H_{2^i}
//       - tilde_H_out is the corresponding \tilde H_{2^{l'}} at the output scale
function _paper_T(builder, k, l, alpha, Hs, tilde_H_2l) {
  // JS-only provenance wrapper: every gate of this T level (and, via nested
  // pushes, its sub-gadgets) is attributed to T_{k,2^l}.
  return builder.withLabel(`T-recursion T_{${k},${1 << l}} (l=${l})`, () =>
    _paper_T_impl(builder, k, l, alpha, Hs, tilde_H_2l));
}

function _paper_T_impl(builder, k, l, alpha, Hs, tilde_H_2l) {
  const field = builder.field;
  const two = field.add(field.one(), field.one());
  const is_char2 = field.is_zero(two);
  if (k < 1) {
    throw new Error('T requires k >= 1');
  }
  if (l < 1) {
    throw new Error('T requires l >= 1');
  }
  if (Hs.length <= l) {
    throw new Error(`T(k=${k},l=${l}) requires Hs up to index ${l} (H_{2^${l}})`);
  }

  const block = 1 << l;
  const need = (k - 1) * block;
  if (alpha.length !== need) {
    throw new Error(`T(k=${k},l=${l}) needs ${k - 1}*2^${l}=${need} alpha params, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  if (k === 1) {
    // Base: T^{(1)} = H_{2^l}, T^{(2)} = \tilde H_{2^l}.
    return [Hs[l], tilde_H_2l, Hs, tilde_H_2l];
  }

  // Even k
  if (k % 2 === 0) {
    // Split: prefix params for recursion, tail block for constructing new powers.
    const rec_len = (Math.floor(k / 2) - 1) * (2 * block);
    const tail = alpha.slice(rec_len);
    const rec_params = alpha.slice(0, rec_len);
    if (tail.length !== block) {
      throw new Error('internal error: T even tail length mismatch');
    }

    // Special case: l = 1 (paper Algorithm `alg:constr-Tk2l-base`, even-k branch).
    if (l === 1) {
      // H4 = (H2 + (x + a1))(H2 - (x + a1)) + a0
      // tilde_H4 = H4 + (tilde_H2-H2)
      const a0 = tail[0];
      const a1 = tail[1];
      const x = builder.x;
      // In all paper call-sites, tilde_H2 is a scalar shift of H2.
      const delta = tilde_H_2l.sub(Hs[1], field);
      const can_fast_shift = delta.terms.size === 0;
      let delta_int = null;
      if (can_fast_shift) {
        try {
          // works for GF(p) elements represented as ints
          // (Python's int(delta.const); over Q, int(Fraction) truncates toward zero.)
          if (typeof delta.const === 'bigint') {
            delta_int = Number(delta.const);
          } else {
            delta_int = Number(delta.const.n / delta.const.d);
          }
          if (!Number.isSafeInteger(delta_int)) throw new Error('not an int');
        } catch (e) {
          delta_int = null;
        }
      }
      let H4;
      let tilde_H4;
      if (is_char2) {
        // Characteristic-2 replacement: H4 = H2 * (H2 + (x + a1)) + a0.
        //
        // This avoids the `(A+B)(A-B)` square-difference gadget, which collapses
        // in char 2, and is decodable given H2 by polynomial division.
        H4 = builder.mul(Hs[1], Hs[1].add(x.add_const(a1, field), field)).add_const(a0, field);
        if (delta_int !== null) {
          // In char 2: (H2+δ)(H2+δ+x+a1) = H2(H2+x+a1) + δ(x+a1) + δ^2.
          const delta_sq = field.mul(delta.const, delta.const);
          const delta_x_plus = _affine_scale_int(field, x.add_const(a1, field), delta_int);
          tilde_H4 = H4.add(delta_x_plus, field).add_const(delta_sq, field);
        } else {
          tilde_H4 = builder
            .mul(tilde_H_2l, tilde_H_2l.add(x.add_const(a1, field), field))
            .add_const(a0, field);
        }
      } else {
        const t_plus = Hs[1].add(x.add_const(a1, field), field);
        const t_minus = Hs[1].sub(x.add_const(a1, field), field);
        H4 = builder.withLabel('H_4 known power', () => builder.mul(t_plus, t_minus))
          .add_const(a0, field);
        if (!can_fast_shift) {
          throw new Error('The shared l=1 base requires tilde_H2-H2 to be scalar');
        }
        // This is the exact-count repair: the shifted quartic is a
        // scalar shift of the first quartic, so no second product is
        // needed.
        tilde_H4 = H4.add(delta, field);
      }
      const Hs_next = Hs.slice();
      if (Hs_next.length <= 2) {
        while (Hs_next.length < 3) Hs_next.push(AffineForm.const_only(field.zero()));
      }
      Hs_next[2] = H4;
      return _paper_T(builder, Math.floor(k / 2), l + 1, rec_params, Hs_next, tilde_H4);
    }

    // Main even case: l >= 2.
    const half = 1 << (l - 1);
    const q_hi = _paper_Q_known_powers(builder, l - 1, tail.slice(half + 1), Hs.slice(0, l - 1));
    const q_lo = _paper_Q_known_powers(builder, l - 1, tail.slice(1, half), Hs.slice(0, l - 1));

    const S1_1 = Hs[l - 1].add(q_hi, field);
    const S1_2 = q_lo;
    let H_next;
    if (is_char2) {
      // Char-2 replacement: H_next = H * (H + S1_1) + S1_2.
      H_next = builder.mul(Hs[l], Hs[l].add(S1_1, field)).add(S1_2, field);
    } else {
      H_next = builder.withLabel(`H_${1 << (l + 1)} known power`, () =>
        builder.mul(Hs[l].add(S1_1, field), Hs[l].sub(S1_1, field))).add(S1_2, field);
    }

    const S2_1 = Hs[l - 1].add_const(tail[half], field);
    const S2_2 = tail[0];
    let tilde_next;
    if (is_char2) {
      tilde_next = builder.mul(tilde_H_2l, tilde_H_2l.add(S2_1, field)).add_const(S2_2, field);
    } else {
      tilde_next = builder.withLabel(`H̃_${1 << (l + 1)} shifted power`, () => builder
        .mul(tilde_H_2l.add(S2_1, field), tilde_H_2l.sub(S2_1, field)))
        .add_const(S2_2, field);
    }

    const Hs_next = Hs.slice();
    if (Hs_next.length <= l + 1) {
      while (Hs_next.length < l + 2) Hs_next.push(AffineForm.const_only(field.zero()));
    }
    Hs_next[l + 1] = H_next;
    return _paper_T(builder, Math.floor(k / 2), l + 1, rec_params, Hs_next, tilde_next);
  }

  // Odd k
  const m = Math.floor((k - 1) / 2);
  if (l === 2) {
    // Special case: k odd, l = 2 (paper Algorithm `alg:constr-Tk2l-base`, odd-k branch).
    //
    // Layout: head block (size 4) + mid (for recursion) + tail block (size 4).
    if (block !== 4) {
      throw new Error('internal error: expected block=4 for l=2');
    }

    const head = alpha.slice(0, 4);
    const tail = alpha.slice(-4);
    const mid = alpha.slice(4, -4);

    // Tail parameters:
    //   tail[0]=α_{4k-8} : shift from H8 to tilde_H8
    //   tail[1]=α_{4k-7} : S1_3
    //   tail[2]=α_{4k-6} : S1_2 shift in (x+α)
    //   tail[3]=α_{4k-5} : shift in S1_1 = H2 + (x+α)
    const next_shift = tail[0];
    const s1_3 = tail[1];
    const s1_2_shift = tail[2];
    const s1_1_shift = tail[3];

    // First-branch (unshifted) auxiliaries:
    //   S1_1 = H2 + (x + s1_1_shift)
    //   S1_2 = x + s1_2_shift
    //   S1_3 = s1_3
    const S1_1 = Hs[1].add(builder.x.add_const(s1_1_shift, field), field);
    const core = Hs[2].add(S1_1, field);
    const S1_2 = builder.x.add_const(s1_2_shift, field);
    const H8 = builder.withLabel('H_8 known power', () =>
      builder.mul(core.add(S1_2, field), core.sub(S1_2, field))).add_const(s1_3, field);

    const Hs_next = Hs.slice();
    if (Hs_next.length <= 3) {
      while (Hs_next.length < 4) Hs_next.push(AffineForm.const_only(field.zero()));
    }
    Hs_next[3] = H8;

    // The input quartics differ by a scalar rho.  Put S2_1=S1_1-rho,
    // S2_2=S1_2 and S2_3=S1_3+next_shift.  The square-difference cores
    // are then identical, so tilde_H8=H8+next_shift shares the H8 gate.
    const rho = tilde_H_2l.sub(Hs[2], field);
    if (rho.terms.size) {
      throw new Error('The shared odd l=2 base requires tilde_H4-H4 to be scalar');
    }
    const S2_1 = S1_1.sub(rho, field);
    const tilde_H8 = H8.add_const(next_shift, field);

    const [T1_rec, T2_rec, Hs_out, tilde_out] = _paper_T(builder, m, l + 1, mid, Hs_next, tilde_H8);

    // Q3(head[1..3]) is the additive term on the first branch.
    const q3 = _paper_Q_known_powers(builder, 2, head.slice(1), Hs.slice(0, 2));

    // (H4 - (k-1)S1_1) * T1_rec + Q3
    const factor1 = Hs[2].sub(_affine_scale_int(field, S1_1, k - 1), field);
    const T1 = builder.mul(factor1, T1_rec).add(q3, field);

    // (tilde_H4 - (k-1)S2_1) * T2_rec + α0
    const factor2 = tilde_H_2l.sub(_affine_scale_int(field, S2_1, k - 1), field);
    const T2 = builder.mul(factor2, T2_rec).add_const(head[0], field);
    return [T1, T2, Hs_out, tilde_out];
  }

  if (l < 3) {
    throw new Error('T odd case requires l >= 3 (or special l=2)');
  }

  // Main odd case: l >= 3.
  // Layout: head block (size 2^l) + mid (for recursion) + tail block (size 2^l).
  const head = alpha.slice(0, block);
  const tail = alpha.slice(-block);
  const mid = alpha.slice(block, -block);

  const half = 1 << (l - 1);
  const quarter = 1 << (l - 2);

  // H_{2^{l+1}} = ((H_{2^l} + S1_1) + S1_2) * ((H_{2^l} + S1_1) - S1_2) + S1_3
  const q_hi = _paper_Q_known_powers(builder, l - 1, tail.slice(half + 1), Hs.slice(0, l - 1));
  const S1_1 = Hs[l - 1].add(q_hi, field);

  const q_mid = _paper_Q_known_powers(builder, l - 2, tail.slice(quarter + 1, half), Hs.slice(0, l - 2));
  const S1_2 = Hs[l - 2].add(q_mid, field);

  const S1_3 = _paper_Q_known_powers(builder, l - 2, tail.slice(1, quarter), Hs.slice(0, l - 2));

  const base = Hs[l].add(S1_1, field);
  const H_next = builder.withLabel(`H_${1 << (l + 1)} known power`, () =>
    builder.mul(base.add(S1_2, field), base.sub(S1_2, field))).add(S1_3, field);

  const S2_1 = Hs[l - 1].add_const(tail[half], field);
  const S2_2 = Hs[l - 2].add_const(tail[quarter], field);
  const S2_3 = tail[0];
  const base2 = tilde_H_2l.add(S2_1, field);
  const tilde_next = builder.withLabel(`H̃_${1 << (l + 1)} shifted power`, () =>
    builder.mul(base2.add(S2_2, field), base2.sub(S2_2, field))).add_const(S2_3, field);

  const Hs_next = Hs.slice();
  if (Hs_next.length <= l + 1) {
    while (Hs_next.length < l + 2) Hs_next.push(AffineForm.const_only(field.zero()));
  }
  Hs_next[l + 1] = H_next;

  const [T1_rec, T2_rec, Hs_out, tilde_out] = _paper_T(builder, m, l + 1, mid, Hs_next, tilde_next);

  const q_low = _paper_Q_known_powers(builder, l, head.slice(1), Hs.slice(0, l));
  const factor1 = Hs[l].sub(_affine_scale_int(field, S1_1, k - 1), field);
  const T1 = builder.mul(factor1, T1_rec).add(q_low, field);

  const factor2 = tilde_H_2l.sub(_affine_scale_int(field, S2_1, k - 1), field);
  const T2 = builder.mul(factor2, T2_rec).add_const(head[0], field);
  return [T1, T2, Hs_out, tilde_out];
}

// py: tools/poly_schedule.py:1782
// 2-adic valuation v2(n) for n>0: largest e such that 2^e | n.
function _v2_positive(n) {
  if (n <= 0) {
    throw new Error('v2_positive requires n > 0');
  }
  let e = 0;
  while ((n & 1) === 0) {
    n >>= 1;
    e += 1;
  }
  return e;
}

// py: tools/poly_schedule.py:1794
// Peeled monic family for any odd degree, given the tower up to
// `H_{2^{floor(log2 deg)}}`:
//
//     QO(d) = (H_h + U) * W + B,   h = 2^{floor(log2 d)},
//     U = QO(2h-d) inside the factor, W = B = QO(d-h),
//
// with Mersenne degrees delegating to the (peeled) known-powers gadget.
// Exactly (d-1)/2 multiplications; parameter layout [U..., W..., B...].
function _paper_QO(builder, deg, alpha, Hs) {
  const field = builder.field;
  if (deg < 1 || deg % 2 === 0) {
    throw new Error('QO requires odd deg >= 1');
  }
  if (alpha.length !== deg) {
    throw new Error(`QO(deg=${deg}) needs ${deg} params, got ${alpha.length}`);
  }
  if (deg === 1) {
    return builder.x.add_const(field.coerce(alpha[0]), field);
  }
  const t = 32 - Math.clz32(deg); // deg.bit_length() for positive Number
  if (deg === (1 << t) - 1) {
    return _paper_Q_known_powers(builder, t, alpha, Hs.slice(0, t));
  }
  const h = 1 << (t - 1);
  const w = deg - h;
  const ud = 2 * h - deg;
  const U = _paper_QO(builder, ud, alpha.slice(0, ud), Hs);
  const W = _paper_QO(builder, w, alpha.slice(ud, ud + w), Hs);
  const B = _paper_QO(builder, w, alpha.slice(ud + w), Hs);
  return builder.mark_value(
    builder.withLabel(`Q_${deg} peeled block`, () => builder.mul(Hs[t - 1].add(U, field), W))
      .add(B, field));
}

// py: tools/poly_schedule.py:1843
// Dispatch helper: for any odd `deg >= 1`, write
//     deg = 2^l * (2k+1) - 1
// where `l = v2(deg+1) >= 1`, and call the known-powers construction
//     Q_{2^{l+1}k + (2^l - 1)} = Q_deg.
//
// Returns:
//     [Q_deg, Hs_out, tilde_out]
function _paper_Q_for_odd_degree_with_powers(builder, deg, alpha, Hs) {
  if (deg < 1 || deg % 2 === 0) {
    throw new Error('Q_for_odd_degree requires odd deg >= 1');
  }
  const l = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l; // == 2k+1
  if (odd % 2 === 0) {
    throw new Error('internal error: expected odd factor (deg+1)/2^l to be odd');
  }
  const k = Math.floor((odd - 1) / 2);
  if (PEELED_Q && deg >= 3 && Hs.length >= 32 - Math.clz32(deg)) {
    return [_paper_QO(builder, deg, alpha, Hs), Hs.slice(), Hs[0]];
  }
  return _paper_Q_2lp1k_minus_1_with_powers(builder, k, l, alpha, Hs);
}

// py: tools/poly_schedule.py:1871
// Fill construction A_{2^l} from sections/constructions.tex (Algorithm `alg:constr-fill`).
//
// Inputs:
//   - l >= 1
//   - alpha: [α0..α_{2^{l+1}-3}] (length 2^{l+1}-2)
//   - beta:  [β0..β_{2^l}]      (length 2^l+1)
//   - S1_2l, S2_2l: the compatible pair components at scale 2^l
//   - Hs: list of known powers, with Hs[i] = H_{2^i} and Hs[0] = x
//         (so len(Hs) >= l+1)
//
// Output:
//   - A_{2^l} = (x + β0) A^{(1)}_{2^l} + A^{(2)}_{2^l}
function _paper_A_fill(builder, l, alpha, beta, S1_2l, S2_2l, Hs) {
  const field = builder.field;
  if (l < 0) {
    throw new Error('A_fill requires l >= 0');
  }
  if (l > 0 && Hs.length <= l) {
    throw new Error(`A_fill requires Hs up to index ${l} (H_{2^${l}})`);
  }

  const need_alpha = (1 << (l + 1)) - 2;
  const need_beta = (1 << l) + 1;
  if (alpha.length !== need_alpha) {
    throw new Error(`A_fill l=${l} needs ${need_alpha} alpha params, got ${alpha.length}`);
  }
  if (beta.length !== need_beta) {
    throw new Error(`A_fill l=${l} needs ${need_beta} beta params, got ${beta.length}`);
  }

  // Coerce parameters once.
  alpha = alpha.map((a) => field.coerce(a));
  beta = beta.map((b) => field.coerce(b));

  function A1(l_, S1) {
    if (l_ === 0) {
      return S1;
    }
    if (l_ === 1) {
      // A^{(1)}_2 = (H2 + β1) S1 + α1
      const t = builder.mul(Hs[1].add_const(beta[1], field), S1);
      return t.add_const(alpha[1], field);
    }

    if (l_ === 2) {
      // S^{(1)}_2 = (H4 + β3) S^{(1)}_4 + Q_3[α3,α4,α5](x,H2)
      const q3 = _paper_q3(builder, alpha[3], alpha[4], alpha[5], Hs[1]);
      const t = builder.mul(Hs[2].add_const(beta[3], field), S1);
      const S1_2 = t.add(q3, field);
      // A^{(1)}_4 = A^{(1)}_2[α0,α1,β2,β1](S^{(1)}_2,(x,H2))
      const t2 = builder.mul(Hs[1].add_const(beta[1], field), S1_2);
      return t2.add_const(alpha[1], field);
    }

    // l_ >= 3:
    // S^{(1)}_{2^{l_-1}} = (H_{2^{l_}} + Q_{2^{l_-1}-1}[β_{2^{l_}-1}..β_{2^{l_-1}+1}]) S^{(1)}_{2^{l_}}
    //                  + Q_{2^{l_}-1}[α_{2^{l_}-1}..α_{2^{l_+1}-3}]
    const k_small = l_ - 1; // Q_{2^{k_small}-1}
    if (k_small < 2) {
      throw new Error('internal error: expected k_small >= 2 for l_>=3');
    }

    // sections/constructions.tex writes this Q polynomial as
    //   Q_{2^{l_-1}-1}[β_{2^{l_}-1}, ..., β_{2^{l_-1}+1}],
    // i.e. parameters in *descending* β-index order.
    const q_small_params = beta.slice((1 << (l_ - 1)) + 1, 1 << l_).reverse();
    const q_small = _paper_Q_known_powers(builder, k_small, q_small_params, Hs.slice(0, l_ - 1));

    const factor = Hs[l_].add(q_small, field);
    const t = builder.mul(factor, S1);

    const q_big_params = alpha.slice((1 << l_) - 1, (1 << (l_ + 1)) - 2);
    const q_big = _paper_Q_known_powers(builder, l_, q_big_params, Hs.slice(0, l_));
    const S1_prev = t.add(q_big, field);
    return A1(l_ - 1, S1_prev);
  }

  function A2(l_, S2) {
    if (l_ === 0) {
      return S2;
    }
    if (l_ === 1) {
      // A^{(2)}_2 = (H2 + β2) S2 + α0
      const t = builder.mul(Hs[1].add_const(beta[2], field), S2);
      return t.add_const(alpha[0], field);
    }

    if (l_ === 2) {
      // S^{(2)}_2 = (H4 + β4) S^{(2)}_4 + α2
      const t = builder.mul(Hs[2].add_const(beta[4], field), S2);
      const S2_2 = t.add_const(alpha[2], field);
      // A^{(2)}_4 = A^{(2)}_2[α0,α1,β2,β1](S^{(2)}_2,(x,H2))
      const t2 = builder.mul(Hs[1].add_const(beta[2], field), S2_2);
      return t2.add_const(alpha[0], field);
    }

    // l_ >= 3:
    // S^{(2)}_{2^{l_-1}} = (H_{2^{l_}} + β_{2^{l_}}) S^{(2)}_{2^{l_}} + α_{2^{l_}-2}
    const t = builder.mul(Hs[l_].add_const(beta[1 << l_], field), S2);
    const S2_prev = t.add_const(alpha[(1 << l_) - 2], field);
    return A2(l_ - 1, S2_prev);
  }

  const A1_out = A1(l, S1_2l);
  const A2_out = A2(l, S2_2l);

  if (l === 0) {
    // Base (not explicitly spelled out in sections/constructions.tex, but needed for the l=1
    // instance of the "4k+1 using known powers" construction):
    //
    //   A_1 = (x + β0) * S1 + S2 + β1
    //
    // This matches the "(x+α)-extraction" pattern while keeping β1 as an
    // independent additive parameter.
    const t = builder.mul(builder.x.add_const(beta[0], field), A1_out);
    return t.add(A2_out, field).add_const(beta[1], field);
  }

  const out = builder.mul(builder.x.add_const(beta[0], field), A1_out).add(A2_out, field);
  return out;
}

// py: tools/poly_schedule.py:1990
function _paper_Q_known_powers(builder, k, alpha, Hs) {
  // JS-only provenance: k<=2 emits no gates of its own (k=2 delegates to the
  // Q_3 gadget, which labels itself), so only k>=3 opens a block scope.
  const run = () => _paper_Q_known_powers_impl(builder, k, alpha, Hs);
  if (k < 3) return builder.mark_value(run());
  const label = `Q_${(1 << k) - 1} known-power block${PEELED_Q ? ' (peeled)' : ''}`;
  return builder.mark_value(builder.withLabel(label, run));
}

// py: tools/poly_schedule.py:1999
// Known-powers construction Q_{2^k-1} from sections/constructions.tex (Algorithm `alg:constr-known-2n-1`).
//
// Inputs:
//   - k >= 2
//   - alpha: [α0..α_{2^k-2}] (length 2^k-1)
//   - Hs: list of known powers with Hs[i]=H_{2^i}, Hs[0]=x, and len(Hs) >= k
//
// Output:
//   - Q_{2^k-1}(x, H2, ..., H_{2^{k-1}})
function _paper_Q_known_powers_impl(builder, k, alpha, Hs) {
  const field = builder.field;
  if (k < 0) {
    throw new Error('Q_known_powers requires k >= 0');
  }
  const need = k === 0 ? 1 : (1 << k) - 1;
  if (alpha.length !== need) {
    throw new Error(`Q_known_powers k=${k} needs ${need} alpha params, got ${alpha.length}`);
  }
  if (k >= 1 && Hs.length <= k - 1) {
    throw new Error(`Q_known_powers k=${k} needs Hs up to index ${k - 1} (H_{2^${k - 1}})`);
  }

  alpha = alpha.map((a) => field.coerce(a));

  if (PEELED_Q && k >= 3) {
    const m = (1 << (k - 1)) - 1;
    const gamma = alpha[0];
    const W = _paper_Q_known_powers(builder, k - 1, alpha.slice(1, 1 + m), Hs.slice(0, k - 1));
    const B = _paper_Q_known_powers(builder, k - 1, alpha.slice(1 + m), Hs.slice(0, k - 1));
    return builder.mul(Hs[k - 1].add_const(gamma, field), W).add(B, field);
  }

  if (k === 0) {
    // Q_0[α0] is just a constant.
    return AffineForm.const_only(alpha[0]);
  }

  if (k === 1) {
    // Q_1[α0](x) = x + α0
    return builder.x.add_const(alpha[0], field);
  }

  if (k === 2) {
    // Q_3[α0,α1,α2](x,H2)
    return _paper_q3(builder, alpha[0], alpha[1], alpha[2], Hs[1]);
  }

  if (k === 3) {
    // S^{(1)}_2 = H4 + α3
    // S^{(2)}_2 = H4 + α2
    // Q_7[α0..α6](x,H2,H4) = A_2[α0,α1,β2=α4,β1=α5,β0=α6](S1,S2,(x,H2))
    const S1 = Hs[2].add_const(alpha[3], field);
    const S2 = Hs[2].add_const(alpha[2], field);
    const a_alpha = [alpha[0], alpha[1]]; // α0..α1
    const beta_block = [alpha[4], alpha[5], alpha[6]]; // corresponds to β2,β1,β0 in that order
    const beta = [field.zero(), field.zero(), field.zero()]; // β0..β2
    // Map alpha[4+i] -> β_{2-i}.
    for (let i = 0; i < beta_block.length; i++) {
      beta[2 - i] = beta_block[i];
    }
    return _paper_A_fill(builder, 1, a_alpha, beta, S1, S2, Hs.slice(0, 2));
  }

  // k >= 4:
  // S^{(1)}_{2^{k-2}} = H_{2^{k-1}} + Q_{2^{k-2}-1}[α_{2^{k-1}-1}..α_{2^{k-1}+2^{k-2}-3}]
  // S^{(2)}_{2^{k-2}} = H_{2^{k-1}} + α_{2^{k-1}-2}
  // Q_{2^k-1} = A_{2^{k-2}}[α0..α_{2^{k-1}-3}, β_{2^{k-2}}..β0](S1,S2,(x,H2..H_{2^{k-2}}))
  const sub_k = k - 2;
  const sub_start = (1 << (k - 1)) - 1;
  const sub_end = (1 << (k - 1)) + (1 << (k - 2)) - 2;
  const q_sub_params = alpha.slice(sub_start, sub_end);
  const q_sub = _paper_Q_known_powers(builder, sub_k, q_sub_params, Hs.slice(0, k - 2));

  const S1 = Hs[k - 1].add(q_sub, field);
  const S2 = Hs[k - 1].add_const(alpha[(1 << (k - 1)) - 2], field);

  const a_alpha = alpha.slice(0, (1 << (k - 1)) - 2); // α0..α_{2^{k-1}-3}

  const beta_block_start = (1 << (k - 1)) + (1 << (k - 2)) - 2;
  const beta_block = alpha.slice(beta_block_start);
  const l = k - 2;
  const need_beta = (1 << l) + 1;
  if (beta_block.length !== need_beta) {
    throw new Error(
      `internal error: expected ${need_beta} beta-block params for k=${k}, got ${beta_block.length}`
    );
  }
  const beta = [];
  for (let i = 0; i < need_beta; i++) beta.push(field.zero()); // β0..β_{2^l}
  for (let i = 0; i < beta_block.length; i++) {
    beta[(1 << l) - i] = beta_block[i];
  }

  return _paper_A_fill(builder, l, a_alpha, beta, S1, S2, Hs.slice(0, l + 1));
}
