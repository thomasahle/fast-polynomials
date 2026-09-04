// g2_emit_barQ.frag.js — chain emitters II for the char-0 lane port of
// tools/poly_schedule.py: Q_{2^{l+1}k-1} with powers, the barQ family,
// _paper_splittable_pair, and the public entry compile_paper_params_chain.
// Fragment: function declarations only; assembled into core.js.

// py: tools/poly_schedule.py:840
// Like `_paper_Q_2lp1k_minus_1`, but also returns the (possibly extended) list
// of known powers produced along the way, plus the terminal `\tilde H` from the
// internal `T` call.
//
// Returns: [Q, Hs_out, tilde_out]
function _paper_Q_2lp1k_minus_1_with_powers(builder, k, l, alpha, Hs) {
  // JS-only provenance wrapper: Q_{2^{l+1}k + 2^l - 1} block (k=0 delegates to
  // the plain known-powers gadget, which labels itself).
  if (k === 0) return _paper_Q_2lp1k_minus_1_with_powers_impl(builder, k, l, alpha, Hs);
  const deg = (1 << (l + 1)) * k + ((1 << l) - 1);
  return builder.withLabel(`Q_${deg} block (2^{l+1}k+2^l−1, k=${k}, l=${l})`, () =>
    _paper_Q_2lp1k_minus_1_with_powers_impl(builder, k, l, alpha, Hs));
}

function _paper_Q_2lp1k_minus_1_with_powers_impl(builder, k, l, alpha, Hs) {
  const field = builder.field;
  if (k < 0 || l < 1) {
    throw new Error('Q_2lp1k_minus_1 requires k>=0 and l>=1');
  }
  // For k=0 we only need H2..H_{2^{l-1}} (since we dispatch to Q_{2^l-1}).
  // For k>0 we additionally need H_{2^l}.
  if (k === 0) {
    if (Hs.length < l) {
      throw new Error(
        `Q_2lp1k_minus_1(k=0,l=${l}) requires Hs up to index ${l - 1} (H_{2^${l - 1}})`
      );
    }
  } else {
    if (Hs.length <= l) {
      throw new Error(`Q_2lp1k_minus_1 requires Hs up to index ${l} (H_{2^${l}})`);
    }
  }

  let deg = (1 << (l + 1)) * k + ((1 << l) - 1);
  if (deg === 0) {
    if (alpha.length !== 1) {
      throw new Error('degree-0 Q requires 1 parameter');
    }
    const z = AffineForm.const_only(field.coerce(alpha[0]));
    return [z, Hs.slice(), z];
  }

  if (alpha.length !== deg) {
    throw new Error(
      `Q_2lp1k_minus_1(k=${k},l=${l}) needs ${deg} alpha params, got ${alpha.length}`
    );
  }

  alpha = alpha.map((a) => field.coerce(a));

  if (k === 0) {
    // Q_{2^l-1} is the known-powers construction.
    const out = _paper_Q_known_powers(builder, l, alpha, Hs.slice(0, l));
    return [out, Hs.slice(), Hs[0]];
  }

  if (l === 1) {
    // Special case needed for the `8k+3` induction: build `Q_{4k+1}(x,H2)` from
    // `T_{2k,2}` using only a shifted quadratic input and a single top-level
    // `(x+β0)` extraction.
    //
    // Parameter layout (deg = 4k+1):
    //   - α0..α_{4k-3}   : T-params for `T_{2k,2}`
    //   - α_{4k-2}       : shift for `\tilde H2 = \hat H2 + α_{4k-2}`
    //   - α_{4k-1}       : quadratic shift `\hat H2 = H2 + α_{4k-1}`
    //   - α_{4k}         : extraction parameter `β0` in `(x+β0)S1 + S2`
    deg = 4 * k + 1;
    if (alpha.length !== deg) {
      throw new Error(
        `Q_2lp1k_minus_1(k=${k},l=1) needs ${deg} alpha params, got ${alpha.length}`
      );
    }
    if (Hs.length < 2) {
      throw new Error('Q_2lp1k_minus_1(l=1) requires Hs=[x,H2]');
    }
    alpha = alpha.map((a) => field.coerce(a));

    const t_params = alpha.slice(0, 4 * k - 2);
    const tilde_shift = alpha[4 * k - 2];
    const hat_shift = alpha[4 * k - 1];
    const beta0 = alpha[4 * k];

    const x = Hs[0];
    const H2 = Hs[1];
    const H_hat = H2.add_const(hat_shift, field);
    const tilde_H2 = H_hat.add_const(tilde_shift, field);

    const [S1, S2, Hs_out, tilde_out] = _paper_T(
      builder, 2 * k, 1, t_params, [x, H_hat], tilde_H2
    );
    const out = builder.mark_value(
      builder.mul(builder.x.add_const(beta0, field), S1).add(S2, field)
    );
    return [out, Hs_out, tilde_out];
  }

  const block = 1 << l;
  const a_alpha = alpha.slice(0, block - 2); // α0..α_{2^l-3}
  const t_start = block - 2;
  const shift_idx = (1 << (l + 1)) * k - 2; // α_{2^{l+1}k-2}
  const t_params = alpha.slice(t_start, shift_idx); // α_{2^l-2}..α_{2^{l+1}k-3}
  const shift = alpha[shift_idx];

  // Q_{2^{l-1}-1} parameters: length 2^{l-1}-1.
  // For l=1 this is 0, i.e. Q_0 is treated as the zero polynomial here.
  const qhat_start = shift_idx + 1;
  const qhat_len = (1 << (l - 1)) - 1;
  const qhat_params = alpha.slice(qhat_start, qhat_start + qhat_len);

  const beta_start = qhat_start + qhat_len;
  const beta_len = (1 << (l - 1)) + 1;
  const beta_params = alpha.slice(beta_start, beta_start + beta_len);
  if (beta_params.length !== beta_len || beta_start + beta_len !== alpha.length) {
    throw new Error('internal error: beta param count mismatch in Q_2lp1k_minus_1');
  }

  // \hat H_{2^l} = H_{2^l} + Q_{2^{l-1}-1}(qhat_params)
  let H_hat;
  if (l === 1) {
    H_hat = Hs[1];
  } else {
    const qhat = _paper_Q_known_powers(builder, l - 1, qhat_params, Hs.slice(0, l - 1));
    H_hat = Hs[l].add(qhat, field);
  }

  // Run T_{2k,2^l} with H_{2^l} replaced by \hat H_{2^l}.
  const Hs_hat = Hs.slice();
  Hs_hat[l] = H_hat;
  const need_t = (2 * k - 1) * block;
  if (t_params.length !== need_t) {
    throw new Error(`internal error: expected ${need_t} T-params, got ${t_params.length}`);
  }
  const [S1, S2, Hs_out, tilde_out] = _paper_T(
    builder, 2 * k, l, t_params, Hs_hat, H_hat.add_const(shift, field)
  );

  // Final fill: A_{2^{l-1}} on (S1,S2).
  const A_l = l - 1;
  const A_alpha_need = (1 << (A_l + 1)) - 2; // == 2^l - 2 (and 0 when l=1)
  if (a_alpha.length !== A_alpha_need) {
    throw new Error('internal error: A_alpha length mismatch in Q_2lp1k_minus_1');
  }

  const A_beta = []; // β0..β_{2^{l-1}}
  for (let i = 0; i < (1 << A_l) + 1; i++) A_beta.push(field.zero());
  for (let i = 0; i < beta_params.length; i++) {
    A_beta[(1 << A_l) - i] = beta_params[i];
  }

  const out = builder.mark_value(
    _paper_A_fill(builder, A_l, a_alpha.slice(), A_beta, S1, S2, Hs.slice(0, A_l + 1))
  );
  return [out, Hs_out, tilde_out];
}

// py: tools/poly_schedule.py:1297
// Concrete realization of the paper's "good polynomial" gadget \bar{Q}_deg.
//
// sections/constructions.tex only specifies how \bar{Q} is *used* (not its
// exact formula), but the surrounding text implies two requirements:
//   1) \bar{Q}_deg should be decodable given (H2,H4), and
//   2) it should fit the tight multiplication budget (deg//2 multiplications,
//      since (H2,H4) are treated as auxiliary wires).
//
// We implement the minimal family that matches these constraints:
//   - If deg = 4m+1:  \bar{Q}_{4m+1} := Q_{4m+1}(x,H2)  (the l=1 known-powers construction)
//   - If deg = 4m+3 (m>=1):
//         \bar{Q}_{4m+3} := (H2 + s) * Q_{4m+1}(x,H2) + (H4 + t)
//     which costs exactly one extra multiplication on top of Q_{4m+1} and uses
//     H4 only additively.
//
// Returns: [barQ, Hs_out] where Hs_out is Hs_in extended with any newly
// created "known powers" produced as byproducts of the internal Q_{4m+1} call.
function _paper_barQ_odd_with_H2_H4_with_powers(builder, deg, alpha, Hs_in) {
  const field = builder.field;
  if (deg < 1 || deg % 2 === 0) {
    throw new Error('barQ requires odd deg >= 1');
  }
  if (alpha.length !== deg) {
    throw new Error(`barQ_${deg} needs ${deg} alpha params, got ${alpha.length}`);
  }
  if (Hs_in.length < 2) {
    throw new Error('barQ requires Hs_in=[x,H2,...]');
  }

  alpha = alpha.map((a) => field.coerce(a));

  // Prefer the paper's known-powers `Q_deg` construction whenever the required
  // known powers are already available. This matches how \bar{Q} is used in
  // the induction steps: we thread through the byproduct powers from earlier
  // computations and use them when possible.
  const l_need = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l_need;
  const kk = Math.floor((odd - 1) / 2);
  const need = kk > 0 ? l_need + 1 : l_need;
  if (Hs_in.length >= need) {
    const [q, Hs_out] = _paper_Q_for_odd_degree_with_powers(builder, deg, alpha, Hs_in);
    return [q, Hs_out];
  }

  if (Hs_in.length < 3) {
    throw new Error('barQ fallback requires H4 (Hs_in[2]) to be available');
  }
  const H2 = Hs_in[1];
  const H4 = Hs_in[2];

  // Keep the hand-crafted \bar{Q}_{15} used by the n=31 special case stable.
  if (deg === 15) {
    return [_paper_barQ_15(builder, alpha, H2, H4), Hs_in.slice()];
  }

  // Fallback for deg ≡ 7 (mod 8), i.e. deg = 8k+7 (k>=2 here since deg=15 is
  // handled above):
  //
  // Here v2(deg+1) >= 3, so the paper's `Q_deg` construction would require
  // higher known powers (H8/H16/...) that may not be available from earlier
  // steps. sections/constructions.tex instead assumes the existence of a "good
  // polynomial" gadget \bar{Q}_{4k+3} that is decodable given only (H2,H4).
  //
  // We realize the required instances using a tight-budget construction based
  // on the paper's own subroutines:
  //   - synthesize an H8 + \tilde H8,
  //   - run `T_{k,8}` to get a degree-(8k) compatible pair,
  //   - apply `A_4` to reach degree (8k+7).
  //
  // This keeps the Jacobian determinant constant and fits the exact (deg//2)
  // multiplication budget given (H2,H4).
  if (deg % 8 === 7 && deg >= 23) {
    const k = Math.floor((deg - 7) / 8);
    const [out, powers_out] = _paper_barQ_8k_plus_7_with_powers(builder, k, alpha, H2, H4);
    const Hs_out = Hs_in.slice();
    if (Hs_out.length < powers_out.length) {
      Hs_out.push(...powers_out.slice(Hs_out.length));
    }
    return [out, Hs_out];
  }

  throw new Error(
    `internal error: no barQ fallback case matched for deg=${deg} (need=${need}, have=${Hs_in.length})`
  );
}

// py: tools/poly_schedule.py:1381
function _paper_barQ_odd_with_H2_H4(builder, deg, alpha, H2, H4) {
  const [q] = _paper_barQ_odd_with_H2_H4_with_powers(builder, deg, alpha, [builder.x, H2, H4]);
  return q;
}

// py: tools/poly_schedule.py:1388
// Concrete construction for \bar{Q}_{15}(x,H2,H4) used in
// sections/constructions.tex (Special case 31).
//
// We implement `\bar{Q}_{15}` as a direct `A_4` (fill) instance, using only
// `H2` and `H4` plus one internally constructed monic degree-8 polynomial `H8`.
//
// Total multiplications given H2,H4: 1 (H8) + 6 (A_4) = 7.
function _paper_barQ_15(builder, alpha, H2, H4) {
  const field = builder.field;
  if (alpha.length !== 15) {
    throw new Error(`barQ_15 needs 15 parameters, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  const x = builder.x;

  // Parameter partition:
  //   - 3 params for H8: a,b,c
  //   - 1 param for shifting S2: d
  //   - 6 params for A_4 alpha: α0..α5
  //   - 5 params for A_4 beta:  β0..β4
  const a_h8 = alpha[0];
  const b_h8 = alpha[1];
  const c_h8 = alpha[2];
  const d_shift = alpha[3];

  const a_alpha = alpha.slice(4, 10);
  const beta = alpha.slice(10, 15);

  // H8 proxy (monic degree 8). We deliberately mix in both `x` and `H2` so the
  // low-degree part has enough structure for the downstream `A_4` fill.
  const A = x.add_const(b_h8, field); // degree 1
  const B = H2.add_const(c_h8, field); // degree 2
  builder.pushLabel('Q̄_15 block');
  const H8 = builder.withLabel('H_8 known power', () =>
    builder.mul(H4.add(A, field), H4.add(B, field))).add_const(a_h8, field);

  const S1 = H8;
  const S2 = H8.add_const(d_shift, field);
  const out = _paper_A_fill(builder, 2, a_alpha, beta, S1, S2, [x, H2, H4]);
  builder.popLabel();
  return out;
}

// py: tools/poly_schedule.py:1427
// Strong construction for \bar{Q}_{8k+7}(x,H2,H4) (k >= 2).
//
// This matches the "\bar Q only needs (H2,H4)" assumption in the induction
// steps, while keeping the Jacobian determinant constant.
//
// Structure (tight multiplication budget):
//   - Build a monic degree-8 power H8 and a shifted \tilde H8.
//   - Use `T_{k,8}` (Algorithm 3) to obtain a degree-(8k) compatible pair.
//   - Apply `A_4` (i.e. `A_fill(l=2)`) to reach degree (8k+7).
//
// Parameter partition (8k+7 total):
//   - 4 params for (H8, \tilde H8): a,b,c,d
//   - (k-1)*8 params for T_{k,8}
//   - 11 params for A_4 (6 alpha + 5 beta)
function _paper_barQ_8k_plus_7_with_powers(builder, k, alpha, H2, H4) {
  const field = builder.field;
  if (k < 2) {
    throw new Error('barQ_{8k+7} requires k>=2');
  }
  const deg = 8 * k + 7;
  if (alpha.length !== deg) {
    throw new Error(`barQ_{8k+7} (k=${k}) needs ${deg} parameters, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  const x = builder.x;

  const [a_h8, b_h8, c_h8, d_tilde] = alpha.slice(0, 4);
  const t_len = (k - 1) * 8;
  const t_params = alpha.slice(4, 4 + t_len);
  const fill = alpha.slice(4 + t_len);
  const a_alpha = fill.slice(0, 6);
  const beta = fill.slice(6);
  if (t_params.length !== t_len || a_alpha.length !== 6 || beta.length !== 5) {
    throw new Error('internal error: barQ_{8k+7} parameter partition mismatch');
  }

  // H8 proxy (monic degree 8) + tilde shift.
  builder.pushLabel(`Q̄_${deg} block (8k+7, k=${k})`);
  const H8 = builder.withLabel('H_8 known power', () => builder.mul(
    H4.add(x.add_const(b_h8, field), field),
    H4.add(H2.add_const(c_h8, field), field)
  )).add_const(a_h8, field);
  const tilde_H8 = H8.add_const(d_tilde, field);

  // Degree-(8k) compatible pair from T_{k,8}.
  const [S1, S2, Hs_out, _tilde_out] = _paper_T(
    builder, k, 3, t_params, [x, H2, H4, H8], tilde_H8
  );

  // Final A_4 fill adds 7 degrees: 8k -> 8k+7.
  const out = _paper_A_fill(builder, 2, a_alpha, beta, S1, S2, [x, H2, H4]);
  builder.popLabel();

  // Expose any higher known powers produced by the internal T recursion.
  return [out, Hs_out.slice()];
}

// py: tools/poly_schedule.py:1546
// Build (T^{(1)}_n, T^{(2)}_n) and return a byproduct list of "known powers".
//
// This implements the casework / induction steps in sections/constructions.tex,
// plus the explicit special cases 15/27/31.
//
// Return value:
//   - [T1, T2, Hs] where Hs[i] is a monic degree-2^i polynomial ("known power"),
//     with Hs[0]=x. (We do not enforce that these are literal iterated squares;
//     the paper's constructions only require the degree/monicity structure.)
function _paper_splittable_pair(builder, n, alpha) {
  // JS-only provenance wrapper: the pair (T^(1)_n, T^(2)_n) with P = x·T^(1) + T^(2).
  return builder.withLabel(`splittable pair (T⁽¹⁾_${n}, T⁽²⁾_${n})`, () =>
    _paper_splittable_pair_impl(builder, n, alpha));
}

function _paper_splittable_pair_impl(builder, n, alpha) {
  const field = builder.field;
  if (n < 1 || n % 2 === 0) {
    throw new Error('splittable_pair requires odd n >= 1');
  }
  if (n === 7) {
    throw new Error('no splittable pair is used for n=7; use the septic base construction instead');
  }
  if (alpha.length !== n) {
    throw new Error(`splittable_pair(${n}) needs ${n} params, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  // Tiny bases.
  if (n === 1) {
    const x = builder.x;
    return [builder.const(field.one()), builder.const(alpha[0]), [x]];
  }

  if (n === 3) {
    // H2 = (x + α2)x + α1
    // T1 = H2, T2 = H2 + α0
    const x = builder.x;
    const H2 = _paper_H2(builder, alpha[1], alpha[2]);
    return [H2, H2.add_const(alpha[0], field), [x, H2]];
  }

  // Explicit special cases from sections/constructions.tex.
  if (n === 15) {
    const H2 = _paper_H2(builder, alpha[6], alpha[7]);
    const x = builder.x;
    const x_shift = x.add_const(alpha[5], field);
    const H4 = builder.withLabel('H_4 known power', () =>
      _paper_square_diff(builder, H2, x_shift)).add_const(alpha[4], field);

    const S1 = _paper_Q_known_powers(builder, 3, alpha.slice(8, 15), [x, H2, H4]);
    const S2 = H2.add_const(alpha[3], field);
    const T1 = _paper_square_diff(builder, S1, S2).add_const(alpha[1], field);

    // sections/constructions.tex defines
    //   T2_low = H4^2 - (H2+α2)^2 + α0
    // which has degree 8. For the later induction steps we need the second
    // component to have degree 14. We "promote" it by adding `T1` (no extra
    // multiplications), mirroring the fix used in the `n=27` special case.
    const T2_low = _paper_square_diff(builder, H4, H2.add_const(alpha[2], field))
      .add_const(alpha[0], field);
    const T2 = T2_low.add(T1, field);
    // Expose the monic degree-8 byproduct (used as H8 in the 8k+7 induction).
    const H8 = T2_low;
    return [T1, T2, [x, H2, H4, H8]];
  }

  if (n === 27) {
    const H2 = _paper_H2(builder, alpha[2], alpha[3]);
    const x = builder.x;

    // Special case 27 from sections/constructions.tex.
    //
    // Note: sections/constructions.tex writes `T^{(2)}_{27}` as a low-degree
    // (deg 14) expression. That version is bijective by itself, but it does not
    // compose correctly as a "splittable pair" inside the later `8k+3` induction.
    //
    // We repair it by following the same template as the `n=31` special case:
    // use the *same* high-degree polynomial (`Q13`) in both components, but
    // introduce an external shift (here we reuse `α13`, which is not used by
    // `Q13`) so the map remains generically invertible.
    const [S1, Hs_out] = _paper_Q_2lp1k_minus_1_with_powers(
      builder, 3, 1, alpha.slice(14, 27), [x, H2]
    );
    if (Hs_out.length <= 2) {
      throw new Error('internal error: expected H4 byproduct in Q_13');
    }
    const H4 = Hs_out[2];
    const Hs = [x, H2].concat(Hs_out.slice(2));

    const S2 = _paper_q3(builder, alpha[4], alpha[5], alpha[6], H2);
    const S3 = _paper_Q_known_powers(builder, 3, alpha.slice(7, 14), [x, H2, H4]);

    const T1 = _paper_square_diff(builder, S1, S2).add_const(alpha[1], field);
    // Promote the low-degree second component by adding `T1` (no extra multiplications).
    // This yields a degree-26 `T2` that composes correctly in later induction steps.
    const T2_low = _paper_square_diff(builder, S3, H2).add_const(alpha[0], field);
    const T2 = T2_low.add(T1, field);
    return [T1, T2, Hs];
  }

  if (n === 31) {
    const H2 = _paper_H2(builder, alpha[6], alpha[7]);
    const x = builder.x;
    const x_shift = x.add_const(alpha[5], field);
    const H4 = builder.withLabel('H_4 known power', () =>
      _paper_square_diff(builder, H2, x_shift)).add_const(alpha[4], field);

    // sections/constructions.tex (Special case 31) references a "good polynomial"
    // gadget \bar{Q}_{15}(x,H2,H4).
    const S1 = _paper_barQ_odd_with_H2_H4(builder, 15, alpha.slice(16, 31), H2, H4);
    const S2 = _paper_Q_known_powers(builder, 3, alpha.slice(8, 15), [x, H2, H4]);
    const S3 = _paper_q3(builder, alpha[1], alpha[2], alpha[3], H2);
    const T1 = _paper_square_diff(builder, S1, S2).add(S3, field);

    const T2 = _paper_square_diff(builder, S1.add_const(alpha[15], field), H4)
      .add_const(alpha[0], field);
    return [T1, T2, [x, H2, H4]];
  }

  // Main families / induction steps.
  if (n % 4 === 1) {
    // n = 4k+1
    const k = Math.floor((n - 1) / 4);
    // Paper indexing/layout (sections/constructions.tex, Lemma "The 4k+1 family
    // is splittable"):
    //   - α0..α_{4k-3}   : parameters for the internal `T_{2k,2}` call
    //   - α_{4k-2}       : scalar shift in \tilde H2 = H2 + α_{4k-2}
    //   - α_{4k-1},α_{4k}: H2 = (x + α_{4k})x + α_{4k-1}
    //
    // This "high-indexed H2" convention is important for the paper-faithful
    // coefficient→parameter decoding algorithms, which recover H2 from the
    // top coefficients of P_{4k+1}.
    const t_params = alpha.slice(0, n - 3);
    const tilde_shift = alpha[n - 3];
    const h2_const = alpha[n - 2];
    const h2_lin = alpha[n - 1];

    const H2 = _paper_H2(builder, h2_const, h2_lin);
    const tilde_H2 = H2.add_const(tilde_shift, field);
    const x = builder.x;
    const [T1, T2, Hs_out, _tilde_out] = _paper_T(
      builder, 2 * k, 1, t_params, [x, H2], tilde_H2
    );
    // Keep the "known powers" produced by the internal T recursion.
    return [T1, T2, Hs_out];
  }

  if (n % 8 === 3) {
    // n = 8k+3 (k>=1 here; n=3 handled above)
    const k = Math.floor((n - 3) / 8);
    const sub_n = 2 * k + 1;
    const [S1_1, S1_2, Hs] = _paper_splittable_pair(builder, sub_n, alpha.slice(2 * k, 4 * k + 1));
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 in splittable_pair output');
    }
    const x = Hs[0];
    const H2 = Hs[1];

    // Paper induction step (sections/constructions.tex, Algorithm "If 2k+1 is
    // splittable then 8k+3 is splittable"):
    //   S2 = Q_{4k+1}(x,H2), which also makes an H4 derivable as a byproduct.
    const [S2, Hs2_raw, _tilde_out] = _paper_Q_2lp1k_minus_1_with_powers(
      builder, k, 1, alpha.slice(4 * k + 2, 8 * k + 3), [x, H2]
    );
    if (Hs2_raw.length <= 2) {
      throw new Error('internal error: expected an H4 byproduct in Q_{4k+1}');
    }

    // The l=1 Q_{4k+1} construction internally shifts H2 to \hat H2; the
    // known-powers byproducts beyond H2 are still valid, but we must keep
    // the original H2 at Hs[1] for downstream Q calls.
    let Hs2 = [x, H2].concat(Hs2_raw.slice(2));

    // S3 = Q_{2k-1}(x, H2, H4, ..., H_{2^ℓ}).
    //
    // sections/constructions.tex special-cases k=1 (so 2k-1=1) and simply uses
    // the constant α1 instead of the generic Q_1 gadget.
    let S3;
    let Hs3;
    if (k === 1) {
      S3 = builder.const(alpha[1]);
      Hs3 = Hs2.slice();
    } else {
      const deg3 = 2 * k - 1;
      [S3, Hs3] = _paper_Q_for_odd_degree_with_powers(builder, deg3, alpha.slice(1, 2 * k), Hs2);
    }

    // Preserve any higher "known powers" produced by the recursive S1 call,
    // and extend with any additional byproducts from S3.
    if (Hs.length > Hs2.length) {
      Hs2 = Hs2.slice().concat(Hs.slice(Hs2.length));
    }
    if (Hs3.length > Hs2.length) {
      Hs2 = Hs2.slice().concat(Hs3.slice(Hs2.length));
    }

    const T1 = _paper_square_diff(builder, S2, S1_1).add(S3, field);
    const T2 = _paper_square_diff(builder, S2.add_const(alpha[4 * k + 1], field), S1_2)
      .add_const(alpha[0], field);
    // Expose the "known powers" computed while building S2; higher-level calls
    // may need H8/H16/... (e.g. when a later Q-construction has v2(deg+1) >= 3).
    return [T1, T2, Hs2];
  }

  if (n % 8 === 7) {
    // n = 8k+7 (n in {7,15,31} handled above)
    const k = Math.floor((n - 7) / 8);
    const sub_n = 2 * k + 1;
    let [S1_1, S1_2, Hs] = _paper_splittable_pair(builder, sub_n, alpha.slice(0, 2 * k + 1));
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 in splittable_pair output for 8k+7 case');
    }
    let H2 = Hs[1];

    // Build the Q_deg polynomial needed by the `8k+7` induction.
    //
    // We prefer the paper's "known powers" Q construction whenever the required
    // known powers are already available from earlier steps (either from the
    // recursive splittable-pair call or produced as byproducts of prior Q calls).
    //
    // If the required powers are *not* available, we must not synthesize them
    // with extra squarings (that would exceed the n/2+1 multiplication budget).
    // In that case we fall back to the `\bar Q` gadget family, which is designed
    // to work using only (H2,H4) as auxiliary inputs.
    function build_Q(deg, params, Hs_in) {
      const l = _v2_positive(deg + 1);
      const odd = (deg + 1) >> l;
      const kk = Math.floor((odd - 1) / 2);
      const need = kk > 0 ? l + 1 : l;

      // If we have enough known powers, use the paper's `Q_deg` construction.
      if (Hs_in.length >= need) {
        const [q, Hs_out] = _paper_Q_for_odd_degree_with_powers(builder, deg, params, Hs_in);
        return [q, Hs_out];
      }

      // Otherwise, fall back to the "good polynomial" gadget family \bar{Q}_deg
      // which is designed to work with only (H2,H4) as auxiliary inputs.
      const [q, Hs_out] = _paper_barQ_odd_with_H2_H4_with_powers(builder, deg, params, Hs_in);
      return [q, Hs_out];
    }

    // S2 = Q_{2k+1}[…], and keep any newly produced known powers.
    let res = build_Q(sub_n, alpha.slice(2 * k + 2, 4 * k + 3), Hs);
    const S2 = res[0];
    Hs = res[1];
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 to remain available after Q_{2k+1}');
    }
    H2 = Hs[1];

    // S3 = Q_{4k+3}[…], which may require more known powers than S1 produced.
    res = build_Q(4 * k + 3, alpha.slice(4 * k + 4, 8 * k + 7), Hs);
    const S3 = res[0];
    Hs = res[1];

    const T1 = _paper_square_diff(builder, S3, S2).add(S1_1, field);

    const S2_shift = S2.add_const(alpha[2 * k + 1], field);
    const S3_shift = S3.add_const(alpha[4 * k + 3], field);
    const T2 = _paper_square_diff(builder, S3_shift, S2_shift).add(S1_2, field);
    return [T1, T2, Hs];
  }

  throw new Error(`internal error: no splittable case matched for odd n=${n}`);
}

// py: tools/poly_schedule.py:6921
// Compile the paper's parameterized polynomial family `P_n[α0..α_{n-1}]` into
// a chain.
//
// This is the forward (evaluation) direction: it does *not* implement the
// coefficient → parameter decoding step from the notes.
// (JS port: `modulus` is a BigInt prime, null (exact rationals — the Python
// float check is dropped), or a ready-made field object exposing the Field
// interface (coerce/add/mul/…), e.g. the website's double-precision field.)
function compile_paper_params_chain(params, modulus = null) {
  const params_list_in = Array.from(params);
  if (params_list_in.length === 0) {
    throw new Error('params must be non-empty');
  }

  const field = (modulus !== null && typeof modulus === 'object' && typeof modulus.coerce === 'function')
    ? modulus : new Field({ modulus });
  const params_list = params_list_in.map((a) => field.coerce(a));

  const n = params_list.length;
  const builder = new ChainBuilder(field);

  function build_P(deg, a) {
    if (deg !== a.length) {
      throw new Error('internal error: parameter length mismatch in build_P');
    }
    if (deg === 1) {
      return builder.x.add_const(a[0], field);
    }
    if (deg === 5) {
      return _paper_P5(builder, a);
    }
    if (deg === 7) {
      const two = field.add(field.one(), field.one());
      if (field.is_zero(two)) {
        // py: return _paper_P7_char2(builder, a) — char-2 lane not ported.
        throw new Error('_paper_P7_char2 is not ported (characteristic-2 branch)');
      }
      return _paper_P7(builder, a);
    }
    if (deg % 2 === 0) {
      const q = build_P(deg - 1, a.slice(1));
      return builder.withLabel(`even lift P_${deg} = x·P_${deg - 1} + α_0`, () =>
        builder.mul(q, builder.x)).add_const(a[0], field);
    }

    const [T1, T2, _H2] = _paper_splittable_pair(builder, deg, a);
    return builder.withLabel(`P_${deg} = x·T⁽¹⁾ + T⁽²⁾`, () =>
      builder.mul(T1, builder.x)).add(T2, field);
  }

  const out = build_P(n, params_list);
  const chain = builder.finalize(out);
  chain.validate();
  return chain;
}
