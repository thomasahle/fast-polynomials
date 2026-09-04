// g3_poly_paper.frag.js — coefficient-level reference expansions
// (_poly_paper_* twins of the chain emitters) from tools/poly_schedule.py.
// Fragment: function declarations only; no imports/exports, no top-level
// side effects.  Depends on runtime.frag.js (Field, PEELED_Q, _poly_* helpers)
// and on _v2_positive (g1_emit_bases.frag.js).

// py: tools/poly_schedule.py:1826
// Coefficient-level twin of `_paper_QO`.
function _poly_QO({ deg, alpha, Hs, field }) {
  if (deg === 1) {
    return _poly_add_const(Hs[0], field.coerce(alpha[0]), field);
  }
  const t = 32 - Math.clz32(deg); // deg.bit_length()
  if (deg === (1 << t) - 1) {
    return _poly_paper_Q_known_powers({ k: t, alpha: alpha, Hs: Hs.slice(0, t), field: field });
  }
  const h = 1 << (t - 1);
  const w = deg - h;
  const ud = 2 * h - deg;
  const U = _poly_QO({ deg: ud, alpha: alpha.slice(0, ud), Hs: Hs, field: field });
  const W = _poly_QO({ deg: w, alpha: alpha.slice(ud, ud + w), Hs: Hs, field: field });
  const B = _poly_QO({ deg: w, alpha: alpha.slice(ud + w), Hs: Hs, field: field });
  return _poly_add(_poly_mul(_poly_add(Hs[t - 1], U, field), W, field), B, field);
}

// py: tools/poly_schedule.py:3641
// Coefficient-level encoder for:
//   Q_3[α0,α1,α2](x,H2) = (x+α2)(H2+α1) + α0
function _poly_paper_q3({ alpha0, alpha1, alpha2, H2, field }) {
  const x = [field.zero(), field.one()];
  const t1 = _poly_add_const(x, alpha2, field);
  const t2 = _poly_add_const(H2, alpha1, field);
  return _poly_add(_poly_mul(t1, t2, field), [field.coerce(alpha0)], field);
}

// py: tools/poly_schedule.py:3653
// Coefficient-level encoder matching `_paper_A_fill` (Algorithm `alg:constr-fill`).
function _poly_paper_A_fill({ l, alpha, beta, S1_2l, S2_2l, Hs, field }) {
  if (l < 0) throw new Error('A_fill requires l >= 0');
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

  alpha = alpha.map((a) => field.coerce(a));
  beta = beta.map((b) => field.coerce(b));

  const x = Hs[0];

  function A1(l_, S1) {
    if (l_ === 0) {
      return _poly_trim(S1, field);
    }
    if (l_ === 1) {
      // A^{(1)}_2 = (H2 + β1) S1 + α1
      const t = _poly_mul(_poly_add_const(Hs[1], beta[1], field), S1, field);
      return _poly_add_const(t, alpha[1], field);
    }
    if (l_ === 2) {
      // S^{(1)}_2 = (H4 + β3) S^{(1)}_4 + Q_3[α3,α4,α5](x,H2)
      const q3 = _poly_paper_q3({ alpha0: alpha[3], alpha1: alpha[4], alpha2: alpha[5], H2: Hs[1], field: field });
      const t = _poly_mul(_poly_add_const(Hs[2], beta[3], field), S1, field);
      const S1_2 = _poly_add(t, q3, field);
      // A^{(1)}_4 = (H2 + β1) S^{(1)}_2 + α1
      const t2 = _poly_mul(_poly_add_const(Hs[1], beta[1], field), S1_2, field);
      return _poly_add_const(t2, alpha[1], field);
    }

    // l_ >= 3
    const k_small = l_ - 1; // Q_{2^{k_small}-1}
    // Q_{2^{l_-1}-1}[β_{2^{l_}-1}, ..., β_{2^{l_-1}+1}] in descending β-index order.
    const q_small_params = beta.slice((1 << (l_ - 1)) + 1, 1 << l_).reverse();
    const q_small = _poly_paper_Q_known_powers({ k: k_small, alpha: q_small_params, Hs: Hs.slice(0, l_ - 1), field: field });

    const factor = _poly_add(Hs[l_], q_small, field);
    const t = _poly_mul(factor, S1, field);

    const q_big_params = alpha.slice((1 << l_) - 1, (1 << (l_ + 1)) - 2);
    const q_big = _poly_paper_Q_known_powers({ k: l_, alpha: q_big_params, Hs: Hs.slice(0, l_), field: field });
    const S1_prev = _poly_add(t, q_big, field);
    return A1(l_ - 1, S1_prev);
  }

  function A2(l_, S2) {
    if (l_ === 0) {
      return _poly_trim(S2, field);
    }
    if (l_ === 1) {
      // A^{(2)}_2 = (H2 + β2) S2 + α0
      const t = _poly_mul(_poly_add_const(Hs[1], beta[2], field), S2, field);
      return _poly_add_const(t, alpha[0], field);
    }
    if (l_ === 2) {
      // S^{(2)}_2 = (H4 + β4) S^{(2)}_4 + α2
      const t = _poly_mul(_poly_add_const(Hs[2], beta[4], field), S2, field);
      const S2_2 = _poly_add_const(t, alpha[2], field);
      // A^{(2)}_4 = (H2 + β2) S^{(2)}_2 + α0
      const t2 = _poly_mul(_poly_add_const(Hs[1], beta[2], field), S2_2, field);
      return _poly_add_const(t2, alpha[0], field);
    }

    // l_ >= 3
    const t = _poly_mul(_poly_add_const(Hs[l_], beta[1 << l_], field), S2, field);
    const S2_prev = _poly_add_const(t, alpha[(1 << l_) - 2], field);
    return A2(l_ - 1, S2_prev);
  }

  const A1_out = A1(l, S1_2l);
  const A2_out = A2(l, S2_2l);

  if (l === 0) {
    const t = _poly_mul(_poly_add_const(x, beta[0], field), A1_out, field);
    return _poly_add_const(_poly_add(t, A2_out, field), beta[1], field);
  }

  const t = _poly_mul(_poly_add_const(x, beta[0], field), A1_out, field);
  return _poly_add(t, A2_out, field);
}

// py: tools/poly_schedule.py:3745
// Coefficient-level encoder matching `_paper_Q_known_powers`
// (Algorithm `alg:constr-known-2n-1`).
function _poly_paper_Q_known_powers({ k, alpha, Hs, field }) {
  if (k < 0) throw new Error('Q_known_powers requires k >= 0');
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
    const W = _poly_paper_Q_known_powers({ k: k - 1, alpha: alpha.slice(1, 1 + m), Hs: Hs.slice(0, k - 1), field: field });
    const B = _poly_paper_Q_known_powers({ k: k - 1, alpha: alpha.slice(1 + m), Hs: Hs.slice(0, k - 1), field: field });
    const t = _poly_mul(_poly_add_const(Hs[k - 1], gamma, field), W, field);
    return _poly_add(t, B, field);
  }

  const x = Hs[0];
  if (k === 0) {
    return [alpha[0]];
  }
  if (k === 1) {
    return _poly_add_const(x, alpha[0], field);
  }
  if (k === 2) {
    return _poly_paper_q3({ alpha0: alpha[0], alpha1: alpha[1], alpha2: alpha[2], H2: Hs[1], field: field });
  }
  if (k === 3) {
    // Q_7 via A_2 on (H4+α3, H4+α2) with β2=α4, β1=α5, β0=α6.
    const H4 = Hs[2];
    const S1 = _poly_add_const(H4, alpha[3], field);
    const S2 = _poly_add_const(H4, alpha[2], field);
    const a_alpha = [alpha[0], alpha[1]];
    const beta = [field.zero(), field.zero(), field.zero()]; // β0..β2
    beta[2] = alpha[4];
    beta[1] = alpha[5];
    beta[0] = alpha[6];
    return _poly_paper_A_fill({ l: 1, alpha: a_alpha, beta: beta, S1_2l: S1, S2_2l: S2, Hs: Hs.slice(0, 2), field: field });
  }

  // k >= 4
  const sub_k = k - 2;
  const sub_start = (1 << (k - 1)) - 1;
  const sub_end = (1 << (k - 1)) + (1 << (k - 2)) - 2;
  const q_sub_params = alpha.slice(sub_start, sub_end);
  const q_sub = _poly_paper_Q_known_powers({ k: sub_k, alpha: q_sub_params, Hs: Hs.slice(0, k - 2), field: field });

  const S1 = _poly_add(Hs[k - 1], q_sub, field);
  const S2 = _poly_add_const(Hs[k - 1], alpha[(1 << (k - 1)) - 2], field);

  const a_alpha = alpha.slice(0, (1 << (k - 1)) - 2);
  const beta_block_start = (1 << (k - 1)) + (1 << (k - 2)) - 2;
  const beta_block = alpha.slice(beta_block_start);
  const l = k - 2;
  const need_beta = (1 << l) + 1;
  if (beta_block.length !== need_beta) {
    throw new Error('internal error: beta-block length mismatch');
  }

  const beta = []; // β0..β_{2^l}
  for (let i = 0; i < need_beta; i++) beta.push(field.zero());
  for (let i = 0; i < beta_block.length; i++) beta[(1 << l) - i] = beta_block[i];
  return _poly_paper_A_fill({ l: l, alpha: a_alpha, beta: beta, S1_2l: S1, S2_2l: S2, Hs: Hs.slice(0, l + 1), field: field });
}

// py: tools/poly_schedule.py:3811
// Coefficient-level encoder for the quadratic base polynomial:
//     H2 = (x + alpha1)*x + alpha0 = x^2 + alpha1*x + alpha0.
function _poly_paper_H2({ x, alpha0, alpha1, field }) {
  x = _poly_trim(x, field);
  if (
    _poly_degree(x) !== 1 ||
    !field.eq(_poly_coeff(x, 1, field), field.one()) ||
    !field.eq(_poly_coeff(x, 0, field), field.zero())
  ) {
    throw new Error('_poly_paper_H2 expects x = [0,1]');
  }
  return [field.coerce(alpha0), field.coerce(alpha1), field.one()];
}

// py: tools/poly_schedule.py:3823
// Coefficient-level square-difference gadget: S1^2 - S2^2.
function _poly_square_diff({ S1, S2, field }) {
  return _poly_sub(_poly_square(S1, field), _poly_square(S2, field), field);
}

// py: tools/poly_schedule.py:3829
// Coefficient-level encoder matching `_paper_Q_2lp1k_minus_1_with_powers`.
// Returns:
//   [Q, Hs_out, tilde_out]
function _poly_paper_Q_2lp1k_minus_1_with_powers({ k, l, alpha, Hs, field }) {
  if (k < 0 || l < 1) throw new Error('Q_2lp1k_minus_1 requires k>=0 and l>=1');
  const x = _poly_trim(Hs[0], field);
  if (
    _poly_degree(x) !== 1 ||
    !field.eq(_poly_coeff(x, 1, field), field.one()) ||
    !field.eq(_poly_coeff(x, 0, field), field.zero())
  ) {
    throw new Error('expected Hs[0]=x');
  }

  let deg = (1 << (l + 1)) * k + ((1 << l) - 1);
  if (deg === 0) {
    if (alpha.length !== 1) throw new Error('degree-0 Q requires 1 parameter');
    const z = [field.coerce(alpha[0])];
    return [z, Hs.slice(), z];
  }
  if (alpha.length !== deg) {
    throw new Error(`Q_2lp1k_minus_1(k=${k},l=${l}) needs ${deg} alpha params, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  if (k === 0) {
    const out = _poly_paper_Q_known_powers({ k: l, alpha: alpha, Hs: Hs.slice(0, l), field: field });
    return [out, Hs.slice(), x];
  }

  if (l === 1) {
    // Special case: Q_{4k+1}(x,H2) using a shifted quadratic input and (x+β0) extraction.
    if (Hs.length < 2) throw new Error('Q_2lp1k_minus_1(l=1) requires Hs=[x,H2]');
    deg = 4 * k + 1;
    if (alpha.length !== deg) {
      throw new Error(`Q_2lp1k_minus_1(k=${k},l=1) needs ${deg} alpha params, got ${alpha.length}`);
    }
    const t_params = alpha.slice(0, 4 * k - 2);
    const tilde_shift = alpha[4 * k - 2];
    const hat_shift = alpha[4 * k - 1];
    const beta0 = alpha[4 * k];

    const H2 = _poly_trim(Hs[1], field);
    const H_hat = _poly_add_const(H2, hat_shift, field);
    const tilde_H2 = _poly_add_const(H_hat, tilde_shift, field);

    const [S1, S2, Hs_out, tilde_out] = _poly_paper_T({
      k: 2 * k, l: 1, alpha: t_params, Hs: [x, H_hat], tilde_H_2l: tilde_H2, field: field,
    });
    const out = _poly_add(_poly_mul(_poly_add_const(x, beta0, field), S1, field), S2, field);
    return [_poly_trim(out, field), Hs_out, tilde_out];
  }

  const block = 1 << l;
  const a_alpha = alpha.slice(0, block - 2); // α0..α_{2^l-3}
  const t_start = block - 2;
  const shift_idx = (1 << (l + 1)) * k - 2; // α_{2^{l+1}k-2}
  const t_params = alpha.slice(t_start, shift_idx); // α_{2^l-2}..α_{2^{l+1}k-3}
  const shift = alpha[shift_idx];

  const qhat_start = shift_idx + 1;
  const qhat_len = (1 << (l - 1)) - 1;
  const qhat_params = alpha.slice(qhat_start, qhat_start + qhat_len);

  const beta_start = qhat_start + qhat_len;
  const beta_len = (1 << (l - 1)) + 1;
  const beta_params = alpha.slice(beta_start, beta_start + beta_len);
  if (beta_params.length !== beta_len || beta_start + beta_len !== alpha.length) {
    throw new Error('internal error: beta param count mismatch in Q_2lp1k_minus_1');
  }

  // \hat H_{2^l} = H_{2^l} + Q_{2^{l-1}-1}(...), for l>=2.
  if (Hs.length <= l) {
    throw new Error(`Q_2lp1k_minus_1(l=${l}) requires Hs up to index ${l} (H_{2^${l}})`);
  }
  let H_hat = _poly_trim(Hs[l], field);
  if (l > 1) {
    const qhat = _poly_paper_Q_known_powers({ k: l - 1, alpha: qhat_params, Hs: Hs.slice(0, l - 1), field: field });
    H_hat = _poly_add(H_hat, qhat, field);
  }

  // Run T_{2k,2^l} with H_{2^l} replaced by \hat H_{2^l}.
  const Hs_hat = Hs.slice();
  if (Hs_hat.length <= l) throw new Error('internal error: Hs_hat too short');
  Hs_hat[l] = H_hat;
  const need_t = (2 * k - 1) * block;
  if (t_params.length !== need_t) {
    throw new Error(`internal error: expected ${need_t} T-params, got ${t_params.length}`);
  }
  const [S1, S2, Hs_out, tilde_out] = _poly_paper_T({
    k: 2 * k, l: l, alpha: t_params, Hs: Hs_hat, tilde_H_2l: _poly_add_const(H_hat, shift, field), field: field,
  });

  // Final fill A_{2^{l-1}} on (S1,S2).
  const A_l = l - 1;
  const A_beta = []; // β0..β_{2^{l-1}}
  for (let i = 0; i < (1 << A_l) + 1; i++) A_beta.push(field.zero());
  for (let i = 0; i < beta_params.length; i++) A_beta[(1 << A_l) - i] = beta_params[i];

  const out = _poly_paper_A_fill({ l: A_l, alpha: a_alpha.slice(), beta: A_beta, S1_2l: S1, S2_2l: S2, Hs: Hs.slice(0, A_l + 1), field: field });
  return [_poly_trim(out, field), Hs_out, tilde_out];
}

// py: tools/poly_schedule.py:3933
function _poly_paper_Q_for_odd_degree_with_powers({ deg, alpha, Hs, field }) {
  if (deg < 1 || deg % 2 === 0) throw new Error('Q_for_odd_degree requires odd deg >= 1');
  const l = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l;
  if (odd % 2 === 0) {
    throw new Error('internal error: expected odd factor (deg+1)/2^l to be odd');
  }
  const k = Math.floor((odd - 1) / 2);
  if (PEELED_Q && deg >= 3 && Hs.length >= 32 - Math.clz32(deg) /* deg.bit_length() */) {
    return [_poly_QO({ deg: deg, alpha: alpha, Hs: Hs, field: field }), Hs.slice(), Hs[0]];
  }
  return _poly_paper_Q_2lp1k_minus_1_with_powers({ k: k, l: l, alpha: alpha, Hs: Hs, field: field });
}

// py: tools/poly_schedule.py:3952
// Coefficient-level encoder matching `_paper_P7` for characteristic != 2.
//
//   y = x * (x + α6)
//   z = (α5 + x + y) * (α4 + x)
//   w = (α3 + z) * x
//   v = (α2 + x + z) * (α1 + w)
//   P7 = α0 + y + w + v
function _poly_paper_P7({ alpha, field }) {
  if (alpha.length !== 7) throw new Error(`P7 needs 7 params, got ${alpha.length}`);
  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error('_poly_paper_P7 only implements the char!=2 variant');
  }
  alpha = alpha.map((a) => field.coerce(a));
  const x = [field.zero(), field.one()];

  const y = _poly_mul(x, _poly_add_const(x, alpha[6], field), field);
  const z = _poly_mul(
    _poly_add_const(_poly_add(_poly_add(x, y, field), [alpha[5]], field), field.zero(), field),
    _poly_add_const(x, alpha[4], field),
    field
  );
  const w = _poly_mul(_poly_add_const(z, alpha[3], field), x, field);
  const v = _poly_mul(
    _poly_add_const(_poly_add(x, z, field), alpha[2], field),
    _poly_add_const(w, alpha[1], field),
    field
  );
  const out = _poly_add(_poly_add(_poly_add_const(y, alpha[0], field), w, field), v, field);
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:3987
// Coefficient-level encoder matching `_paper_P5`:
//
//   P5[α0..α4](x) = (x + α2) * ( (x^2 + α4) * (x^2 + x + α3) + α1 ) + α0
function _poly_paper_P5({ alpha, field }) {
  if (alpha.length !== 5) throw new Error(`P5 needs 5 params, got ${alpha.length}`);
  alpha = alpha.map((a) => field.coerce(a));
  const x = [field.zero(), field.one()];

  const x2 = _poly_square(x, field);
  const z = _poly_mul(
    _poly_add_const(x2, alpha[4], field),
    _poly_add_const(_poly_add(x2, x, field), alpha[3], field),
    field
  );
  const w = _poly_mul(_poly_add_const(x, alpha[2], field), _poly_add_const(z, alpha[1], field), field);
  const out = _poly_add_const(w, alpha[0], field);
  return _poly_trim(out, field);
}

// py: tools/poly_schedule.py:4006
// Coefficient-level encoder matching `_paper_barQ_15` (special case 31 gadget).
function _poly_paper_barQ_15({ alpha, H2, H4, field }) {
  if (alpha.length !== 15) throw new Error(`barQ_15 needs 15 parameters, got ${alpha.length}`);
  alpha = alpha.map((a) => field.coerce(a));
  const x = [field.zero(), field.one()];

  const a_h8 = alpha[0], b_h8 = alpha[1], c_h8 = alpha[2];
  const d_shift = alpha[3];
  const a_alpha = alpha.slice(4, 10);
  const beta = alpha.slice(10, 15);

  const A = _poly_add_const(x, b_h8, field);
  const B = _poly_add_const(_poly_trim(H2, field), c_h8, field);
  const H8 = _poly_add_const(
    _poly_mul(_poly_add(_poly_trim(H4, field), A, field), _poly_add(_poly_trim(H4, field), B, field), field),
    a_h8,
    field
  );
  const S1 = H8;
  const S2 = _poly_add_const(H8, d_shift, field);
  return _poly_paper_A_fill({ l: 2, alpha: a_alpha.slice(), beta: beta.slice(), S1_2l: S1, S2_2l: S2, Hs: [x, H2, H4], field: field });
}

// py: tools/poly_schedule.py:4033
// Coefficient-level encoder matching `_paper_barQ_8k_plus_7_with_powers`.
// Returns:
//   [barQ, Hs_out]
function _poly_paper_barQ_8k_plus_7_with_powers({ k, alpha, H2, H4, field }) {
  if (k < 2) throw new Error('barQ_{8k+7} requires k>=2');
  const deg = 8 * k + 7;
  if (alpha.length !== deg) {
    throw new Error(`barQ_{8k+7} (k=${k}) needs ${deg} parameters, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  const x = [field.zero(), field.one()];

  const [a_h8, b_h8, c_h8, d_tilde] = alpha.slice(0, 4);
  const t_len = (k - 1) * 8;
  const t_params = alpha.slice(4, 4 + t_len);
  const fill = alpha.slice(4 + t_len);
  const a_alpha = fill.slice(0, 6);
  const beta = fill.slice(6);
  if (a_alpha.length !== 6 || beta.length !== 5) {
    throw new Error('internal error: barQ_{8k+7} fill parameter partition mismatch');
  }

  const H8 = _poly_add_const(
    _poly_mul(
      _poly_add(_poly_trim(H4, field), _poly_add_const(x, b_h8, field), field),
      _poly_add(_poly_trim(H4, field), _poly_add_const(_poly_trim(H2, field), c_h8, field), field),
      field
    ),
    a_h8,
    field
  );
  const tilde_H8 = _poly_add_const(H8, d_tilde, field);

  const [S1, S2, Hs_out, _tilde_out] = _poly_paper_T({
    k: k, l: 3, alpha: t_params, Hs: [x, H2, H4, H8], tilde_H_2l: tilde_H8, field: field,
  });
  const out = _poly_paper_A_fill({ l: 2, alpha: a_alpha.slice(), beta: beta.slice(), S1_2l: S1, S2_2l: S2, Hs: [x, H2, H4], field: field });
  return [_poly_trim(out, field), Hs_out.slice()];
}

// py: tools/poly_schedule.py:4084
// Coefficient-level encoder matching `_paper_barQ_odd_with_H2_H4_with_powers`.
function _poly_paper_barQ_odd_with_H2_H4_with_powers({ deg, alpha, Hs_in, field }) {
  if (deg < 1 || deg % 2 === 0) throw new Error('barQ requires odd deg >= 1');
  if (alpha.length !== deg) {
    throw new Error(`barQ_${deg} needs ${deg} alpha params, got ${alpha.length}`);
  }
  if (Hs_in.length < 2) throw new Error('barQ requires Hs_in=[x,H2,...]');
  alpha = alpha.map((a) => field.coerce(a));

  const l_need = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l_need;
  const kk = Math.floor((odd - 1) / 2);
  const need = kk > 0 ? l_need + 1 : l_need;
  if (Hs_in.length >= need) {
    const [q, Hs_out] = _poly_paper_Q_for_odd_degree_with_powers({ deg: deg, alpha: alpha, Hs: Hs_in, field: field });
    return [_poly_trim(q, field), Hs_out.slice()];
  }

  if (Hs_in.length < 3) throw new Error('barQ fallback requires H4 (Hs_in[2]) to be available');
  const x = _poly_trim(Hs_in[0], field);
  const H2 = _poly_trim(Hs_in[1], field);
  const H4 = _poly_trim(Hs_in[2], field);

  if (deg === 15) {
    return [_poly_paper_barQ_15({ alpha: alpha, H2: H2, H4: H4, field: field }), Hs_in.slice()];
  }

  if (deg % 8 === 7 && deg >= 23) {
    const k = Math.floor((deg - 7) / 8);
    const [out, powers_out] = _poly_paper_barQ_8k_plus_7_with_powers({ k: k, alpha: alpha, H2: H2, H4: H4, field: field });
    const Hs_out = Hs_in.slice();
    if (Hs_out.length < powers_out.length) {
      for (const p of powers_out.slice(Hs_out.length)) Hs_out.push(p);
    }
    return [_poly_trim(out, field), Hs_out];
  }

  throw new Error(
    `internal error: no barQ fallback case matched for deg=${deg} (need=${need}, have=${Hs_in.length})`
  );
}

// py: tools/poly_schedule.py:4133
// Coefficient-level encoder matching `_paper_splittable_pair`.
// Returns:
//   [T1, T2, Hs] where Hs[i] is monic degree 2^i, Hs[0]=x.
function _poly_paper_splittable_pair({ n, alpha, field }) {
  if (n < 1 || n % 2 === 0) throw new Error('splittable_pair requires odd n >= 1');
  if (n === 7) {
    throw new Error('no splittable pair is used for n=7; use the septic base construction instead');
  }
  if (alpha.length !== n) throw new Error(`splittable_pair(${n}) needs ${n} params, got ${alpha.length}`);
  alpha = alpha.map((a) => field.coerce(a));

  const x = [field.zero(), field.one()];

  if (n === 1) {
    return [[field.one()], [alpha[0]], [x]];
  }

  if (n === 3) {
    const H2 = _poly_paper_H2({ x: x, alpha0: alpha[1], alpha1: alpha[2], field: field });
    return [H2, _poly_add_const(H2, alpha[0], field), [x, H2]];
  }

  // Special cases.
  if (n === 15) {
    const H2 = _poly_paper_H2({ x: x, alpha0: alpha[6], alpha1: alpha[7], field: field });
    const x_shift = _poly_add_const(x, alpha[5], field);
    const H4 = _poly_add_const(_poly_square_diff({ S1: H2, S2: x_shift, field: field }), alpha[4], field);

    const S1 = _poly_paper_Q_known_powers({ k: 3, alpha: alpha.slice(8, 15), Hs: [x, H2, H4], field: field });
    const S2 = _poly_add_const(H2, alpha[3], field);
    const T1 = _poly_add_const(_poly_square_diff({ S1: S1, S2: S2, field: field }), alpha[1], field);

    // Easier: T2_low = square_diff(H4, H2+α2) + α0.
    const T2_low = _poly_add_const(
      _poly_square_diff({ S1: H4, S2: _poly_add_const(H2, alpha[2], field), field: field }),
      alpha[0],
      field
    );
    const T2 = _poly_add(T2_low, T1, field);
    const H8 = T2_low;
    return [_poly_trim(T1, field), _poly_trim(T2, field), [x, H2, H4, H8]];
  }

  if (n === 27) {
    const H2 = _poly_paper_H2({ x: x, alpha0: alpha[2], alpha1: alpha[3], field: field });
    const [S1, Hs_out] = _poly_paper_Q_2lp1k_minus_1_with_powers({ k: 3, l: 1, alpha: alpha.slice(14, 27), Hs: [x, H2], field: field });
    if (Hs_out.length <= 2) {
      throw new Error('internal error: expected H4 byproduct in Q_13');
    }
    const H4 = Hs_out[2];
    const Hs = [x, H2].concat(Hs_out.slice(2));

    const S2 = _poly_paper_q3({ alpha0: alpha[4], alpha1: alpha[5], alpha2: alpha[6], H2: H2, field: field });
    const S3 = _poly_paper_Q_known_powers({ k: 3, alpha: alpha.slice(7, 14), Hs: [x, H2, H4], field: field });

    const T1 = _poly_add_const(_poly_square_diff({ S1: S1, S2: S2, field: field }), alpha[1], field);
    const T2_low = _poly_add_const(_poly_square_diff({ S1: S3, S2: H2, field: field }), alpha[0], field);
    const T2 = _poly_add(T2_low, T1, field);
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs];
  }

  if (n === 31) {
    const H2 = _poly_paper_H2({ x: x, alpha0: alpha[6], alpha1: alpha[7], field: field });
    const x_shift = _poly_add_const(x, alpha[5], field);
    const H4 = _poly_add_const(_poly_square_diff({ S1: H2, S2: x_shift, field: field }), alpha[4], field);

    const [S1] = _poly_paper_barQ_odd_with_H2_H4_with_powers({
      deg: 15, alpha: alpha.slice(16, 31), Hs_in: [x, H2, H4], field: field,
    });
    const S2 = _poly_paper_Q_known_powers({ k: 3, alpha: alpha.slice(8, 15), Hs: [x, H2, H4], field: field });
    const S3 = _poly_paper_q3({ alpha0: alpha[1], alpha1: alpha[2], alpha2: alpha[3], H2: H2, field: field });
    const T1 = _poly_add(_poly_square_diff({ S1: S1, S2: S2, field: field }), S3, field);

    const T2 = _poly_add_const(
      _poly_square_diff({ S1: _poly_add_const(S1, alpha[15], field), S2: H4, field: field }),
      alpha[0],
      field
    );
    return [_poly_trim(T1, field), _poly_trim(T2, field), [x, H2, H4]];
  }

  // Main families.
  if (n % 4 === 1) {
    const k = Math.floor((n - 1) / 4);
    const t_params = alpha.slice(0, n - 3);
    const tilde_shift = alpha[n - 3];
    const h2_const = alpha[n - 2];
    const h2_lin = alpha[n - 1];

    const H2 = _poly_paper_H2({ x: x, alpha0: h2_const, alpha1: h2_lin, field: field });
    const tilde_H2 = _poly_add_const(H2, tilde_shift, field);
    const [T1, T2, Hs_out] = _poly_paper_T({ k: 2 * k, l: 1, alpha: t_params, Hs: [x, H2], tilde_H_2l: tilde_H2, field: field });
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs_out];
  }

  if (n % 8 === 3) {
    const k = Math.floor((n - 3) / 8);
    const sub_n = 2 * k + 1;
    const [S1_1, S1_2, Hs] = _poly_paper_splittable_pair({ n: sub_n, alpha: alpha.slice(2 * k, 4 * k + 1), field: field });
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 in splittable_pair output');
    }
    const H2 = Hs[1];

    const [S2, Hs2_raw] = _poly_paper_Q_2lp1k_minus_1_with_powers({ k: k, l: 1, alpha: alpha.slice(4 * k + 2, 8 * k + 3), Hs: [x, H2], field: field });
    if (Hs2_raw.length <= 2) {
      throw new Error('internal error: expected an H4 byproduct in Q_{4k+1}');
    }
    let Hs2 = [x, H2].concat(Hs2_raw.slice(2));

    let S3, Hs3;
    if (k === 1) {
      S3 = [alpha[1]];
      Hs3 = Hs2.slice();
    } else {
      const deg3 = 2 * k - 1;
      const res3 = _poly_paper_Q_for_odd_degree_with_powers({ deg: deg3, alpha: alpha.slice(1, 2 * k), Hs: Hs2, field: field });
      S3 = res3[0];
      Hs3 = res3[1];
    }

    if (Hs.length > Hs2.length) {
      Hs2 = Hs2.slice().concat(Hs.slice(Hs2.length));
    }
    if (Hs3.length > Hs2.length) {
      Hs2 = Hs2.slice().concat(Hs3.slice(Hs2.length));
    }

    const T1 = _poly_add(_poly_square_diff({ S1: S2, S2: S1_1, field: field }), S3, field);
    const T2 = _poly_add_const(
      _poly_square_diff({ S1: _poly_add_const(S2, alpha[4 * k + 1], field), S2: S1_2, field: field }),
      alpha[0],
      field
    );
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs2];
  }

  if (n % 8 === 7) {
    const k = Math.floor((n - 7) / 8);
    const sub_n = 2 * k + 1;
    let [S1_1, S1_2, Hs] = _poly_paper_splittable_pair({ n: sub_n, alpha: alpha.slice(0, 2 * k + 1), field: field });
    if (Hs.length < 2) {
      throw new Error('internal error: expected H2 in splittable_pair output for 8k+7 case');
    }
    const H2 = Hs[1];

    function build_Q({ deg, params, Hs_in }) {
      const l = _v2_positive(deg + 1);
      const odd = (deg + 1) >> l;
      const kk = Math.floor((odd - 1) / 2);
      const need = kk > 0 ? l + 1 : l;
      if (Hs_in.length >= need) {
        const [q, Hs_out] = _poly_paper_Q_for_odd_degree_with_powers({ deg: deg, alpha: params, Hs: Hs_in, field: field });
        return [_poly_trim(q, field), Hs_out.slice()];
      }
      const [q, Hs_out] = _poly_paper_barQ_odd_with_H2_H4_with_powers({ deg: deg, alpha: params, Hs_in: Hs_in, field: field });
      return [_poly_trim(q, field), Hs_out.slice()];
    }

    // S2 = Q_{2k+1}[...].
    let res = build_Q({ deg: sub_n, params: alpha.slice(2 * k + 2, 4 * k + 3), Hs_in: Hs });
    const S2 = res[0];
    Hs = res[1];
    if (Hs.length < 3) {
      throw new Error('internal error: expected H4 to remain available after Q_{2k+1}');
    }

    // S3 = Q_{4k+3}[...].
    res = build_Q({ deg: 4 * k + 3, params: alpha.slice(4 * k + 4, 8 * k + 7), Hs_in: Hs });
    const S3 = res[0];
    Hs = res[1];

    const T1 = _poly_add(_poly_square_diff({ S1: S3, S2: S2, field: field }), S1_1, field);
    const S2_shift = _poly_add_const(S2, alpha[2 * k + 1], field);
    const S3_shift = _poly_add_const(S3, alpha[4 * k + 3], field);
    const T2 = _poly_add(_poly_square_diff({ S1: S3_shift, S2: S2_shift, field: field }), S1_2, field);
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs];
  }

  throw new Error(`internal error: no splittable case matched for odd n=${n}`);
}

// py: tools/poly_schedule.py:4296
// Coefficient-level encoder for the full paper family P_n[α].
// Returns coefficient list [a0..a_{n-1}, 1] for the monic polynomial of degree n.
function _poly_paper_P_from_params({ params, field }) {
  if (params.length === 0) throw new Error('params must be non-empty');
  params = params.map((a) => field.coerce(a));
  const n = params.length;

  const x = [field.zero(), field.one()];
  if (n === 1) {
    return _poly_add_const(x, params[0], field);
  }
  if (n === 5) {
    return _poly_paper_P5({ alpha: params, field: field });
  }
  if (n === 7) {
    return _poly_paper_P7({ alpha: params, field: field });
  }
  if (n % 2 === 0) {
    // P_n = α0 + x*P_{n-1}(α1..)
    const q = _poly_paper_P_from_params({ params: params.slice(1), field: field });
    return _poly_add_const(_poly_mul(q, x, field), params[0], field);
  }

  const [T1, T2] = _poly_paper_splittable_pair({ n: n, alpha: params, field: field });
  return _poly_add(_poly_mul(T1, x, field), T2, field);
}

// py: tools/poly_schedule.py:4324
// Coefficient-level encoder matching `_paper_T` (splittable-pair recursion).
//
// This is intended for coefficient-level decoding routines that need to
// re-materialize tail-only / zero-parameter instances (paper "derivable"
// polynomials) without using probing.
//
// Currently only supports char(F) != 2.
// Returns:
//   [T1, T2, Hs_out, tilde_out]
function _poly_paper_T({ k, l, alpha, Hs, tilde_H_2l, field }) {
  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error('_poly_paper_T is not implemented for char(F)=2');
  }

  if (k < 1) throw new Error('T requires k >= 1');
  if (l < 1) throw new Error('T requires l >= 1');
  if (Hs.length <= l) {
    throw new Error(`T(k=${k},l=${l}) requires Hs up to index ${l} (H_{2^${l}})`);
  }

  const block = 1 << l;
  const need = (k - 1) * block;
  if (alpha.length !== need) {
    throw new Error(`T(k=${k},l=${l}) needs ${k - 1}*2^${l}=${need} alpha params, got ${alpha.length}`);
  }
  alpha = alpha.map((a) => field.coerce(a));

  const x = _poly_trim(Hs[0], field);
  tilde_H_2l = _poly_trim(tilde_H_2l, field);

  if (k === 1) {
    return [_poly_trim(Hs[l], field), tilde_H_2l, Hs.slice(), tilde_H_2l];
  }

  // Even k
  if (k % 2 === 0) {
    const rec_len = (Math.floor(k / 2) - 1) * (2 * block);
    const tail = alpha.slice(rec_len);
    const rec_params = alpha.slice(0, rec_len);
    if (tail.length !== block) {
      throw new Error('internal error: T even tail length mismatch');
    }

    if (l === 1) {
      const a0 = tail[0], a1 = tail[1];
      const H2 = _poly_trim(Hs[1], field);
      const x_plus = _poly_add_const(x, a1, field);
      const H4 = _poly_add(_poly_sub(_poly_square(H2, field), _poly_square(x_plus, field), field), [a0], field);
      const Ht2 = _poly_trim(tilde_H_2l, field);
      const delta = _poly_sub(Ht2, H2, field);
      if (_poly_trim(delta, field).length > 1) {
        throw new Error('The shared l=1 base requires tilde_H2-H2 to be scalar');
      }
      const tilde_H4 = _poly_add(H4, delta, field);

      const Hs_next = Hs.slice();
      while (Hs_next.length < 3) Hs_next.push([field.zero()]);
      Hs_next[2] = _poly_trim(H4, field);
      return _poly_paper_T({
        k: Math.floor(k / 2), l: l + 1, alpha: rec_params, Hs: Hs_next, tilde_H_2l: tilde_H4, field: field,
      });
    }

    // l >= 2
    const half = 1 << (l - 1);
    const q_hi = _poly_paper_Q_known_powers({ k: l - 1, alpha: tail.slice(half + 1), Hs: Hs.slice(0, l - 1), field: field });
    const q_lo = _poly_paper_Q_known_powers({ k: l - 1, alpha: tail.slice(1, half), Hs: Hs.slice(0, l - 1), field: field });

    const S1_1 = _poly_add(Hs[l - 1], q_hi, field);
    const S1_2 = _poly_trim(q_lo, field);
    const H_next = _poly_add(_poly_mul(_poly_add(Hs[l], S1_1, field), _poly_sub(Hs[l], S1_1, field), field), S1_2, field);

    const S2_1 = _poly_add_const(Hs[l - 1], tail[half], field);
    const S2_2 = [tail[0]];
    const tilde_next = _poly_add(
      _poly_mul(_poly_add(tilde_H_2l, S2_1, field), _poly_sub(tilde_H_2l, S2_1, field), field),
      S2_2,
      field
    );

    const Hs_next = Hs.slice();
    while (Hs_next.length < l + 2) Hs_next.push([field.zero()]);
    Hs_next[l + 1] = _poly_trim(H_next, field);
    return _poly_paper_T({
      k: Math.floor(k / 2), l: l + 1, alpha: rec_params, Hs: Hs_next, tilde_H_2l: tilde_next, field: field,
    });
  }

  // Odd k
  const m = Math.floor((k - 1) / 2);
  if (l === 2) {
    if (block !== 4) throw new Error('internal error: expected block=4 for l=2');
    const head = alpha.slice(0, 4);
    const tail = alpha.slice(alpha.length - 4);
    const mid = alpha.slice(4, alpha.length - 4);

    const H2 = _poly_trim(Hs[1], field);
    const H4 = _poly_trim(Hs[2], field);

    // Tail parameters follow the shared-product odd base:
    //   tail[0]=α_{4k-8} : shift from H8 to tilde_H8
    //   tail[1]=α_{4k-7} : S1_3
    //   tail[2]=α_{4k-6} : S1_2 shift in (x+α)
    //   tail[3]=α_{4k-5} : shift in S1_1 = H2 + (x+α)
    const next_shift = tail[0], s1_3 = tail[1], s1_2_shift = tail[2], s1_1_shift = tail[3];

    // First branch:
    //   S1_1 = H2 + (x + s1_1_shift)
    //   S1_2 = x + s1_2_shift
    //   S1_3 = s1_3
    const S1_1 = _poly_add(H2, _poly_add_const(x, s1_1_shift, field), field);
    const core = _poly_add(H4, S1_1, field);
    const S1_2 = _poly_add_const(x, s1_2_shift, field);
    const H8 = _poly_add(
      _poly_mul(_poly_add(core, S1_2, field), _poly_sub(core, S1_2, field), field),
      [s1_3],
      field
    );

    const Hs_next = Hs.slice();
    while (Hs_next.length < 4) Hs_next.push([field.zero()]);
    Hs_next[3] = _poly_trim(H8, field);

    const rho = _poly_sub(_poly_trim(tilde_H_2l, field), H4, field);
    if (_poly_trim(rho, field).length > 1) {
      throw new Error('The shared odd l=2 base requires tilde_H4-H4 to be scalar');
    }
    const S2_1 = _poly_sub(S1_1, rho, field);
    const tilde_H8 = _poly_add(H8, [next_shift], field);

    const [T1_rec, T2_rec, Hs_out, tilde_out] = _poly_paper_T({
      k: m, l: l + 1, alpha: mid, Hs: Hs_next, tilde_H_2l: tilde_H8, field: field,
    });

    const q3 = _poly_paper_Q_known_powers({ k: 2, alpha: head.slice(1), Hs: Hs.slice(0, 2), field: field });
    const factor1 = _poly_sub(H4, _poly_scale_int(S1_1, k - 1, field), field);
    const T1 = _poly_add(_poly_mul(factor1, T1_rec, field), q3, field);

    const factor2 = _poly_sub(_poly_trim(tilde_H_2l, field), _poly_scale_int(S2_1, k - 1, field), field);
    const T2 = _poly_add_const(_poly_mul(factor2, T2_rec, field), head[0], field);
    return [_poly_trim(T1, field), _poly_trim(T2, field), Hs_out, tilde_out];
  }

  if (l < 3) throw new Error('T odd case requires l >= 3 (or special l=2)');

  const head = alpha.slice(0, block);
  const tail = alpha.slice(alpha.length - block);
  const mid = alpha.slice(block, alpha.length - block);
  const half = 1 << (l - 1);
  const quarter = 1 << (l - 2);

  const q_hi = _poly_paper_Q_known_powers({ k: l - 1, alpha: tail.slice(half + 1), Hs: Hs.slice(0, l - 1), field: field });
  const S1_1 = _poly_add(Hs[l - 1], q_hi, field);

  const q_mid = _poly_paper_Q_known_powers({ k: l - 2, alpha: tail.slice(quarter + 1, half), Hs: Hs.slice(0, l - 2), field: field });
  const S1_2 = _poly_add(Hs[l - 2], q_mid, field);

  const S1_3 = _poly_paper_Q_known_powers({ k: l - 2, alpha: tail.slice(1, quarter), Hs: Hs.slice(0, l - 2), field: field });

  const base = _poly_add(Hs[l], S1_1, field);
  const H_next = _poly_add(_poly_mul(_poly_add(base, S1_2, field), _poly_sub(base, S1_2, field), field), S1_3, field);

  const S2_1 = _poly_add_const(Hs[l - 1], tail[half], field);
  const S2_2 = _poly_add_const(Hs[l - 2], tail[quarter], field);
  const S2_3 = [tail[0]];
  const base2 = _poly_add(tilde_H_2l, S2_1, field);
  const tilde_next = _poly_add(_poly_mul(_poly_add(base2, S2_2, field), _poly_sub(base2, S2_2, field), field), S2_3, field);

  const Hs_next = Hs.slice();
  while (Hs_next.length < l + 2) Hs_next.push([field.zero()]);
  Hs_next[l + 1] = _poly_trim(H_next, field);

  const [T1_rec, T2_rec, Hs_out, tilde_out] = _poly_paper_T({
    k: m, l: l + 1, alpha: mid, Hs: Hs_next, tilde_H_2l: tilde_next, field: field,
  });

  const q_low = _poly_paper_Q_known_powers({ k: l, alpha: head.slice(1), Hs: Hs.slice(0, l), field: field });
  const factor1 = _poly_sub(Hs[l], _poly_scale_int(S1_1, k - 1, field), field);
  const T1 = _poly_add(_poly_mul(factor1, T1_rec, field), q_low, field);

  const factor2 = _poly_sub(tilde_H_2l, _poly_scale_int(S2_1, k - 1, field), field);
  const T2 = _poly_add_const(_poly_mul(factor2, T2_rec, field), head[0], field);
  return [_poly_trim(T1, field), _poly_trim(T2, field), Hs_out, tilde_out];
}

// py: tools/poly_schedule.py:4515
// Compute the proof-remainder polynomial:
//     P_R := x (T^{(1)}_{k,2^l} - H_{2^l}^k) + (T^{(2)}_{k,2^l} - \tilde H_{2^l}^k)
// for the coefficient-level `_poly_paper_T` encoder.
function _poly_remainder_poly_from_T({ k, l, alpha, Hs, tilde_H_2l, field }) {
  const x = _poly_trim(Hs[0], field);
  const H_base = _poly_trim(Hs[l], field);
  const [T1, T2] = _poly_paper_T({ k: k, l: l, alpha: alpha, Hs: Hs, tilde_H_2l: tilde_H_2l, field: field });

  const H_pow = _poly_pow(H_base, k, field);
  const Ht_pow = _poly_pow(_poly_trim(tilde_H_2l, field), k, field);
  const left = _poly_shift_xk(_poly_sub(T1, H_pow, field), 1, field);
  const right = _poly_sub(T2, Ht_pow, field);
  return _poly_add(left, right, field);
}
