// g6_decode_Rk.frag.js — R_k remainder decoders (paper alg:decode-Rk2l).
// Fragment: function declarations only; assembled into core.js after
// runtime.frag.js.  Cross-group callees (supplied by other fragments):
//   _poly_paper_T, _poly_remainder_poly_from_T                      (g3)
//   _recover_monic_factor_high_coeffs_from_product (returns a
//     Map<number, field element>, mirror of Python Dict[int, Number]),
//   _scalar_shift_from_square_boundary, _decode_by_descending_pivots,
//   _decode_Q_power_of_2_minus_1_coeffs_to_alpha                    (g4)

// JS-only private helper standing in for Python's math.comb (exact for the
// small arguments used here: r <= 5, products well below 2^53).
function _g6_math_comb(n, r) {
  if (r < 0 || n < 0 || r > n) return 0;
  let res = 1;
  for (let i = 0; i < r; i++) {
    // res == C(n, i), so res * (n - i) is divisible by (i + 1): exact.
    res = (res * (n - i)) / (i + 1);
  }
  return res;
}

// py: tools/poly_schedule.py:4541
// Decode the remainder polynomial `P_R = x R^{(1)}_{k,2^l} + R^{(2)}_{k,2^l}`.
//
// Returns:
//   [alpha_block, Hs_out, tilde_out]
//
// This is a coefficient-level port of the paper-shaped peeling decoders in
// `tools/impl/splittable_decode.py`, but restricted (for now) to the even-k
// branch. Odd-k decoding is not implemented yet.
function _decode_R_k({ k, l, P_R, Hs, tilde_H_2l, field }) {
  if (k < 1) throw new Error('k must be >= 1');
  if (l < 1) throw new Error('l must be >= 1');
  if (Hs.length <= l) throw new Error('Hs must include H_{2^l} at index l');

  if (k === 1) return [[], Hs.slice(), _poly_trim(tilde_H_2l, field)];
  if (k % 2 !== 0) {
    return _decode_R_odd_k({ k, l, P_R, Hs, tilde_H_2l, field });
  }

  return _decode_R_even_k({ k, l, P_R, Hs, tilde_H_2l, field });
}

// py: tools/poly_schedule.py:4576
// Even-k branch of `_decode_R_k` (paper Algorithm `alg:decode-Rk2l` / Lemma R_{k,2^l}).
//
// Handles both the shared l==1 base (`alg:constr-Tk2l-base`) and l>=2.
function _decode_R_even_k({ k, l, P_R, Hs, tilde_H_2l, field }) {
  if (k < 2 || k % 2 !== 0) throw new Error('decode_R_even_k expects even k>=2');

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) throw new Error('R-decoding requires char(F) != 2');
  const inv2 = field.inv(two);

  if (l === 1) {
    // Shared even-k l==1 base (`alg:constr-Tk2l-base`):
    //   H4 = H2^2 - (x + a1)^2 + a0,   tilde_H4 = H4 + (tilde_H2 - H2).
    // The two tail scalars are descending affine pivots of P_R at degrees
    // 2k-2 and 2k-3; at degree 2k-3 the inner remainder contributes only
    // through its constant leading coefficient (`lem:Rk2l-leading-coeff`),
    // so probing the tail-only remainder encoder yields exact pivot data.
    P_R = _poly_trim(P_R, field);
    const H2 = _poly_trim(Hs[1], field);
    const tilde_H2 = _poly_trim(tilde_H_2l, field);
    if (_poly_degree(H2) !== 2 || !field.eq(_poly_coeff(H2, 2, field), field.one())) {
      throw new Error('expected monic degree-2 H2 for l==1 remainder decoder');
    }
    if (_poly_degree(tilde_H2) !== 2 || !field.eq(_poly_coeff(tilde_H2, 2, field), field.one())) {
      throw new Error('expected monic degree-2 tilde_H2 for l==1 remainder decoder');
    }
    const delta = _poly_trim(_poly_sub(tilde_H2, H2, field), field);
    if (_poly_degree(delta) > 0) {
      throw new Error('the shared l==1 base requires tilde_H2 - H2 to be a scalar');
    }

    const m_int = Math.floor(k / 2);
    const total = (k - 1) * 2;
    const x = [field.zero(), field.one()];

    function _tail_remainder(a0, a1) {
      const al = new Array(total).fill(field.zero());
      al[total - 2] = a0;
      al[total - 1] = a1;
      return _poly_remainder_poly_from_T({ k, l: 1, alpha: al, Hs, tilde_H_2l: tilde_H2, field });
    }

    const tail_vals = [field.zero(), field.zero()]; // (a0, a1)
    for (const [idx, row] of [[1, 2 * k - 2], [0, 2 * k - 3]]) {
      const base = _tail_remainder(tail_vals[0], tail_vals[1]);
      const probe_vals = tail_vals.slice();
      probe_vals[idx] = field.add(probe_vals[idx], field.one());
      const probe = _tail_remainder(probe_vals[0], probe_vals[1]);
      const slope = field.sub(_poly_coeff(probe, row, field), _poly_coeff(base, row, field));
      if (field.is_zero(slope)) {
        throw new Error('l==1 even decoder: zero pivot slope (field not admissible?)');
      }
      tail_vals[idx] = field.div(
        field.sub(_poly_coeff(P_R, row, field), _poly_coeff(base, row, field)), slope
      );
    }
    const alpha_const = tail_vals[0], alpha_shift = tail_vals[1];

    // Build (H4, tilde_H4) and isolate the inner remainder exactly.
    const x_plus = _poly_add_const(x, alpha_shift, field);
    const H4 = _poly_add(_poly_sub(_poly_square(H2, field), _poly_square(x_plus, field), field), [alpha_const], field);
    const tilde_H4 = _poly_trim(_poly_add(H4, delta, field), field);

    const base_poly = _poly_add(
      _poly_shift_xk(_poly_sub(_poly_pow(H4, m_int, field), _poly_pow(H2, k, field), field), 1, field),
      _poly_sub(_poly_pow(tilde_H4, m_int, field), _poly_pow(tilde_H2, k, field), field),
      field
    );
    const P_inner = _poly_sub(P_R, base_poly, field);

    let inner_alphas = [];
    let Hs_out = [Hs[0], H2, _poly_trim(H4, field)];
    let tilde_out = tilde_H4;
    if (m_int > 1) {
      [inner_alphas, Hs_out, tilde_out] = _decode_R_k({
        k: m_int, l: 2, P_R: P_inner, Hs: [Hs[0], H2, _poly_trim(H4, field)], tilde_H_2l: tilde_H4, field,
      });
    }

    const full = inner_alphas.concat([alpha_const, alpha_shift]);
    if (full.length !== total) {
      throw new Error('internal: decoded alpha count mismatch (l==1 even decoder)');
    }
    return [full, Hs_out, tilde_out];
  }

  // l>=2 branch
  const D = 1 << l;
  const total = (k - 1) * D;
  const d = (k - 2) * D;
  const m = Math.floor(k / 2);
  const inv_m = field.inv(field.coerce(m));

  P_R = _poly_trim(P_R, field);
  const H = _poly_trim(Hs[l], field);
  const H_half = _poly_trim(Hs[l - 1], field);
  tilde_H_2l = _poly_trim(tilde_H_2l, field);

  const H_pow = _poly_pow(H, k - 2, field);
  const Ht_pow = _poly_pow(tilde_H_2l, k - 2, field);

  // Stage 1: recover S1_1 from the top window (> d + D/2) by peeling the monic factor.
  const known_tilde_top = _poly_scale_int(_poly_mul(_poly_square(H_half, field), Ht_pow, field), -1, field);

  const max_prod_deg = d + D;
  const prod = new Array(max_prod_deg + 1).fill(field.zero());
  for (let u_deg = D; u_deg >= Math.floor(D / 2); u_deg--) {
    const p_deg = d + u_deg;
    const pr_deg = p_deg + 1;
    const rhs = field.sub(field.mul(_poly_coeff(P_R, pr_deg, field), inv_m), _poly_coeff(known_tilde_top, pr_deg, field));
    prod[p_deg] = field.neg(rhs);
  }

  const S1_1_sq_high = _recover_monic_factor_high_coeffs_from_product({
    product: prod,
    known_factor: H_pow,
    factor_deg: D,
    min_deg: Math.floor(D / 2),
    field,
  });
  const S1_1_sq_poly = new Array(D + 1).fill(field.zero());
  for (const [deg_i, coeff_i] of S1_1_sq_high) {
    S1_1_sq_poly[deg_i] = field.coerce(coeff_i);
  }
  S1_1_sq_poly[D] = field.one();
  const S1_1 = _monic_sqrt_from_high_square_coeffs(S1_1_sq_poly, Math.floor(D / 2), field);

  // Decode the embedded Q_{2^{l-1}-1} block in S1_1: Q_hi = S1_1 - H_half.
  const Q_hi = _poly_sub(S1_1, H_half, field);
  const k_q = l - 1;
  const q_hi_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: Q_hi, k: k_q, Hs: Hs.slice(0, l - 1), field });

  // Stage 1.5: recover scalar shift s in S2_1 = H_half + s from the boundary degree.
  const target_deg = d + Math.floor(D / 2);
  const C_tdeg = field.mul(_poly_coeff(P_R, target_deg, field), inv_m);
  const x_neg_s1_sq_hpow = _poly_shift_xk(
    _poly_scale_int(_poly_mul(_poly_square(S1_1, field), H_pow, field), -1, field), 1, field
  );
  const tilde_base = _poly_coeff(known_tilde_top, target_deg, field);
  const s2_1_shift = field.mul(field.sub(field.add(field.add(_poly_coeff(x_neg_s1_sq_hpow, target_deg, field), field.one()), tilde_base), C_tdeg), inv2);
  const S2_1 = _poly_add_const(H_half, s2_1_shift, field);
  const tilde_term = _poly_scale_int(_poly_mul(_poly_square(S2_1, field), Ht_pow, field), -1, field);

  // Stage 2: recover S1_2 coefficients in degrees >= 1 via monic-factor peeling.
  const factor_deg = Math.floor(D / 2) - 1;
  const prod2 = new Array(d + Math.floor(D / 2) + 1).fill(field.zero());
  for (let u_deg = Math.floor(D / 2) - 1; u_deg >= 1; u_deg--) {
    const pr_deg = d + u_deg + 1;
    if (pr_deg <= d + 1) continue;
    const C_pr = field.mul(_poly_coeff(P_R, pr_deg, field), inv_m);
    const known = field.add(_poly_coeff(x_neg_s1_sq_hpow, pr_deg, field), _poly_coeff(tilde_term, pr_deg, field));
    const rhs = field.sub(C_pr, known);
    prod2[pr_deg - 1] = rhs;
  }

  const S1_2_high = _recover_monic_factor_high_coeffs_from_product({
    product: prod2,
    known_factor: H_pow,
    factor_deg,
    min_deg: 1,
    field,
  });
  let S1_2_no_const = new Array(factor_deg + 1).fill(field.zero());
  for (const [deg_i, coeff_i] of S1_2_high) {
    if (deg_i <= factor_deg) {
      S1_2_no_const[deg_i] = field.coerce(coeff_i);
    }
  }
  S1_2_no_const[0] = field.zero();
  S1_2_no_const = _poly_trim(S1_2_no_const, field);

  // Boundary degrees: solve the constant term of S1_2 and the scalar S2_2.
  //
  // We compute the paper's boundary-error coefficients (e_{d+1}, e_d) using an
  // auxiliary assignment where:
  //   - recursive block is 0 (prefix all zeros),
  //   - S2_2 is 0,
  //   - and S1_2 is any monic polynomial with the recovered high coefficients
  //     and constant term forced to 0 (so it's still a valid Q instance by decodability).
  const q_lo_params_aux = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
    Q: S1_2_no_const, k: k_q, Hs: Hs.slice(0, l - 1), field,
  });
  const tail = new Array(D).fill(field.zero());
  tail[0] = field.zero(); // S2_2 scalar forced to 0
  for (const [i, v] of q_lo_params_aux.entries()) {
    tail[1 + i] = v;
  }
  tail[Math.floor(D / 2)] = s2_1_shift;
  for (const [i, v] of q_hi_params.entries()) {
    tail[Math.floor(D / 2) + 1 + i] = v;
  }

  const alphas_aux = new Array(total).fill(field.zero());
  for (let i = 0; i < D; i++) {
    alphas_aux[d + i] = tail[i];
  }
  const P_aux = _poly_remainder_poly_from_T({ k, l, alpha: alphas_aux, Hs, tilde_H_2l, field });

  const C_aux = _poly_add(
    _poly_shift_xk(_poly_mul(_poly_add(_poly_scale_int(_poly_square(S1_1, field), -1, field), S1_2_no_const, field), H_pow, field), 1, field),
    _poly_mul(_poly_scale_int(_poly_square(S2_1, field), -1, field), Ht_pow, field),
    field
  );
  const E_aux = _poly_sub(P_aux, _poly_scale_int(C_aux, m, field), field);
  const e_d1 = _poly_coeff(E_aux, d + 1, field);
  const e_d0 = _poly_coeff(E_aux, d, field);

  // Solve s1_2_0 from degree d+1.
  const C_d1 = field.mul(field.sub(_poly_coeff(P_R, d + 1, field), e_d1), inv_m);
  const known_d1 = field.add(_poly_coeff(x_neg_s1_sq_hpow, d + 1, field), _poly_coeff(tilde_term, d + 1, field));
  const prod_d = field.sub(C_d1, known_d1); // equals [x^d](S1_2*H_pow)
  const prod_known = _poly_coeff(_poly_mul(S1_2_no_const, H_pow, field), d, field);
  const s1_2_0 = field.sub(prod_d, prod_known);
  const S1_2 = _poly_add_const(S1_2_no_const, s1_2_0, field);

  // Solve S2_2 scalar from degree d.
  const C_d0 = field.mul(field.sub(_poly_coeff(P_R, d, field), e_d0), inv_m);
  const x_s1_2_hpow_d0 = _poly_coeff(_poly_shift_xk(_poly_mul(S1_2, H_pow, field), 1, field), d, field);
  const known_d0 = field.add(field.add(_poly_coeff(x_neg_s1_sq_hpow, d, field), x_s1_2_hpow_d0), _poly_coeff(tilde_term, d, field));
  const s2_2_scalar = field.sub(C_d0, known_d0);

  // Decode q_lo parameters from the fully recovered S1_2.
  const q_lo_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: S1_2, k: k_q, Hs: Hs.slice(0, l - 1), field });

  // Assemble the tail alphas in the exact layout used by `_paper_T` (even case l>=2).
  const tail_out = new Array(D).fill(field.zero());
  tail_out[0] = s2_2_scalar;
  for (const [i, v] of q_lo_params.entries()) {
    tail_out[1 + i] = v;
  }
  tail_out[Math.floor(D / 2)] = s2_1_shift;
  for (const [i, v] of q_hi_params.entries()) {
    tail_out[Math.floor(D / 2) + 1 + i] = v;
  }

  // Build H_{2^{l+1}} and \tilde H_{2^{l+1}} from the decoded tail, using the k=2 instance.
  const [T1_tail, T2_tail, Hs_out_tail, tilde_out_tail] = _poly_paper_T({
    k: 2, l, alpha: tail_out, Hs, tilde_H_2l, field,
  });
  const H_next = _poly_trim(Hs_out_tail[l + 1], field);
  const H_tilde_next = _poly_trim(tilde_out_tail, field);

  // Isolate the prefix remainder polynomial by subtracting the tail-only remainder,
  // then compensate by adding the zero-parameter recursive remainder (boundary correction).
  const tail_only = new Array(total).fill(field.zero());
  for (let i = 0; i < D; i++) {
    tail_only[d + i] = tail_out[i];
  }
  const P_tail = _poly_remainder_poly_from_T({ k, l, alpha: tail_only, Hs, tilde_H_2l, field });

  let prefix = [];
  let P_prefix = _poly_sub(P_R, P_tail, field);
  let Hs_out_final, tilde_out_final;
  if (m > 1) {
    const P_inner0 = _poly_remainder_poly_from_T({
      k: m, l: l + 1, alpha: new Array(d).fill(field.zero()), Hs: Hs.concat([H_next]), tilde_H_2l: H_tilde_next, field,
    });
    P_prefix = _poly_add(P_prefix, P_inner0, field);

    const [inner_alpha, Hs_out, tilde_out] = _decode_R_k({
      k: m, l: l + 1, P_R: P_prefix, Hs: Hs.concat([H_next]), tilde_H_2l: H_tilde_next, field,
    });
    if (inner_alpha.length !== d) {
      throw new Error('internal: prefix length mismatch in even-k decoder');
    }
    prefix = inner_alpha;
    Hs_out_final = Hs_out;
    tilde_out_final = tilde_out;
  } else {
    Hs_out_final = Hs.concat([H_next]);
    tilde_out_final = H_tilde_next;
  }

  const alpha_out = prefix.concat(tail_out);
  if (alpha_out.length !== total) {
    throw new Error('internal: decoded alpha count mismatch in even-k decoder');
  }
  return [alpha_out, Hs_out_final, tilde_out_final];
}

// py: tools/poly_schedule.py:4846
// Coefficient helper for the odd-k branch of `R_{k,2^l}` decoding.
//
// Matches `tools/impl/splittable_decode.py:_hatR1_combined_coeff_at_degree` in
// coefficient-list arithmetic:
//
//   \hat R^{(1)}_1 = sum_{i=3}^{k-1} binom(k-1,i) H^{k-i} S1_1^i
//                    - (k-1) sum_{i=2}^{k-1} binom(k-1,i) H^{k-i-1} S1_1^{i+1}
//   \hat R^{(2)}_1 = same with (H_tilde,S2_1)
//
// Returns coeff( x*\hat R^{(1)}_1 + \hat R^{(2)}_1, deg ).
//
// We truncate to i<=4, which suffices for the boundary degrees used by the
// proof/decoder (higher i cannot reach those degrees by degree reasons).
function _hatR1_combined_coeff_at_degree({ k, H, S1_1, H_tilde, S2_1, deg, field }) {
  if (k < 3 || k % 2 === 0) throw new Error('_hatR1 helper requires odd k>=3');
  if (deg < 0) return field.zero();

  H = _poly_trim(H, field);
  S1_1 = _poly_trim(S1_1, field);
  H_tilde = _poly_trim(H_tilde, field);
  S2_1 = _poly_trim(S2_1, field);

  const i_max = Math.min(4, k - 1);

  let hat1 = [field.zero()];
  for (let i = 3; i <= i_max; i++) {
    const term = _poly_mul(_poly_pow(H, k - i, field), _poly_pow(S1_1, i, field), field);
    hat1 = _poly_add(hat1, _poly_scale_int(term, _g6_math_comb(k - 1, i), field), field);
  }
  for (let i = 2; i <= i_max; i++) {
    if (k - i - 1 < 0) continue;
    const term = _poly_mul(_poly_pow(H, k - i - 1, field), _poly_pow(S1_1, i + 1, field), field);
    hat1 = _poly_sub(hat1, _poly_scale_int(term, (k - 1) * _g6_math_comb(k - 1, i), field), field);
  }

  let hat2 = [field.zero()];
  for (let i = 3; i <= i_max; i++) {
    const term = _poly_mul(_poly_pow(H_tilde, k - i, field), _poly_pow(S2_1, i, field), field);
    hat2 = _poly_add(hat2, _poly_scale_int(term, _g6_math_comb(k - 1, i), field), field);
  }
  for (let i = 2; i <= i_max; i++) {
    if (k - i - 1 < 0) continue;
    const term = _poly_mul(_poly_pow(H_tilde, k - i - 1, field), _poly_pow(S2_1, i + 1, field), field);
    hat2 = _poly_sub(hat2, _poly_scale_int(term, (k - 1) * _g6_math_comb(k - 1, i), field), field);
  }

  const combined = _poly_add(_poly_shift_xk(hat1, 1, field), hat2, field);
  return _poly_coeff(combined, deg, field);
}

// py: tools/poly_schedule.py:4908
// Odd-k branch of `_decode_R_k` (paper Algorithm `alg:decode-Rk2l` / Lemma `lem:Rk2l`).
//
// Structure:
//   - `l == 2` (shared-product base, Algorithm `alg:constr-Tk2l-base`, odd
//     branch): the four tail scalars u,v,w,z are recovered from the four
//     descending affine pivots of `P_R` at degrees d-1..d-4 (d = 4(k-1)),
//     whose slopes are -k(k-1), -(k-1), m, m -- the pivot table in the
//     shared-base part of the proof of `lem:Rk2l`.
//   - `l >= 3`: the tail block is recovered by the stage-1/stage-2 window
//     peeling of the proof of `lem:Rk2l` (`lem:peel-monic-factor`,
//     `lem:monic-from-power` with m=2, `lem:scalar-shift-square`).
//   - In both cases the remaining head+mid parameters are then extracted by
//     descending affine pivots of the frozen-tail remainder map
//     (`_decode_by_descending_pivots`); this realizes the Multiplicativity /
//     Additivity certificate steps of `alg:decode-Rk2l` numerically.
function _decode_R_odd_k({ k, l, P_R, Hs, tilde_H_2l, field }) {
  if (k < 3 || k % 2 === 0) throw new Error('decode_R_odd_k expects odd k>=3');
  if (l < 2) throw new Error('odd-k remainder decoding requires l>=2');
  if (Hs.length <= l) throw new Error('Hs must include H_{2^l} at index l');

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) throw new Error('odd-k remainder decoding requires char(F) != 2');
  const inv2 = field.inv(two);

  const three = field.coerce(3);
  if (field.is_zero(three)) {
    throw new Error('odd-k remainder decoding currently requires char(F) != 3');
  }
  const inv3 = field.inv(three);

  const D = 1 << l;
  const total = (k - 1) * D;
  const k_half = Math.floor((k - 1) / 2);
  const m = field.coerce(k_half);
  if (field.is_zero(m)) {
    throw new Error('odd-k remainder decoding requires (k-1)/2 invertible in the field');
  }
  const inv_m = field.inv(m);

  P_R = _poly_trim(P_R, field);
  const H = _poly_trim(Hs[l], field);
  const H_tilde = _poly_trim(tilde_H_2l, field);
  const H_half = _poly_trim(Hs[l - 1], field);
  const H_quarter = _poly_trim(Hs[l - 2], field);

  let tail_out;
  if (l === 2) {
    // Shared-product odd base.  Check the admissibility precondition
    // tilde_H4 - H4 scalar, then run the four tail pivots.
    const rho = _poly_trim(_poly_sub(H_tilde, H, field), field);
    if (_poly_degree(rho) > 0) {
      throw new Error('the shared odd l==2 base requires tilde_H4 - H4 to be a scalar');
    }

    const d = total;
    // Tail layout (alpha[total-4:total]): [z, w, v, u] with
    //   u = alpha_{4k-5} (S1_1 shift), v = alpha_{4k-6} (S1_2 shift),
    //   w = alpha_{4k-7} (S1_3),       z = alpha_{4k-8} (tilde_H8 shift).
    const expected_slopes = { 1: -k * (k - 1), 2: -(k - 1), 3: k_half, 4: k_half };

    function _tail_remainder(vals) {
      const al = new Array(total).fill(field.zero());
      for (const [i, v] of vals.entries()) {
        al[total - 4 + i] = v;
      }
      return _poly_remainder_poly_from_T({ k, l: 2, alpha: al, Hs, tilde_H_2l: H_tilde, field });
    }

    const tail_vals = new Array(4).fill(field.zero());
    for (const j of [1, 2, 3, 4]) {
      const row = d - j;
      const base = _tail_remainder(tail_vals);
      const probe_vals = tail_vals.slice();
      probe_vals[4 - j] = field.add(probe_vals[4 - j], field.one());
      const probe = _tail_remainder(probe_vals);
      const slope = field.sub(_poly_coeff(probe, row, field), _poly_coeff(base, row, field));
      if (field.is_zero(slope)) {
        throw new Error('l==2 odd base: zero pivot slope (field not admissible?)');
      }
      if (!field.eq(slope, field.coerce(expected_slopes[j]))) {
        throw new Error('l==2 odd base: pivot slope does not match the lem:Rk2l table');
      }
      tail_vals[4 - j] = field.div(
        field.sub(_poly_coeff(P_R, row, field), _poly_coeff(base, row, field)), slope
      );
    }
    tail_out = tail_vals.slice();
  } else {
    // Stage 1: recover S1_1 (monic degree D/2).
    const c1 = field.mul(field.mul(field.coerce(k), field.coerce(k - 1)), inv2); // k(k-1)/2
    if (field.is_zero(c1)) {
      throw new Error('odd-k remainder decoding requires k(k-1)/2 invertible in the field');
    }
    const inv_c1 = field.inv(c1);

    const H_pow = _poly_pow(H, k - 2, field);
    const Ht_pow = _poly_pow(H_tilde, k - 2, field);

    const known_R2_top = _poly_mul(_poly_mul(_poly_square(H_half, field), Ht_pow, field), [field.neg(c1)], field);

    const prod1 = new Array((k - 1) * D + 1).fill(field.zero()); // degrees 0..(k-1)D
    const cubic_top = field.mul(field.coerce(k * (k - 1) * (k - 2)), inv3); // k(k-1)(k-2)/3
    for (let d = (k - 1) * D; d >= (k - 2) * D + Math.floor(D / 2); d--) {
      const pr_deg = d + 1;
      let rhs = field.sub(_poly_coeff(P_R, pr_deg, field), _poly_coeff(known_R2_top, pr_deg, field));
      if (d === (k - 2) * D + Math.floor(D / 2)) {
        // Boundary correction: stage-2 contributes -m at this top degree and
        // the x-shifted cubic term contributes -cubic_top.
        rhs = field.add(rhs, field.add(field.coerce(k_half), cubic_top));
      }
      prod1[d] = field.mul(field.neg(rhs), inv_c1);
    }

    const U1_high = _recover_monic_factor_high_coeffs_from_product({
      product: prod1,
      known_factor: H_pow,
      factor_deg: D,
      min_deg: Math.floor(D / 2),
      field,
    });
    const U1_poly = new Array(D + 1).fill(field.zero());
    for (const [deg_i, coeff_i] of U1_high) {
      U1_poly[deg_i] = field.coerce(coeff_i);
    }
    U1_poly[D] = field.one();
    const S1_1 = _monic_sqrt_from_high_square_coeffs(_poly_trim(U1_poly, field), Math.floor(D / 2), field);

    const Q_hi = _poly_sub(S1_1, H_half, field);
    const q_hi_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: Q_hi, k: l - 1, Hs: Hs.slice(0, l - 1), field });

    // Precompute K1 (depends only on H and S1_1).
    const K1 = _poly_mul(
      _poly_sub(H, _poly_scale_int(S1_1, k - 1, field), field),
      _poly_pow(_poly_add(H, S1_1, field), k - 3, field),
      field
    );
    const degK1 = _poly_degree(K1);
    if (degK1 !== (k - 2) * D) {
      throw new Error('internal: unexpected deg(K1) in odd-k decoder');
    }

    // Stage 1.5: recover the scalar shift in S2_1 = H_half + s.
    const deg_shift = (k - 2) * D + Math.floor(D / 2);
    const stage1_x = _poly_shift_xk(
      _poly_mul(_poly_mul(_poly_square(S1_1, field), H_pow, field), [field.neg(c1)], field),
      1,
      field
    );
    const cubic_coeff = field.neg(cubic_top);
    const cubic_x = _poly_shift_xk(
      _poly_mul(_poly_mul(_poly_pow(H, k - 3, field), _poly_pow(S1_1, 3, field), field), [cubic_coeff], field),
      1,
      field
    );

    // Stage-2 contribution at deg_shift uses only the top 2 coefficients of G1 and K1.
    // Leading G1 coefficient is -1; next is -2*a where a = [x^{D/4-1}]S1_2 and
    // S1_2's top-two coefficients are known from H_quarter and monicity.
    const D4 = Math.floor(D / 4);
    const a_s1_2 = field.add(_poly_coeff(H_quarter, D4 - 1, field), field.one());
    const g1k1_deg_shift_minus1 = field.sub(field.neg(_poly_coeff(K1, degK1 - 1, field)), _field_mul_int(field, a_s1_2, 2));
    const stage2_at_deg_shift = field.mul(m, field.sub(g1k1_deg_shift_minus1, field.one()));

    // Also subtract the tilde-side cubic top coefficient at this degree: cubic_coeff.
    let coeff_stage1_tilde_boundary = field.sub(_poly_coeff(P_R, deg_shift, field), _poly_coeff(stage1_x, deg_shift, field));
    coeff_stage1_tilde_boundary = field.sub(coeff_stage1_tilde_boundary, _poly_coeff(cubic_x, deg_shift, field));
    coeff_stage1_tilde_boundary = field.sub(coeff_stage1_tilde_boundary, cubic_coeff);
    coeff_stage1_tilde_boundary = field.sub(coeff_stage1_tilde_boundary, stage2_at_deg_shift);

    const s2_1_shift = _scalar_shift_from_square_boundary({
      coeff_P_at_boundary: coeff_stage1_tilde_boundary,
      H: H_half,
      M: Ht_pow,
      lam: field.neg(c1),
      field,
    });
    const S2_1 = _poly_add_const(H_half, s2_1_shift, field);

    // Stage 2: recover U=(S1_2)^2 - S1_3 and the scalar shift in S2_2 = H_quarter + t.
    const K2 = _poly_mul(
      _poly_sub(H_tilde, _poly_scale_int(S2_1, k - 1, field), field),
      _poly_pow(_poly_add(H_tilde, S2_1, field), k - 3, field),
      field
    );
    const degK2 = _poly_degree(K2);
    if (degK2 !== (k - 2) * D) {
      throw new Error('internal: unexpected deg(K2) in odd-k decoder');
    }

    const stage1_tilde = _poly_mul(_poly_mul(_poly_square(S2_1, field), Ht_pow, field), [field.neg(c1)], field);
    const cubic_tilde = _poly_mul(
      _poly_mul(_poly_pow(H_tilde, k - 3, field), _poly_pow(S2_1, 3, field), field),
      [cubic_coeff],
      field
    );
    const known_stage12 = _poly_add(_poly_add(stage1_x, stage1_tilde, field), _poly_add(cubic_x, cubic_tilde, field), field);

    // High part of G2 is independent of t and equals -H_quarter^2 in degrees > D/4.
    const Hq2 = _poly_square(H_quarter, field);
    const g2_high = new Array(Math.floor(D / 2) + 1).fill(field.zero());
    for (let i = D4 + 1; i <= Math.floor(D / 2); i++) {
      g2_high[i] = field.neg(_poly_coeff(Hq2, i, field));
    }
    const g2_high_term = _poly_mul(g2_high, K2, field);

    const prod2 = new Array((k - 2) * D + Math.floor(D / 2) + 1).fill(field.zero());
    for (let d = (k - 2) * D + Math.floor(D / 2); d >= (k - 2) * D + D4; d--) {
      const pr_deg = d + 1;
      let rhs = field.sub(_poly_coeff(P_R, pr_deg, field), _poly_coeff(known_stage12, pr_deg, field));
      rhs = field.mul(rhs, inv_m);
      rhs = field.sub(rhs, _poly_coeff(g2_high_term, pr_deg, field));
      prod2[d] = field.neg(rhs);
    }

    const U_high = _recover_monic_factor_high_coeffs_from_product({
      product: prod2,
      known_factor: K1,
      factor_deg: Math.floor(D / 2),
      min_deg: D4,
      field,
    });
    const U_poly = new Array(Math.floor(D / 2) + 1).fill(field.zero());
    for (const [deg_i, coeff_i] of U_high) {
      U_poly[deg_i] = field.coerce(coeff_i);
    }
    U_poly[Math.floor(D / 2)] = field.one();
    const S1_2 = _monic_sqrt_from_high_square_coeffs(_poly_trim(U_poly, field), D4, field);

    let Q_mid = _poly_sub(S1_2, H_quarter, field);
    let q_mid_params;
    if (l === 2) {
      // In the special base construction at l==2 (Alg. `alg:constr-Tk2l-base`, odd branch),
      // S1_2 is fixed to x and carries no Q_{2^{l-2}-1} parameter block.
      Q_mid = _poly_trim(Q_mid, field);
      if (_poly_degree(Q_mid) > 0 || !field.eq(_poly_coeff(Q_mid, 0, field), field.zero())) {
        throw new Error('l==2 odd-k decoder expected S1_2 == x (no mid Q-block)');
      }
      q_mid_params = [];
    } else {
      q_mid_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: Q_mid, k: l - 2, Hs: Hs.slice(0, l - 2), field });
    }

    // Recover t := s2_2 shift at the boundary degree (k-2)D + D/4.
    const deg_t = (k - 2) * D + D4;
    let stage2_coeff = field.sub(_poly_coeff(P_R, deg_t, field), _poly_coeff(known_stage12, deg_t, field));
    stage2_coeff = field.mul(stage2_coeff, inv_m);

    // Compute the x*G1*K1 contribution at this degree using U_high's degree-(D4-1) coefficient.
    const S1_2_sq = _poly_square(S1_2, field);
    const u_d4m1 = field.sub(_poly_coeff(S1_2_sq, D4 - 1, field), field.one());
    let uk1_coeff = field.zero();
    // prod_deg = (k-2)D + (D4-1) uses only U degrees >= D4-1.
    for (let j = 0; j <= Math.floor(D / 2) - (D4 - 1); j++) {
      const udeg = (D4 - 1) + j;
      if (udeg > Math.floor(D / 2)) break;
      let ucoef;
      if (udeg === D4 - 1) {
        ucoef = u_d4m1;
      } else {
        ucoef = field.coerce(U_high.has(udeg) ? U_high.get(udeg) : field.zero());
      }
      uk1_coeff = field.add(uk1_coeff, field.mul(ucoef, _poly_coeff(K1, degK1 - j, field)));
    }
    const x_g1k1_at_deg_t = field.neg(uk1_coeff); // G1=-U, x-shift

    // Isolate g2k2 coefficient at this degree and solve t from [x^{D4}]G2 = -Hq2[D4] - 2t.
    const g2k2_coeff = field.sub(stage2_coeff, x_g1k1_at_deg_t);
    let g2_known_high = field.zero();
    for (let j = 1; j <= Math.floor(D / 2) - D4; j++) {
      const gdeg = D4 + j;
      const gcoef = field.neg(_poly_coeff(Hq2, gdeg, field));
      g2_known_high = field.add(g2_known_high, field.mul(gcoef, _poly_coeff(K2, degK2 - j, field)));
    }
    const g2_d4_coeff = field.sub(g2k2_coeff, g2_known_high);
    const s2_2_shift = field.mul(field.neg(field.add(g2_d4_coeff, _poly_coeff(Hq2, D4, field))), inv2);
    const S2_2 = _poly_add_const(H_quarter, s2_2_shift, field);

    // Recover U down to degree 1 (clean window) and then solve U0 on the contaminated boundary.
    const G2_no_const = _poly_scale_int(_poly_square(S2_2, field), -1, field);
    const g2k2_no_const = _poly_mul(G2_no_const, K2, field);

    const prod2_low = new Array((k - 2) * D + Math.floor(D / 2) + 1).fill(field.zero());
    // Clean stage-2 window: recover U down to degree 1 (inclusive), i.e. d down to (k-2)D+1.
    for (let d = (k - 2) * D + Math.floor(D / 2); d >= (k - 2) * D + 1; d--) {
      const pr_deg = d + 1;
      let rhs = field.sub(_poly_coeff(P_R, pr_deg, field), _poly_coeff(known_stage12, pr_deg, field));
      rhs = field.mul(rhs, inv_m);
      rhs = field.sub(rhs, _poly_coeff(g2k2_no_const, pr_deg, field));
      prod2_low[d] = field.neg(rhs);
    }

    const U_low = _recover_monic_factor_high_coeffs_from_product({
      product: prod2_low,
      known_factor: K1,
      factor_deg: Math.floor(D / 2),
      min_deg: 1,
      field,
    });

    const degB = (k - 2) * D + 1;
    let inner_lead;
    if (k_half % 2 === 0) {
      inner_lead = field.neg(field.mul(field.coerce(k_half), inv2));
    } else {
      inner_lead = field.neg(field.mul(field.coerce(k_half * (k_half - 1)), inv2));
    }

    let rhsB = field.sub(_poly_coeff(P_R, degB, field), _poly_coeff(stage1_x, degB, field));
    rhsB = field.sub(rhsB, _poly_coeff(stage1_tilde, degB, field));
    rhsB = field.sub(rhsB, _hatR1_combined_coeff_at_degree({ k, H, S1_1, H_tilde, S2_1, deg: degB, field }));
    rhsB = field.sub(rhsB, inner_lead);
    rhsB = field.mul(rhsB, inv_m);
    rhsB = field.sub(rhsB, _poly_coeff(g2k2_no_const, degB, field));

    // rhsB == (G1*K1)[(k-2)D] = -(U*K1)[degK1]; solve U0.
    let known_sum = field.zero();
    for (let j = 1; j <= Math.floor(D / 2); j++) {
      const uj = field.coerce(U_low.has(j) ? U_low.get(j) : field.zero());
      if (field.is_zero(uj)) continue;
      known_sum = field.add(known_sum, field.mul(uj, _poly_coeff(K1, degK1 - j, field)));
    }
    const U0 = field.sub(field.neg(rhsB), known_sum);

    // Build S1_3 = S1_2^2 - U (degree < D/4, monic degree D/4-1).
    let S1_3 = new Array(D4).fill(field.zero());
    S1_3[D4 - 1] = field.one();
    for (let i = 1; i <= D4 - 2; i++) {
      const ui = field.coerce(U_low.has(i) ? U_low.get(i) : field.zero());
      S1_3[i] = field.sub(_poly_coeff(S1_2_sq, i, field), ui);
    }
    S1_3[0] = field.sub(_poly_coeff(S1_2_sq, 0, field), U0);
    S1_3 = _poly_trim(S1_3, field);

    let q_low_params;
    if (l === 2) {
      // In the l==2 base construction, S1_3 is fixed to 0 and has no parameters.
      if (_poly_degree(S1_3) > 0 || !field.eq(_poly_coeff(S1_3, 0, field), field.zero())) {
        throw new Error('l==2 odd-k decoder expected S1_3 == 0 (no low Q-block)');
      }
      q_low_params = [];
    } else {
      q_low_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: S1_3, k: l - 2, Hs: Hs.slice(0, l - 2), field });
    }

    // Recover s2_3 from degree (k-2)D (clean of inner recursion and head).
    const degC = (k - 2) * D;
    let rhsC = field.sub(_poly_coeff(P_R, degC, field), _poly_coeff(stage1_x, degC, field));
    rhsC = field.sub(rhsC, _poly_coeff(stage1_tilde, degC, field));
    rhsC = field.sub(rhsC, _hatR1_combined_coeff_at_degree({ k, H, S1_1, H_tilde, S2_1, deg: degC, field }));
    rhsC = field.mul(rhsC, inv_m);

    // Subtract x*G1*K1 and the known -S2_2^2*K2 part to isolate the constant s2_3.
    const U_full = new Array(Math.floor(D / 2) + 1).fill(field.zero());
    for (const [deg_i, coeff_i] of U_low) {
      U_full[deg_i] = field.coerce(coeff_i);
    }
    U_full[0] = U0;
    U_full[Math.floor(D / 2)] = field.one();
    const x_g1k1_at_degC = _poly_coeff(_poly_shift_xk(_poly_mul(_poly_scale_int(U_full, -1, field), K1, field), 1, field), degC, field);
    rhsC = field.sub(rhsC, x_g1k1_at_degC);
    rhsC = field.sub(rhsC, _poly_coeff(g2k2_no_const, degC, field));

    // rhsC is affine in the unknown scalar s2_3 (tail[0]), but can include a fixed
    // contribution from the inner recursion / head gadget that is independent of s2_3.
    //
    // Compute and subtract that fixed part by evaluating the same expression on a
    // synthetic instance where head/mid are zero and s2_3 is set to 0, while all
    // other already-recovered tail parameters are kept.
    const alpha_synth = new Array(total).fill(field.zero());
    const tail_synth = new Array(D).fill(field.zero());
    // tail layout: [s2_3] + q_low + [s2_2_shift] + q_mid + [s2_1_shift] + q_hi
    tail_synth[0] = field.zero();
    for (const [i, v] of q_low_params.entries()) {
      tail_synth[1 + i] = v;
    }
    tail_synth[Math.floor(D / 4)] = s2_2_shift;
    for (const [i, v] of q_mid_params.entries()) {
      tail_synth[Math.floor(D / 4) + 1 + i] = v;
    }
    tail_synth[Math.floor(D / 2)] = s2_1_shift;
    for (const [i, v] of q_hi_params.entries()) {
      tail_synth[Math.floor(D / 2) + 1 + i] = v;
    }
    const tail_start = D + ((k - 3) * D);
    for (const [i, v] of tail_synth.entries()) {
      alpha_synth[tail_start + i] = v;
    }
    const P_R_synth = _poly_remainder_poly_from_T({ k, l, alpha: alpha_synth, Hs, tilde_H_2l: H_tilde, field });

    let rhsC_synth = field.sub(_poly_coeff(P_R_synth, degC, field), _poly_coeff(stage1_x, degC, field));
    rhsC_synth = field.sub(rhsC_synth, _poly_coeff(stage1_tilde, degC, field));
    rhsC_synth = field.sub(
      rhsC_synth,
      _hatR1_combined_coeff_at_degree({ k, H, S1_1, H_tilde, S2_1, deg: degC, field })
    );
    rhsC_synth = field.mul(rhsC_synth, inv_m);
    rhsC_synth = field.sub(rhsC_synth, x_g1k1_at_degC);
    rhsC_synth = field.sub(rhsC_synth, _poly_coeff(g2k2_no_const, degC, field));

    const s2_3 = field.sub(rhsC, rhsC_synth);

    // Assemble tail alpha layout (exactly as `_poly_paper_T`, odd case l>=3).
    tail_out = new Array(D).fill(field.zero());
    tail_out[0] = s2_3;
    for (const [i, v] of q_low_params.entries()) {
      tail_out[1 + i] = v;
    }
    tail_out[Math.floor(D / 4)] = s2_2_shift;
    for (const [i, v] of q_mid_params.entries()) {
      tail_out[Math.floor(D / 4) + 1 + i] = v;
    }
    tail_out[Math.floor(D / 2)] = s2_1_shift;
    for (const [i, v] of q_hi_params.entries()) {
      tail_out[Math.floor(D / 2) + 1 + i] = v;
    }
  }

  // ---- Head + mid parameters via descending pivots of the frozen-tail map. ----
  const rest_len = total - D;

  function _rest_remainder(rest) {
    const al = rest.concat(tail_out);
    return _poly_remainder_poly_from_T({ k, l, alpha: al, Hs, tilde_H_2l: H_tilde, field });
  }

  const rest = _decode_by_descending_pivots({
    target: P_R, encode_fn: _rest_remainder, nparams: rest_len, field, what: `R_odd(k=${k},l=${l})`,
  });

  const alphas_out = rest.concat(tail_out);
  if (alphas_out.length !== total) {
    throw new Error('internal: odd-k alpha length mismatch');
  }
  const [_T1, _T2, Hs_out, tilde_out] = _poly_paper_T({
    k, l, alpha: alphas_out, Hs, tilde_H_2l: H_tilde, field,
  });
  return [alphas_out, Hs_out, tilde_out];
}
