// =============================================================================
// g5_decode_P.frag.js — P coefficient decoders for the paper family P_n[α]:
// bases P3/P5/P7, the 4k+1 family, specials P11/P15, and the dispatch
// _decode_P_coeffs_to_paper_params.
// Fragment: function declarations only; runtime (Field, _poly_* helpers) and
// other groups (_decode_square_gadget, _decode_R_k, _decode_Q5_coeffs_to_alpha_given_H2,
// _decode_Q_power_of_2_minus_1_coeffs_to_alpha, _poly_paper_P_from_params) are
// supplied by sibling fragments at assembly time.
// =============================================================================

// py: tools/poly_schedule.py:3212
function _decode_P3_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (coeffs.length !== 4 || !field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error("P3 decoder expects monic degree-3 polynomial coeffs [a0..a2,1]");
  }
  const a0 = coeffs[0], a1 = coeffs[1], a2 = coeffs[2];
  const alpha2 = field.sub(a2, field.one());
  const alpha1 = field.sub(a1, alpha2);
  const alpha0 = field.sub(a0, alpha1);
  return [alpha0, alpha1, alpha2];
}

// py: tools/poly_schedule.py:3223
function _decode_P7_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (coeffs.length !== 8 || !field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error("P7 decoder expects monic degree-7 polynomial coeffs [a0..a6,1]");
  }

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error("P7 decoding for char(F)=2 is not implemented");
  }
  const inv2 = field.inv(two);

  const [c0, c1, c2, c3, c4, c5, c6] = [coeffs[0], coeffs[1], coeffs[2], coeffs[3], coeffs[4], coeffs[5], coeffs[6]];

  const z2 = field.mul(c6, inv2);
  const z2_sq = field.mul(z2, z2);

  const z1 = field.mul(field.sub(field.sub(c5, z2_sq), field.one()), inv2);
  const z1_sq = field.mul(z1, z1);

  const v4 = field.sub(c4, field.one());
  const two_z2z1 = field.add(field.mul(z2, z1), field.mul(z2, z1));
  const RHS1 = field.sub(field.sub(field.sub(v4, two_z2z1), z2), field.zero());

  const v3 = field.sub(c3, z2);
  const alpha1 = field.sub(field.sub(field.sub(v3, field.mul(z2, RHS1)), z1_sq), z1);

  const v2 = field.sub(field.sub(c2, z1), field.one());
  const W1 = field.sub(field.sub(v2, field.mul(z2, alpha1)), field.mul(z1, RHS1));

  // alpha6 = c1 - (z1+1)*alpha1 - W1*(RHS1 + 1 - W1)
  const z1_plus_1 = field.add(z1, field.one());
  const term1 = field.mul(z1_plus_1, alpha1);
  const term2 = field.mul(W1, field.sub(field.add(RHS1, field.one()), W1));
  const alpha6 = field.sub(field.sub(c1, term1), term2);

  const alpha4 = field.sub(field.sub(z2, field.one()), alpha6);
  const alpha5 = field.sub(z1, field.mul(alpha4, field.add(field.one(), alpha6)));
  const z0 = field.mul(alpha4, alpha5);
  const alpha3 = field.sub(W1, z0);
  const alpha2 = field.sub(field.sub(RHS1, field.add(z0, z0)), alpha3);
  const alpha0 = field.sub(c0, field.mul(field.add(z0, alpha2), alpha1));

  return [alpha0, alpha1, alpha2, alpha3, alpha4, alpha5, alpha6];
}

// py: tools/poly_schedule.py:3267
// Decode the paper base construction for `P_5[α0..α4]` implemented by `_paper_P5`:
//
//   P5[α0..α4](x) = (x + α2) * ( (x^2 + α4) * (x^2 + x + α3) + α1 ) + α0
//
// This decoder is solver-free and works in any characteristic.
function _decode_P5_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (coeffs.length !== 6 || !field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error("P5 decoder expects monic degree-5 polynomial coeffs [a0..a4,1]");
  }

  const [a0, a1, a2, a3, a4] = [coeffs[0], coeffs[1], coeffs[2], coeffs[3], coeffs[4]];

  const alpha2 = field.sub(a4, field.one());
  const alpha2_sq = field.mul(alpha2, alpha2);
  const alpha4 = field.add(field.sub(a2, field.mul(alpha2, a3)), alpha2_sq);
  const alpha3 = field.sub(field.sub(a3, alpha2), alpha4);
  const alpha4_sq = field.mul(alpha4, alpha4);
  const alpha1 = field.add(field.sub(a1, field.mul(alpha4, a3)), alpha4_sq);
  const alpha0 = field.add(field.sub(a0, field.mul(alpha2, a1)), field.mul(alpha2_sq, alpha4));
  return [alpha0, alpha1, alpha2, alpha3, alpha4];
}

// py: tools/poly_schedule.py:3409
// Decode `P_{4k+1}[α0..α_{4k}]` (the main `4k+1` splittable family) for any `k>=2`.
//
// Paper structure (sections/constructions.tex, “4k+1 is splittable”):
//   - H2 = (x + α_{4k})x + α_{4k-1} = x^2 + u*x + v, with (u,v) at the *end*.
//   - \tilde H2 = H2 + α_{4k-2}.
//   - The first `4k-2` parameters are exactly the internal `T_{2k,2}` block.
//   - P = x*T^{(1)}_{2k,2} + T^{(2)}_{2k,2}.
//
// Decoder outline:
//   1) Recover (u,v,\tilde shift) from the top three coefficients (independent of the T-block).
//   2) Form the remainder polynomial P_R = P - (x*H2^{2k} + \tilde H2^{2k}).
//   3) Decode the T-block via `_decode_R_k(k=2k,l=1,...)`.
function _decode_P_4k_plus_1_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (_poly_degree(coeffs) < 0 || !field.eq(_poly_coeff(coeffs, _poly_degree(coeffs), field), field.one())) {
    throw new Error("P_{4k+1} decoder expects a monic polynomial");
  }

  const n = _poly_degree(coeffs);
  if (n < 9 || (n % 4) !== 1) {
    throw new Error(`expected n=4k+1 with k>=2, got n=${n}`);
  }
  const k = Math.floor((n - 1) / 4);

  const two_k = field.coerce(2 * k);
  if (field.is_zero(two_k)) {
    throw new Error("4k+1 decoding requires (2k) invertible in the field");
  }
  const inv_two_k = field.inv(two_k);

  const c_n_minus_1 = _poly_coeff(coeffs, n - 1, field);
  const c_n_minus_2 = _poly_coeff(coeffs, n - 2, field);
  const c_n_minus_3 = _poly_coeff(coeffs, n - 3, field);

  // u from: [x^{4k}]P = 2k*u + 1.
  const u = field.mul(field.sub(c_n_minus_1, field.one()), inv_two_k);

  // v from: [x^{4k-1}]P = C(2k,2)u^2 + 2k*v + 2k*u - k.
  const u2 = field.mul(u, u);
  const choose2 = (2 * k) * (2 * k - 1) / 2; // math.comb(2*k, 2), exact integer
  const term_choose2_u2 = _field_mul_int(field, u2, choose2);
  const num_v = field.add(
    field.sub(field.sub(c_n_minus_2, term_choose2_u2), _field_mul_int(field, u, 2 * k)),
    field.coerce(k),
  );
  const v = field.mul(num_v, inv_two_k);

  // Remaining outer pivots (paper `lem:4k+1-splittable` pivot table):
  //   coeff 4k-2 -> a   (= alpha_{4k-3}, slope -2k)
  //   coeff 4k-3 -> e   (= alpha_{4k-4}, slope  k)
  //   coeff 4k-4 -> rho (= alpha_{4k-2}, slope  k)
  // The parameter-free boundary contributions of the remainder pair
  // (`lem:Rk2l-top-boundary`) are captured by synthetically re-encoding the
  // partial parameter vector, so each pivot is an exact affine solve.
  const partial = new Array(n).fill(field.zero());
  partial[n - 1] = u;
  partial[n - 2] = v;

  for (const [idx, row] of [[n - 4, n - 3], [n - 5, n - 4], [n - 3, n - 5]]) {
    const base_enc = _poly_paper_P_from_params({ params: partial, field: field });
    const probe = partial.slice();
    probe[idx] = field.add(probe[idx], field.one());
    const probe_enc = _poly_paper_P_from_params({ params: probe, field: field });
    const slope = field.sub(_poly_coeff(probe_enc, row, field), _poly_coeff(base_enc, row, field));
    if (field.is_zero(slope)) {
      throw new Error("P_{4k+1} decoder: zero pivot slope (field not admissible?)");
    }
    partial[idx] = field.div(
      field.sub(_poly_coeff(coeffs, row, field), _poly_coeff(base_enc, row, field)), slope
    );
  }
  const tilde_shift = partial[n - 3];

  const x = [field.zero(), field.one()];
  const H2 = [field.coerce(v), field.coerce(u), field.one()];
  const tilde_H2 = _poly_add_const(H2, tilde_shift, field);

  const H_pow = _poly_pow(H2, 2 * k, field);
  const Ht_pow = _poly_pow(_poly_trim(tilde_H2, field), 2 * k, field);
  const known = _poly_add(_poly_shift_xk(H_pow, 1, field), Ht_pow, field);
  const P_R = _poly_sub(coeffs, known, field);

  const [t_params, _Hs_out, _tilde_out] = _decode_R_k({
    k: 2 * k, l: 1, P_R: P_R, Hs: [x, H2], tilde_H_2l: tilde_H2, field: field,
  });
  if (t_params.length !== n - 3) {
    throw new Error("internal error: T_{2k,2} parameter block length mismatch");
  }

  const alpha = t_params.slice().concat([tilde_shift, v, u]);

  const chk = _poly_trim(_poly_paper_P_from_params({ params: alpha, field: field }), field);
  if (!_poly_eq(chk, coeffs, field)) {
    throw new Error("4k+1 decoder produced parameters that do not reproduce the input polynomial");
  }
  return alpha;
}

// py: tools/poly_schedule.py:6087
// Decode `P_11[α0..α10]` (the k=1 instance of the 8k+3 induction).
//
// For k=1 the “compatibility” recovery step collapses to a genuine square-gadget
// because the inner splittable pair is `n=3`, where
//   (S1_1,S1_2) = (H2, H2+α2).
function _decode_P11_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (_poly_degree(coeffs) !== 11 || !field.eq(_poly_coeff(coeffs, 11, field), field.one())) {
    throw new Error("P11 decoder expects a monic degree-11 polynomial");
  }

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error("P11 decoding requires char(F) != 2");
  }

  // Step 1: decode S2=Q5 and a=α5 from the outer square gadget at d=5.
  // The error term contributes degree-5 coefficient -1 (from -x*(S1_1)^2, with S1_1 monic degree 2).
  const [S2, a] = _decode_square_gadget({
    G: coeffs,
    field: field,
    boundary_error_coeff_deg_d: field.neg(field.one()),
  });
  if (_poly_degree(S2) !== 5) {
    throw new Error("internal error: expected deg(S2)=5 in P11 decoding");
  }

  // Subtract the square gadget to isolate the residual.
  const xS2_sq = _poly_shift_xk(_poly_square(S2, field), 1, field);
  const S2_plus_a_sq = _poly_square(_poly_add_const(S2, a, field), field);
  const P_rem = _poly_sub(coeffs, _poly_add(xS2_sq, S2_plus_a_sq, field), field);

  // Step 2: recover (S1_1, α2) from Ψ = x(S1_1)^2 + (S1_1+α2)^2.
  //
  // For degrees >= 2, the low-degree term (x*α1 + α0) does not contribute, so:
  //   Ψ_{>=2} = -P_rem_{>=2}.
  let psi = new Array(6).fill(field.zero()); // degree 5 max
  for (let d = 2; d < 6; d++) {
    psi[d] = field.neg(_poly_coeff(P_rem, d, field));
  }
  psi[5] = field.one();
  psi = _poly_trim(psi, field);

  const [S1_1, alpha2] = _decode_square_gadget({ G: psi, field: field, boundary_error_coeff_deg_d: field.zero() });
  if (_poly_degree(S1_1) !== 2) {
    throw new Error("internal error: expected deg(S1_1)=2 in P11 decoding");
  }

  // Step 3: recover α0, α1 from P_rem = -Ψ + x*α1 + α0.
  const psi_full = _poly_add(_poly_shift_xk(_poly_square(S1_1, field), 1, field), _poly_square(_poly_add_const(S1_1, alpha2, field), field), field);
  const resid = _poly_add(P_rem, psi_full, field);
  const alpha0 = _poly_coeff(resid, 0, field);
  const alpha1 = _poly_coeff(resid, 1, field);

  // Step 4: recover the embedded `n=3` block parameters α3,α4 from S1_1 (=H2).
  // Here H2 = x^2 + α4 x + α3.
  const alpha4 = _poly_coeff(S1_1, 1, field);
  const alpha3 = _poly_coeff(S1_1, 0, field);

  // Step 5: decode the `Q5` parameter block α6..α10 given H2.
  const q_params = _decode_Q5_coeffs_to_alpha_given_H2(S2, S1_1, field);
  if (q_params.length !== 5) {
    throw new Error("internal error: expected 5 params from Q5 decoder");
  }

  // Global α layout for n=11 (k=1) per `_paper_splittable_pair`:
  //   α0           : scalar in the final T2
  //   α1           : S3 constant
  //   α2..α4       : P3 block
  //   α5           : square-gadget shift on S2
  //   α6..α10      : Q5 block
  const alpha = new Array(11).fill(field.zero());
  alpha[0] = alpha0;
  alpha[1] = alpha1;
  alpha[2] = alpha2;
  alpha[3] = alpha3;
  alpha[4] = alpha4;
  alpha[5] = a;
  for (let i = 0; i < 5; i++) {
    alpha[6 + i] = q_params[i];
  }
  return alpha;
}

// py: tools/poly_schedule.py:6167
// Decode `P_15[α0..α14]` induced by this file’s special-case `n=15` splittable pair.
//
// Structure (from `_paper_splittable_pair(n=15)`):
//   - H2 = x^2 + α7 x + α6
//   - H4 = H2^2 - (x+α5)^2 + α4
//   - S  = Q_7[α8..α14](x,H2,H4)     (paper `Q_known_powers(k=3)`)
//   - T1 = S^2 - (H2+α3)^2 + α1
//   - H8 = H4^2 - (H2+α2)^2 + α0
//   - P  = (x+1)*T1 + H8
//
// This decoder is solver-free and uses coefficient algebra + monic square roots.
// Requires char(F) != 2 (and 4 invertible).
function _decode_P15_coeffs_to_alpha(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (_poly_degree(coeffs) !== 15 || !field.eq(_poly_coeff(coeffs, 15, field), field.one())) {
    throw new Error("P15 decoder expects a monic degree-15 polynomial");
  }

  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error("P15 decoding requires char(F) != 2");
  }
  const inv2 = field.inv(two);
  const four = field.add(two, two);
  if (field.is_zero(four)) {
    throw new Error("P15 decoding requires 4 invertible in the field");
  }
  const inv4 = field.inv(four);

  const x = [field.zero(), field.one()];
  const x_plus_1 = [field.one(), field.one()];

  // Step 1: recover S^2 coefficients in degrees 7..14 from the clean high window.
  const S_sq_high = new Array(15).fill(field.zero()); // degree 14 max
  S_sq_high[14] = field.one();
  for (let d = 14; d > 8; d--) { // d=14..9 gives S^2[d-1]
    S_sq_high[d - 1] = field.sub(_poly_coeff(coeffs, d, field), S_sq_high[d]);
  }
  // Degree 8 is still clean (other terms max degree 8 but do not contribute to deg 9+).
  // Degree 7 is obtained from [x^8]P = (S^2[8]+S^2[7]) + [x^8]H4^2, and H4 is monic => [x^8]H4^2 = 1.
  S_sq_high[7] = field.sub(field.sub(_poly_coeff(coeffs, 8, field), field.one()), S_sq_high[8]);

  const S = _monic_sqrt_from_high_square_coeffs(S_sq_high, 7, field);
  if (_poly_degree(S) !== 7 || !field.eq(_poly_coeff(S, 7, field), field.one())) {
    throw new Error("internal error: expected monic degree-7 S in P15 decoding");
  }
  const S_sq = _poly_square(S, field);

  // Step 2: residual R = P - (x+1)*S^2 = H4^2 - (x+1)(H2+α3)^2 - (H2+α2)^2 + (x+1)α1 + α0.
  const R = _poly_sub(coeffs, _poly_mul(S_sq, x_plus_1, field), field);

  // Step 3: recover H4 coefficients from (mostly clean) H4^2 coefficients.
  const H4_sq_8 = _poly_coeff(R, 8, field);
  const H4_sq_7 = _poly_coeff(R, 7, field);
  const H4_sq_6 = _poly_coeff(R, 6, field);
  // Degree 5: subtract the known contribution from -x*(H2+α3)^2, which is -1 at degree 5.
  const H4_sq_5 = field.add(_poly_coeff(R, 5, field), field.one());

  if (!field.eq(H4_sq_8, field.one())) {
    throw new Error("internal error: expected monic H4^2 at degree 8 in P15 decoding");
  }

  // Let H4 = x^4 + A x^3 + B x^2 + C x + D.
  // Then H4^2 has:
  //   [x^7]=2A, [x^6]=A^2+2B, [x^5]=2AB+2C, [x^4]=B^2+2AC+2D.
  const A = field.mul(H4_sq_7, inv2);
  // A = 2*α7 (since H4[3] = 2*α7).
  const alpha7 = field.mul(A, inv2);

  const A2 = field.mul(A, A);
  const B = field.mul(field.sub(H4_sq_6, A2), inv2);
  const twoAB = field.add(field.mul(A, B), field.mul(A, B));
  const C = field.mul(field.sub(H4_sq_5, twoAB), inv2);

  // Degree 4: R_4 = (H4^2)_4 - ((H2+α3)^2)_3 - 2, and ((H2+α3)^2)_3 = 2*α7 (independent of α3).
  const H4_sq_4 = field.add(_poly_coeff(R, 4, field), field.add(_field_mul_int(field, alpha7, 2), field.coerce(2)));
  const B2 = field.mul(B, B);
  const twoAC = _field_mul_int(field, field.mul(A, C), 2);
  const D = field.mul(field.sub(field.sub(H4_sq_4, B2), twoAC), inv2);

  const H4 = _poly_trim([D, C, B, A, field.one()], field);
  if (_poly_degree(H4) !== 4 || !field.eq(_poly_coeff(H4, 4, field), field.one())) {
    throw new Error("internal error: expected monic degree-4 H4 in P15 decoding");
  }

  // Step 4: recover H2 params and α4,α5 from H4 = H2^2 - (x+α5)^2 + α4.
  // Here H2 = x^2 + α7 x + α6.
  const alpha6 = field.mul(field.sub(field.add(B, field.one()), field.mul(alpha7, alpha7)), inv2);
  const alpha5 = field.sub(field.mul(alpha7, alpha6), field.mul(C, inv2));
  const alpha4 = field.sub(D, field.sub(field.mul(alpha6, alpha6), field.mul(alpha5, alpha5)));

  const H2 = _poly_trim([alpha6, alpha7, field.one()], field);

  // Step 5: subtract H4^2 and solve the remaining low scalars α0..α3.
  const H4_sq_full = _poly_square(H4, field);
  const R2 = _poly_sub(R, H4_sq_full, field);

  const b = alpha7;
  const c = alpha6;
  // From degree 3:
  //   R2_3 = -((x+1)(H2+α3)^2)_3 - ((H2+α2)^2)_3
  //        = -((H2+α3)^2_3 + (H2+α3)^2_2) - 2b
  // and (H2+α3)^2_2 = b^2 + 2(c+α3).
  const s2_sq_2 = field.sub(field.neg(_poly_coeff(R2, 3, field)), _field_mul_int(field, b, 4));
  const d3 = field.mul(field.sub(s2_sq_2, field.mul(b, b)), inv2); // d3 = c + α3
  const alpha3 = field.sub(d3, c);

  // From degree 2:
  //   R2_2 = -( (H2+α3)^2_2 + (H2+α3)^2_1 ) - (H2+α2)^2_2
  // where (H2+α3)^2_1 = 2*b*d3 and (H2+α2)^2_2 = b^2 + 2*d2.
  const two_b_d3 = _field_mul_int(field, field.mul(b, d3), 2);
  const num_d2 = field.sub(
    field.sub(field.neg(_poly_coeff(R2, 2, field)), field.add(s2_sq_2, two_b_d3)),
    field.mul(b, b),
  );
  const d2 = field.mul(num_d2, inv2); // d2 = c + α2
  const alpha2 = field.sub(d2, c);

  // Degree 1: R2_1 = -(2*b*d3 + d3^2) - (2*b*d2) + α1.
  const alpha1 = field.add(
    _poly_coeff(R2, 1, field),
    field.add(field.add(two_b_d3, field.mul(d3, d3)), _field_mul_int(field, field.mul(b, d2), 2)),
  );

  // Degree 0: R2_0 = -d3^2 - d2^2 + α1 + α0.
  const alpha0 = field.sub(
    field.add(_poly_coeff(R2, 0, field), field.add(field.mul(d3, d3), field.mul(d2, d2))),
    alpha1,
  );

  // Step 6: decode the embedded Q7 block α8..α14 from S given (H2,H4).
  const q_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q: S, k: 3, Hs: [x, H2, H4], field: field });
  if (q_params.length !== 7) {
    throw new Error("internal error: expected 7 params from Q7 decoder");
  }

  const alpha = new Array(15).fill(field.zero());
  alpha[0] = alpha0;
  alpha[1] = alpha1;
  alpha[2] = alpha2;
  alpha[3] = alpha3;
  alpha[4] = alpha4;
  alpha[5] = alpha5;
  alpha[6] = alpha6;
  alpha[7] = alpha7;
  for (let i = 0; i < q_params.length; i++) {
    alpha[8 + i] = q_params[i];
  }

  // Sanity: re-encode.
  const chk = _poly_trim(_poly_paper_P_from_params({ params: alpha, field: field }), field);
  if (!_poly_eq(chk, coeffs, field)) {
    throw new Error("P15 decoder produced parameters that do not reproduce the input polynomial");
  }
  return alpha;
}

// py: tools/poly_schedule.py:6606
// Decode a monic polynomial's coefficients into the paper parameters α0..α_{n-1}
// for the family P_n[α] implemented by `compile_paper_params_chain`.
//
// Implemented here:
//   - the bases n = 1,3,5,7 and the specials n = 11, 15;
//   - all even n by the paper's even-lift: P_n = α0 + x * P_{n-1}(α1..);
//   - the main splittable family n ≡ 1 (mod 4) (lem:4k+1-splittable +
//     alg:decode-Rk2l via `_decode_R_k`).
//
// The remaining odd families (8k+3, 8k+7, and the specials 27/31) are
// implemented in `tools/polychain.py` on top of the primitives in this file.
function _decode_P_coeffs_to_paper_params(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  if (coeffs.length <= 1) {
    throw new Error("polynomial must have positive degree for paper decoding");
  }
  if (!field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error("paper decoding requires a monic polynomial (leading coefficient 1)");
  }

  const n = coeffs.length - 1;
  if (n === 1) {
    return [coeffs[0]];
  }

  if ((n % 2) === 0) {
    // P_n = α0 + x * P_{n-1}(α1..)
    const alpha0 = coeffs[0];
    const rest = _decode_P_coeffs_to_paper_params(coeffs.slice(1), field);
    return [alpha0].concat(rest);
  }

  if (n === 3) {
    return _decode_P3_coeffs_to_alpha(coeffs, field);
  }
  if (n === 5) {
    return _decode_P5_coeffs_to_alpha(coeffs, field);
  }
  if (n === 7) {
    return _decode_P7_coeffs_to_alpha(coeffs, field);
  }
  if (n === 11) {
    return _decode_P11_coeffs_to_alpha(coeffs, field);
  }
  if (n === 15) {
    return _decode_P15_coeffs_to_alpha(coeffs, field);
  }

  // Main splittable family: n = 4k+1, k>=2.
  if ((n % 4) === 1 && n >= 9) {
    return _decode_P_4k_plus_1_coeffs_to_alpha(coeffs, field);
  }

  // py: the peeling fallback is intentionally not ported because the branch is dead.
  throw new Error('peeling fallback not ported');
}
