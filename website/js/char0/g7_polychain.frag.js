// g7_polychain.frag.js — polychain spine (tools/polychain.py) for the char-0
// lane port.  Fragment: function declarations only (plus the MERSENNE61
// constant); no imports/exports, no top-level side effects.  All ps.* names
// from the Python are bare names here — other fragments supply them.

// py: tools/polychain.py:61
const MERSENNE61 = (1n << 61n) - 1n;

// =============================================================================
// Fields
// =============================================================================

// py: tools/polychain.py:69
// The prime field GF(p) (odd p; characteristic 2 is rejected at decode time).
// JS: p may be a Number or a BigInt; the Field stores the modulus as BigInt.
function GF(p) {
  return new Field({ modulus: BigInt(p) });
}

// py: tools/polychain.py:75
// Exact rational arithmetic (Python `fractions.Fraction` -> Rat).
// (Python passes use_fractions=True; in this port modulus=null implies it.)
function rationals() {
  return new Field({ modulus: null });
}

// py: tools/polychain.py:81
function default_field() {
  return GF(MERSENNE61);
}

// py: tools/polychain.py:85
function _require_odd_characteristic(field, purpose) {
  if (field.modulus === 2n) {
    throw new Error(
      `${purpose} over characteristic 2 is not supported by polychain; ` +
      "see poly_schedule's char-2 septic base for the GF(2^k) constructions"
    );
  }
}

// =============================================================================
// Encoding (coefficient expansion of P_n[α])
// =============================================================================

// py: tools/polychain.py:98
// Expand P_n[α_0..α_{n-1}] and return its non-leading coefficients
// [c_0, ..., c_{n-1}]  (the polynomial is x^n + Σ_j c_j x^j).
//
// With peeled=true the known-powers gadgets Q_{2^k-1} use the depth-balanced
// peeled recursion (same multiplications and additions, height O(log n)
// overall); the parameter layout inside those blocks changes accordingly.
function encode(n, alphas, field = null, { peeled = false } = {}) {
  field = field || default_field();
  if (peeled) {
    return _with_peeled(() => encode(n, alphas, field));
  }
  if (n < 1) {
    throw new Error('encode requires n >= 1');
  }
  alphas = alphas.map((a) => field.coerce(a));
  if (alphas.length !== n) {
    throw new Error(`P_${n} takes exactly ${n} parameters, got ${alphas.length}`);
  }
  let P = _poly_paper_P_from_params({ params: alphas, field });
  P = _poly_trim(P, field);
  if (_poly_degree(P) !== n || !field.eq(P[P.length - 1], field.one())) {
    throw new Error('internal error: encoder did not produce a monic degree-n polynomial');
  }
  return P.slice(0, n);
}

// =============================================================================
// Decoding (rational preprocessing: coefficients -> parameters)
// =============================================================================

// py: tools/polychain.py:130
// Invert `encode`: given the coefficients c_0..c_{n-1} of the monic
// polynomial x^n + Σ_j c_j x^j, return parameters α_0..α_{n-1} with
// P_n[α] equal to that polynomial.  The result is verified by re-expansion.
//
// Mirrors `alg:final-decoder` in sections/constructions.tex.
function decode(n, coeffs, field = null, { peeled = false } = {}) {
  field = field || default_field();
  if (peeled) {
    return _with_peeled(() => decode(n, coeffs, field));
  }
  _require_odd_characteristic(field, 'decoding');
  if (n < 1) {
    throw new Error('decode requires n >= 1');
  }
  let cs = coeffs.map((c) => field.coerce(c));
  if (cs.length === n + 1) {
    if (!field.eq(cs[cs.length - 1], field.one())) {
      throw new Error('decode expects a monic polynomial (leading coefficient 1)');
    }
    cs = cs.slice(0, n);
  }
  if (cs.length !== n) {
    throw new Error(`decode of degree ${n} needs ${n} coefficients c_0..c_${n - 1}, got ${cs.length}`);
  }
  const full = cs.concat([field.one()]);

  const alphas = _decode_monic(full, field);

  const check = _poly_trim(_poly_paper_P_from_params({ params: alphas, field }), field);
  if (!_poly_eq(check, _poly_trim(full, field), field)) {
    throw new Error(`decode(n=${n}): parameters failed re-expansion verification`);
  }
  return alphas;
}

// py: tools/polychain.py:163
// Even lift P_n = α_0 + x·P_{n-1}, then odd-degree dispatch.
function _decode_monic(coeffs, field) {
  coeffs = _poly_trim(coeffs, field);
  const n = _poly_degree(coeffs);
  if (n < 1) {
    throw new Error('polynomial must have positive degree');
  }
  if (!field.eq(coeffs[coeffs.length - 1], field.one())) {
    throw new Error('decode expects a monic polynomial');
  }
  if (n % 2 === 0) {
    return [coeffs[0]].concat(_decode_monic(coeffs.slice(1), field));
  }
  return _decode_odd(coeffs, field, { pair_context: false });
}

// py: tools/polychain.py:177
// Decode odd-degree P_n = x·T^{(1)}_n + T^{(2)}_n.
//
// `pair_context` selects the splittable-pair parameterization for n=5
// (used as the inner block of the 8k+7 step), which differs from the
// top-level P_5 base construction.  n=7 never occurs as an inner block
// (k=3 instances are the special cases 27 and 31).
function _decode_odd(coeffs, field, { pair_context }) {
  coeffs = _poly_trim(coeffs, field);
  const n = _poly_degree(coeffs);
  if (n === 1) {
    return [coeffs[0]];
  }
  if (pair_context && n === 5) {
    // Splittable pair for 5 = k=1 instance of the 4k+1 family.
    function enc5(a) {
      const [T1, T2] = _poly_paper_splittable_pair({ n: 5, alpha: a.slice(), field });
      return _poly_add(_poly_shift_xk(T1, 1, field), T2, field);
    }

    return _decode_by_descending_pivots({
      target: coeffs, encode_fn: enc5, nparams: 5, field, what: 'pair(5)',
    });
  }
  if (pair_context && n === 7) {
    throw new Error('internal error: no splittable pair exists for 7');
  }
  if ([3, 5, 7, 11, 15].includes(n) || n % 4 === 1) {
    // Bases, the 4k+1 family (lem:4k+1-splittable + alg:decode-Rk2l),
    // and the specials 11/15 — all implemented in poly_schedule.
    return _decode_P_coeffs_to_paper_params(coeffs, field);
  }
  if (n === 27) {
    return _decode_pair_27(coeffs, field);
  }
  if (n === 31) {
    return _decode_pair_31(coeffs, field);
  }
  if (n % 8 === 3) {
    return _decode_pair_8k3(coeffs, field);
  }
  if (n % 8 === 7) {
    return _decode_pair_8k7(coeffs, field);
  }
  throw new Error(`internal error: no decoding family matched odd n=${n}`);
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

// py: tools/polychain.py:222
function _x(field) {
  return [field.zero(), field.one()];
}

// py: tools/polychain.py:226
// x·S^2 + (S+δ)^2 (the square gadget of `lem:square-gadget`).
function _square_gadget_poly(S, delta, field) {
  const S_sq = _poly_square(S, field);
  const shifted = _poly_square(_poly_add_const(S, delta, field), field);
  return _poly_add(_poly_shift_xk(S_sq, 1, field), shifted, field);
}

// py: tools/polychain.py:234
// Divide by x, requiring a zero constant term is NOT required (drop it).
function _shift_down(p, field) {
  return _poly_trim(p.slice(1), field);
}

// py: tools/polychain.py:240
// Mirror of the encoder's `build_Q` in `_poly_paper_splittable_pair` (8k+7
// branch): the odd-degree known-powers gadget when enough powers are
// available, the bar-Q fallback otherwise.  Returns [encode_fn, hs_out_fn].
function _build_Q_encoder(deg, Hs_in, field) {
  const l = _v2_positive(deg + 1);
  const odd = (deg + 1) >> l;
  const kk = Math.floor((odd - 1) / 2);
  const need = kk > 0 ? l + 1 : l;
  if (Hs_in.length >= need) {
    function enc(a) {
      const [q] = _poly_paper_Q_for_odd_degree_with_powers({
        deg, alpha: a.slice(), Hs: Hs_in, field,
      });
      return _poly_trim(q, field);
    }

    function hs_out(a) {
      const [, hs] = _poly_paper_Q_for_odd_degree_with_powers({
        deg, alpha: a.slice(), Hs: Hs_in, field,
      });
      return hs.slice();
    }

    return [enc, hs_out];
  } else {
    function enc(a) {
      const [q] = _poly_paper_barQ_odd_with_H2_H4_with_powers({
        deg, alpha: a.slice(), Hs_in, field,
      });
      return _poly_trim(q, field);
    }

    function hs_out(a) {
      const [, hs] = _poly_paper_barQ_odd_with_H2_H4_with_powers({
        deg, alpha: a.slice(), Hs_in, field,
      });
      return hs.slice();
    }

    return [enc, hs_out];
  }
}

// py: tools/polychain.py:278
// Parameter block of Q_{4k+1}(x, H_2) (lem:Q4k+1-from-H2) by descending pivots.
function _solve_Q4kp1(target, kk, H2, field) {
  const x = _x(field);

  function enc(av) {
    const [q] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k: kk, l: 1, alpha: av.slice(), Hs: [x, H2], field,
    });
    return _poly_trim(q, field);
  }

  return _decode_by_descending_pivots({
    target, encode_fn: enc, nparams: 4 * kk + 1, field, what: `Q_{${4 * kk + 1}} given H2`,
  });
}

// py: tools/polychain.py:294
// Known-power byproducts [x, H_2, H_4, ...] of a Q_{4k+1}(x,H_2) instance.
function _Q4kp1_powers(params, kk, H2, field) {
  const x = _x(field);
  const [, hs_raw] = _poly_paper_Q_2lp1k_minus_1_with_powers({
    k: kk, l: 1, alpha: params.slice(), Hs: [x, H2], field,
  });
  return [x, H2].concat(hs_raw.slice(2));
}

// py: tools/polychain.py:304
// Parameter block of the odd-degree known-powers gadget Q_deg (lem:Q-odd-degree-with-powers).
function _solve_Qodd(target, deg, Hs, field) {
  function enc(av) {
    const [q] = _poly_paper_Q_for_odd_degree_with_powers({ deg, alpha: av.slice(), Hs, field });
    return _poly_trim(q, field);
  }

  return _decode_by_descending_pivots({
    target, encode_fn: enc, nparams: deg, field, what: `Q_{${deg}} with powers`,
  });
}

// py: tools/polychain.py:316
// [α_4, α_5, α_6, α_7] from H_4 = H_2² − (x+α_5)² + α_4, H_2 = x² + α_7 x + α_6.
function _h4_block_params(H4, field) {
  const one = field.one();

  function enc(a) {
    const H2 = [a[2], a[3], one];
    return _poly_add_const(
      _poly_sub(_poly_square(H2, field), _poly_square([a[1], one], field), field),
      a[0],
      field
    );
  }

  return _decode_by_descending_pivots({ target: H4, encode_fn: enc, nparams: 4, field, what: 'H4 block' });
}

// py: tools/polychain.py:332
// Closed-form chain for P3 = −(x+1)·Q_3² + (x+1)·α_1 − H_2² + α_0 with
// Q_3 = x³+γ₂x²+γ₁x+γ₀ = Q_3[α_4,α_5,α_6](x,H_2) and H_2 = x²+bx+c
// (b = α_3, c = α_2).  Returns [α_0, ..., α_6].
function _decode_27_low_block(P3, field) {
  const one = field.one();
  const inv2 = field.inv(field.add(one, one));
  const c_ = (j) => _poly_coeff(P3, j, field);
  const mul = (u, v) => field.mul(u, v);
  const add = (u, v) => field.add(u, v);
  const sub = (u, v) => field.sub(u, v);
  const neg = (u) => field.neg(u);

  function dbl(v) {
    return add(v, v);
  }

  const g2 = mul(sub(neg(c_(6)), one), inv2);                        // P3_6 = −(2γ₂ + 1)
  const q5 = dbl(g2);                                                // [x^5]Q_3²
  const g1 = mul(sub(sub(neg(c_(5)), mul(g2, g2)), q5), inv2);       // P3_5 = −(γ₂²+2γ₁ + q5)
  const q4 = add(mul(g2, g2), dbl(g1));
  const g0 = mul(sub(sub(sub(neg(c_(4)), one), dbl(mul(g2, g1))), q4), inv2);  // P3_4 = −(2γ₀+2γ₂γ₁ + q4) − 1
  const q3 = add(dbl(g0), dbl(mul(g2, g1)));
  const q2 = add(mul(g1, g1), dbl(mul(g2, g0)));
  const b = mul(sub(sub(neg(c_(3)), q2), q3), inv2);                 // P3_3 = −(q2+q3) − 2b
  const q1 = dbl(mul(g1, g0));
  const c = mul(sub(sub(sub(neg(c_(2)), q1), q2), mul(b, b)), inv2); // P3_2 = −(q1+q2) − (b²+2c)
  const q0 = mul(g0, g0);
  const alpha1 = add(add(add(c_(1), q0), q1), dbl(mul(b, c)));       // P3_1 = −(q0+q1) + α_1 − 2bc
  const alpha0 = add(sub(add(c_(0), q0), alpha1), mul(c, c));        // P3_0 = −q0 + α_1 + α_0 − c²

  const alpha6 = sub(g2, b);                                         // γ₂ = b + α_6
  const alpha5 = sub(sub(g1, c), mul(alpha6, b));                    // γ₁ = c + α_5 + α_6 b
  const alpha4 = sub(g0, mul(alpha6, add(c, alpha5)));               // γ₀ = α_6 (c + α_5) + α_4
  return [alpha0, alpha1, c, b, alpha4, alpha5, alpha6];
}

// ---------------------------------------------------------------------------
// Inner pair from its squares: Ψ = x·T1² + T2²  (lem:compatible-power)
// ---------------------------------------------------------------------------
//
// The 8k+3 step exposes the inner splittable pair (T1, T2) only through
// Ψ = x·T1² + T2² on the degrees >= deg T1.  The paper recovers the pair via
// the square-closure certificate; numerically we solve the map vals -> Ψ by
// descending affine pivots after *re-parameterizing* the pair: every
// Q-sub-block is replaced by its free polynomial coefficients (the known-powers
// Q maps are coefficient-bijective by lem:Q-unitriangular), recursively through
// the family tree.  In these coordinates each unknown first appears affinely
// with a constant slope, so `_decode_by_descending_pivots` applies; the actual
// parameter blocks are then extracted from the recovered sub-polynomials by the
// same Q-decoders the top-level families use.

// py: tools/polychain.py:383
function _pairsq_psi(T1, T2, field) {
  return _poly_add(_poly_shift_xk(_poly_square(T1, field), 1, field), _poly_square(T2, field), field);
}

// py: tools/polychain.py:387
// Free-coordinate parameterization of the splittable pair for odd m.
//
// Returns [nvals, build, extract] with build(vals) -> [T1, T2] and
// extract(vals) -> the paper parameter block α' (extract runs the
// appropriate Q-block decoders on the recovered free polynomials).
function _pair_free(m, field) {
  const one = field.one();
  const sq = (p) => _poly_square(p, field);
  const add = (p, q) => _poly_add(p, q, field);
  const sub = (p, q) => _poly_sub(p, q, field);
  const addc = (p, c) => _poly_add_const(p, c, field);

  if (m <= 5 || m % 4 === 1) {
    // The T-tower families are descending-triangular in their own
    // parameters (cf. the pivot tables of lem:4k+1-splittable / lem:Rk2l).
    function build(vals) {
      const [T1, T2] = _poly_paper_splittable_pair({ n: m, alpha: vals.slice(), field });
      return [T1, T2];
    }

    return [m, build, (vals) => vals.slice()];
  }

  if (m === 15) {
    // [α0..α7 | S free(7)] with S = Q7(x,H2,H4).
    function build(vals) {
      const a8 = vals.slice(0, 8);
      const S = vals.slice(8, 15).concat([one]);
      const H2 = [a8[6], a8[7], one];
      const H4 = addc(sub(sq(H2), sq([a8[5], one])), a8[4]);
      const T1 = addc(sub(sq(S), sq(addc(H2, a8[3]))), a8[1]);
      const T2 = addc(add(T1, sub(sq(H4), sq(addc(H2, a8[2])))), a8[0]);
      return [T1, T2];
    }

    function extract(vals) {
      const H2 = [vals[6], vals[7], one];
      const H4 = addc(sub(sq(H2), sq([vals[5], one])), vals[4]);
      const S = _poly_trim(vals.slice(8, 15).concat([one]), field);
      const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
        Q: S, k: 3, Hs: [_x(field), H2, H4], field,
      });
      return vals.slice(0, 8).concat(q7);
    }

    return [15, build, extract];
  }

  if (m === 27) {
    // [α0, α1, α2, α3 | Q3 free(3) | S3 free(7) | S1 free(13)].
    function build(vals) {
      const H2 = [vals[2], vals[3], one];
      const q3 = vals.slice(4, 7).concat([one]);
      const S3 = vals.slice(7, 14).concat([one]);
      const S1 = vals.slice(14, 27).concat([one]);
      const T1 = addc(sub(sq(S1), sq(q3)), vals[1]);
      const T2 = add(T1, addc(sub(sq(S3), sq(H2)), vals[0]));
      return [T1, T2];
    }

    function extract(vals) {
      const H2 = [vals[2], vals[3], one];
      const q3poly = _poly_trim(vals.slice(4, 7).concat([one]), field);
      const S3poly = _poly_trim(vals.slice(7, 14).concat([one]), field);
      const S1poly = _poly_trim(vals.slice(14, 27).concat([one]), field);
      const q3block = _decode_Q3_coeffs_to_alpha_given_H2(q3poly, H2, field);
      const q13 = _solve_Q4kp1(S1poly, 3, H2, field);
      const H4 = _Q4kp1_powers(q13, 3, H2, field)[2];
      const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
        Q: S3poly, k: 3, Hs: [_x(field), H2, H4], field,
      });
      return [vals[0], vals[1], vals[2], vals[3]].concat(q3block, q7, q13);
    }

    return [27, build, extract];
  }

  if (m === 31) {
    // [α0 | Q3 free(3) | H4 free(4) | S2 free(7) | α15 | S1 free(15)].
    function build(vals) {
      const S3q = vals.slice(1, 4).concat([one]);
      const H4 = vals.slice(4, 8).concat([one]);
      const S2 = vals.slice(8, 15).concat([one]);
      const a15 = vals[15];
      const S1 = vals.slice(16, 31).concat([one]);
      const T1 = add(sub(sq(S1), sq(S2)), S3q);
      const T2 = addc(sub(sq(addc(S1, a15)), sq(H4)), vals[0]);
      return [T1, T2];
    }

    function extract(vals) {
      const S3q = _poly_trim(vals.slice(1, 4).concat([one]), field);
      const H4 = _poly_trim(vals.slice(4, 8).concat([one]), field);
      const S2 = _poly_trim(vals.slice(8, 15).concat([one]), field);
      const S1 = _poly_trim(vals.slice(16, 31).concat([one]), field);
      const a47 = _h4_block_params(H4, field);
      const H2 = [a47[2], a47[3], one];
      const q3 = _decode_Q3_coeffs_to_alpha_given_H2(S3q, H2, field);
      const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
        Q: S2, k: 3, Hs: [_x(field), H2, H4], field,
      });

      function enc_bar(a) {
        return _poly_trim(_poly_paper_barQ_15({ alpha: a.slice(), H2, H4, field }), field);
      }

      const bar = _decode_by_descending_pivots({
        target: S1, encode_fn: enc_bar, nparams: 15, field, what: 'barQ15 given (H2,H4)',
      });
      return [vals[0]].concat(q3, a47, q7, [vals[15]], bar);
    }

    return [31, build, extract];
  }

  if (m % 8 === 3) {
    const kk = Math.floor((m - 3) / 8);
    const inner_len = 2 * kk + 1;
    const [n_inner, build_inner, extract_inner] = _pair_free(inner_len, field);
    const s3_free = kk === 1 ? 1 : 2 * kk - 1;
    const s2_free = 4 * kk + 1;
    // [α0 | S3 free | inner | a | S2 free].
    const nvals = 1 + s3_free + n_inner + 1 + s2_free;

    function build(vals) {
      const alpha0 = vals[0];
      const S3 = vals.slice(1, 1 + s3_free).concat(kk === 1 ? [] : [one]);
      const [S1_1, S1_2] = build_inner(vals.slice(1 + s3_free, 1 + s3_free + n_inner));
      const a = vals[1 + s3_free + n_inner];
      const S2 = vals.slice(-s2_free).concat([one]);
      const T1 = add(sub(sq(S2), sq(S1_1)), S3);
      const T2 = addc(sub(sq(addc(S2, a)), sq(S1_2)), alpha0);
      return [T1, T2];
    }

    function extract(vals) {
      const alpha0 = vals[0];
      const inner = extract_inner(vals.slice(1 + s3_free, 1 + s3_free + n_inner));
      const a = vals[1 + s3_free + n_inner];
      const [, , Hs] = _poly_paper_splittable_pair({ n: inner_len, alpha: inner, field });
      const H2 = Hs[1];
      const S2poly = _poly_trim(vals.slice(-s2_free).concat([one]), field);
      const S2block = _solve_Q4kp1(S2poly, kk, H2, field);
      let S3block;
      if (kk === 1) {
        S3block = [vals[1]];
      } else {
        const S3poly = _poly_trim(vals.slice(1, 1 + s3_free).concat([one]), field);
        const Hs2 = _Q4kp1_powers(S2block, kk, H2, field);
        S3block = _solve_Qodd(S3poly, 2 * kk - 1, Hs2, field);
      }
      return [alpha0].concat(S3block, inner, [a], S2block);
    }

    return [nvals, build, extract];
  }

  if (m % 8 === 7) {
    const kk = Math.floor((m - 7) / 8);
    const inner_len = 2 * kk + 1;
    const [n_inner, build_inner, extract_inner] = _pair_free(inner_len, field);
    const s2_free = 2 * kk + 1;
    const s3_free = 4 * kk + 3;
    // [inner | a | S2 free | b | S3 free].
    const nvals = n_inner + 1 + s2_free + 1 + s3_free;

    function build(vals) {
      const [S1_1, S1_2] = build_inner(vals.slice(0, n_inner));
      const a = vals[n_inner];
      const S2 = vals.slice(n_inner + 1, n_inner + 1 + s2_free).concat([one]);
      const b = vals[n_inner + 1 + s2_free];
      const S3 = vals.slice(-s3_free).concat([one]);
      const T1 = add(sub(sq(S3), sq(S2)), S1_1);
      const T2 = add(sub(sq(addc(S3, b)), sq(addc(S2, a))), S1_2);
      return [T1, T2];
    }

    function extract(vals) {
      const inner = extract_inner(vals.slice(0, n_inner));
      const a = vals[n_inner];
      const S2poly = _poly_trim(vals.slice(n_inner + 1, n_inner + 1 + s2_free).concat([one]), field);
      const b = vals[n_inner + 1 + s2_free];
      const S3poly = _poly_trim(vals.slice(-s3_free).concat([one]), field);
      let [, , Hs] = _poly_paper_splittable_pair({ n: inner_len, alpha: inner, field });
      const [enc2, hs2] = _build_Q_encoder(2 * kk + 1, Hs, field);
      const S2block = _decode_by_descending_pivots({
        target: S2poly, encode_fn: enc2, nparams: 2 * kk + 1, field, what: 'Q_{2k+1}',
      });
      Hs = hs2(S2block);
      const [enc3] = _build_Q_encoder(4 * kk + 3, Hs, field);
      const S3block = _decode_by_descending_pivots({
        target: S3poly, encode_fn: enc3, nparams: 4 * kk + 3, field, what: 'Q_{4k+3}',
      });
      return inner.concat([a], S2block, [b], S3block);
    }

    return [nvals, build, extract];
  }

  throw new Error(`internal error: no pair parameterization for m=${m}`);
}

// py: tools/polychain.py:566
// Parameter block α' of the inner splittable pair for odd m from
// Ψ = x·T1(α')² + T2(α')² known in degrees >= m−1 (lem:compatible-power).
function _decode_pairsq(m, psi, field) {
  const n = m - 1;
  const [nvals, build, extract] = _pair_free(m, field);

  function enc(vals) {
    const [T1, T2] = build(vals);
    return _pairsq_psi(T1, T2, field);
  }

  // rows=range(n, 2*n+2) -> explicit array of row indices.
  const rows = [];
  for (let w = n; w < 2 * n + 2; w++) rows.push(w);

  const vals = _decode_by_descending_pivots({
    target: psi, encode_fn: enc, nparams: nvals, field, rows,
    what: `pair-squares (m=${m})`,
  });
  const alpha = extract(vals);

  const [T1, T2] = _poly_paper_splittable_pair({ n: m, alpha, field });
  const chk = _pairsq_psi(T1, T2, field);
  for (let w = n; w < 2 * n + 2; w++) {
    if (!field.eq(_poly_coeff(chk, w, field), _poly_coeff(psi, w, field))) {
      throw new Error(`pair-squares (m=${m}): decoded block failed verification at degree ${w}`);
    }
  }
  return alpha;
}

// ---------------------------------------------------------------------------
// The 8k+3 induction step (lem:8k+3-splittable)
// ---------------------------------------------------------------------------

// py: tools/polychain.py:598
// Decode P_{8k+3} = x·S_2² + (S_2+a)² − x·S1_1² − S1_2² + x·S_3 + α_0
// following the proof of `lem:8k+3-splittable`:
//
//   1. square gadget at degree 4k+1 recovers (S_2, a); boundary error −1;
//   2. the window ≥ 2k of Ψ = x·S1_1² + S1_2² recovers the inner
//      splittable-pair block for 2k+1 (descending pivots — the numerical
//      realization of the compatibility/square-closure certificate);
//   3. the residual x·S_3 + α_0 gives α_0 and the S_3 = Q_{2k-1} block;
//   4. S_2 = Q_{4k+1}(x, H_2) is decoded given the recovered H_2.
function _decode_pair_8k3(coeffs, field) {
  const n = _poly_degree(coeffs);
  const k = Math.floor((n - 3) / 8);
  const m = 2 * k + 1;
  const one = field.one();
  const x = _x(field);

  // 1. Outer square gadget; the error term −x·S1_1² contributes −1 at degree 4k+1.
  const [S2poly, a] = _decode_square_gadget({
    G: coeffs, field, boundary_error_coeff_deg_d: field.neg(one),
  });
  const P1 = _poly_sub(coeffs, _square_gadget_poly(S2poly, a, field), field);

  // 2. Ψ = x·S1_1² + S1_2² on the window ≥ 2k (boundary at 2k corrected by
  //    the known top coefficient of x·S_3: 1 for k>1, 0 for k=1).
  const psi = [];
  for (let i = 0; i < 2 * m; i++) psi.push(field.zero());
  for (let d = 2 * k + 1; d < 4 * k + 2; d++) {
    psi[d] = field.neg(_poly_coeff(P1, d, field));
  }
  const s3_top = k > 1 ? one : field.zero();
  psi[2 * k] = field.sub(s3_top, _poly_coeff(P1, 2 * k, field));

  const inner = _decode_pairsq(m, psi, field);
  const [T1i, T2i, Hs] = _poly_paper_splittable_pair({ n: m, alpha: inner, field });
  const H2 = Hs[1];

  // 3. Residual x·S_3 + α_0.
  const psi_full = _poly_add(
    _poly_shift_xk(_poly_square(T1i, field), 1, field),
    _poly_square(T2i, field),
    field
  );
  const low = _poly_add(P1, psi_full, field);
  const alpha0 = _poly_coeff(low, 0, field);
  const S3poly = _shift_down(low, field);

  // 4. Sub-gadget parameter blocks.
  function enc_S2(av) {
    const [q] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k, l: 1, alpha: av.slice(), Hs: [x, H2], field,
    });
    return _poly_trim(q, field);
  }

  const S2block = _decode_by_descending_pivots({
    target: S2poly, encode_fn: enc_S2, nparams: 4 * k + 1, field, what: 'Q_{4k+1} given H2',
  });

  let S3block;
  if (k === 1) {
    if (_poly_degree(S3poly) > 0) {
      throw new Error('8k+3 decode: expected scalar S_3 for k=1');
    }
    S3block = [_poly_coeff(S3poly, 0, field)];
  } else {
    const [, hs2_raw] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k, l: 1, alpha: S2block, Hs: [x, H2], field,
    });
    const Hs2 = [x, H2].concat(hs2_raw.slice(2));

    function enc_S3(av) {
      const [q] = _poly_paper_Q_for_odd_degree_with_powers({
        deg: 2 * k - 1, alpha: av.slice(), Hs: Hs2, field,
      });
      return _poly_trim(q, field);
    }

    S3block = _decode_by_descending_pivots({
      target: S3poly, encode_fn: enc_S3, nparams: 2 * k - 1, field, what: 'Q_{2k-1}',
    });
  }

  const alpha = [alpha0].concat(S3block, inner, [a], S2block);
  if (alpha.length !== n) {
    throw new Error('internal error: 8k+3 parameter count mismatch');
  }
  return alpha;
}

// ---------------------------------------------------------------------------
// The 8k+7 induction step (lem:8k+7-splittable)
// ---------------------------------------------------------------------------

// py: tools/polychain.py:687
// Decode P_{8k+7} = x·S_3² + (S_3+b)² − x·S_2² − (S_2+a)² + P_{2k+1}
// following the proof of `lem:8k+7-splittable`: two nested square gadgets,
// then recursion on P_{2k+1}, then the Q blocks for S_2 and S_3.
function _decode_pair_8k7(coeffs, field) {
  const n = _poly_degree(coeffs);
  const k = Math.floor((n - 7) / 8);
  if (k < 2) {
    throw new Error('internal error: 8k+7 decoding requires k >= 2 (15 is special-cased)');
  }
  const one = field.one();

  const [S3poly, b] = _decode_square_gadget({
    G: coeffs, field, boundary_error_coeff_deg_d: field.neg(one),
  });
  const P1 = _poly_sub(coeffs, _square_gadget_poly(S3poly, b, field), field);

  const G2 = _poly_scale_int(P1, -1, field); // = x·S_2² + (S_2+a)² − P_{2k+1}
  const [S2poly, a] = _decode_square_gadget({
    G: G2, field, boundary_error_coeff_deg_d: field.neg(one),
  });
  const Pm = _poly_add(P1, _square_gadget_poly(S2poly, a, field), field); // = P_{2k+1}

  const inner = _decode_odd(_poly_trim(Pm, field), field, { pair_context: true });
  let [, , Hs] = _poly_paper_splittable_pair({ n: 2 * k + 1, alpha: inner, field });

  const [enc2, hs2] = _build_Q_encoder(2 * k + 1, Hs, field);
  const S2block = _decode_by_descending_pivots({
    target: S2poly, encode_fn: enc2, nparams: 2 * k + 1, field, what: 'Q_{2k+1}',
  });
  Hs = hs2(S2block);

  const [enc3] = _build_Q_encoder(4 * k + 3, Hs, field);
  const S3block = _decode_by_descending_pivots({
    target: S3poly, encode_fn: enc3, nparams: 4 * k + 3, field, what: 'Q_{4k+3}',
  });

  const alpha = inner.concat([a], S2block, [b], S3block);
  if (alpha.length !== n) {
    throw new Error('internal error: 8k+7 parameter count mismatch');
  }
  return alpha;
}

// ---------------------------------------------------------------------------
// Special case 27
// ---------------------------------------------------------------------------

// py: tools/polychain.py:736
// Decode the special-case construction for 27:
//   P = (x+1)·T_1 + S_3² − H_2² + α_0,   T_1 = S_1² − S_2² + α_1,
//   S_1 = Q_13(x,H_2)  (which yields H_4),  S_2 = Q_3(x,H_2),
//   S_3 = Q_7(x,H_2,H_4).
function _decode_pair_27(coeffs, field) {
  const one = field.one();
  const x = _x(field);
  const x_plus_1 = [one, one];

  // T_1 top coefficients by back-substitution on (x+1)T_1 (rows >= 15 clean;
  // row 14 carries the +1 of the monic S_3²).
  const t = new Map([[26, one]]);
  for (let j = 26; j > 14; j--) {
    t.set(j - 1, field.sub(_poly_coeff(coeffs, j, field), t.get(j)));
  }
  t.set(13, field.sub(field.sub(_poly_coeff(coeffs, 14, field), t.get(14)), one));

  // S_1² agrees with T_1 in degrees >= 13; monic square root (lem:monic-from-power, m=2).
  const S1_sq = [];
  for (let i = 0; i < 27; i++) S1_sq.push(field.zero());
  for (let j = 13; j < 27; j++) {
    S1_sq[j] = t.get(j);
  }
  const S1 = _monic_sqrt_from_high_square_coeffs(_poly_trim(S1_sq, field), 13, field);

  const P2 = _poly_sub(coeffs, _poly_mul(x_plus_1, _poly_square(S1, field), field), field);

  // S_3² from rows 8..14 of P2 (+1 correction at row 7 from the monic Q_3²).
  const S3_sq = [];
  for (let i = 0; i < 15; i++) S3_sq.push(field.zero());
  for (let j = 8; j < 15; j++) {
    S3_sq[j] = _poly_coeff(P2, j, field);
  }
  S3_sq[7] = field.add(_poly_coeff(P2, 7, field), one);
  const S3 = _monic_sqrt_from_high_square_coeffs(_poly_trim(S3_sq, field), 7, field);

  const P3 = _poly_sub(P2, _poly_square(S3, field), field);

  // Remaining low block: P3 = −(x+1)·Q_3² + (x+1)·α_1 − H_2² + α_0, read
  // from degree 6 downwards in the coefficients of Q_3 = x³+γ₂x²+γ₁x+γ₀
  // and H_2 = x²+bx+c (a triangular chain, one new quantity per degree).
  const low = _decode_27_low_block(P3, field);
  const H2 = [low[2], low[3], one];

  // S_1 = Q_13(x, H_2): the k=3, l=1 known-powers gadget; byproduct H_4.
  function enc_q13(a) {
    const [q] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k: 3, l: 1, alpha: a.slice(), Hs: [x, H2], field,
    });
    return _poly_trim(q, field);
  }

  const q13 = _decode_by_descending_pivots({
    target: S1, encode_fn: enc_q13, nparams: 13, field, what: 'Q13 given H2',
  });
  const [, hs_raw] = _poly_paper_Q_2lp1k_minus_1_with_powers({
    k: 3, l: 1, alpha: q13, Hs: [x, H2], field,
  });
  const H4 = hs_raw[2];

  const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
    Q: S3, k: 3, Hs: [_x(field), H2, H4], field,
  });

  const alpha = low.concat(q7, q13);
  if (alpha.length !== 27) {
    throw new Error('internal error: 27 parameter count mismatch');
  }
  return alpha;
}

// ---------------------------------------------------------------------------
// Special case 31
// ---------------------------------------------------------------------------

// py: tools/polychain.py:806
// Decode the special-case construction for 31:
//   P = x·S_1² + (S_1+α_15)² − x·S_2² − H_4² + x·S_3 + α_0,
//   S_1 = bar-Q_15(x,H_2,H_4), S_2 = Q_7(x,H_2,H_4), S_3 = Q_3(x,H_2),
//   H_4 = H_2² − (x+α_5)² + α_4.
function _decode_pair_31(coeffs, field) {
  const one = field.one();

  const [S1, a15] = _decode_square_gadget({
    G: coeffs, field, boundary_error_coeff_deg_d: field.neg(one),
  });
  const P1 = _poly_sub(coeffs, _square_gadget_poly(S1, a15, field), field);

  // S_2² from −P1 on rows 9..15 (row 8 corrected by the monic H_4²).
  const S2_sq = [];
  for (let i = 0; i < 15; i++) S2_sq.push(field.zero());
  for (let d = 9; d < 16; d++) {
    S2_sq[d - 1] = field.neg(_poly_coeff(P1, d, field));
  }
  S2_sq[7] = field.neg(field.add(_poly_coeff(P1, 8, field), one));
  const S2 = _monic_sqrt_from_high_square_coeffs(_poly_trim(S2_sq, field), 7, field);

  const P2 = _poly_add(P1, _poly_shift_xk(_poly_square(S2, field), 1, field), field);

  // H_4² from −P2 on rows 5..8 (row 4 corrected by the monic x·S_3).
  const H4_sq = [];
  for (let i = 0; i < 9; i++) H4_sq.push(field.zero());
  for (let d = 5; d < 9; d++) {
    H4_sq[d] = field.neg(_poly_coeff(P2, d, field));
  }
  H4_sq[4] = field.sub(one, _poly_coeff(P2, 4, field));
  const H4 = _monic_sqrt_from_high_square_coeffs(_poly_trim(H4_sq, field), 4, field);

  const low = _poly_add(P2, _poly_square(H4, field), field); // = x·S_3 + α_0
  const alpha0 = _poly_coeff(low, 0, field);
  const S3 = _shift_down(low, field);

  // α_4..α_7 from H_4 = H_2² − (x+α_5)² + α_4 with H_2 = x² + α_7 x + α_6.
  function enc_H4(a) {
    const H2 = [a[2], a[3], one];
    return _poly_add_const(
      _poly_sub(_poly_square(H2, field), _poly_square([a[1], one], field), field),
      a[0],
      field
    );
  }

  const a47 = _decode_by_descending_pivots({
    target: H4, encode_fn: enc_H4, nparams: 4, field, what: 'H4 block',
  });
  const H2 = [a47[2], a47[3], one];

  const q3 = _decode_Q3_coeffs_to_alpha_given_H2(S3, H2, field);
  const q7 = _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
    Q: S2, k: 3, Hs: [_x(field), H2, H4], field,
  });

  function enc_bar(a) {
    return _poly_trim(_poly_paper_barQ_15({ alpha: a.slice(), H2, H4, field }), field);
  }

  const bar = _decode_by_descending_pivots({
    target: S1, encode_fn: enc_bar, nparams: 15, field, what: 'barQ15 given (H2,H4)',
  });

  const alpha = [alpha0].concat(q3, a47, q7, [a15], bar);
  if (alpha.length !== 31) {
    throw new Error('internal error: 31 parameter count mismatch');
  }
  return alpha;
}

// py: tools/polychain.py:1170
// Run a callable with the peeled known-powers gadget mode enabled.
function _with_peeled(thunk) {
  set_peeled_q(true);
  try {
    return thunk();
  } finally {
    set_peeled_q(false);
  }
}
