// g4_decode_prims.frag.js — decoder primitives from tools/poly_schedule.py.
// Fragment: function declarations only. Assembled into core.js after
// runtime.frag.js (Field, poly helpers, makeRng, PEELED_Q are in scope).
// Cross-group calls: _poly_paper_Q_2lp1k_minus_1_with_powers,
// _poly_paper_Q_known_powers (both g3, kwarg-only -> options object).

// g4 private helper: Python dict.get(key, default) over a Map.
function _g4_get(m, k, dflt) {
  return m.has(k) ? m.get(k) : dflt;
}

// py: tools/poly_schedule.py:2544
// Decode the "square gadget" from `sections/constructions.tex`, Lemma
// `lem:square-gadget`.
//
// Given a polynomial of the form
//     G = x*S^2 + (S + δ)^2 + E
// where S is monic of degree d and deg(E) <= d,
// recover (S, δ) assuming:
//   - char(F) != 2,
//   - and `boundary_error_coeff_deg_d` equals coeff(E, d) (defaults to 0).
//
// This matches how the lemma is used in the induction-step decoders, where
// the additive error term may have degree exactly d but its degree-d
// coefficient is known/derivable from surrounding structure.
// Returns [S, delta].
function _decode_square_gadget({ G, field, boundary_error_coeff_deg_d = null }) {
  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error('square gadget decoding requires char(F) != 2');
  }
  const inv2 = field.inv(two);

  G = _poly_trim(G, field);
  const degG = _poly_degree(G);
  if (degG < 3 || degG % 2 === 0) {
    throw new Error('square gadget expects odd degree >= 3');
  }
  if (!field.eq(_poly_coeff(G, degG, field), field.one())) {
    throw new Error('square gadget polynomial must be monic');
  }

  const d = Math.floor((degG - 1) / 2);
  if (boundary_error_coeff_deg_d === null) {
    boundary_error_coeff_deg_d = field.zero();
  }

  // Recover the coefficients of A = S^2 in degrees [d..2d] from the identities
  //   [x^i]G = A_{i-1} + A_i  for i=d+1..2d+1,
  // which are unaffected by the low-degree error term E.
  const A_high = new Map([[2 * d, field.one()]]); // Map<degree, field element>
  for (let i = 2 * d + 1; i > d; i--) { // i=2d+1 .. d+1
    const A_i = _g4_get(A_high, i, field.zero());
    const A_im1 = field.sub(_poly_coeff(G, i, field), A_i);
    A_high.set(i - 1, A_im1);
  }

  const A_partial = [];
  for (let j = 0; j < 2 * d + 1; j++) A_partial.push(field.zero());
  for (let j = d; j <= 2 * d; j++) {
    A_partial[j] = _g4_get(A_high, j, field.zero());
  }
  // Ensure monic at top.
  A_partial[2 * d] = field.one();

  const S = _monic_sqrt_from_high_square_coeffs(A_partial, d, field);
  const S_sq = _poly_square(S, field);

  // δ from the boundary coefficient at degree d:
  //   (G - x*S^2 - S^2)[d] = 2δ + E[d].
  const xS_sq = _poly_shift_xk(S_sq, 1, field);
  const D = _poly_sub(_poly_sub(G, xS_sq, field), S_sq, field);
  const coeff_D_d = _poly_coeff(D, d, field);
  const delta = field.mul(
    field.sub(coeff_D_d, field.coerce(boundary_error_coeff_deg_d)),
    inv2
  );

  return [S, delta];
}

// py: tools/poly_schedule.py:2889
// Coefficient-level version of `sections/constructions.tex`, Lemma
// `lem:peel-monic-factor`.
//
// Recover coefficients of a monic polynomial U of degree `factor_deg` from the
// *high* coefficients of the product P = U * known_factor, where
// `known_factor` is monic.
//
// Returns:
//     Map<degree, field element> mapping degrees -> coeff(U, degree) for
//     degrees in [min_deg..factor_deg] (inclusive), always including degree
//     `factor_deg` with coefficient 1.  (Python returns Dict[int, Number];
//     consumers use .items() / .get(deg, default) — iterate the Map with
//     for..of and read with _g4_get.)
function _recover_monic_factor_high_coeffs_from_product({
  product,
  known_factor,
  factor_deg,
  min_deg,
  field,
}) {
  if (min_deg > factor_deg) {
    throw new Error('min_deg must be <= factor_deg');
  }
  known_factor = _poly_trim(known_factor, field);
  product = _poly_trim(product, field);

  const degH = _poly_degree(known_factor);
  if (!field.eq(_poly_coeff(known_factor, degH, field), field.one())) {
    throw new Error('known_factor must be monic');
  }

  const U = new Map([[factor_deg, field.one()]]);
  for (let u_deg = factor_deg - 1; u_deg >= min_deg; u_deg--) {
    const p_deg = degH + u_deg;
    const target = _poly_coeff(product, p_deg, field);
    let known_sum = field.zero();

    // P_{degH+u_deg} = U_{u_deg} + sum_{j=1..t} U_{u_deg+j} * H_{degH-j}
    for (let j = 1; j <= factor_deg - u_deg; j++) {
      known_sum = field.add(
        known_sum,
        field.mul(U.get(u_deg + j), _poly_coeff(known_factor, degH - j, field))
      );
    }

    U.set(u_deg, field.sub(target, known_sum));
  }

  return U;
}

// py: tools/poly_schedule.py:2935
// Extract the scalar shift δ from Lemma `lem:scalar-shift-square`.
//
// Given:
//   - H monic degree d
//   - M monic degree e
//   - λ != 0
//   - coeff(P, d+e) where P = λ (H+δ)^2 M + E and deg(E) <= d+e-1
//
// Return:
//   δ
function _scalar_shift_from_square_boundary({ coeff_P_at_boundary, H, M, lam, field }) {
  const two = field.add(field.one(), field.one());
  if (field.is_zero(two)) {
    throw new Error('scalar-shift-square requires char(F) != 2');
  }
  if (field.is_zero(lam)) {
    throw new Error('lam must be nonzero');
  }

  H = _poly_trim(H, field);
  M = _poly_trim(M, field);
  const d = _poly_degree(H);
  const e = _poly_degree(M);
  if (!field.eq(_poly_coeff(H, d, field), field.one())) {
    throw new Error('H must be monic');
  }
  if (!field.eq(_poly_coeff(M, e, field), field.one())) {
    throw new Error('M must be monic');
  }

  // Compute coeff(H^2 * M, d+e).
  const H_sq = _poly_square(H, field);
  const boundary_deg = d + e;
  let coeff_H2M = field.zero();
  // coeff(H^2 M, boundary) = sum_i H_sq[i] * M[boundary-i]
  for (
    let i = Math.max(0, boundary_deg - e);
    i <= Math.min(boundary_deg, _poly_degree(H_sq));
    i++
  ) {
    coeff_H2M = field.add(
      coeff_H2M,
      field.mul(_poly_coeff(H_sq, i, field), _poly_coeff(M, boundary_deg - i, field))
    );
  }

  const num = field.sub(coeff_P_at_boundary, field.mul(lam, coeff_H2M));
  const den = field.mul(two, lam);
  return field.div(num, den);
}

// py: tools/poly_schedule.py:2987
// Random field element for probing (small integers in the rational case).
function _field_rand(field, rng) {
  if (field.modulus !== null) {
    // Python draws rng.randrange(p) directly; p exceeds Number range here, so
    // compose two 30-bit draws and reduce mod p via coerce.  Exact values need
    // not match Python (the callers self-verify; see makeRng note).
    const hi = rng.randrange(0, 1073741824); // 2^30
    const lo = rng.randrange(0, 1073741824); // 2^30
    return field.coerce((BigInt(hi) << 30n) | BigInt(lo));
  }
  return field.coerce(rng.randrange(-9, 10));
}

// py: tools/poly_schedule.py:2995
// Solve M x = rhs over `field` (M is r x c with r >= c).  Returns x, or null
// if M does not have full column rank.  Small dense elimination; the systems
// here have at most a handful of unknowns (the paper's 2x2 / 3x3 blocks).
function _field_gauss_solve(M, rhs, field) {
  const rows = M.map((row, idx) => row.concat([rhs[idx]]));
  const ncols = M.length ? M[0].length : 0;
  const piv_rows = [];
  for (let col = 0; col < ncols; col++) {
    let piv = null;
    for (const r of rows) {
      if (!field.is_zero(r[col])) {
        piv = r;
        break;
      }
    }
    if (piv === null) return null;
    rows.splice(rows.indexOf(piv), 1);
    const inv = field.inv(piv[col]);
    piv = piv.map((v) => field.mul(v, inv));
    for (const r of rows) {
      const f = r[col];
      if (!field.is_zero(f)) {
        for (let j = col; j <= ncols; j++) {
          r[j] = field.sub(r[j], field.mul(f, piv[j]));
        }
      }
    }
    piv_rows.push(piv);
  }
  // Back-substitute.
  const x = [];
  for (let i = 0; i < ncols; i++) x.push(field.zero());
  for (let col = ncols - 1; col >= 0; col--) {
    const r = piv_rows[col];
    let acc = r[ncols];
    for (let j = col + 1; j < ncols; j++) {
      acc = field.sub(acc, field.mul(r[j], x[j]));
    }
    x[col] = acc;
  }
  return x;
}

// py: tools/poly_schedule.py:3033
// Generic structural decoder for the paper's "descending affine pivot" maps.
//
// The paper's decoding lemmas (e.g. `lem:Q-unitriangular`, the pivot tables in
// `lem:4k+1-splittable` / `lem:Rk2l`, and the small linear blocks in
// `lem:barQ15` / `lem:septic-base`) all have the same shape: processing the
// coefficients of the output polynomial from high to low degree, each new
// coefficient exposes one fresh parameter affinely with a constant slope --
// or, occasionally, a small group of parameters that a constant affine system
// over a few otherwise-unused coefficient rows determines (the 2x2/3x3
// blocks).  This routine realizes that procedure numerically for an arbitrary
// encoder `encode_fn: params -> Poly`:
//
//   1. probe the encoder at two random points to find, for every parameter,
//      the set of coefficient rows it touches and its (constant) slopes;
//   2. eliminate parameters from the highest pivot row downwards, solving
//      collided pivot rows as small affine blocks over rows not touched by
//      any other unresolved parameter;
//   3. verify the result by re-encoding (raise `ValueError` on failure).
//
// `rows`, if given, restricts the usable coefficient window (used when only a
// window of the target polynomial is known, cf. the square-gadget steps).
function _decode_by_descending_pivots({
  target,
  encode_fn,
  nparams,
  field,
  rows = null,
  seed = 0,
  what = 'map',
}) {
  const rng = makeRng(0xc0ffee ^ seed ^ (nparams << 8));
  const allowed = rows === null ? null : new Set(rows);

  const bases = [];
  for (let t = 0; t < 2; t++) {
    const b = [];
    for (let i = 0; i < nparams; i++) b.push(_field_rand(field, rng));
    bases.push(b);
  }
  const enc_bases = bases.map((b) => encode_fn(b));

  // diffs[i][t]: row -> slope of parameter i probed at base t.
  const diffs = []; // Array<[Map<row, slope>, Map<row, slope>]>
  const support = []; // Array<Set<row>>
  for (let i = 0; i < nparams; i++) {
    const per_base = [];
    const sup = new Set();
    for (let t = 0; t < 2; t++) {
      const b2 = bases[t].slice();
      b2[i] = field.add(b2[i], field.one());
      const d = _poly_sub(encode_fn(b2), enc_bases[t], field);
      const entries = new Map();
      for (let deg = 0; deg < d.length; deg++) {
        if (!field.is_zero(d[deg])) {
          entries.set(deg, d[deg]);
          sup.add(deg);
        }
      }
      per_base.push(entries);
    }
    diffs.push(per_base);
    support.push(sup);
  }

  const piv_row = [];
  for (let i = 0; i < nparams; i++) {
    let cand;
    if (allowed === null) {
      cand = support[i];
    } else {
      cand = new Set();
      for (const w of support[i]) if (allowed.has(w)) cand.add(w);
    }
    if (cand.size === 0) {
      throw new Error(
        `${what}: parameter ${i} has no effect on the available coefficient window`
      );
    }
    let mx = null;
    for (const w of cand) if (mx === null || w > mx) mx = w;
    piv_row.push(mx);
  }

  // (The Python source defines _diff_vec twice, identically; one suffices.)
  function _diff_vec(a, b) {
    const d = _poly_sub(a, b, field);
    const out = new Map();
    for (let i = 0; i < d.length; i++) {
      if (!field.is_zero(d[i])) out.set(i, d[i]);
    }
    return out;
  }

  const recovered = [];
  for (let i = 0; i < nparams; i++) recovered.push(field.zero());
  const unresolved = new Set();
  for (let i = 0; i < nparams; i++) unresolved.add(i);

  while (unresolved.size > 0) {
    let r = null;
    for (const i of unresolved) if (r === null || piv_row[i] > r) r = piv_row[i];
    let group = [];
    for (const i of unresolved) if (piv_row[i] === r) group.push(i);
    group.sort((a, b) => a - b);

    // Slopes are evaluated lazily at the *current* partial point: by the
    // time a pivot block is reached, all higher-pivot parameters are known,
    // so the block acts affinely there with the constant slopes the paper's
    // pivot lemmas provide.
    const base_now = encode_fn(recovered);
    const cols = new Map(); // param index -> Map<row, slope>

    const _col = (i) => {
      if (!cols.has(i)) {
        const probe = recovered.slice();
        probe[i] = field.add(probe[i], field.one());
        cols.set(i, _diff_vec(encode_fn(probe), base_now));
      }
      return cols.get(i);
    };

    // Grow the block downwards (merging lower pivot groups) until enough
    // clean affine equation rows exist -- the numerical analogue of the
    // paper's small linear blocks (e.g. the 2x2 solve in `lem:barQ15`).
    while (true) {
      const others = [];
      for (const i of unresolved) if (!group.includes(i)) others.push(i);
      let candidates = [];
      for (let w = r; w >= 0; w--) {
        if (allowed !== null && !allowed.has(w)) continue;
        if (others.some((j) => support[j].has(w))) continue;
        if (group.every((i) => field.is_zero(_g4_get(_col(i), w, field.zero())))) continue;
        candidates.push(w);
        if (candidates.length >= group.length + 6) break;
      }

      // Affineness checks on the candidate rows (cheap when the initial
      // two-point probe already agreed there).
      const bad_rows = new Set();
      for (const i of group) {
        const needs_check = candidates.some(
          (w) =>
            !field.eq(_g4_get(diffs[i][0], w, field.zero()), _g4_get(_col(i), w, field.zero())) ||
            !field.eq(_g4_get(diffs[i][1], w, field.zero()), _g4_get(_col(i), w, field.zero()))
        );
        if (!needs_check) continue;
        const probe = recovered.slice();
        probe[i] = field.add(probe[i], field.add(field.one(), field.one()));
        const d2 = _diff_vec(encode_fn(probe), base_now);
        for (const w of candidates) {
          const s = _g4_get(_col(i), w, field.zero());
          if (!field.eq(_g4_get(d2, w, field.zero()), field.add(s, s))) {
            bad_rows.add(w);
          }
        }
      }
      if (group.length <= 8) {
        for (let ai = 0; ai < group.length; ai++) {
          for (let bi = ai + 1; bi < group.length; bi++) {
            const i = group[ai];
            const j = group[bi];
            const probe = recovered.slice();
            probe[i] = field.add(probe[i], field.one());
            probe[j] = field.add(probe[j], field.one());
            const dij = _diff_vec(encode_fn(probe), base_now);
            for (const w of candidates) {
              const want = field.add(
                _g4_get(_col(i), w, field.zero()),
                _g4_get(_col(j), w, field.zero())
              );
              if (!field.eq(_g4_get(dij, w, field.zero()), want)) {
                bad_rows.add(w);
              }
            }
          }
        }
      }
      candidates = candidates.filter((w) => !bad_rows.has(w));

      let solved = false;
      if (candidates.length >= group.length) {
        const M = candidates.map((w) => group.map((i) => _g4_get(_col(i), w, field.zero())));
        const rhs = candidates.map((w) =>
          field.sub(_poly_coeff(target, w, field), _poly_coeff(base_now, w, field))
        );
        const sol = _field_gauss_solve(M, rhs, field);
        if (sol !== null) {
          for (let t = 0; t < group.length; t++) {
            recovered[group[t]] = sol[t];
            unresolved.delete(group[t]);
          }
          solved = true;
        }
      }
      if (solved) break;
      if (others.length === 0) {
        throw new Error(`${what}: not enough clean rows to solve pivot group at degree ${r}`);
      }
      let r_next = null;
      for (const i of others) if (r_next === null || piv_row[i] > r_next) r_next = piv_row[i];
      group = group.concat(others.filter((i) => piv_row[i] === r_next));
      group.sort((a, b) => a - b);
    }
  }

  const chk = encode_fn(recovered);
  if (allowed === null) {
    if (!_poly_eq(chk, target, field)) {
      throw new Error(`${what}: descending-pivot decode failed verification`);
    }
  } else {
    for (const w of allowed) {
      if (!field.eq(_poly_coeff(chk, w, field), _poly_coeff(target, w, field))) {
        throw new Error(`${what}: descending-pivot decode failed verification (row ${w})`);
      }
    }
  }
  return recovered;
}

// py: tools/poly_schedule.py:3503
// Decode the `Q_5[α0..α4](x,H2)` instance that arises as the k=1, l=1 case of
// `_paper_Q_2lp1k_minus_1_with_powers` (Lemma `lem:Q4k+1-from-H2` with k=1),
// by the lemma's descending affine pivots (via `_decode_by_descending_pivots`).
function _decode_Q5_coeffs_to_alpha_given_H2(Q5, H2, field) {
  Q5 = _poly_trim(Q5, field);
  H2 = _poly_trim(H2, field);
  if (_poly_degree(Q5) !== 5 || !field.eq(_poly_coeff(Q5, 5, field), field.one())) {
    throw new Error('Q5 decoder expects a monic degree-5 polynomial');
  }
  if (_poly_degree(H2) !== 2 || !field.eq(_poly_coeff(H2, 2, field), field.one())) {
    throw new Error('Q5 decoder expects monic degree-2 H2');
  }

  const x = [field.zero(), field.one()];

  const _enc = (a) => {
    const [out, _hs, _tilde] = _poly_paper_Q_2lp1k_minus_1_with_powers({
      k: 1,
      l: 1,
      alpha: a.slice(),
      Hs: [x, H2],
      field,
    });
    return out;
  };

  return _decode_by_descending_pivots({
    target: Q5,
    encode_fn: _enc,
    nparams: 5,
    field,
    what: 'Q5-given-H2',
  });
}

// py: tools/poly_schedule.py:3526
// Decode `Q_3[α0,α1,α2](x,H2) = (x+α2)(H2+α1) + α0` given monic quadratic H2.
//
// This matches the direct algebra in sections/constructions.tex.
function _decode_Q3_coeffs_to_alpha_given_H2(Q3, H2, field) {
  Q3 = _poly_trim(Q3, field);
  H2 = _poly_trim(H2, field);
  if (_poly_degree(Q3) !== 3 || !field.eq(_poly_coeff(Q3, 3, field), field.one())) {
    throw new Error('Q3 decoder expects monic degree-3 polynomial');
  }
  if (_poly_degree(H2) !== 2 || !field.eq(_poly_coeff(H2, 2, field), field.one())) {
    throw new Error('Q3 decoder expects monic degree-2 H2');
  }

  const h1 = _poly_coeff(H2, 1, field);
  const h0 = _poly_coeff(H2, 0, field);

  const alpha2 = field.sub(_poly_coeff(Q3, 2, field), h1);
  const alpha1 = field.sub(
    _poly_coeff(Q3, 1, field),
    field.add(h0, field.mul(alpha2, h1))
  );
  const alpha0 = field.sub(
    _poly_coeff(Q3, 0, field),
    field.mul(alpha2, field.add(h0, alpha1))
  );
  return [alpha0, alpha1, alpha2];
}

// py: tools/poly_schedule.py:3549
// Decode `Q_7[α0..α6](x,H2,H4)` given monic (H2,H4).
//
// In paper notation:
//   S1 = H4 + α3
//   S2 = H4 + α2
//   Q7 = A_2[α0,α1, β2=α4, β1=α5, β0=α6](S1,S2,(x,H2))
//
// This is a solver-free coefficient decoder; it mirrors
// `tools/impl/q_decode.py:decode_Q7`.
function _decode_Q7_coeffs_to_alpha_given_H2_H4(Q7, H2, H4, field) {
  Q7 = _poly_trim(Q7, field);
  H2 = _poly_trim(H2, field);
  H4 = _poly_trim(H4, field);
  if (_poly_degree(Q7) !== 7 || !field.eq(_poly_coeff(Q7, 7, field), field.one())) {
    throw new Error('Q7 decoder expects monic degree-7 polynomial');
  }
  if (_poly_degree(H2) !== 2 || !field.eq(_poly_coeff(H2, 2, field), field.one())) {
    throw new Error('Q7 decoder expects monic degree-2 H2');
  }
  if (_poly_degree(H4) !== 4 || !field.eq(_poly_coeff(H4, 4, field), field.one())) {
    throw new Error('Q7 decoder expects monic degree-4 H4');
  }

  const h2_1 = _poly_coeff(H2, 1, field);
  const h2_0 = _poly_coeff(H2, 0, field);

  const h4_3 = _poly_coeff(H4, 3, field);
  const h4_2 = _poly_coeff(H4, 2, field);
  const h4_1 = _poly_coeff(H4, 1, field);
  const h4_0 = _poly_coeff(H4, 0, field);

  // In A2 notation, n = deg(S1) = deg(S2) = 4.
  const n = 4;

  // beta0 (=α6) from [x^{n+2}]Q = beta0 + [x^{n+1}]A1 + [x^{n+2}]A2.
  // Here [x^{n+2}]A2 = 1, and [x^{n+1}]A1 = h2_1 + h4_3 (since alpha3 is constant).
  const beta0 = field.sub(
    field.sub(_poly_coeff(Q7, n + 2, field), field.add(h2_1, h4_3)),
    field.one()
  );

  // High-degree coefficients of A1 and A2 are independent of alpha2/alpha3 and alpha0/alpha1.
  // Use Q_d = A1_{d-1} + beta0*A1_d + A2_d.
  const A1_6 = field.one();
  const A2_6 = field.one();
  const A2_5 = field.add(h2_1, h4_3);

  const A1_5 = field.sub(_poly_coeff(Q7, 6, field), field.add(beta0, A2_6));
  // A1_4 from degree 5 equation: Q5 = A1_4 + beta0*A1_5 + A2_5.
  const A1_4 = field.sub(
    _poly_coeff(Q7, 5, field),
    field.add(field.mul(beta0, A1_5), A2_5)
  );
  const beta1 = field.sub(
    A1_4,
    field.add(h2_0, field.add(field.mul(h2_1, h4_3), h4_2))
  );

  // A1_3 depends only on known H2/H4 and beta1.
  const A1_3 = field.add(
    h4_1,
    field.add(field.mul(h2_1, h4_2), field.mul(field.add(h2_0, beta1), h4_3))
  );
  // Degree 4 equation: Q4 = A1_3 + beta0*A1_4 + A2_4.
  const A2_4 = field.sub(
    _poly_coeff(Q7, 4, field),
    field.add(A1_3, field.mul(beta0, A1_4))
  );
  const beta2 = field.sub(
    A2_4,
    field.add(h2_0, field.add(field.mul(h2_1, h4_3), h4_2))
  );

  // A2_3 depends only on known H2/H4 and beta2.
  const A2_3 = field.add(
    h4_1,
    field.add(field.mul(h2_1, h4_2), field.mul(field.add(h2_0, beta2), h4_3))
  );
  // Degree 3 equation: Q3 = A1_2 + beta0*A1_3 + A2_3.
  const A1_2 = field.sub(
    _poly_coeff(Q7, 3, field),
    field.add(field.mul(beta0, A1_3), A2_3)
  );
  const base_A1_2 = field.add(
    h4_0,
    field.add(field.mul(h2_1, h4_1), field.mul(field.add(h2_0, beta1), h4_2))
  );
  const alpha3 = field.sub(A1_2, base_A1_2);

  // A1_1 = [x^1]((H2+beta1)*(H4+alpha3)), alpha1 doesn't contribute.
  const base_A1_1 = field.add(
    field.mul(h2_1, h4_0),
    field.mul(field.add(h2_0, beta1), h4_1)
  );
  const A1_1 = field.add(base_A1_1, field.mul(alpha3, h2_1));
  // Degree 2 equation: Q2 = A1_1 + beta0*A1_2 + A2_2.
  const A2_2 = field.sub(
    _poly_coeff(Q7, 2, field),
    field.add(A1_1, field.mul(beta0, A1_2))
  );
  const base_A2_2 = field.add(
    h4_0,
    field.add(field.mul(h2_1, h4_1), field.mul(field.add(h2_0, beta2), h4_2))
  );
  const alpha2 = field.sub(A2_2, base_A2_2);

  // A2_1 = [x^1]((H2+beta2)*(H4+alpha2)), alpha0 doesn't contribute.
  const base_A2_1 = field.add(
    field.mul(h2_1, h4_0),
    field.mul(field.add(h2_0, beta2), h4_1)
  );
  const A2_1 = field.add(base_A2_1, field.mul(alpha2, h2_1));

  // Degree 1 equation: Q1 = A1_0 + beta0*A1_1 + A2_1, where A1_0 includes alpha1.
  const A1_0 = field.sub(
    _poly_coeff(Q7, 1, field),
    field.add(field.mul(beta0, A1_1), A2_1)
  );
  const base_A1_0 = field.mul(field.add(h2_0, beta1), field.add(h4_0, alpha3));
  const alpha1 = field.sub(A1_0, base_A1_0);

  // Degree 0 equation: Q0 = beta0*A1_0 + A2_0, where A2_0 includes alpha0.
  const A2_0 = field.sub(_poly_coeff(Q7, 0, field), field.mul(beta0, A1_0));
  const base_A2_0 = field.mul(field.add(h2_0, beta2), field.add(h4_0, alpha2));
  const alpha0 = field.sub(A2_0, base_A2_0);

  // Map (beta0,beta1,beta2) to (α6,α5,α4).
  return [alpha0, alpha1, alpha2, alpha3, beta2, beta1, beta0];
}

// py: tools/poly_schedule.py:5838
// Decode `Q_{2^k-1}` (Algorithm `alg:constr-known-2n-1`) to its α-parameters.
//
// Constructive (paper-faithful) decoder following Algorithm `alg:decode-Q-2kminus1`.
function _decode_Q_power_of_2_minus_1_coeffs_to_alpha({ Q, k, Hs, field }) {
  Q = _poly_trim(Q, field);
  if (
    _poly_degree(Q) !== (1 << k) - 1 ||
    !field.eq(_poly_coeff(Q, (1 << k) - 1, field), field.one())
  ) {
    throw new Error('Q decoder expects monic degree (2^k-1)');
  }
  if (Hs.length < k) {
    throw new Error('Q decoder expects Hs=[x,H2,...,H_{2^{k-1}}]');
  }

  if (PEELED_Q && k >= 3) {
    // Q = (H_{2^{k-1}} + gamma) * W + B: divide by the known monic H
    // (quotient = W since deg(gamma*W + B) < deg H), read gamma at the
    // residual's top row (W and B are monic), subtract.
    const m = (1 << (k - 1)) - 1;
    const [W, R] = _poly_divmod_monic(Q, Hs[k - 1], field);
    if (_poly_degree(W) !== m || !field.eq(_poly_coeff(W, m, field), field.one())) {
      throw new Error('peeled Q decoder: quotient is not monic of the right degree');
    }
    const gamma = field.sub(_poly_coeff(R, m, field), field.one());
    const B = _poly_sub(R, _poly_scale_const(W, gamma, field), field);
    return [gamma]
      .concat(
        _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
          Q: W,
          k: k - 1,
          Hs: Hs.slice(0, k - 1),
          field,
        })
      )
      .concat(
        _decode_Q_power_of_2_minus_1_coeffs_to_alpha({
          Q: B,
          k: k - 1,
          Hs: Hs.slice(0, k - 1),
          field,
        })
      );
  }

  const x = Hs[0];
  if (k === 1) {
    // Q_1 = x + α0.
    if (_poly_degree(Q) !== 1) {
      throw new Error('Q1 must have degree 1');
    }
    return [field.sub(_poly_coeff(Q, 0, field), _poly_coeff(x, 0, field))];
  }
  if (k === 2) {
    return _decode_Q3_coeffs_to_alpha_given_H2(Q, Hs[1], field);
  }
  if (k === 3) {
    return _decode_Q7_coeffs_to_alpha_given_H2_H4(Q, Hs[1], Hs[2], field);
  }
  if (k < 4) {
    throw new Error('unreachable');
  }

  // k >= 4: by Lemma `lem:Q-unitriangular` the coefficient map of `Q_{2^k-1}`
  // is unitriangular from high to low degree in the encoder's own parameter
  // order: coeff_j = alpha_j + f_j(alpha_{j+1}, ..., alpha_{2^k-2}).  Solve by
  // descending back-substitution, re-encoding to evaluate each f_j.
  const q = (1 << k) - 1;
  const alpha = [];
  for (let i = 0; i < q; i++) alpha.push(field.zero());
  for (let j = q - 1; j >= 0; j--) {
    const cur = _poly_paper_Q_known_powers({ k, alpha, Hs, field });
    alpha[j] = field.sub(_poly_coeff(Q, j, field), _poly_coeff(cur, j, field));
  }

  const chk = _poly_paper_Q_known_powers({ k, alpha, Hs, field });
  if (!_poly_eq(chk, Q, field)) {
    throw new Error(
      'Q_{2^k-1} decode failed verification (input is not a Q instance for these powers)'
    );
  }
  return alpha;
}
