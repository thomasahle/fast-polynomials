// char0.test.js — port of the essential tests from tools/test_polychain.py
// for the char-0 lane JS port (website/js/char0/core.js).
// Plain node, no test framework: console asserts, process.exit(1) on failure.
// Golden vectors were generated from the Python reference implementation
// (tools/polychain.py) — see comments at each golden block.

import {
  Rat,
  GF,
  rationals,
  encode,
  decode,
  compile_paper_params_chain,
  makeRng,
  _poly_trim,
  _poly_paper_P_from_params,
} from '../js/char0/core.js';

let failures = 0;
let checks = 0;

function check(cond, msg) {
  checks += 1;
  if (!cond) {
    failures += 1;
    console.error(`FAIL: ${msg}`);
  }
}

function eqEl(field, a, b) {
  return field.eq(a, b);
}

function eqVec(field, xs, ys) {
  if (xs.length !== ys.length) return false;
  for (let i = 0; i < xs.length; i++) if (!field.eq(xs[i], ys[i])) return false;
  return true;
}

function show(field, xs) {
  return '[' + xs.map((x) => String(x)).join(', ') + ']';
}

// Horner evaluation of a dense ascending coefficient list at x.
function horner(coeffs, x, field) {
  let acc = field.zero();
  for (let i = coeffs.length - 1; i >= 0; i--) {
    acc = field.add(field.mul(acc, x), field.coerce(coeffs[i]));
  }
  return acc;
}

const MERSENNE61 = (1n << 61n) - 1n;

// =====================================================================
// (a) Concrete golden checks over Q (generated from Python 2026-08-29):
//   PYTHONPATH=tools python3 -c "import polychain as pc; ..."
//   encode(7, [1,2,-1,3,2,-2,1])  == [-9,11,-2,-12,15,21,8]
//   encode(15, [2,-1,1,3,-2,1,-1,2,1,-3,2,-1,1,2,-2]) ==
//     [170,648,908,60,-1299,-1359,92,1152,688,-207,-390,-112,51,43,11]
// =====================================================================
function testGolden() {
  const field = rationals();
  const goldens = [
    {
      n: 7,
      alphas: [1, 2, -1, 3, 2, -2, 1],
      coeffs: [-9, 11, -2, -12, 15, 21, 8],
    },
    {
      n: 15,
      alphas: [2, -1, 1, 3, -2, 1, -1, 2, 1, -3, 2, -1, 1, 2, -2],
      coeffs: [170, 648, 908, 60, -1299, -1359, 92, 1152, 688, -207, -390, -112, 51, 43, 11],
    },
  ];
  for (const { n, alphas, coeffs } of goldens) {
    const alphasF = alphas.map((a) => field.coerce(a));
    const coeffsF = coeffs.map((c) => field.coerce(c));
    // decode(coeffs + [1]) must return exactly the golden alphas
    const dec = decode(n, coeffsF.concat([field.one()]), field);
    check(
      eqVec(field, dec, alphasF),
      `golden n=${n}: decode mismatch\n  got ${show(field, dec)}\n  want ${show(field, alphasF)}`
    );
    // _poly_paper_P_from_params must re-expand to exactly the golden coeffs
    const P = _poly_trim(_poly_paper_P_from_params({ params: alphasF, field }), field);
    check(
      eqVec(field, P, coeffsF.concat([field.one()])),
      `golden n=${n}: P_from_params mismatch\n  got ${show(field, P)}`
    );
    // and JS encode must agree too
    const enc = encode(n, alphasF, field);
    check(eqVec(field, enc, coeffsF), `golden n=${n}: encode mismatch\n  got ${show(field, enc)}`);
  }
  console.log('golden checks done');
}

// =====================================================================
// (b) Round-trip over rationals, n = 1..40
// =====================================================================
function testRoundTripQ() {
  const field = rationals();
  const rng = makeRng(12345);
  for (let n = 1; n <= 40; n++) {
    // random small integer monic coeffs: decode -> re-expand -> exact compare
    const coeffs = [];
    for (let i = 0; i < n; i++) coeffs.push(field.coerce(rng.randrange(-9, 10)));
    coeffs.push(field.one());
    let alphas;
    try {
      alphas = decode(n, coeffs, field);
    } catch (e) {
      failures += 1;
      console.error(`FAIL: Q round-trip n=${n}: decode threw: ${e.message}`);
      continue;
    }
    const P = _poly_trim(_poly_paper_P_from_params({ params: alphas, field }), field);
    check(eqVec(field, P, coeffs), `Q round-trip n=${n}: re-expansion mismatch`);

    // encode(random small alphas) -> decode -> compare alphas
    const alphas2 = [];
    for (let i = 0; i < n; i++) alphas2.push(field.coerce(rng.randrange(-9, 10)));
    let coeffs2, dec2;
    try {
      coeffs2 = encode(n, alphas2, field);
      dec2 = decode(n, coeffs2.concat([field.one()]), field);
    } catch (e) {
      failures += 1;
      console.error(`FAIL: Q encode/decode n=${n}: threw: ${e.message}`);
      continue;
    }
    check(eqVec(field, dec2, alphas2), `Q encode->decode n=${n}: alpha mismatch`);
  }
  console.log('Q round-trips done (n=1..40)');
}

// =====================================================================
// (c) Round-trip over GF(2^61-1), n = 1..80 plus {97, 128, 200}
// =====================================================================
function testRoundTripGF() {
  const field = GF(MERSENNE61);
  const rng = makeRng(67890);
  const ns = [];
  for (let n = 1; n <= 80; n++) ns.push(n);
  ns.push(97, 128, 200);
  for (const n of ns) {
    const coeffs = [];
    for (let i = 0; i < n; i++) coeffs.push(field.coerce(rng.randrange(-9, 10)));
    coeffs.push(field.one());
    let alphas;
    try {
      alphas = decode(n, coeffs, field);
    } catch (e) {
      failures += 1;
      console.error(`FAIL: GF round-trip n=${n}: decode threw: ${e.message}`);
      continue;
    }
    const P = _poly_trim(_poly_paper_P_from_params({ params: alphas, field }), field);
    check(eqVec(field, P, coeffs), `GF round-trip n=${n}: re-expansion mismatch`);
  }
  console.log('GF(2^61-1) round-trips done (n=1..80, 97, 128, 200)');
}

// =====================================================================
// (d) Chain check: compile_paper_params_chain on decoded params.
//     mul count == (n<=1 ? 0 : n==2 ? 1 : floor(n/2)+1) for n in 3..120 (GF)
//     chain.eval(x0) == Horner(original coeffs, x0) at 5 random points
//     (over GF(p); over Q for n <= 20).
// =====================================================================
function expectedMulCount(n) {
  return n <= 1 ? 0 : n === 2 ? 1 : Math.floor(n / 2) + 1;
}

function testChainGF() {
  const field = GF(MERSENNE61);
  const rng = makeRng(24680);
  for (let n = 3; n <= 120; n++) {
    const coeffs = [];
    for (let i = 0; i < n; i++) coeffs.push(field.coerce(rng.randrange(-9, 10)));
    coeffs.push(field.one());
    let alphas, chain;
    try {
      alphas = decode(n, coeffs, field);
      chain = compile_paper_params_chain(alphas, MERSENNE61);
      chain.validate();
    } catch (e) {
      failures += 1;
      console.error(`FAIL: GF chain n=${n}: threw: ${e.message}`);
      continue;
    }
    check(
      chain.mul_count === expectedMulCount(n),
      `GF chain n=${n}: mul_count ${chain.mul_count} != ${expectedMulCount(n)}`
    );
    for (let t = 0; t < 5; t++) {
      const x0 = field.coerce(rng.randrange(-1000000, 1000000));
      const got = chain.eval(x0);
      const want = horner(coeffs, x0, field);
      check(eqEl(field, got, want), `GF chain n=${n}: eval mismatch at point ${t}`);
    }
  }
  console.log('GF chain checks done (n=3..120)');
}

function testChainQ() {
  const field = rationals();
  const rng = makeRng(13579);
  for (let n = 3; n <= 20; n++) {
    const coeffs = [];
    for (let i = 0; i < n; i++) coeffs.push(field.coerce(rng.randrange(-9, 10)));
    coeffs.push(field.one());
    let alphas, chain;
    try {
      alphas = decode(n, coeffs, field);
      chain = compile_paper_params_chain(alphas, null);
      chain.validate();
    } catch (e) {
      failures += 1;
      console.error(`FAIL: Q chain n=${n}: threw: ${e.message}`);
      continue;
    }
    check(
      chain.mul_count === expectedMulCount(n),
      `Q chain n=${n}: mul_count ${chain.mul_count} != ${expectedMulCount(n)}`
    );
    for (let t = 0; t < 5; t++) {
      const x0 = field.coerce(rng.randrange(-50, 51));
      const got = chain.eval(x0);
      const want = horner(coeffs, x0, field);
      check(eqEl(field, got, want), `Q chain n=${n}: eval mismatch at point ${t}`);
    }
  }
  console.log('Q chain checks done (n=3..20)');
}

// =====================================================================
// (e) Registry fields of the char-0 lane: GF(2^127-1) round trips through
//     core.GF (same decoder, larger prime), and the compileChar0 pipeline
//     end to end for 'p61', 'p127' (exact), 'Q', 'R' and 'C' (the same exact
//     rational chain; R displays and emits its constants as doubles, C — over
//     the Gaussian rationals — displays them as complex doubles, no C yet):
//     decode -> chain -> chain.eval == Horner exactly, for n = 3..20 and a
//     few larger degrees; R's C body must be identical to Q's float style.
// =====================================================================
const MERSENNE127 = (1n << 127n) - 1n;
function testRoundTripGF127() {
  const field = GF(MERSENNE127);
  const rng = makeRng(31337);
  for (let n = 1; n <= 40; n++) {
    const coeffs = [];
    for (let i = 0; i < n; i++) coeffs.push(field.coerce(rng.randrange(-9, 10)));
    coeffs.push(field.one());
    let alphas, chain;
    try {
      alphas = decode(n, coeffs, field);
      chain = compile_paper_params_chain(alphas, MERSENNE127);
      chain.validate();
    } catch (e) {
      failures += 1;
      console.error(`FAIL: GF(2^127-1) round-trip n=${n}: threw: ${e.message}`);
      continue;
    }
    const P = _poly_trim(_poly_paper_P_from_params({ params: alphas, field }), field);
    check(eqVec(field, P, coeffs), `GF(2^127-1) round-trip n=${n}: re-expansion mismatch`);
    for (let t = 0; t < 3; t++) {
      const x0 = field.coerce((BigInt(rng.randrange(0, 1073741824)) << 97n) | BigInt(rng.randrange(0, 1073741824)));
      check(eqEl(field, chain.eval(x0), horner(coeffs, x0, field)), `GF(2^127-1) chain n=${n}: eval mismatch`);
    }
  }
  console.log('GF(2^127-1) round-trips done (n=1..40)');
}

const intSrc = ints => ints.map((c, i) => `${c < 0 ? '-' : '+'}${Math.abs(c)}${i === 0 ? '' : i === 1 ? 'x' : 'x^' + i}`)
  .reverse().join('').replace(/^\+/, '');

async function testCompilePipeline() {
  const { compileChar0 } = await import('../js/compile0.js');
  const { fieldById } = await import('../js/field.js');
  const { GaussRat } = await import('../js/gauss.js');
  const { Rat } = await import('../js/rat.js');
  const { COMPLEX_TOKEN, COMPLEX_SRC } = await import('../js/tokens.js');
  const rng = makeRng(4242);
  const ns = Array.from({ length: 18 }, (_, i) => i + 3).concat([23, 31]);
  for (const n of ns) {
    const ints = Array.from({ length: n + 1 }, (_, i) => (i === n ? 1 : rng.randrange(-9, 10) || 3));
    const src = intSrc(ints);
    const results = {};
    for (const mode of ['p61', 'p127', 'Q', 'R', 'C']) {
      let r;
      try { r = await compileChar0(src, mode); }
      catch (e) { failures += 1; console.error(`FAIL: compileChar0 ${mode} n=${n}: threw: ${e.message}`); continue; }
      results[mode] = r;
      check(r.mults === expectedMulCount(n), `compileChar0 ${mode} n=${n}: mults ${r.mults} != ${expectedMulCount(n)}`);
      const fd = fieldById(mode), exact = fd.exact;
      check(r.fieldId === mode && r.exact === exact && r.status === (exact ? 'exact' : '≈ numeric') &&
            r.field.name === { p61: 'GF(2^61−1)', p127: 'GF(2^127−1)', Q: 'ℚ', R: 'ℝ', C: 'ℂ' }[mode],
        `compileChar0 ${mode} n=${n}: field info`);
      // C is rendered unless a constant exceeds the double range (Q / R only);
      // a field without an emitter yet (registry cCode false) renders none, silently
      const cOk = typeof r.cText === 'string' && r.cText.includes('eval_P');
      check(fd.cCode ? cOk || (!exact || mode === 'Q') && /no C rendering: constant -?Infinity/.test(r.note)
                     : r.cText === null && r.cTextFraction === null && !/no C rendering/.test(r.note), `compileChar0 ${mode} n=${n}: C rendering`);
      // independent exact evaluation check against Horner in the field of the chain
      const field = r.chain.field;
      const dense = ints.map(c => field.coerce(BigInt(c)));
      for (let t = 0; t < 3; t++) {
        const x0 = field.coerce(field.modulus === null ? rng.randrange(-50, 51) : rng.randrange(-1000000, 1000000));
        check(eqEl(field, r.chain.eval(x0), horner(dense, x0, field)), `compileChar0 ${mode} n=${n}: eval mismatch at point ${t}`);
      }
      if (!exact) {
        // no C (constants beyond the double range) ⇒ an infinite error; the converse can fail:
        // representable constants whose evaluation overflows at the sample points still get C
        check(typeof r.maxRelError === 'number' && r.maxRelError >= 0 && (!fd.cCode || r.cText !== null || r.maxRelError === Infinity),
          `compileChar0 ${mode} n=${n}: maxRelError ${r.maxRelError}`);
        check(!/\d\/\d/.test(r.mathText) && /≈ numeric/.test(r.note), `compileChar0 ${mode} n=${n}: constants shown as doubles`);
      }
      if (mode === 'C') {
        // real input: every constant a real double, never a complex token, and a
        // Gaussian point with Im x ≠ 0 evaluates as Horner does
        check(!/[\d+\-−(]\s*i\b/.test(r.mathText) && r.chain.field.modulus === null, `compileChar0 C n=${n}: real input shows real doubles`);
        const x = new GaussRat(new Rat(-3n, 7n), new Rat(2n, 5n));
        check(eqEl(r.chain.field, r.chain.eval(x), horner(dense, x, r.chain.field)), `compileChar0 C n=${n}: eval mismatch at a complex point`);
      }
    }
    // R is Q's chain with the constants printed as doubles: same structure, and
    // the C below the banner is byte-identical to Q's float style
    const q = results.Q, r = results.R;
    if (q && r) {
      check(q.mathText.split('\n').length === r.mathText.split('\n').length && q.mults === r.mults && q.adds === r.adds && q.height === r.height,
        `compileChar0 R n=${n}: same chain shape as Q`);
      check(q.chain.gates.every((g, i) => q.chain.field.eq(g.left.const, r.chain.gates[i].left.const) && q.chain.field.eq(g.right.const, r.chain.gates[i].right.const)),
        `compileChar0 R n=${n}: same exact constants as Q`);
      // (Q's table comments carry the exact fractions, R's only the slot name: compare code, not comments)
      const body = t => (t === null ? null : t.slice(t.indexOf('/* chain constants')).replace(/[ \t]*\/\/.*$/gm, ''));
      check(body(q.cText) === body(r.cText), `compileChar0 R n=${n}: C code identical to Q (float constants)`);
    }
    // C on a real input is Q's chain over ℚ(i): same shape, the same exact constants, R's display
    const c = results.C;
    if (q && r && c) {
      check(q.mathText.split('\n').length === c.mathText.split('\n').length && q.mults === c.mults && q.adds === c.adds && q.height === c.height,
        `compileChar0 C n=${n}: same chain shape as Q`);
      check(q.chain.gates.every((g, i) => c.chain.field.eq(g.left.const, c.chain.gates[i].left.const) && c.chain.field.eq(g.right.const, c.chain.gates[i].right.const)),
        `compileChar0 C n=${n}: same exact constants as Q`);
      check(c.mathText === r.mathText && c.maxRelError === r.maxRelError, `compileChar0 C n=${n}: a real input displays exactly as R`);
    }
  }
  // R: decimal inputs are parsed exactly (0.5 = 1/2, 1.5e-1 = 3/20) and rendered
  // back as doubles; the leading-coefficient scale shows the double
  const r = await compileChar0('0.5x^7 + 0.25x^5 - 1.5e-1x^3 + 2x - 0.125', 'R');
  check(r.mults === expectedMulCount(7) + 1 && /P̃/.test(r.mathText) && r.maxRelError < 1e-12, 'compileChar0 R: decimal, non-monic input');
  check(/0\.5 \* P̃/.test(r.mathText) && !/\d\/\d/.test(r.mathText), 'compileChar0 R: double constants in the math view');
  const q = await compileChar0('0.5x^7 + 0.25x^5 - 1.5e-1x^3 + 2x - 0.125', 'Q');
  check(/1\/2 \* P̃/.test(q.mathText) && q.mults === r.mults, 'compileChar0 Q: the same input shows exact fractions');
  // shortest round-trip decimals, scientific notation when needed
  const tiny = await compileChar0('0.0000001x^5 + x^3 + 0.5x + 3', 'R');
  check(/1e-7 \* P̃/.test(tiny.mathText) && /return P \* 1e-7;/.test(tiny.cText) && /10000001/.test(tiny.mathText), 'compileChar0 R: 1e-7 rendering');
  const tiny2 = await compileChar0('x^5 + 0.0000001x + 3', 'R');
  check(/1\.0000001/.test(tiny2.mathText) && /1\.0000001/.test(tiny2.cText) && !/\d\/\d/.test(tiny2.mathText), 'compileChar0 R: 1.0000001 rendering');
  // C: complex coefficients parse (i, 2i, (1+2i), (1/2-3/4i)), every non-real
  // constant is the canonical (re±imi) token, the leading-coefficient scale
  // shows the complex double, and the chain agrees with Horner at complex points
  {
    const src = '(1+2i)x^5 + ix^3 - 2x + (1/2-3/4i)';
    const c = await compileChar0(src, 'C');
    check(c.mults === expectedMulCount(5) + 1 && /\(1\+2i\) \* P̃/.test(c.mathText) && c.maxRelError < 1e-12, `compileChar0 C: complex non-monic input (${c.mults}, ${c.maxRelError})`);
    const toks = c.mathText.match(new RegExp(COMPLEX_SRC, 'g')) ?? [];
    check(toks.length >= 2 && toks.every(t => COMPLEX_TOKEN.test(t)) && !/[\d+\-−(]\s*i\b/.test(c.mathText.replace(new RegExp(COMPLEX_SRC, 'g'), '')),
      `compileChar0 C: canonical complex tokens only (${toks.join(' ')})`);
    const { parsePoly } = await import('../js/polyparse.js');
    const cs = parsePoly(src, { complex: true }).coeffs;
    for (const x of [new GaussRat(new Rat(1n, 3n), new Rat(-2n, 7n)), GaussRat.I, new GaussRat(new Rat(5n), new Rat(0n))])
      check(c.chain.eval(x).mul(cs[5]).eq(horner(cs, x, c.chain.field)), `compileChar0 C: eval at ${x}`);
    // degree 2 (the smallest even lift): with and without a linear term, in every char-0 display
    for (const [src2, mode2] of [['x^2 + 1', 'Q'], ['x^2 + 3x + 1', 'Q'], ['x^2 + 1', 'R'], ['x^2 + i', 'C'], ['x^2 + (1+2i)x + 1', 'C']]) {
      const d2 = await compileChar0(src2, mode2);
      check(d2.mults === 1 && /P_1|P/.test(d2.mathTextOriginal ?? '') && typeof d2.mathText === 'string', `compileChar0 ${mode2} degree 2 (${src2}): ${d2.mults} mults, original form renders`);
    }
    const c2 = await compileChar0('2ix^4 + x + 1', 'C');
    check(/\(0\+2i\) \* P̃/.test(c2.mathText) && /\(0-0\.5i\)/.test(c2.mathText) && /double complex/.test(c2.cText ?? ''),
      'compileChar0 C: purely imaginary constants print as (0±bi), and the C99 rendering exists');
  }
  console.log('compileChar0 pipeline checks done (p61, p127, Q, R, C; n = 3..20, 23, 31)');
}

testGolden();
testRoundTripQ();
testRoundTripGF();
testChainGF();
testChainQ();
testRoundTripGF127();
await testCompilePipeline();

if (failures > 0) {
  console.error(`\n${failures} failure(s) out of ${checks} checks`);
  process.exit(1);
}
console.log(`\nAll ${checks} checks passed`);
