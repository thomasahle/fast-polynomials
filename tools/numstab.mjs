// Numerical-stability experiment: rounding depth rho, schedule amplification A,
// and observed double-precision forward error (vs exact Q) for every method.
import { Q } from '../website/js/field.js';
import { Rat } from '../website/js/rat.js';
import * as P from '../website/js/poly.js';
import * as core from '../website/js/char0/core.js';
import { parseRhs } from '../website/js/cgen.js';
import { compileHorner } from '../website/js/methods/horner.js';
import { compileEstrin } from '../website/js/methods/estrin.js';
import { compileRW } from '../website/js/methods/rw.js';
import { compileMotzkin } from '../website/js/methods/motzkin.js';
import { writeFileSync } from 'fs';

const U = 2 ** -53;
let seed = 12345n;
const rnd = () => { seed = (seed * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n); return seed; };
const rint = (lo, hi) => lo + Number(rnd() % BigInt(hi - lo + 1));

// ---- line-chain evaluation over an "ops" object ----
// ops: { lit(tokenString)->val, wire(name)->val, add(a,b), sub(a,b), mul(a,b) }
function evalAst(node, ops) {
  if (node.tok !== undefined) {
    if (/^-?(0x[0-9a-fA-F]+|\d+(\.\d+)?([eE][+-]?\d+)?(\/\d+)?)$/.test(node.tok)) return ops.lit(node.tok);
    if (node.tok.startsWith('-')) return ops.sub(ops.zero, ops.wire(node.tok.slice(1)));
    return ops.wire(node.tok);
  }
  let acc = null;
  for (const { neg, t } of node.sum) {
    // with FMA: a two-factor product added to a running sum is fused (one rounding)
    if (ops.fma && acc !== null && t.length === 2) {
      const a = evalAst(t[0], ops), b = evalAst(t[1], ops);
      acc = ops.fma(neg ? -a : a, b, acc);
      continue;
    }
    let v = null;
    for (const f of t) { const fv = evalAst(f, ops); v = v === null ? fv : ops.mul(v, fv); }
    acc = acc === null ? (neg ? ops.sub(ops.zero, v) : v) : (neg ? ops.sub(acc, v) : ops.add(acc, v));
  }
  return acc;
}
function evalLines(lines, x, mk) {
  const env = { x };
  const ops = mk(name => env[name]);
  for (const l of lines) env[l.lhs] = evalAst(parseRhs(l.rhs), ops);
  return env[lines[lines.length - 1].lhs];
}
// rounding-depth over line chains: count rounded ops along worst path.
// constants: exactCoeffs=true -> 0 (they ARE the input coefficients), else 1 (preprocessed, rounded to fl)
function rhoLines(lines, constRho) {
  const env = { x: 0 };
  const opsR = w => env[w];
  const rho = node => {
    if (node.tok !== undefined) {
      if (/^-?(0x|\d)/.test(node.tok)) return constRho;
      return node.tok.startsWith('-') ? opsR(node.tok.slice(1)) : opsR(node.tok);
    }
    let best = 0;
    const m = node.sum.length;
    for (const { t } of node.sum) {
      let r = 0;
      for (const f of t) r += rho(f);   // product lemma: factors ADD across a product
      r += t.length - 1;                // one rounding per multiplication
      best = Math.max(best, r);
    }
    return best + (m - 1);              // additions
  };
  for (const l of lines) env[l.lhs] = rho(parseRhs(l.rhs));
  return env[lines[lines.length - 1].lhs];
}
const litRat = t => {
  const neg = t.startsWith('-'); if (neg) t = t.slice(1);
  let r;
  if (t.includes('/')) { const [a, b] = t.split('/'); r = new Rat(BigInt(a), BigInt(b)); }
  else if (t.includes('.') || /e/i.test(t)) { r = floatToRat(Number(t)); }
  else r = new Rat(BigInt(t));
  return neg ? r.neg() : r;
};
const floatToRat = doubleToRat;
// Correctly rounded conversion of an exact rational to the nearest double
// (round-half-to-even), via BigInt: this is the single rounding of the model.
function ratToDouble(r) {
  if (r.isZero()) return 0;
  const neg = r.n < 0n; let n = neg ? -r.n : r.n, d = r.d;
  // scale so that the quotient has 54..55 bits: q = floor(n * 2^k / d)
  const bl = v => v.toString(2).length;
  let k = 55 - (bl(n) - bl(d));
  let q = k >= 0 ? (n << BigInt(k)) / d : n / (d << BigInt(-k));
  let rem = k >= 0 ? (n << BigInt(k)) % d : n % (d << BigInt(-k));
  while (bl(q) > 55) { // adjust if estimate off by one
    k -= 1; q = k >= 0 ? (n << BigInt(k)) / d : n / (d << BigInt(-k));
    rem = k >= 0 ? (n << BigInt(k)) % d : n % (d << BigInt(-k));
  }
  while (bl(q) < 54) { k += 1; q = k >= 0 ? (n << BigInt(k)) / d : n / (d << BigInt(-k));
    rem = k >= 0 ? (n << BigInt(k)) % d : n % (d << BigInt(-k)); }
  // q has 54 or 55 bits; round to 53 significant bits (half-to-even, sticky from rem)
  const extra = bl(q) - 53;                  // 1 or 2 bits to drop
  const drop = q & ((1n << BigInt(extra)) - 1n);
  let m = q >> BigInt(extra);
  const half = 1n << BigInt(extra - 1);
  const sticky = rem !== 0n;
  if (drop > half || (drop === half && (sticky || (m & 1n) === 1n))) m += 1n;
  const e = extra - k;                       // value = m * 2^e
  let v = Number(m) * 2 ** e;
  if (!Number.isFinite(v)) v = Number(m) * 2 ** (e - 60) * 2 ** 60;
  return neg ? -v : v;
}
const ratToNum = r => ratToDouble(r);
function doubleToRat(v) {                    // exact dyadic conversion
  if (!Number.isFinite(v)) throw new Error('nonfinite');
  if (v === 0) return Rat.ZERO;
  let m = v, e = 0;
  while (!Number.isInteger(m)) { m *= 2; e++; }
  return new Rat(BigInt(m), 1n << BigInt(e));
}
// emulated fused multiply-add: correctly rounded a*b + c
const fma = (a, b, c) => {
  if (!Number.isFinite(a) || !Number.isFinite(b) || !Number.isFinite(c)) return a * b + c;   // propagate Inf/NaN
  const exact = doubleToRat(a).mul(doubleToRat(b)).add(doubleToRat(c));
  const abs = exact.isNeg() ? exact.neg() : exact;
  if (abs.n.toString().length - abs.d.toString().length > 309) return exact.isNeg() ? -Infinity : Infinity;  // overflow
  return ratToDouble(exact);
};
const FMA = (process.argv[5] ?? '') === 'fma';
const ratLog10 = r => {                              // robust for astronomically large ratios
  if (r.isZero()) return -Infinity;
  const n = (r.n < 0n ? -r.n : r.n).toString(), d = r.d.toString();
  const lead = s => Number(s.slice(0, 15)) / 10 ** (Math.min(s.length, 15) - 1);
  return (n.length - 1 + Math.log10(lead(n))) - (d.length - 1 + Math.log10(lead(d)));
};
const ratAbs = r => (r.isNeg() ? r.neg() : r);
const mkDouble = wire => ({ zero: 0, lit: t => ratToNum(litRat(t)), wire, add: (a, b) => a + b, sub: (a, b) => a - b, mul: (a, b) => a * b, fma: FMA ? fma : null });
const mkRat = wire => ({ zero: Rat.ZERO, lit: t => litRat(t), wire, add: (a, b) => a.add(b), sub: (a, b) => a.sub(b), mul: (a, b) => a.mul(b) });
const mkMajorant = wire => ({ zero: Rat.ZERO, lit: t => ratAbs(litRat(t)), wire, add: (a, b) => a.add(b), sub: (a, b) => a.add(b), mul: (a, b) => a.mul(b) });

// ---- our PolynomialChain (AffineForm with Map terms) ----
const cst = c => Rat.of(typeof c === 'number' ? BigInt(c) : c);
function evalOurs(chain, x, mode /* 'double' | 'rat' | 'maj' */) {
  const wires = { 0: mode === 'double' ? 1 : Rat.ONE, 1: x };
  const form = f => {
    let acc = mode === 'double' ? ratToNum(cst(f.const)) : (mode === 'maj' ? ratAbs(cst(f.const)) : cst(f.const));
    for (const [w, k] of f.terms) {
      if (k === 0) continue;
      const kk = mode === 'maj' ? Math.abs(k) : k;
      if (mode === 'double') acc = FMA ? fma(kk, wires[w], acc) : acc + kk * wires[w];
      else acc = acc.add(Rat.of(BigInt(kk)).mul(wires[w]));
    }
    return acc;
  };
  for (const g of chain.gates) {
    const l = form(g.left), r = form(g.right);
    wires[g.out_wire] = mode === 'double' ? l * r : l.mul(r);
  }
  return form(chain.output);
}
function rhoOurs(chain) {
  const rho = { 0: 1, 1: 0 };   // constant wire: preprocessed constant -> 1 rounding (representation)
  const formRho = f => {
    let terms = 0, best = 0;
    if (!cst(f.const).isZero()) { terms++; best = Math.max(best, 1); }
    for (const [w, k] of f.terms) {
      if (k === 0) continue;
      terms++;
      best = Math.max(best, rho[w] + (Math.abs(k) === 1 ? 0 : 1));
    }
    return best + Math.max(0, terms - 1);
  };
  for (const g of chain.gates) rho[g.out_wire] = 1 + formRho(g.left) + formRho(g.right);
  return formRho(chain.output);
}

// ---- experiment ----
const DEGREES = (process.argv[2] ? process.argv[2].split(',').map(Number) : [7, 15, 31, 63]);
const TRIALS = Number(process.argv[3] ?? 12);
const REGIME = process.argv[4] ?? 'coeffs';     // 'coeffs' | 'keys'
const results = {};
for (const n of DEGREES) {
  const rows = {};
  const stat = (name) => (rows[name] ??= { rho: null, A: [], err: [], errH: [] });
  let t0 = Date.now();
  for (let trial = 0; trial < TRIALS; trial++) {
    let coeffs, presetParams = null;
    if (REGIME === 'keys') {
      // hashing regime: random dyadic keys in [-1,1], polynomial induced by the chain
      const nparams = n;   // one key per coefficient (bijection)
      presetParams = Array.from({ length: nparams }, () => new Rat(BigInt(rint(-16, 16)), 16n));
      const cl = core._poly_paper_P_from_params({ params: presetParams, field: core.rationals() });
      coeffs = cl.map(c => Rat.of(typeof c === 'number' ? BigInt(c) : c));
    } else {
      coeffs = [...Array.from({ length: n }, () => new Rat(BigInt(rint(-5, 5)))), Rat.ONE];
    }
    if (coeffs.every((c, i) => i === n || c.isZero())) continue;
    const xs = Array.from({ length: 3 }, () => new Rat(BigInt(rint(-128, 128)), 64n));   // exact dyadic x in [-2,2]
    // chains
    const chains = {};
    chains.Horner = { lines: compileHorner(coeffs, Q).lines, cr: 0 };
    chains.Estrin = { lines: compileEstrin(coeffs, Q).lines, cr: 0 };
    chains['Rabin–Winograd'] = { lines: compileRW(coeffs, Q).lines, cr: 1 };
    try { chains['Motzkin–Eve'] = { lines: compileMotzkin(coeffs.map(ratToNum)).lines, cr: 1 }; } catch (e) { /* skip */ }
    const field = core.rationals();
    const params = presetParams ?? core.decode(n, coeffs, field);
    chains['this paper'] = { ours: core.compile_paper_params_chain(params, null) };
    for (const [name, ch] of Object.entries(chains)) {
      const st = stat(name);
      // rho is a property of the schedule, not of the sampled keys: a key that
      // happens to be 0 would drop a rounding, so measure it on generic keys.
      if (st.rho === null) st.rho = ch.ours
        ? rhoOurs(core.compile_paper_params_chain(Array.from({ length: n }, (_, i) => new Rat(BigInt(2 * i + 3), 7n)), null))
        : rhoLines(ch.lines, ch.cr);
      for (const x of xs) {
        const exact = P.evalAt(Q, coeffs, x);
        // Σ|a_i||x|^i exactly
        let Ssum = Rat.ZERO, xp = Rat.ONE, ax = ratAbs(x);
        for (let i = 0; i <= n; i++) { Ssum = Ssum.add(ratAbs(coeffs[i]).mul(xp)); xp = xp.mul(ax); }
        const xd = ratToNum(x);
        let approx, maj;
        if (ch.ours) { approx = evalOurs(ch.ours, xd, 'double'); maj = evalOurs(ch.ours, ax, 'maj'); }
        else { approx = evalLines(ch.lines, xd, mkDouble); maj = evalLines(ch.lines, ax, mkMajorant); }
        const Sd = ratToNum(Ssum);
        st.A.push(ratLog10(maj) - ratLog10(Ssum));     // log10 of the amplification
        if (!Number.isFinite(approx)) st.err.push(Infinity);   // overflow / NaN in double
        else st.err.push(Math.abs(approx - ratToNum(exact)) / (U * Sd));   // units of u·Σ|a_i||x|^i
      }
    }
  }
  const summarize = a => { const s = [...a].sort((p, q) => p - q); return { median: s[Math.floor(s.length / 2)], max: s[s.length - 1] }; };
  results[n] = {};
  for (const [name, st] of Object.entries(rows))
    results[n][name] = { rho: st.rho, logA: summarize(st.A), err: summarize(st.err),
                         overflow: st.err.filter(e => !Number.isFinite(e)).length, samples: st.err.length };
  console.error(`n=${n} done in ${((Date.now() - t0) / 1000).toFixed(1)}s`);
  for (const [name, r] of Object.entries(results[n]))
    console.log(`n=${n} ${name.padEnd(16)} rho=${String(r.rho).padStart(3)}  log10A med=${r.logA.median.toFixed(1)} max=${r.logA.max.toFixed(1)}  err/(uΣ) med=${r.err.median.toExponential(2)} max=${r.err.max.toExponential(2)}  overflow=${r.overflow}/${r.samples}`);
}
writeFileSync(new URL(`../notes/numstab_${REGIME}${FMA ? '_fma' : ''}.json`, import.meta.url), JSON.stringify(results, null, 1));
