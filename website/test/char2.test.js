import { GF2k } from '../js/field.js';
import * as P from '../js/poly.js';
import { CIRCUITS, evalCircuit, decodeChar2, circuitStats, SUPPORTED_DEGREES, CIRCUIT_DEGREES,
         MAX_DEGREE, baseDegree, isEverywhereDefined, keysFromQ } from '../js/char2.js';
import { compileChar2, circuitFor } from '../js/compile2.js';
import { parseRhs } from '../js/cgen.js';

let seed = 0x9e3779b97f4a7c15n;
const rnd = () => { seed ^= seed << 13n; seed &= (1n << 64n) - 1n;
  seed ^= seed >> 7n; seed ^= seed << 17n; seed &= (1n << 64n) - 1n; return seed; };
const randElt = F => rnd() & ((1n << BigInt(F.k)) - 1n);

const fields = [GF2k(1, 0b11n), GF2k(2, 0b111n), GF2k(4, 0b10011n),
                GF2k(8, 0x11bn), GF2k(64)];
let fails = 0;
const fail = msg => { console.log(`FAIL ${msg}`); fails++; };
const t0 = Date.now();
const since = () => `${((Date.now() - t0) / 1000).toFixed(1)}s`;
const STRESS = process.env.FAST_POLY_STRESS === '1';
const SMALL_RANDOM_TRIALS = STRESS ? 2000 : 250;
const PACKED_CROSS_TRIALS = STRESS ? 300 : 60;
const LARGE_RANDOM_TRIALS = STRESS
  ? [[64, 2000], [8, 20000]]
  : [[64, 200], [8, 2000]];
const PIPELINE_MONIC_TRIALS = STRESS ? 100 : 16;
const PIPELINE_NON_MONIC_TRIALS = STRESS ? 20 : 4;
console.log(`characteristic-2 ${STRESS ? 'stress' : 'fast'} suite`);

// ---------- structure: one circuit per odd degree, floor(n/2)+1 multiplications ----------
const ODD = [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25];
if (JSON.stringify(CIRCUIT_DEGREES) !== JSON.stringify(ODD)) fail(`circuit degrees ${CIRCUIT_DEGREES}`);
// the lane compiles every degree 1..26: odd degrees by their circuits, 1 and 2 directly,
// even degrees >= 4 by lifting the circuit of degree n-1 (compile2.js)
if (MAX_DEGREE !== 26 || JSON.stringify(SUPPORTED_DEGREES) !== JSON.stringify(Array.from({ length: 26 }, (_, i) => i + 1)))
  fail(`supported degrees ${SUPPORTED_DEGREES}`);
for (const n of SUPPORTED_DEGREES) {
  const m = n <= 2 || n % 2 ? n : n - 1;
  if (baseDegree(n) !== m) fail(`baseDegree(${n}) = ${baseDegree(n)}, want ${m}`);
  const spec = circuitFor(n);
  if (!spec || spec.n !== m || spec.keys !== m) fail(`n=${n}: circuitFor -> degree ${spec?.n}`);
  if (m >= 3 && spec !== CIRCUITS[m]) fail(`n=${n}: circuitFor is not CIRCUITS[${m}]`);
}
for (const n of CIRCUIT_DEGREES) {
  const spec = CIRCUITS[n], st = circuitStats(spec);
  if (spec.n !== n || spec.keys !== n) fail(`n=${n}: spec.n/keys`);
  if (st.mults !== Math.floor(n / 2) + 1) fail(`n=${n}: ${st.mults} multiplications, want ${Math.floor(n / 2) + 1}`);
  // every key index used exactly once, all wires defined before use
  const used = new Array(n).fill(0), wires = new Set(['x']);
  for (const gate of spec.gates) {
    for (const f of [gate.l, gate.r]) {
      if (f.k !== null) used[f.k]++;
      for (const tap of f.t) if (!wires.has(tap)) fail(`n=${n}: gate ${gate.w} taps undefined wire ${tap}`);
    }
    wires.add(gate.w);
  }
  if (spec.out.k !== null) used[spec.out.k]++;
  for (const tap of spec.out.t) if (!wires.has(tap)) fail(`n=${n}: output taps undefined wire ${tap}`);
  if (!used.every(u => u === 1)) fail(`n=${n}: key usage ${used}`);
  if (spec.rootDepths && spec.rootDepths.length !== n) fail(`n=${n}: rootDepths length`);
}
// decoder classes: polynomial (every characteristic-2 field) vs Frobenius (finite fields)
// (the lift and the degree-1/2 identities are polynomial: an even degree inherits its base circuit's class)
if (JSON.stringify(CIRCUIT_DEGREES.filter(isEverywhereDefined)) !== JSON.stringify([3, 5, 9, 11, 13, 15, 19, 21, 23, 25]))
  fail(`everywhere-defined set ${CIRCUIT_DEGREES.filter(isEverywhereDefined)}`);
if (JSON.stringify(SUPPORTED_DEGREES.filter(isEverywhereDefined)) !==
    JSON.stringify([1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24, 25, 26]))
  fail(`everywhere-defined set (all degrees) ${SUPPORTED_DEGREES.filter(isEverywhereDefined)}`);

// ---------- key/coefficient roundtrips over five fields ----------
for (const n of CIRCUIT_DEGREES) {
  const spec = CIRCUITS[n];
  const st = circuitStats(spec);
  let bad = 0;
  for (const F of fields) {
    // keys -> coeffs -> keys
    for (let trial = 0; trial < 20; trial++) {
      const keys = Array.from({ length: spec.keys }, () => randElt(F));
      const { coeffs } = evalCircuit(spec, keys, F);
      if (P.deg(coeffs) !== n || !F.isOne(coeffs[n])) { fail(`${n} ${F.name}: not monic deg ${n} (got ${P.deg(coeffs)})`); bad++; break; }
      const c = coeffs.slice(0, n);
      const dec = decodeChar2(n, c, F);
      if (!dec.every((k, i) => k === keys[i])) { fail(`${n} ${F.name}: key roundtrip`); bad++; break; }
    }
    // arbitrary monic coeffs -> keys -> coeffs
    for (let trial = 0; trial < 8; trial++) {
      const c = Array.from({ length: n }, () => randElt(F));
      const keys = decodeChar2(n, c, F);
      const { coeffs } = evalCircuit(spec, keys, F);
      const ok = P.deg(coeffs) === n && F.isOne(coeffs[n]) &&
        c.every((ci, i) => P.coeff(F, coeffs, i) === ci);
      if (!ok) { fail(`${n} ${F.name}: coeff roundtrip`); bad++; break; }
    }
  }
  console.log(`n=${n}: mults=${st.mults} adds=${st.adds} height=${st.height} family=${spec.family}  ${bad ? 'FAIL' : 'ok over ' + fields.length + ' fields'}`);
}

// ---------- small degrees: randomized monic polynomials over GF(2^64) ----------
const F64 = GF2k(64);
const SMALL = [3, 5, 7, 9, 11];
for (const n of SMALL) {
  const spec = CIRCUITS[n];
  let bad = 0;
  for (let trial = 0; trial < SMALL_RANDOM_TRIALS; trial++) {
    const c = Array.from({ length: n }, () => randElt(F64));
    const keys = decodeChar2(n, c, F64);
    const { coeffs } = evalCircuit(spec, keys, F64);
    if (!(P.deg(coeffs) === n && F64.isOne(coeffs[n]) && c.every((ci, i) => P.coeff(F64, coeffs, i) === ci))) { bad++; break; }
  }
  if (bad) fail(`n=${n}: GF(2^64) decode/re-expand`);
  else console.log(`n=${n}: ${SMALL_RANDOM_TRIALS} random monic polynomials over GF(2^64) decode and re-expand exactly (${since()})`);
  // the site's pipeline (monic and non-monic input; the re-expansion check throws on mismatch)
  for (let trial = 0; trial < 5; trial++) {
    const lead = trial === 0 ? 1n : (randElt(F64) | 1n);
    const coeffs = [...Array.from({ length: n }, () => randElt(F64)), lead];
    try {
      const r = compileChar2(coeffs, F64);
      const want = Math.floor(n / 2) + 1 + (lead === 1n ? 0 : 1);
      if (r.mults !== want) fail(`n=${n}: compileChar2 reports ${r.mults} multiplications, want ${want}`);
      if (r.n !== n || !r.lines.length || typeof r.mathText !== 'string') fail(`n=${n}: compileChar2 result shape`);
    } catch (e) { fail(`n=${n}: compileChar2 threw: ${e.message}`); }
  }
}

// ---------- exhaustive bijection over GF(4) ----------
// Packed GF(4)[x] arithmetic on two GF(2) bit-planes (lo = bit 0 of each
// coefficient, hi = bit 1; w = 0b10 with w^2 = w + 1, matching GF2k(2, 0b111)).
// A polynomial of degree <= 15 is one Number: lo in bits 0..15, hi in bits 16..31.
const clmul16 = (a, b) => { let r = 0; for (let i = 0; b; i++, b >>>= 1) if (b & 1) r ^= a << i; return r >>> 0; };
const gf4mul = (A, B) => {
  const a0 = A & 0xffff, a1 = A >>> 16, b0 = B & 0xffff, b1 = B >>> 16;
  const p00 = clmul16(a0, b0), p11 = clmul16(a1, b1), p01 = clmul16(a0, b1), p10 = clmul16(a1, b0);
  return (((p11 ^ p01 ^ p10) << 16) | (p00 ^ p11)) >>> 0;
};
const packElt = e => ((e & 1) | ((e >> 1) << 16)) >>> 0;   // GF(4) element (0..3) as a constant
function packedEval(spec, keyInts) {                        // keyInts: array of 0..3
  const w = { x: 2 };
  const factor = f => { let p = 0; for (const t of f.t) p ^= w[t]; if (f.k !== null) p ^= packElt(keyInts[f.k]); return p >>> 0; };
  for (const g of spec.gates) w[g.w] = gf4mul(factor(g.l), factor(g.r));
  return factor(spec.out);
}
const G4 = GF2k(2, 0b111n);
for (const n of SMALL) {
  const spec = CIRCUITS[n];
  // cross-validate the packed evaluator against evalCircuit over GF2k(2)
  let bad = 0;
  for (let trial = 0; trial < PACKED_CROSS_TRIALS; trial++) {
    const keyInts = Array.from({ length: n }, () => Number(rnd() & 3n));
    const packed = packedEval(spec, keyInts);
    const { coeffs } = evalCircuit(spec, keyInts.map(BigInt), G4);
    for (let i = 0; i <= 15; i++) {
      const e = Number(P.coeff(G4, coeffs, i));
      if (((packed >>> i) & 1) !== (e & 1) || ((packed >>> (16 + i)) & 1) !== (e >> 1)) bad++;
    }
  }
  if (bad) { fail(`n=${n}: packed GF(4) evaluator disagrees with evalCircuit`); continue; }
  // sweep all 4^n key vectors: output monic of degree n, all coefficient vectors distinct
  const total = 4 ** n, seen = new Uint8Array(total), lowMask = (1 << n) - 1;
  const keyInts = new Array(n).fill(0);
  let monicBad = 0, dup = 0;
  for (let idx = 0; idx < total; idx++) {
    for (let j = 0; j < n; j++) keyInts[j] = (idx >>> (2 * j)) & 3;
    const p = packedEval(spec, keyInts);
    const lo = p & 0xffff, hi = p >>> 16;
    if (((lo >>> n) & 1) !== 1 || (lo >>> (n + 1)) !== 0 || (hi >>> n) !== 0) { monicBad++; break; }
    const key = (lo & lowMask) | ((hi & lowMask) << n);
    if (seen[key]) { dup++; break; }
    seen[key] = 1;
  }
  if (monicBad || dup) fail(`n=${n}: GF(4) exhaustive — ${monicBad ? 'not monic degree ' + n : 'collision'}`);
  else console.log(`n=${n}: bijective GF(4)^${n} -> monic degree-${n} polynomials, all ${total} key vectors (${since()})`);
  // for n <= 7 also decode every coefficient vector back to its keys
  if (n <= 7) {
    let decBad = 0;
    for (let idx = 0; idx < total; idx++) {
      const keys = Array.from({ length: n }, (_, j) => BigInt((idx >>> (2 * j)) & 3));
      const { coeffs } = evalCircuit(spec, keys, G4);
      const dec = decodeChar2(n, coeffs.slice(0, n), G4);
      if (!dec.every((k, i) => k === keys[i])) { decBad++; break; }
    }
    if (decBad) fail(`n=${n}: GF(4) exhaustive decode roundtrip`);
    else console.log(`n=${n}: every one of the ${total} GF(4) key vectors decodes back exactly (${since()})`);
  }
}

// ---------- n = 23, 25: the core-B certificates (unit pivots, every char-2 field) ----------
// A GF(4) sweep is out of reach here (4^23 > 7e13 key vectors), so use randomized
// monic polynomials over GF(2^64) and GF(2^8), decoded and re-expanded exactly.
const F8 = GF2k(8, 0x11bn);
for (const n of [23, 25]) {
  const spec = CIRCUITS[n], st = circuitStats(spec);
  if (st.mults !== Math.floor(n / 2) + 1) fail(`n=${n}: ${st.mults} multiplications, want ${Math.floor(n / 2) + 1}`);
  if (!isEverywhereDefined(n)) fail(`n=${n}: not marked everywhere-defined`);
  for (const [bits, trials] of LARGE_RANDOM_TRIALS) {
    const F = bits === 64 ? F64 : F8;
    let bad = 0;
    for (let trial = 0; trial < trials; trial++) {
      const c = Array.from({ length: n }, () => randElt(F));
      const keys = decodeChar2(n, c, F);
      const { coeffs } = evalCircuit(spec, keys, F);
      if (!(P.deg(coeffs) === n && F.isOne(coeffs[n]) && c.every((ci, i) => P.coeff(F, coeffs, i) === ci))) { bad++; break; }
    }
    if (bad) fail(`n=${n}: ${F.name} decode/re-expand`);
    else console.log(`n=${n}: ${trials} random monic polynomials over ${F.name} decode and re-expand exactly (${since()})`);
  }
  // the unit-pivot structure of the coordinate change itself: row x^(n-1-i) of
  // P(A(Q)) minus the same row at the prefix point A(Q_0..Q_{i-1}, 0, ..) is exactly Q_i
  let tri = 0;
  for (let trial = 0; trial < 3; trial++) {
    const Q = Array.from({ length: n }, () => randElt(F8));
    const full = evalCircuit(spec, keysFromQ(n, Q, F8), F8).coeffs;
    for (let i = 0; i < n; i++) {
      const pre = evalCircuit(spec, keysFromQ(n, Q.map((v, t) => (t < i ? v : 0n)), F8), F8).coeffs;
      if ((P.coeff(F8, full, n - 1 - i) ^ P.coeff(F8, pre, n - 1 - i)) !== Q[i]) tri++;
    }
  }
  if (tri) fail(`n=${n}: coordinate change is not unit-triangular (${tri} rows)`);
  else console.log(`n=${n}: A(Q) is unit-triangular on all ${n} rows (3 random Q over GF(2^8), ${since()})`);
  // the site's pipeline (monic and non-monic input; the re-expansion check throws on mismatch)
  for (let trial = 0; trial < 3; trial++) {
    const lead = trial === 0 ? 1n : (randElt(F64) | 1n);
    const coeffs = [...Array.from({ length: n }, () => randElt(F64)), lead];
    try {
      const r = compileChar2(coeffs, F64);
      const want = Math.floor(n / 2) + 1 + (lead === 1n ? 0 : 1);
      if (r.mults !== want) fail(`n=${n}: compileChar2 reports ${r.mults} multiplications, want ${want}`);
      if (r.n !== n || !r.lines.length || typeof r.mathText !== 'string') fail(`n=${n}: compileChar2 result shape`);
    } catch (e) { fail(`n=${n}: compileChar2 threw: ${e.message}`); }
  }
}

// multiplications: floor(n/2)+1 from degree 3 on; degrees 1 and 2 are P = x + c0 and
// P = x (x + c1) + c0 (Horner-optimal: 0 and 1); a non-monic input adds the scale row
const wantMults = n => (n <= 2 ? n - 1 : Math.floor(n / 2) + 1);

// ---------- the site's pipeline over every registry field: GF(2^32), GF(2^64), GF(2^128) ----------
// decode -> exact re-expansion check -> chain + C (gfK_mul); non-monic input adds the scale gate
for (const F of [GF2k(32), GF2k(64), GF2k(128)]) {
  let bad = 0;
  for (const n of [1, 2, 13, 14, 15, 21, 25, 26]) {
    for (let trial = 0; trial < 3; trial++) {
      const lead = trial === 0 ? 1n : (randElt(F) | 2n);
      const coeffs = [...Array.from({ length: n }, () => randElt(F)), lead];
      try {
        const r = compileChar2(coeffs, F);
        const want = wantMults(n) + (lead === 1n ? 0 : 1);
        if (r.mults !== want || r.field.name !== F.name) { fail(`${F.name} n=${n}: compileChar2 mults ${r.mults} / field ${r.field.name}`); bad++; }
        if (typeof r.cText !== 'string' || !r.cText.includes(`gf${F.k}_mul(`) || (lead !== 1n) !== /leading coefficient/.test(r.cText))
          { fail(`${F.name} n=${n}: compileChar2 C rendering`); bad++; }
      } catch (e) { fail(`${F.name} n=${n}: compileChar2 threw: ${e.message}`); bad++; }
    }
  }
  if (!bad) console.log(`compileChar2 over ${F.name}: n = 1, 2, 13, 14, 15, 21, 25, 26, monic and non-monic, with C output (${since()})`);
}

// ---------- every degree 1..26 through the site's pipeline ----------
// The rendered chain (r.lines: the gate rows, the even-degree lift row
// P = x * P_{n-1} + c0, the scale row P = lc * P̃) is re-expanded over F[x] by an
// independent interpreter of the displayed rows (cgen.parseRhs on each rhs) and
// compared with the input coefficients exactly; the same for the paper rendering.
function expandLines(F, lines) {
  const wires = new Map([['x', P.X(F)]]);
  const atom = tok => {
    if (wires.has(tok)) return wires.get(tok);
    if (/^(0x[0-9a-f]+|\d+)$/i.test(tok)) return P.C(F, BigInt(tok));
    throw new Error(`unknown atom ${tok}`);
  };
  const evalNode = node => {
    if (node.tok !== undefined) return atom(node.tok);
    let sum = [];
    for (const { neg, t } of node.sum) {
      if (neg) throw new Error('subtraction in a char-2 chain');
      let prod = null;
      for (const f of t) prod = prod === null ? evalNode(f) : P.mul(F, prod, evalNode(f));
      sum = P.add(F, sum, prod);
    }
    return sum;
  };
  let last = null;
  for (const l of lines) {
    if (l.heading !== undefined) continue;
    last = evalNode(parseRhs(l.rhs.replace(/\s{2,}\([A-Za-z][A-Za-z -]*\)\s*$/, '')));  // drop the row comment
    wires.set(l.lhs, last);
  }
  return last;
}
for (const n of SUPPORTED_DEGREES) {
  const even = n >= 4 && n % 2 === 0;
  let bad = 0, nonMonic = 0;
  const pipelineTrials = PIPELINE_MONIC_TRIALS + PIPELINE_NON_MONIC_TRIALS;
  for (let trial = 0; trial < pipelineTrials && !bad; trial++) {
    const monic = trial < PIPELINE_MONIC_TRIALS;
    const lead = monic ? 1n : (randElt(F64) | 2n);
    if (!monic) nonMonic++;
    const coeffs = [...Array.from({ length: n }, () => randElt(F64)), lead];
    const input = P.normalize(F64, coeffs);
    let r;
    try { r = compileChar2(coeffs, F64); } catch (e) { fail(`n=${n}: compileChar2 threw: ${e.message}`); bad++; break; }
    const want = wantMults(n) + (monic ? 0 : 1);
    const err = msg => { fail(`n=${n}${monic ? '' : ' (non-monic)'}: ${msg}`); bad++; };
    if (r.n !== n || r.hornerMults !== n - 1 || r.baseDegree !== baseDegree(n)) err(`result shape n=${r.n} horner=${r.hornerMults} base=${r.baseDegree}`);
    if (r.mults !== want) err(`${r.mults} multiplications, want ${want}`);
    if (r.lines.filter(l => l.mul).length !== want) err(`${r.lines.filter(l => l.mul).length} multiplication rows, want ${want}`);
    if (r.linesPaper.filter(l => l.mul).length !== want) err(`paper rendering: multiplication rows`);
    if (monic && r.mults > r.hornerMults) err(`more multiplications than Horner (${r.mults} > ${r.hornerMults})`);   // hornerMults = n-1 is the monic count
    let back = null, backPaper = null;
    try { back = expandLines(F64, r.lines); backPaper = expandLines(F64, r.linesPaper); }
    catch (e) { err(`rendered rows do not parse: ${e.message}`); }
    if (back && !P.eqPoly(F64, back, input)) err('rendered chain does not re-expand to the input');
    if (backPaper && !P.eqPoly(F64, backPaper, input)) err('paper rendering does not re-expand to the input');
    if (typeof r.mathText !== 'string' || typeof r.mathTextOriginal !== 'string') err('mathText shape');
    // the extra rows: P_{n-1} then the lift row for even n >= 4; the scale row last for non-monic input
    const lift = r.lines.filter(l => /even-degree lift/.test(l.rhs));
    if (lift.length !== (even ? 1 : 0)) err(`${lift.length} lift rows`);
    if (even) {
      const i = r.lines.indexOf(lift[0]);
      const re = new RegExp(`^x \\* P_${n - 1}(   | \\+ (0x[0-9a-f]+|\\d+)   )\\(even-degree lift\\)$`);
      if (!re.test(lift[0].rhs) || !lift[0].mul) err(`lift row "${lift[0].rhs}"`);
      if (r.lines[i - 1].lhs !== `P_${n - 1}` || r.lines[i - 1].mul) err(`row before the lift is "${r.lines[i - 1].lhs}"`);
      if (lift[0].lhs !== (monic ? 'P' : 'P̃')) err(`lift row lhs "${lift[0].lhs}"`);
      if (!(r.liftStep && r.liftStep.mul)) err('liftStep missing');
    } else if (r.liftStep !== null) err('liftStep on an unlifted degree');
    const lastRow = r.lines[r.lines.length - 1];
    if (lastRow.lhs !== 'P') err(`last row is "${lastRow.lhs}"`);
    if (/leading-coefficient scale/.test(lastRow.rhs) !== !monic) err('scale row');
    if (!monic && r.lines[r.lines.length - 2].lhs !== 'P̃') err('scaled: penultimate row is not P̃');
    // counts: the lift adds one multiplication, one addition and one level of depth
    const spec = circuitFor(n), st = circuitStats(spec);
    const extra = even ? 1 : 0;
    if (r.adds !== st.adds + extra || r.height !== st.height + extra) err(`adds/height ${r.adds}/${r.height}`);
    // the graph IR carries exactly one '*' node per multiplication; C mirrors the rows
    if (!r.graph || r.graph.nodes.filter(nd => nd.kind === 'mul').length !== want) err('graph mul nodes');
    if (typeof r.cText !== 'string' || !r.cText.includes('eval_P')) err('C rendering missing');
    else {
      if (r.cText.includes('even-degree lift') !== even || r.cText.includes(`P_${n - 1}`) !== even) err('C lift row');
      if (/leading coefficient/.test(r.cText) !== !monic) err('C scale');
      if (!r.cText.includes(`${want} multiplications (Horner: ${n - 1}), ${n} key`)) err('C header counts');
      const body = r.cText.slice(r.cText.indexOf('eval_P('));                       // the header defines gf64_mul (per ISA)
      if ((body.match(/gf64_mul\(/g) || []).length !== want) err(`${(body.match(/gf64_mul\(/g) || []).length} gf64_mul calls, want ${want}`);
    }
  }
  if (!bad) console.log(`n=${n}: ${PIPELINE_MONIC_TRIALS} random monic + ${nonMonic} non-monic polynomials over GF(2^64) compile, re-expand exactly from the rendered rows, ${wantMults(n)} multiplications (+1 scale)${even ? ' (degree-' + (n - 1) + ' circuit + lift)' : ''} (${since()})`);
}
// out-of-range degrees: a readable message naming the frontier
for (const n of [27, 30, 40]) {
  try { compileChar2([...Array(n).fill(1n), 1n], F64); fail(`degree ${n} did not throw`); }
  catch (e) {
    if (!new RegExp(`^characteristic-2 chains exist for every degree up to 26 \\(you entered degree ${n}\\); degree 27 is the open frontier of the paper — see the outlook section\\.$`).test(e.message))
      fail(`degree ${n} message: ${e.message}`);
  }
}

if (fails) { console.log(`${fails} FAILURES`); process.exit(1); }
console.log(`ALL CHAR2 ROUNDTRIPS PASS (${since()})`);
