import { GF2k, Q } from '../js/field.js';
import { Rat } from '../js/rat.js';
import * as P from '../js/poly.js';
import { compileHorner } from '../js/methods/horner.js';
import { compileEstrin } from '../js/methods/estrin.js';

// tiny evaluator for rendered chain lines: rhs = sum of terms, term = atom | atom * atom
function evalLines(lines, F, x, parseConst) {
  const env = { x };
  const atom = s => {
    s = s.trim();
    if (s.startsWith('(') && s.endsWith(')')) return sum(s.slice(1, -1));
    if (s in env) return env[s];
    return parseConst(s);
  };
  const splitTop = (s, sep) => {
    const parts = []; let d = 0, cur = '';
    for (const ch of s) {
      if (ch === '(') d++;
      if (ch === ')') d--;
      if (d === 0 && s.startsWith) {}
      cur += ch;
    }
    // simpler: no nested parens beyond depth 1 in our formats
    const out = []; let depth = 0, buf = '';
    for (let i = 0; i < s.length; i++) {
      const ch = s[i];
      if (ch === '(') depth++;
      if (ch === ')') depth--;
      if (depth === 0 && s.slice(i, i + sep.length) === sep) { out.push(buf); buf = ''; i += sep.length - 1; }
      else buf += ch;
    }
    out.push(buf);
    return out;
  };
  const prod = s => splitTop(s, ' * ').map(atom).reduce((a, b) => F.mul(a, b));
  const sum = s => {
    // handle both ' + ' and typographic ' \u2212 ' (subtraction)
    const addParts = splitTop(s, ' + ');
    return addParts.map(part => {
      const subParts = splitTop(part, ' \u2212 ');
      return subParts.map(prod).reduce((a, b) => F.sub(a, b));
    }).reduce((a, b) => F.add(a, b));
  };
  for (const l of lines) env[l.lhs] = sum(l.rhs);
  return env[lines[lines.length - 1].lhs];
}

let seed = 77n;
const rnd = () => { seed = (seed * 6364136223846793005n + 1442695040888963407n) & ((1n<<64n)-1n); return seed; };
let fails = 0;

// char2 lane
for (const n of [13, 15, 21]) {
  const F = GF2k(64);
  const coeffs = [...Array.from({ length: n }, () => rnd()), 1n];
  const parseC = s => BigInt(s);
  for (const [nm, fn] of [['horner', compileHorner], ['estrin', compileEstrin]]) {
    const r = fn(coeffs, F);
    for (let t = 0; t < 5; t++) {
      const x = rnd();
      const got = evalLines(r.lines, F, x, parseC);
      const want = P.evalAt(F, coeffs, x);
      if (got !== want) { console.log(`FAIL ${nm} n=${n} char2`); fails++; break; }
    }
    console.log(`${nm} n=${n} GF(2^64): mults=${r.mults} adds=${r.adds} height=${r.height}`);
  }
}
// char0 lane
{
  const F = Q;
  const coeffs = [new Rat(3n,2n), new Rat(-2n), Rat.ZERO, new Rat(7n), new Rat(1n,3n), new Rat(-1n), Rat.ONE];
  const parseC = s => {
    const neg = s.startsWith('-'); if (neg) s = s.slice(1);
    const [a, b] = s.split('/');
    const r = new Rat(BigInt(a), b ? BigInt(b) : 1n);
    return neg ? r.neg() : r;
  };
  for (const [nm, fn] of [['horner', compileHorner], ['estrin', compileEstrin]]) {
    const r = fn(coeffs, F);
    for (let t = 0; t < 5; t++) {
      const x = new Rat(BigInt(t * 3 - 7), 2n);
      const got = evalLines(r.lines, F, x, parseC);
      const want = P.evalAt(F, coeffs, x);
      if (!got.eq(want)) { console.log(`FAIL ${nm} char0 at t=${t}: got ${got} want ${want}`); fails++; break; }
    }
    console.log(`${nm} deg 6 over Q: mults=${r.mults} adds=${r.adds} height=${r.height}`);
  }
}
if (fails) process.exit(1);
console.log('METHOD BASELINES PASS');

// ---- Rabin-Winograd ----
import { compileRW } from '../js/methods/rw.js';
{
  let rwfails = 0;
  for (const n of [3, 4, 5, 7, 8, 9, 13, 15, 16, 21, 31, 32, 40, 63, 64, 100]) {
    const F = GF2k(64);
    const coeffs = [...Array.from({ length: n }, () => rnd()), 1n];
    let r;
    try { r = compileRW(coeffs, F); }
    catch (e) { console.log(`rw n=${n} char2: ${e.message.slice(0, 50)}`); continue; }
    for (let t = 0; t < 5; t++) {
      const x = rnd();
      const got = evalLines(r.lines, F, x, s => BigInt(s));
      const want = P.evalAt(F, coeffs, x);
      if (got !== want) { console.log(`FAIL rw n=${n} char2`); rwfails++; break; }
    }
    const bound = Math.ceil(n / 2) + Math.ceil(Math.log2(n)) + 2;
    if (r.mults > bound) { console.log(`FAIL rw count n=${n}: ${r.mults} > ${bound}`); rwfails++; }
    console.log(`rw n=${n} GF(2^64): mults=${r.mults} (bound ${bound}) adds=${r.adds} height=${r.height}`);
  }
  // char0 over Q
  const F = Q;
  const parseC = s => {
    const neg = s.startsWith('-'); if (neg) s = s.slice(1);
    const [a, b] = s.split('/');
    const r = new Rat(BigInt(a), b ? BigInt(b) : 1n);
    return neg ? r.neg() : r;
  };
  for (const n of [4, 7, 9, 10, 15, 23]) {
    let seedq = 5n;
    const coeffs = [...Array.from({ length: n }, (_, i) => new Rat(BigInt((i * 7 + 3) % 11 - 5), BigInt(1 + (i % 3)))), Rat.ONE];
    let r;
    try { r = compileRW(coeffs, F); }
    catch (e) { console.log(`rw n=${n} Q: ${e.message.slice(0, 60)}`); continue; }
    for (let t = 0; t < 4; t++) {
      const x = new Rat(BigInt(2 * t - 3), 2n);
      const got = evalLines(r.lines, F, x, parseC);
      const want = P.evalAt(F, coeffs, x);
      if (!got.eq(want)) { console.log(`FAIL rw n=${n} Q at ${x}`); rwfails++; break; }
    }
    console.log(`rw n=${n} over Q: mults=${r.mults} adds=${r.adds} height=${r.height}`);
  }
  if (rwfails) process.exit(1);
  console.log('RW PASSES');
}

// ---- Knuth-Eve through the site's own path (buildComparisons over Q: float
// coefficients rescaled to monic, leading coefficient restored by one
// multiplication), on the example chips at every degree 3..20.  Pan has its
// own focused tests for the separate degree-8 and general degree >=9 maps. ----
import { buildComparisons } from '../js/compare.js';
import { examplesFor } from '../js/uistate.js';
import { parsePoly } from '../js/polyparse.js';
{
  // evaluator for chainToText output: "lhs = rhs" lines; rhs uses ' + ', ' - '
  // or ' − ', unary minus, parentheses, real or "(a+bi)" literals, and
  // identifiers such as P̃ (any non-ASCII letters allowed).
  const Cx = (re, im = 0) => ({ re, im });
  const add = (a, b) => Cx(a.re + b.re, a.im + b.im);
  const sub = (a, b) => Cx(a.re - b.re, a.im - b.im);
  const mul = (a, b) => Cx(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re);
  function evalText(text, x) {
    const env = Object.create(null);
    env.x = Cx(x);
    let last = null;
    for (const raw of text.split('\n')) {
      const line = raw.trim();
      if (!line) continue;
      const eq = line.indexOf('=');
      const lhs = line.slice(0, eq).trim(), rhs = line.slice(eq + 1).trim();
      env[lhs] = evalRhs(rhs, env);
      last = lhs;
    }
    return env[last];
  }
  function evalRhs(src, env) {
    let i = 0;
    const ws = () => { while (i < src.length && src[i] === ' ') i++; };
    const isMinus = c => c === '-' || c === '−';
    function expr() {
      let v = term();
      for (;;) {
        ws();
        const c = src[i];
        if (c === '+' || isMinus(c)) { i++; const t = term(); v = c === '+' ? add(v, t) : sub(v, t); }
        else return v;
      }
    }
    function term() {
      let v = factor();
      for (;;) { ws(); if (src[i] === '*') { i++; v = mul(v, factor()); } else return v; }
    }
    function factor() {
      ws();
      let neg = false;
      if (isMinus(src[i])) { neg = true; i++; ws(); }
      let v;
      if (src[i] === '(') {
        i++; v = expr(); ws();
        if (src[i] !== ')') throw new Error('missing ) in: ' + src);
        i++;
      } else {
        const rest = src.slice(i);
        const num = /^\d+(?:\.\d+)?(?:[eE][+-]?\d+)?i?/.exec(rest);
        if (num) {
          i += num[0].length;
          v = num[0].endsWith('i') ? Cx(0, parseFloat(num[0].slice(0, -1))) : Cx(parseFloat(num[0]));
        } else {
          const id = /^[\p{L}_][\p{L}\p{M}\w]*/u.exec(rest);
          if (!id) throw new Error('bad atom in: ' + src);
          if (!(id[0] in env)) throw new Error('undefined wire ' + id[0] + ' in: ' + src);
          i += id[0].length; v = env[id[0]];
        }
      }
      return neg ? Cx(-v.re, -v.im) : v;
    }
    const v = expr();
    ws();
    if (i !== src.length) throw new Error('trailing input in: ' + src);
    return v;
  }
  let e2e = 0, e2eFails = 0;
  // The method-specific suites cover every degree. Keep this integration test to a
  // representative set so it exercises buildComparisons without recompiling 54
  // numerically solved comparison tables on every commit.
  const wrapperCases = [
    ['exp', 3], ['exp', 8], ['exp', 9], ['exp', 13],
    ['ln', 7], ['ln', 13], ['sqrt', 8], ['sqrt', 15],
  ];
  for (const [key, n] of wrapperCases) {
      const { coeffs } = parsePoly(examplesFor('Q', n).find(e => e.key === key).src);
      const fl = coeffs.map(c => Number(c.n) / Number(c.d));
      const rows = buildComparisons(coeffs, Q, 'Q');
      for (const name of ['Knuth–Eve']) {
        const row = rows.find(r => r.name === name);
        e2e++;
        const label = `${name} ${key} n=${n}`;
        if (!row || !row.ok) { console.log(`FAIL ${label}: ${row ? row.note : 'row missing'}`); e2eFails++; continue; }
        if (name === 'Knuth–Eve' && row.preprocessing !== 'real roots (numeric)') { console.log(`FAIL ${label}: preprocessing ${row.preprocessing}`); e2eFails++; }
        if (row.exact !== false || !/max rel\. error/.test(row.note)) { console.log(`FAIL ${label}: exact/note`); e2eFails++; }
        for (const form of ['mathTextOriginal', 'mathText']) {
          for (const x of [-1.7, -0.3, 0, 0.9, 1.6, 2.5]) {
            let got;
            try { got = evalText(row[form], x); } catch (e) { console.log(`FAIL ${label} ${form}: ${e.message}`); e2eFails++; break; }
            let want = 0; for (let i = fl.length - 1; i >= 0; i--) want = want * x + fl[i];
            let scale = 0, xp = 1; for (let i = 0; i < fl.length; i++) { scale += Math.abs(fl[i]) * xp; xp *= Math.max(1, Math.abs(x)); }
            const denom = Math.max(Math.abs(want), 1e-3 * scale, 1e-300);
            if (!(Math.hypot(got.re - want, got.im) / denom <= 1e-5)) { console.log(`FAIL ${label} ${form} at x=${x}: got ${got.re} want ${want}`); e2eFails++; break; }
          }
        }
      }
  }
  console.log(`buildComparisons over Q, representative example chips: ${e2e - e2eFails}/${e2e} rows ok and numerically verified`);
  if (e2eFails) process.exit(1);
  console.log('NUMERIC ROWS PASS');
}
