// The "original" view of the paper's chains follows sections/constructions:
// named gadget rows (H_2, H_4, Q_k, T⁽¹⁾, T⁽²⁾, P_n, working letters y,z,w,v),
// products inlined into their consumer, P_n = x·(…) + … as the last row.
// Every row set must evaluate to the input polynomial exactly.
import { Rat } from '../js/rat.js';
import * as core from '../js/char0/core.js';
import { renderConstructionsForm } from '../js/chain.js';
import { parseRhs } from '../js/cgen.js';
import { COMPLEX_TOKEN } from '../js/tokens.js';
const R = c => Rat.of(typeof c === 'number' ? BigInt(c) : c);
const QD = { name: 'ℚ', isZero: c => R(c).isZero(), isOne: c => R(c).isOne(), eq: (a, b) => R(a).eq(R(b)), toDisplay: c => R(c).toString() };
const plain = s => s.replace(/H̃/g, 'Ht').replace(/⁽¹⁾/g, '_1').replace(/⁽²⁾/g, '_2');
const lit = s => { const [a, b] = s.split('/'); return new Rat(BigInt(a), b ? BigInt(b) : 1n); };
function evalRows(text, x) {
  const env = { x };
  const ev = n => {
    if (n.tok !== undefined) {
      const neg = n.tok.startsWith('-'); const b = neg ? n.tok.slice(1) : n.tok;
      if (COMPLEX_TOKEN.test(b)) throw new Error('complex constant in an exact constructions-form row: ' + b);
      const [k, nmw] = b.includes('·') ? b.split('·') : [null, b];
      const v = k !== null ? lit(k).mul(env[nmw]) : /^\d/.test(b) ? lit(b) : env[b];
      if (v === undefined) throw new Error('undefined name ' + b);
      return neg ? v.neg() : v;
    }
    let acc = null;
    for (const { neg, t } of n.sum) { let v = null; for (const f of t) { const fv = ev(f); v = v === null ? fv : v.mul(fv); }
      acc = acc === null ? (neg ? v.neg() : v) : (neg ? acc.sub(v) : acc.add(v)); }
    return acc;
  };
  let lastName = null;
  for (const row of text.split('\n')) {
    const m = /^(\S+)\s*= (.*)$/.exec(plain(row)); if (!m) throw new Error('bad row: ' + row);
    env[m[1]] = ev(parseRhs(m[2])); lastName = m[1];
  }
  return env[lastName];
}
let checked = 0, fails = 0;
// This is the exact-rational UI rendering range. Higher-degree construction and
// decoder coverage lives in char0.test.js; repeating it here made n=25..30 dominate
// the entire browser-facing suite without testing another rendering shape.
for (let n = 3; n <= 24; n++) {
  // fractional coefficients for small n (exercises the ℚ decoders), integers above
  const coeffs = [...Array.from({ length: n }, (_, i) => new Rat(BigInt((i * 7 + 3) % 11 - 5), BigInt(n <= 16 ? 1 + (i % 3) : 1))), Rat.ONE];
  const chain = core.compile_paper_params_chain(core.decode(n, coeffs, core.rationals()), null);
  const text = renderConstructionsForm(QD, chain);
  const rows = text.split('\n');
  const products = (text.match(/\) \* \(|\) \* [A-Za-z]|[A-Za-z0-9_⁾] \* \(/g) ?? []).length;
  if (!/^P_\d+ /.test(rows[rows.length - 1])) { console.log(`n=${n}: last row is not P_n:`, rows[rows.length - 1]); fails++; }
  if (n >= 9 && !rows[0].startsWith('H_2 ')) { console.log(`n=${n}: first row is not H_2:`, rows[0]); fails++; }
  for (const xv of [new Rat(2n), new Rat(-3n, 7n), new Rat(5n, 2n)]) {
    let want = Rat.ZERO; for (let i = n; i >= 0; i--) want = want.mul(xv).add(coeffs[i]);
    const got = evalRows(text, xv); checked++;
    if (!got.eq(want)) { console.log(`n=${n} x=${xv}: MISMATCH`); fails++; }
  }
  console.log(`n=${n}: ${rows.length} rows, ${chain.gates.length} gates — ${rows.map(r => r.split(' ')[0]).join(', ')}`);
}
console.log(`${checked} evaluations, ${fails} failures`);
if (fails) process.exit(1);
console.log('CONSTRUCTIONS FORM PASSES');
