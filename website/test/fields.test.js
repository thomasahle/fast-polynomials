// fields.test.js — the field registry (js/field.js FIELDS) and the worker's
// acceptance of every field id: each descriptor builds a working field object,
// handleMessage compiles a polynomial in every field (with C output and the
// comparison rows), legacy message spellings still resolve, the parser reads
// decimal coefficients exactly, ℝ is exact rational arithmetic displayed as
// doubles, ℂ the same over the Gaussian rationals displayed as complex doubles
// (C99 double complex over ℂ: registry cCode), and every backend decodes +
// renders C for degrees 3..20 (char 2: the odd degrees it has circuits for).
// Plain node, exit 1 on failure.
import { FIELDS, FIELD_GROUPS, FIELD_IDS, fieldById, resolveField, ratToDoubleString, doubleString, ratToDouble, R, Q, Fp, GF2k,
         MERSENNE61, MERSENNE89, MERSENNE127 } from '../js/field.js';
import { parsePoly, decimalToRat } from '../js/polyparse.js';
import { Rat } from '../js/rat.js';
import { GaussRat } from '../js/gauss.js';
import { COMPLEX_SRC, COMPLEX_TOKEN } from '../js/tokens.js';
import { handleMessage } from '../js/worker.js';
import { examplesFor } from '../js/uistate.js';
import { compileChar0 } from '../js/compile0.js';
import { compileChar2 } from '../js/compile2.js';
import { SUPPORTED_DEGREES } from '../js/char2.js';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };

// ---------- registry ----------
check(FIELD_IDS.join(',') === 'Q,R,C,p61,p89,p127,gf32,gf64,gf128', `registry ids: ${FIELD_IDS.join(',')}`);
check(new Set(FIELD_IDS).size === FIELDS.length, 'ids unique');
const groupIds = FIELD_GROUPS.map(g => g.id);
for (const f of FIELDS) {
  check(groupIds.includes(f.group), `${f.id}: group ${f.group} exists`);
  check(['char0', 'char2'].includes(f.lane) && f.worker.lane === f.lane && f.worker.fieldMode === f.id, `${f.id}: worker fields`);
  check(typeof f.label === 'string' && !/\^/.test(f.label) && /<sup>|ℚ|ℝ|ℂ/.test(f.labelHtml), `${f.id}: labels (${f.label} / ${f.labelHtml})`);
  check(['exact', '≈ numeric'].includes(f.status) && f.exact === (f.status === 'exact'), `${f.id}: status`);
  check(Object.isFrozen(f), `${f.id}: frozen`);
  const F = f.make();
  check(F.name === f.name, `${f.id}: make().name ${F.name} == ${f.name}`);
  // arithmetic sanity (any characteristic): (3*5)/5 == 3 and 3 - 3 == 0
  const three = F.fromInt(3), five = F.fromInt(5);
  const v = F.div(F.mul(three, five), five);
  check(F.eq(v, three) && F.isZero(F.sub(three, three)) && F.eq(F.neg(F.neg(five)), five), `${f.id}: (3*5)/5 == 3`);
  check(F.isOne(F.one) && F.isZero(F.zero), `${f.id}: zero/one`);
  check(typeof F.toDisplay(v) === 'string', `${f.id}: toDisplay`);
}
check(fieldById('p89').prime === MERSENNE89 && fieldById('p61').prime === MERSENNE61 && fieldById('p127').prime === MERSENNE127, 'primes');
check(fieldById('gf128').make().mod === ((1n << 128n) | 0x87n), 'GF(2^128) modulus x^128+x^7+x^2+x+1');
check(fieldById('gf32').make().mod === ((1n << 32n) | 0x8dn), 'GF(2^32) modulus x^32+x^7+x^3+x^2+1');
check(fieldById('gf64').make().mod === ((1n << 64n) | 0x1bn), 'GF(2^64) modulus x^64+x^4+x^3+x+1');
check(fieldById('p61').label === '2⁶¹−1' && fieldById('gf128').label === 'GF(2¹²⁸)' && fieldById('p127').labelHtml === '2<sup>127</sup>−1'
      && fieldById('p127').name === 'GF(2^127−1)', 'exponent formatting (short chooser labels; the GF(…) name is kept for results)');
check(groupIds.join(',') === 'exact,mersenne,binary' && fieldById('Q').group === 'exact' && fieldById('R').group === 'exact' && fieldById('C').group === 'exact',
      'three groups: ℚ, ℝ and ℂ share the exact group');
check(fieldById('R').status === '≈ numeric' && fieldById('R').char === 0 && fieldById('p89').char === 'p' && fieldById('gf64').char === 2, 'char / status');
check(fieldById('C').status === '≈ numeric' && fieldById('C').char === 0 && fieldById('C').complex === true && fieldById('C').lane === 'char0' &&
      fieldById('C').make().complex === true && !fieldById('C').make().real && !fieldById('R').complex && !fieldById('Q').complex, 'ℂ: char 0, complex, ≈ numeric');
check(fieldById('C').cCode === true, 'ℂ renders C (C99 double complex)');
check(FIELDS.filter(f => f.lane === 'char0' && !f.exact).map(f => f.id).join(',') === 'R,C', 'the inexact char-0 fields are ℝ and ℂ');
let threw = false; try { fieldById('gf16'); } catch (e) { threw = true; } check(threw, 'unknown id throws');
// legacy spellings
check(resolveField('char0', 'p').id === 'p89' && resolveField('char0', 'Q').id === 'Q' && resolveField('char0', undefined).id === 'Q', 'legacy char0 ids');
check(resolveField('char2', null).id === 'gf64' && resolveField('char2', 'gf2k').id === 'gf64' && resolveField(undefined, 'gf128').id === 'gf128', 'legacy char2 ids');
threw = false; try { resolveField('char2', 'p61'); } catch (e) { threw = true; } check(threw, 'lane mismatch throws');

// ---------- doubles: shortest round-trip decimals, scientific when needed ----------
check(doubleString(1e-7) === '1e-7' && doubleString(1.5e21) === '1.5e+21' && doubleString(-2.5e-3) === '-0.0025' &&
      doubleString(0.1) === '0.1' && doubleString(3) === '3' && doubleString(-0) === '0' && doubleString(1.25e2) === '125', 'doubleString');
for (const x of [1e-7, 1.5e21, -2.5e-3, 0.1, 123456.789, 5e-324, 1.7976931348623157e308])
  check(Number(doubleString(x)) === x, `doubleString round trip ${x}`);
threw = false; try { doubleString(Infinity); } catch (e) { threw = true; } check(threw, 'doubleString rejects non-finite');
// exact rational -> the correctly rounded double's shortest decimal
check(ratToDoubleString(1n, 10n ** 7n) === '1e-7' && ratToDoubleString(1n, 3n) === '0.3333333333333333' && ratToDoubleString(3n, 2n) === '1.5' &&
      ratToDoubleString(15n, 10n ** 22n) === '1.5e-21' && ratToDoubleString(-25n, 10000n) === '-0.0025' && ratToDoubleString(3n, 1n) === '3' &&
      ratToDoubleString(0n, 5n) === '0' && ratToDoubleString(3n, -2n) === '-1.5' && ratToDoubleString(10n ** 21n, 1n) === '1e+21', 'ratToDoubleString');
// no double exists (overflow / underflow of a nonzero value): 17 significant digits from the exact rational
check(ratToDoubleString(10n ** 400n, 7n) === '1.4285714285714286e+399' && ratToDoubleString(1n, 10n ** 400n) === '1e-400' &&
      ratToDoubleString(-(10n ** 320n), 3n) === '-3.3333333333333333e+319' && ratToDoubleString(999999999999999999n * 10n ** 300n, 1n) === '1e+318',
      'ratToDoubleString beyond the double range');
// ℝ is the exact arithmetic of ℚ (0.1 + 0.2 = 0.3, unlike doubles); only its display rounds
check(R.fromRat(new Rat(1n, 3n)).eq(new Rat(1n, 3n)) && ratToDouble(-3n, 2n) === -1.5 && R.real === true && R.char === 0, 'R.fromRat is exact');
check(R.eq(R.add(R.fromRat(new Rat(1n, 10n)), R.fromRat(new Rat(2n, 10n))), R.fromRat(new Rat(3n, 10n))) && R.isOne(R.mul(R.fromRat(new Rat(1n, 3n)), R.fromInt(3))), 'R arithmetic is exact');
check(R.toDisplay(R.div(R.one, R.fromInt(3))) === '0.3333333333333333' && R.toDisplay(R.fromRat(new Rat(1n, 10n ** 7n))) === '1e-7' &&
      R.toDisplay(R.fromInt(-4)) === '-4' && Q.toDisplay(Q.fromRat(new Rat(1n, 3n))) === '1/3', 'R display');

// ---------- parser: decimals ----------
check(decimalToRat('1.25').eq(new Rat(5n, 4n)) && decimalToRat('.5').eq(new Rat(1n, 2n)) && decimalToRat('2.5e-3').eq(new Rat(1n, 400n)) &&
      decimalToRat('3e2').eq(new Rat(300n)) && decimalToRat('7').eq(new Rat(7n)), 'decimalToRat');
{
  const { coeffs } = parsePoly('0.5x^3 - 1.5e-2x + 2e1 + .25x^2');
  check(coeffs.length === 4 && coeffs[3].eq(new Rat(1n, 2n)) && coeffs[2].eq(new Rat(1n, 4n)) && coeffs[1].eq(new Rat(-3n, 200n)) && coeffs[0].eq(new Rat(20n)),
        `decimal polynomial: ${coeffs.map(String).join(', ')}`);
  const { coeffs: c2 } = parsePoly('x^2 - 3/2x + 1');            // rationals still fine
  check(c2[1].eq(new Rat(-3n, 2n)), 'rational coefficients unchanged');
  threw = false; try { parsePoly('1.5x', { char2: true }); } catch (e) { threw = true; } check(threw, 'char 2 rejects decimals');
}

/** An imaginary unit written outside a complex token: 2i, +i, − i, (i — never the
 *  i of prose such as "(leading-coefficient scale)". */
const BARE_I = /[\d+\-−(]\s*i\b/;

// ---------- worker: every field id ----------
const src0 = '2x^9 - 4x^8 + 4x^7 - 7x^6 - 4x^5 - 11/2x^4 - 11x^3 + 5x^2 - 9/3x - 7';
const src2 = 'x^15 + 4x^14 + 0x14x^13 + 0xfx^12 + 3x^11 + 2x^10 + 4x^9 + 8x^8 + 9x^7 + 0x12x^6 + 0x15x^5 + 2x^4 + 0x13x^3 + 8x^2 + 0x18x + 0x16';
for (const f of FIELDS) {
  const tag = `worker ${f.id}`;
  let r;
  try { r = await handleMessage({ lane: f.lane, src: f.lane === 'char2' ? src2 : src0, fieldMode: f.id }); }
  catch (e) { check(false, `${tag}: threw ${e.message}`); continue; }
  check(!r.oursFailed, `${tag}: ours compiled (${r.oursFailed})`);
  check(r.fieldId === f.id && r.fieldName === f.name && r.status === f.status && r.exact === f.exact, `${tag}: field info ${r.fieldId} ${r.fieldName} ${r.status}`);
  check(r.mults === (f.lane === 'char2' ? 8 : 6), `${tag}: mults ${r.mults}`);
  check(f.cCode ? typeof r.cText === 'string' && r.cText.includes('eval_P') : r.cText === null, `${tag}: C code`);
  check((r.cTextFraction !== null) === (f.id === 'Q'), `${tag}: fraction C only over Q`);
  check(typeof r.mathText === 'string' && r.mathText.length > 0 && r.graph && r.graphSvg, `${tag}: math + graph views`);
  check((typeof r.cText === 'string') === f.cCode, `${tag}: registry cCode flag matches the rendering`);
  check(f.exact ? r.maxRelError === null : typeof r.maxRelError === 'number' && r.maxRelError < 1e-9, `${tag}: rounding error ${r.maxRelError}`);
  const names = r.comparisons.filter(c => c.ok).map(c => c.name);
  // the numeric methods run over ℚ and ℝ (Knuth–Eve, Pan) and over ℂ (Knuth–Eve,
  // Pan — degree ≥ 11 only, so not at this degree 9 — and Belaga)
  const want = f.lane === 'char2' || f.char === 'p' ? 3 : 5;
  check(names.length === want, `${tag}: comparison rows ${names.join(',')}`);
  if (f.complex) check(names.join(',') === 'Horner,Estrin,Rabin–Winograd,Knuth–Eve,Belaga' && /degree 11/.test(r.comparisons.find(c => c.name === 'Pan')?.note ?? ''),
                       `${tag}: ℂ rows ${r.comparisons.map(c => `${c.name}${c.ok ? '' : '✗'}`).join(',')}`);
  for (const c of r.comparisons) if (c.ok) check((typeof c.cText === 'string') === f.cCode, `${tag}/${c.name}: C code`);
  if (f.id === 'R') {
    const rw = r.comparisons.find(c => c.name === 'Rabin–Winograd');
    check(rw && rw.exact === false && rw.preprocessing === 'numeric', `${tag}: RW is numeric over R`);
    check(!/\d\/\d/.test(r.mathText) && /−?\d+\.\d+/.test(r.mathText), `${tag}: constants displayed as doubles, not fractions`);
    check(/exact rational preprocessing/.test(r.note) && /≈ numeric/.test(r.note), `${tag}: note ${r.note.slice(0, 80)}`);
  }
  if (f.id === 'C') {
    const rw = r.comparisons.find(c => c.name === 'Rabin–Winograd');
    check(rw && rw.exact === false && rw.preprocessing === 'numeric', `${tag}: RW is numeric over C`);
    check(!/\d\/\d/.test(r.mathText) && /−?\d+\.\d+/.test(r.mathText) && !BARE_I.test(r.mathText), `${tag}: a real input shows real doubles, no complex tokens`);
    check(/Gaussian rationals/.test(r.note) && /≈ numeric/.test(r.note) && !/no C rendering/.test(r.note), `${tag}: note ${r.note.slice(0, 80)}`);
  }
  try { structuredClone(r); } catch (e) { check(false, `${tag}: structuredClone ${e.message}`); }
}
// ℂ with complex coefficients: every constant of the chain (ours and every
// comparison row) is a real double or the canonical (re±imi) token — never a bare
// i — the C is C99 double complex, the views survive, and the chain agrees with
// Horner at points with Im x ≠ 0
{
  const r = await handleMessage({ lane: 'char0', src: '(1+2i)x^7 - ix^5 + 3x^4 - (1/2-3/4i)x^2 + x + i', fieldMode: 'C' });
  check(!r.oursFailed && r.fieldId === 'C' && r.fieldName === 'ℂ' && r.exact === false && r.status === '≈ numeric', `ℂ complex input: ${r.oursFailed ?? 'compiled'}`);
  check(r.mults === 5 && typeof r.cText === 'string' && r.cTextFraction === null && typeof r.graphSvg === 'string' && typeof r.mathTextOriginal === 'string', 'ℂ complex input: 4 + 1 scale multiplications, C, graph + original form');
  check(/double complex eval_P\(double complex x\)/.test(r.cText) && /return P \* \(1\.0 \+ 2\.0\*I\);/.test(r.cText) && /#include <complex.h>/.test(r.cText), 'ℂ complex input: C99 double complex with the complex leading coefficient');
  check(r.comparisons.filter(c => c.ok).every(c => typeof c.cText === 'string' && /double complex eval_P/.test(c.cText)), 'ℂ complex input: every comparison row has complex C');
  const texts = [r.mathText, r.mathTextOriginal, ...r.comparisons.filter(c => c.ok).map(c => c.mathText)];
  const cx = new RegExp(COMPLEX_SRC, 'g');
  for (const t of texts) {
    const toks = t.match(cx) ?? [];
    check(toks.length > 0 && toks.every(tok => COMPLEX_TOKEN.test(tok)), `ℂ complex input: canonical complex tokens (${toks.slice(0, 3).join(' ')})`);
    check(!BARE_I.test(t.replace(cx, '')), `ℂ complex input: no bare i outside the tokens in ${t.split('\n')[0]}`);
  }
  check(/\(1\+2i\) \* P̃/.test(r.mathText) && typeof r.maxRelError === 'number' && r.maxRelError < 1e-12, `ℂ complex input: scale line and rounding error ${r.maxRelError}`);
  check(r.comparisons.filter(c => c.ok).map(c => c.name).join(',') === 'Horner,Estrin,Rabin–Winograd,Knuth–Eve,Belaga' && r.comparisons.every(c => c.ok || (c.name === 'Pan' && /degree 11/.test(c.note))),
        `ℂ complex input: rows ${r.comparisons.map(c => `${c.name}${c.ok ? '' : '✗'}`).join(',')}`);
  for (const nm of ['Knuth–Eve', 'Belaga']) {
    const c = r.comparisons.find(c => c.name === nm);
    check(c.exact === false && /complex roots \(numeric\)/.test(c.preprocessing) && /max rel\. error \d/.test(c.note) && c.mults === 5, `ℂ complex input: ${nm} row ${c.preprocessing} ${c.mults} (${c.note.slice(-30)})`);
  }
  try { structuredClone(r); } catch (e) { check(false, `ℂ complex input: structuredClone ${e.message}`); }
  // Pan over ℂ with real coefficients: the real schemes run first (the complex
  // homotopy cannot track the degree-11 e^x Taylor polynomial), so the row is
  // the same 6-multiplication chain as over ℝ, with real constants only
  const expSrc = examplesFor('Q', 11, 0, false).find(e => e.key === 'exp').src;
  const panC = (await handleMessage({ lane: 'char0', src: expSrc, fieldMode: 'C', part: 'numeric', only: 'Pan' })).comparisons[0];
  check(panC.name === 'Pan' && panC.ok && panC.mults === 6 && !BARE_I.test(panC.mathText) && /double complex eval_P/.test(panC.cText ?? ''),
        `ℂ real input: Pan row ${panC.ok ? `${panC.mults} mults` : panC.note}`);
  const panR = (await handleMessage({ lane: 'char0', src: expSrc, fieldMode: 'R', part: 'numeric', only: 'Pan' })).comparisons[0];
  check(panR.ok && panR.mults === 6 && panR.mathText === panC.mathText, 'ℂ real input: the Pan chain is the ℝ one');
  const c = await compileChar0('(1+2i)x^7 - ix^5 + 3x^4 - (1/2-3/4i)x^2 + x + i', 'C');
  const cs = parsePoly('(1+2i)x^7 - ix^5 + 3x^4 - (1/2-3/4i)x^2 + x + i', { complex: true }).coeffs;
  for (const x of [new GaussRat(new Rat(2n, 3n), new Rat(-5n, 7n)), GaussRat.I, new GaussRat(new Rat(-3n), new Rat(1n, 2n))]) {
    let want = GaussRat.ZERO;
    for (let i = 7; i >= 0; i--) want = want.mul(x).add(cs[i]);
    check(c.chain.eval(x).mul(cs[7]).eq(want), `ℂ complex input: chain.eval == Horner at ${x}`);
  }
}
// a polynomial the field cannot read (fractions / decimals in GF(2^k)) fails with a
// readable message naming the field, not BigInt's "Cannot convert 1/2 to a BigInt"
for (const [src, id, what] of [['1/3628800x^10 + 1/2x^2 + x + 1', 'gf64', 'fraction'], ['0.5x^3 + x', 'gf32', 'decimal']]) {
  let msg = null;
  try { await handleMessage({ lane: 'char2', src, fieldMode: id }); } catch (e) { msg = e.message; }
  check(msg !== null && !/BigInt|Cannot convert/.test(msg) && msg.startsWith(`cannot read the polynomial over ${fieldById(id).name}:`) && msg.includes(what) && /ℚ/.test(msg),
        `${what} over ${id}: ${msg}`);
}
// legacy messages
{
  const a = await handleMessage({ lane: 'char0', src: 'x^7 - 2x^6 - 8x^5 - 6x^4 - 11x^3 + 10/3x^2 + 4/2x - 7/3', fieldMode: 'p' });
  check(a.fieldId === 'p89' && a.fieldName === 'GF(2^89−1)', 'legacy fieldMode p → p89');
  const b = await handleMessage({ lane: 'char2', src: src2, fieldMode: null });
  check(b.fieldId === 'gf64' && b.fieldName === 'GF(2^64)', 'legacy char2 null → gf64');
}
// R mode reports (rather than hides) what rounding the exact constants to doubles
// costs; when a constant has no double at all the chain and math view survive
// (constants written to 17 significant digits) and only the C rendering is dropped.
const intSrc = n => Array.from({ length: n + 1 }, (_, i) => (i === n ? 1 : ((i * 37 + 11) % 19 - 9) || 3))
  .map((c, i) => `${c < 0 ? '-' : '+'}${Math.abs(c)}${i === 0 ? '' : i === 1 ? 'x' : 'x^' + i}`).reverse().join('').replace(/^\+/, '');
{
  const ill = Array.from({ length: 13 }, (_, i) => `${((i * 7919) % 23 - 11) || 1}/${1 + i % 5}x^${i}`).join(' + ').replace(/\+ -/g, '- ');
  const r = await handleMessage({ lane: 'char0', src: ill, fieldMode: 'R' });
  check(!r.oursFailed && r.maxRelError > 1e-6 && /lose accuracy/.test(r.note) && typeof r.cText === 'string', `R ill-conditioned: err ${r.maxRelError} note ${r.note.slice(0, 60)}`);
  const q = await handleMessage({ lane: 'char0', src: ill, fieldMode: 'Q' });
  check(q.mults === r.mults && q.mathText.split('\n').length === r.mathText.split('\n').length && /\d\/\d/.test(q.mathText) && !/\d\/\d/.test(r.mathText),
        'R ill-conditioned: the same exact chain as Q, displayed as doubles');
  // A huge coefficient exercises the same overflow path without asking the exact
  // degree-31 decoder to manufacture enormous intermediate rational constants.
  const h = await handleMessage({ lane: 'char0', src: 'x^9 + 1e400', fieldMode: 'R' });
  check(!h.oursFailed && h.mults === 5 && h.cText === null && /no C rendering: constant -?Infinity/.test(h.note) && /exceed the double range/.test(h.note),
        `R beyond double range: ${h.oursFailed ?? h.note.slice(0, 80)}`);
  check(/\de\+\d{3}/.test(h.mathText) && typeof h.graphSvg === 'string' && h.comparisons.some(c => c.ok), 'R beyond double range: math view (17-digit constants), graph and comparisons survive');
  try { structuredClone(h); } catch (e) { check(false, `R beyond double range: structuredClone ${e.message}`); }
}

// ---------- representative degree sweep: every backend decodes, re-expands and renders C ----------
// (char 0: every degree through compileChar0, whose decoder self-verifies by
// re-expansion, plus an exact chain.eval vs Horner check here; char 2: the odd
// degrees with circuits, compileChar2 verifies by exact re-expansion.)
{
  const expectedMults = n => (n <= 1 ? 0 : n === 2 ? 1 : Math.floor(n / 2) + 1);
  const MUL = { Q: 'double eval_P(double x)', R: 'double eval_P(double x)', C: 'double complex eval_P(double complex x)', p61: 'mul61(', p89: 'mult_mod', p127: 'mul127(',
                gf32: 'gf32_mul(', gf64: 'gf64_mul(', gf128: 'gf128_mul(' };
  let seed = 0x2545F4914F6CDD1Dn;
  const rnd = () => { seed = (seed * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n); return seed; };
  const withC = [];
  for (const f of FIELDS) {
    const F = f.make();
    // Exhaustive degree coverage belongs to char0.test.js and char2.test.js. These
    // boundary representatives verify that every registry backend reaches those
    // compilers and renderers, without repeating the expensive decoder sweep.
    const representative = new Set([3, 4, 7, 8, 9, 13, 20]);
    const degrees = f.lane === 'char2'
      ? SUPPORTED_DEGREES.filter(n => representative.has(n))
      : [...representative];
    let allC = true;
    for (const n of degrees) {
      const tag = `sweep ${f.id} n=${n}`;
      try {
        if (f.lane === 'char2') {
          const bits = BigInt(f.k), rk = () => ((rnd() << 64n) | rnd()) & ((1n << bits) - 1n);
          const coeffs = [...Array.from({ length: n }, rk), n % 4 === 3 ? 1n : (rk() | 2n)];   // monic and non-monic inputs
          const r = compileChar2(coeffs, F);
          check(r.n === n && r.mults >= expectedMults(n) && typeof r.mathText === 'string', `${tag}: result`);
          allC &&= typeof r.cText === 'string' && r.cText.includes('eval_P') && r.cText.includes(MUL[f.id]);
        } else {
          const r = await compileChar0(intSrc(n), f.id);
          check(r.mults === expectedMults(n) && r.fieldId === f.id && r.exact === f.exact && r.status === f.status, `${tag}: result`);
          const field = r.chain.field, cs = parsePoly(intSrc(n)).coeffs.map(c => (field.modulus === null ? c : field.coerce(c.n)));
          for (const x of [7n, -12345n]) {
            const x0 = field.coerce(x);
            let want = field.zero();
            for (let i = n; i >= 0; i--) want = field.add(field.mul(want, x0), cs[i]);
            check(field.eq(r.chain.eval(x0), want), `${tag}: chain.eval == Horner at ${x}`);
          }
          if (!f.exact) check(typeof r.maxRelError === 'number' && !/\d\/\d/.test(r.mathText), `${tag}: ${f.id} diagnostics`);
          allC &&= typeof r.cText === 'string' && r.cText.includes('eval_P') && r.cText.includes(MUL[f.id]);
        }
      } catch (e) { check(false, `${tag}: threw ${e.message}`); allC = false; }
    }
    check(allC === f.cCode, `sweep ${f.id}: C rendered for every degree (${degrees[0]}..${degrees[degrees.length - 1]}) == registry cCode`);
    if (allC) withC.push(f.id);
  }
  console.log(`C output for representative degrees 3, 4, 7, 8, 9, 13, 20: ${withC.join(', ')}` +
              (withC.length === FIELDS.length ? ' (every field)' : ''));
}

console.log(`${checks} checks, ${fails} failures`);
if (fails) process.exit(1);
console.log('FIELDS PASS');
