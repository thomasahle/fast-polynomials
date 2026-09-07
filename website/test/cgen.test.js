// cgen.test.js — generated C is compiled with the system `cc` and executed;
// every binary's output is compared against the exact JS evaluation.
//   ours char 2 (GF(2^64), n = 15 non-monic, n = 13 monic): ARM native
//     (-march=armv8-a+crypto) and, when Rosetta is available, x86 cross
//     (-arch x86_64 -mpclmul -mssse3, run through `arch -x86_64`).
//   ours Mersenne (2^89-1, n = 15 and 31): native and x86 cross.
//   ours Q (n = 9, both constant styles): compared to double Horner (1e-9 rel).
//   Horner / Rabin–Winograd / Estrin chains in each of the three modes.
//   The other registry fields, ours + the three methods, native and x86 cross:
//     GF(2^32) (uint32_t, PCLMUL/PMULL), GF(2^128) (__uint128_t,
//     4-clmul general products / 2-clmul squares),
//     2^61-1 (uint64_t, lazy folds; x any 64-bit word), 2^127-1 (__uint128_t;
//     x any 128-bit word), R (the exact chain, constants rounded to doubles),
//     C (C99 double complex: ours on Gaussian and on real coefficients, the three
//     classical methods, and the numeric rows Knuth–Eve / Pan / Belaga as the
//     page builds them; compiled with -lm, compared by |.|-relative error).
// Plus unit checks of ratToDouble (correct rounding) and the naming helpers.
// Exit 1 on any mismatch. Scratch files go under /tmp/site2/cgen_test/.
import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, writeFileSync } from 'node:fs';
import { GF2k, Fp, Q, R, Cx, MERSENNE61, MERSENNE127 } from '../js/field.js';
import { Rat } from '../js/rat.js';
import { GaussRat } from '../js/gauss.js';
import * as P from '../js/poly.js';
import { parsePoly } from '../js/polyparse.js';
import { compileChar2 } from '../js/compile2.js';
import { compileChar0 } from '../js/compile0.js';
import { compileHorner } from '../js/methods/horner.js';
import { compileRW } from '../js/methods/rw.js';
import { compileEstrin } from '../js/methods/estrin.js';
import { buildComparisons } from '../js/compare.js';
import { methodChainC, char0C, char2C, ratToDouble, doubleLiteral, qConst, complexLiteral, cxConst,
         wireLetter, cIdent, parseRhs, MERSENNE89, hasCProvenance } from '../js/cgen.js';

const TMP = '/tmp/site2/cgen_test';
mkdirSync(TMP, { recursive: true });
let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };

let seed = 0x1234567n;
const rnd = () => { seed = (seed * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n); return seed; };

// ---------- toolchains ----------
const hostArm = process.arch === 'arm64';
const targets = [];   // { label, cflags(mode), run(bin) }
if (hostArm) {
  targets.push({ label: 'arm64', gfFlags: ['-march=armv8-a+crypto'], run: bin => execFileSync(bin) });
  const ros = spawnSync('arch', ['-x86_64', '/usr/bin/true']);
  if (process.platform === 'darwin' && ros.status === 0)
    targets.push({ label: 'x86_64 (Rosetta)', arch: ['-arch', 'x86_64'], gfFlags: ['-mpclmul', '-mssse3'],
                   run: bin => execFileSync('arch', ['-x86_64', bin]) });
  else console.log('note: x86_64 cross-run unavailable; skipping');
} else {
  targets.push({ label: process.arch, gfFlags: ['-mpclmul', '-mssse3'], run: bin => execFileSync(bin) });
}

let fileNo = 0;
// value kind per mode: how main() declares xs and prints eval_P's result
const KINDS = {
  Q: 'double', R: 'double', C: 'complex',
  gf2k: 'u64', gf64: 'u64', gf32: 'u32', gf128: 'u128',
  p: 'u64_u128', p89: 'u64_u128', p61: 'u64', p127: 'u128',
};
const u128Lit = x => `U128(0x${(x >> 64n).toString(16)}ULL, 0x${(x & ((1n << 64n) - 1n)).toString(16)}ULL)`;
const MAINS = {
  double: xs => `    static const double xs[] = {${xs.map(doubleLiteral).join(', ')}};\n` +
    `    for (unsigned i = 0; i < sizeof xs / sizeof *xs; i++) printf("%.17g\\n", eval_P(xs[i]));\n`,
  // xs: [{ re, im }]; one "re im" line per point
  complex: xs => `    static const double complex xs[] = {${xs.map(z => `(${complexLiteral(z.re, z.im)})`).join(', ')}};\n` +
    `    for (unsigned i = 0; i < sizeof xs / sizeof *xs; i++) { double complex r = eval_P(xs[i]);\n` +
    `        printf("%.17g %.17g\\n", creal(r), cimag(r)); }\n`,
  u32: xs => `    static const uint32_t xs[] = {${xs.map(x => '0x' + x.toString(16) + 'U').join(', ')}};\n` +
    `    for (unsigned i = 0; i < sizeof xs / sizeof *xs; i++) printf("%08x\\n", (unsigned)eval_P(xs[i]));\n`,
  u64: xs => `    static const uint64_t xs[] = {${xs.map(x => '0x' + x.toString(16) + 'ULL').join(', ')}};\n` +
    `    for (unsigned i = 0; i < sizeof xs / sizeof *xs; i++) printf("%016llx\\n", (unsigned long long)eval_P(xs[i]));\n`,
  u64_u128: xs => `    static const uint64_t xs[] = {${xs.map(x => x + 'ULL').join(', ')}};\n` +
    `    for (unsigned i = 0; i < sizeof xs / sizeof *xs; i++) { __uint128_t r = eval_P(xs[i]);\n` +
    `        printf("%llx:%016llx\\n", (unsigned long long)(r >> 64), (unsigned long long)r); }\n`,
  u128: xs => `    static const __uint128_t xs[] = {${xs.map(u128Lit).join(', ')}};\n` +
    `    for (unsigned i = 0; i < sizeof xs / sizeof *xs; i++) { __uint128_t r = eval_P(xs[i]);\n` +
    `        printf("%llx:%016llx\\n", (unsigned long long)(r >> 64), (unsigned long long)r); }\n`,
};
function buildAndRun(cText, mode, xs, tag, mainBody = null) {
  // xs: bigint[] (finite fields) or number[] (Q / R); mainBody: the body of
  // main() in place of the mode's default (MAINS), e.g. to call eval_P_key
  check(hasCProvenance(cText), `${tag}: generated-source provenance`);
  const outs = {};
  const kind = KINDS[mode];
  if (!kind) throw new Error(`buildAndRun: unknown mode ${mode}`);
  const main = `\n#include <stdio.h>\nint main(void) {\n${mainBody ?? MAINS[kind](xs)}    return 0;\n}\n`;
  const gf = /^gf/.test(mode), cx = kind === 'complex';
  for (const t of targets) {
    if ((kind === 'double' || cx) && t.arch) continue;   // doubles: native is enough
    const src = `${TMP}/${tag}_${++fileNo}.c`, bin = src.replace(/\.c$/, '');
    writeFileSync(src, cText + main);
    const flags = ['-O2', '-std=c11', '-Wall', ...(t.arch ?? []), ...(gf ? t.gfFlags : []), src, '-o', bin, ...(cx ? ['-lm'] : [])];
    const cc = spawnSync('cc', flags, { encoding: 'utf8' });
    if (cc.status !== 0) { check(false, `${tag} [${t.label}] compile: ${cc.stderr.slice(0, 400)}`); continue; }
    if (cc.stderr.trim()) console.log(`  warnings ${tag} [${t.label}]: ${cc.stderr.trim().split('\n')[0]}`);
    outs[t.label] = t.run(bin).toString().trim().split('\n');
  }
  return outs;
}
const compare = (outs, expect, tag, eq) => {
  for (const [label, got] of Object.entries(outs)) {
    check(got.length === expect.length, `${tag} [${label}] line count`);
    for (let i = 0; i < expect.length; i++)
      check(eq(got[i], expect[i]), `${tag} [${label}] x#${i}: got ${got[i]} want ${expect[i]}`);
  }
};
const hex8 = v => v.toString(16).padStart(8, '0');
const hex16 = v => v.toString(16).padStart(16, '0');
const hex128 = v => `${(v >> 64n).toString(16)}:${hex16(v & ((1n << 64n) - 1n))}`;
const relClose = (a, b, tol = 1e-9) => Math.abs(a - b) <= tol * Math.max(1, Math.abs(b));
// complex output line "re im" against { re, im }, |.|-relative
const parseCx = line => { const [re, im] = line.trim().split(/\s+/).map(Number); return { re, im }; };
const cxClose = (line, w, tol = 1e-9) => { const g = parseCx(line); return Math.hypot(g.re - w.re, g.im - w.im) <= tol * Math.max(1, Math.hypot(w.re, w.im)); };

// ---------- unit checks ----------
{
  check(wireLetter(0) === 'y' && wireLetter(5) === 'w' && wireLetter(19) === 'b' && wireLetter(20) === 'g20', 'wireLetter');
  check(cIdent('P̃') === 'Pt' && cIdent('x2') === 'x2', 'cIdent');
  check(doubleLiteral(3) === '3.0' && doubleLiteral(-0.5) === '-0.5' && doubleLiteral(1e21) === '1e+21', 'doubleLiteral');
  check(qConst(new Rat(-3n, 2n), 'fraction').expr === '(double)-3/2', 'qConst fraction');
  check(qConst(new Rat(-3n, 2n), 'float').expr === '-1.5', 'qConst float');
  check(complexLiteral(1.5, -0.25) === '1.5 - 0.25*I' && complexLiteral(2, 0) === '2.0' && complexLiteral(0, 1) === '0.0 + 1.0*I' && complexLiteral(-1e-7, 3e21) === '-1e-7 + 3e+21*I', 'complexLiteral');
  check(cxConst(new GaussRat(new Rat(1n, 2n), new Rat(-3n, 4n))) === '0.5 - 0.75*I' && cxConst(new Rat(-3n)) === '-3.0' && cxConst(7n) === '7.0' && cxConst(0) === '0.0', 'cxConst');
  const big = qConst(new Rat((1n << 60n) + 1n, 3n), 'fraction');
  check(!big.expr.includes('/') && big.note.includes('rounded'), 'qConst big fraction falls back to float');
  // correctly-rounded conversion: nearest neighbour test with exact rationals
  const buf = new DataView(new ArrayBuffer(8));
  const bits = x => { buf.setFloat64(0, x); return buf.getBigUint64(0); };
  const fromBits = b => { buf.setBigUint64(0, b); return buf.getFloat64(0); };
  const exact = x => {                                   // double -> Rat (finite, nonzero)
    const b = bits(x); const neg = b >> 63n; const ex = Number((b >> 52n) & 0x7ffn); let m = b & ((1n << 52n) - 1n);
    let e; if (ex === 0) e = -1074; else { m |= 1n << 52n; e = ex - 1075; }
    let r = e >= 0 ? new Rat(m << BigInt(e)) : new Rat(m, 1n << BigInt(-e));
    return neg ? r.neg() : r;
  };
  const nextUp = x => fromBits(x >= 0 ? bits(x) + 1n : bits(x) - 1n);
  const nextDown = x => fromBits(x > 0 ? bits(x) - 1n : bits(x) + 1n);
  const absR = r => (r.isNeg() ? r.neg() : r);
  const lt = (a, b) => a.sub(b).isNeg();
  for (let i = 0; i < 300; i++) {
    const nb = Number(rnd() % 120n) + 1, db = Number(rnd() % 120n) + 1;
    let n = rnd() % (1n << BigInt(nb)) + 1n, d = rnd() % (1n << BigInt(db)) + 1n;
    if (i % 5 === 0) n *= (1n << 40n) + 1n;                   // long numerators
    if (i % 3 === 0) n = -n;
    if (i % 7 === 0) d = 1n << BigInt(i % 60);                 // exact / tie cases
    const v = ratToDouble(n, d);
    const an = n < 0n ? -n : n;
    if (an < (1n << 53n) && d < (1n << 53n)) check(v === Number(n) / Number(d), `ratToDouble small ${n}/${d}`);
    const target = new Rat(n, d);
    const err = absR(exact(v).sub(target));
    const eu = absR(exact(nextUp(v)).sub(target)), ed = absR(exact(nextDown(v)).sub(target));
    check(!lt(eu, err) && !lt(ed, err), `ratToDouble nearest ${n}/${d}`);
    if (eu.eq(err) || ed.eq(err)) check((bits(v) & 1n) === 0n, `ratToDouble tie-to-even ${n}/${d}`);
  }
  // rhs parser round trip
  const ast = parseRhs('(y + 2) * (w − 3/2) + t');
  check(ast.sum.length === 2 && ast.sum[0].t.length === 2, 'parseRhs');
  // a complex literal (re±imi) is one atomic token, never a bracketed sum
  const cx = parseRhs('(1+2i) * (y + (0-1i))');
  check(cx.sum.length === 1 && cx.sum[0].t.length === 2 && cx.sum[0].t[0].tok === '(1+2i)', `parseRhs atomic complex factor: ${JSON.stringify(cx)}`);
  check(cx.sum[0].t[1].sum?.length === 2 && cx.sum[0].t[1].sum[1].t[0].tok === '(0-1i)', `parseRhs atomic complex summand: ${JSON.stringify(cx)}`);
  const cx2 = parseRhs('x − (1.5e-7+3.2e+5i)');
  check(cx2.sum.length === 2 && cx2.sum[1].neg && cx2.sum[1].t[0].tok === '(1.5e-7+3.2e+5i)', `parseRhs complex with exponents: ${JSON.stringify(cx2)}`);
}

// ---------- ours: char 2 (GF(2^64)) ----------
const F2 = GF2k(64);
for (const [n, lead] of [[15, 0x9215806a699341f8n], [13, 1n]]) {
  const coeffs = [...Array.from({ length: n }, () => rnd()), lead];
  const r = compileChar2(coeffs, F2);
  check(!/portable|for \(int i/.test(r.cText) && r.cText.includes('#error'), `char2 n=${n}: hardware-only gf64_mul`);
  check(r.cText.includes('static const uint64_t P_a[') && r.cText.includes('// z = (') , `char2 n=${n}: keys table + trailing comments`);
  const xs = Array.from({ length: 6 }, () => rnd());
  const outs = buildAndRun(r.cText, 'gf2k', xs, `ours2_n${n}`);
  compare(outs, xs.map(x => hex16(P.evalAt(F2, coeffs, x))), `ours char2 n=${n}`, (a, b) => a === b);
  for (const [nm, fn] of [['Horner', compileHorner], ['RW', compileRW], ['Estrin', compileEstrin]]) {
    const m = fn(coeffs, F2);
    const c = methodChainC(m.lines, 'gf2k', F2, { name: nm, mults: m.mults, preprocessing: m.preprocessing });
    const o = buildAndRun(c, 'gf2k', xs, `${nm}2_n${n}`);
    compare(o, xs.map(x => hex16(P.evalAt(F2, coeffs, x))), `${nm} char2 n=${n}`, (a, b) => a === b);
  }
}

// ---------- ours: Mersenne 2^89-1 ----------
const Fp89 = Fp(MERSENNE89);
const ratSrc = cs => cs.map((c, i) => {
  if (c.isZero()) return '';
  const mag = `${c.n < 0n ? -c.n : c.n}${c.d === 1n ? '' : '/' + c.d}`;
  const mono = i === 0 ? '' : i === 1 ? 'x' : `x^${i}`;
  const coef = mag === '1' && mono ? '' : mag;
  return `${c.n < 0n ? ' - ' : ' + '}${coef}${mono}`;
}).reverse().join('').replace(/^ \+ /, '').replace(/^ - /, '-');
// n = 14 is included because its chain has 2*x terms: x is a uint64_t parameter,
// so the multiple must be widened to 128 bits (regression: wrapped for x >= 2^63).
for (const [n, lead] of [[14, Rat.ONE], [15, new Rat(3n)], [31, Rat.ONE]]) {
  const cs = [...Array.from({ length: n }, (_, i) => new Rat(BigInt(i * 7 + 3) % 23n - 11n, BigInt(1 + (i % 4)))), lead];
  const src = ratSrc(cs);
  const r = await compileChar0(src, 'p');
  check(r.field.name === 'GF(2^89−1)', 'Mersenne field name');
  if (n === 14) check(r.cText.includes('2*(__uint128_t)x') && !/[^_a-z0-9]\d+\*x[^_a-z0-9]/.test(r.cText.replace(/\/\/.*$/gm, '').replace(/\/\*[\s\S]*?\*\//g, '')),
                      'mersenne n=14: integer multiples of x are widened');
  check(r.cText.includes('fast_large_mult_mod_2(') && r.cText.includes('extra_large_mult_add_mod(') &&
        r.cText.includes('if (P >= M89) P -= M89;') && r.cText.includes('static const __uint128_t P_alpha['), `mersenne n=${n}: shape`);
  check(r.cTextFraction === null, 'mersenne: no fraction variant');
  const fcs = cs.map(c => Fp89.mul(Fp89.fromInt(c.n), Fp89.inv(Fp89.fromInt(c.d))));
  const xs = [(1n << 64n) - 1n, (1n << 63n) | 5n, ...Array.from({ length: 6 }, () => rnd())];
  const outs = buildAndRun(r.cText, 'p', xs, `oursP_n${n}`);
  compare(outs, xs.map(x => hex128(P.evalAt(Fp89, fcs, x))), `ours mersenne n=${n}`, (a, b) => a === b);
  for (const [nm, fn] of [['Horner', compileHorner], ['RW', compileRW], ['Estrin', compileEstrin]]) {
    const m = fn(fcs, Fp89);
    const c = methodChainC(m.lines, 'p', Fp89, { name: nm, mults: m.mults, preprocessing: m.preprocessing });
    const o = buildAndRun(c, 'p', xs, `${nm}P_n${n}`);
    compare(o, xs.map(x => hex128(P.evalAt(Fp89, fcs, x))), `${nm} mersenne n=${n}`, (a, b) => a === b);
  }
}
// direct char0C on a hand-made chain with a coefficient-2 term and a negative wire
{
  const core = await import('../js/char0/core.js');
  const field = core.GF(MERSENNE89);
  const params = Array.from({ length: 9 }, (_, i) => field.coerce(BigInt(i * 1234567 + 89)));
  const chain = core.compile_paper_params_chain(params, MERSENNE89);
  const c = char0C(chain, 'p');
  const xs = [5n, 123456789n, (1n << 64n) - 1n];
  const outs = buildAndRun(c, 'p', xs, 'char0C_p');
  compare(outs, xs.map(x => hex128(chain.eval(x))), 'char0C mersenne chain', (a, b) => a === b);
}

// ---------- ours: Q (doubles), both constant styles ----------
{
  const src = '2x^9 - 4x^8 + 4x^7 - 7x^6 - 4x^5 - 11/2x^4 - 11x^3 + 5x^2 - 9/3x - 7';
  const cs = parsePoly(src, { char2: false }).coeffs;
  const r = await compileChar0(src, 'Q');
  check(typeof r.cText === 'string' && typeof r.cTextFraction === 'string', 'Q: both C variants');
  check(r.cTextFraction.includes('(double)') && !r.cText.includes('(double)'), 'Q: cstyle differs');
  check(/double y = /.test(r.cText) && /double z = /.test(r.cText) && !/y0/.test(r.cText), 'Q: letter wire names');
  const xs = [-1.5, -0.7, 0.3, 0.9, 1.7, 2.5];
  const dc = cs.map(c => ratToDouble(c.n, c.d));
  const horner = x => { let a = 0; for (let i = dc.length - 1; i >= 0; i--) a = a * x + dc[i]; return a; };
  const want = xs.map(horner);
  for (const [style, text] of [['float', r.cText], ['fraction', r.cTextFraction]]) {
    const outs = buildAndRun(text, 'Q', xs, `oursQ_${style}`);
    compare(outs, want, `ours Q ${style}`, (a, b) => relClose(Number(a), b));
  }
  for (const [nm, fn] of [['Horner', compileHorner], ['RW', compileRW], ['Estrin', compileEstrin]]) {
    const m = fn(cs, Q);
    for (const style of ['float', 'fraction']) {
      const c = methodChainC(m.lines, 'Q', Q, { name: nm, mults: m.mults, preprocessing: m.preprocessing, cstyle: style });
      if (nm === 'RW') check(c.includes('static const double P_c['), 'RW Q: constants table');
      check(c.includes(' * Reference: ') && /Horner|Estrin|Rabin/.test(c.split('Reference: ')[1] ?? '') && /doi\.org/.test(c.split('Reference: ')[1] ?? ''),
            `${nm} Q: the header cites the method's reference with its link`);
      if (nm === 'Horner') check(!c.includes('static const'), 'Horner Q: inline coefficients');
      const o = buildAndRun(c, 'Q', xs, `${nm}Q_${style}`);
      compare(o, want, `${nm} Q ${style}`, (a, b) => relClose(Number(a), b));
    }
  }
  // the numeric methods (Knuth–Eve, Pan) as the page builds them: their C compiles, runs
  // and evaluates the polynomial to the accuracy of their numerical preprocessing
  const rows = buildComparisons(cs.map(c => Q.fromRat(c)), Q, 'Q', { poly: src });
  const coefScale = x => cs.reduce((s, c, i) => s + Math.abs(ratToDouble(c.n, c.d)) * Math.pow(Math.max(1, Math.abs(x)), i), 0);
  for (const nm of ['Knuth–Eve', 'Pan']) {
    const row = rows.find(r => r.name === nm);
    check(!!row?.ok && typeof row.cText === 'string', `${nm} Q: the page has C for it (${row?.note?.slice(0, 60)})`);
    if (!row?.cText) continue;
    check(row.cText.includes(' * Reference: ') && /Knuth|Pan/.test(row.cText.split('Reference: ')[1] ?? ''), `${nm} Q: header cites its reference`);
    const o = buildAndRun(row.cText, 'Q', xs, `${cIdent(nm)}Q`);
    compare(o, want, `${nm} Q (numeric preprocessing)`, (a, b) => {
      const x = xs[want.indexOf(b)];
      return Math.abs(Number(a) - b) <= 1e-6 * (1 + Math.abs(b) + coefScale(x));
    });
  }
  // exact fraction constants: (double)NUM/DEN must equal the correctly rounded double
  const alphaLines = r.cTextFraction.split('\n').filter(l => /^\s+\(double\)-?\d+\/\d+,/.test(l));
  check(alphaLines.length > 0, 'Q fraction: table entries');
}

// ---------- ours: Q whose exact constants exceed the double range ----------
// The C rendering must be dropped (cText null, note extended) while the
// verified chain, math text and graph still come back (regression: the whole
// compile used to fail with "constant Infinity is not representable").
{
  const src = 'x^23 - 8/8*x^0 - 8/3*x^1 + 11/5*x^2 + 11/6*x^3 + 17/8*x^4 + 19/5*x^5 - 17/4*x^6 + 7/3*x^7' +
    ' - 6/4*x^8 + 6/4*x^9 - 13/4*x^10 - 13/4*x^11 - 13/5*x^12 + 6/2*x^13 - 15/7*x^14 + 17/8*x^15 + 9/2*x^16' +
    ' - 8/2*x^17 - 5/10*x^18 - 8/3*x^19 + 19/2*x^20 + 20/7*x^21 - 20/4*x^22';
  const r = await compileChar0(src, 'Q');
  check(r.cText === null && r.cTextFraction === null, 'Q overflow: no C rendering');
  check(/no C rendering: constant Infinity/.test(r.note), 'Q overflow: note explains');
  check(/^an exact constant exceeds the double range, so no double-precision chain exists/.test(r.cMissing ?? ''), `Q overflow: cMissing (${r.cMissing})`);
  check(r.mults === 12 && typeof r.mathText === 'string' && r.graph && r.graph.nodes.filter(n => n.kind === 'mul').length === 12,
        'Q overflow: chain, math text and graph survive');
}

// ---------- ours: GF(2^32) and GF(2^128) (registry binary fields) ----------
for (const [k, mode, fmt] of [[32, 'gf32', hex8], [128, 'gf128', hex128]]) {
  const F = GF2k(k);
  const randK = () => (k === 128 ? (rnd() << 64n) | rnd() : rnd() & ((1n << BigInt(k)) - 1n));
  for (const [n, monic] of [[15, false], [13, true]]) {
    const coeffs = [...Array.from({ length: n }, randK), monic ? 1n : (randK() | 2n)];
    const r = compileChar2(coeffs, F);
    check(r.cText.includes(`gf${k}_mul(`) && r.cText.includes('#error') && r.cText.includes(k === 32 ? 'clmul32(' : 'clmul64('),
          `gf${k} n=${n}: hardware-only gf${k}_mul`);
    check(r.cText.includes(`static const ${k === 32 ? 'uint32_t' : '__uint128_t'} P_a[`) && r.cText.includes('// z = ('), `gf${k} n=${n}: keys table + comments`);
    const xs = [0n, 1n, (1n << BigInt(k)) - 1n, ...Array.from({ length: 6 }, randK)];
    const outs = buildAndRun(r.cText, mode, xs, `ours${k}_n${n}`);
    compare(outs, xs.map(x => fmt(P.evalAt(F, coeffs, x))), `ours gf${k} n=${n}`, (a, b) => a === b);
    for (const [nm, fn] of [['Horner', compileHorner], ['RW', compileRW], ['Estrin', compileEstrin]]) {
      const m = fn(coeffs, F);
      const c = methodChainC(m.lines, nm === 'Horner' ? 'gf2k' : mode, F, { name: nm, mults: m.mults, preprocessing: m.preprocessing });
      if (k === 128 && nm === 'Estrin')
        check(c.includes('gf128_square(x)') && c.includes('gf128_square(x2)'),
              'gf128 Estrin power ladder uses the two-CLMUL square kernel');
      const o = buildAndRun(c, mode, xs, `${nm}${k}_n${n}`);
      compare(o, xs.map(x => fmt(P.evalAt(F, coeffs, x))), `${nm} gf${k} n=${n}`, (a, b) => a === b);
    }
  }
}

// ---------- ours: Mersenne 2^61-1 (64-bit words) and 2^127-1 (128-bit values) ----------
for (const [mode, prime, bits, fmt, edge] of [
  ['p61', MERSENNE61, 61, hex16, [(1n << 64n) - 1n, (1n << 63n) | 5n, MERSENNE61, MERSENNE61 + 1n, 0n]],
  ['p127', MERSENNE127, 127, hex128, [(1n << 128n) - 1n, MERSENNE127, MERSENNE127 + 1n, 1n << 127n, 0n]],
]) {
  const Fq = Fp(prime);
  const randX = () => (mode === 'p127' ? (rnd() << 64n) | rnd() : rnd());
  for (const [n, lead] of [[14, Rat.ONE], [15, new Rat(3n)], [31, Rat.ONE]]) {
    const cs = [...Array.from({ length: n }, (_, i) => new Rat(BigInt(i * 7 + 3) % 23n - 11n, BigInt(1 + (i % 4)))), lead];
    const r = await compileChar0(ratSrc(cs), mode);
    check(r.field.name === `GF(2^${bits}−1)` && r.fieldId === mode, `${mode} field name`);
    if (mode === 'p61')
      check(r.cText.includes('mul61(') && r.cText.includes('x = fold61(x);') && r.cText.includes('if (P >= M61) P -= M61;') &&
            r.cText.includes('static const uint64_t P_alpha[') && r.cText.includes('uint64_t eval_P(uint64_t x)'), `p61 n=${n}: shape`);
    else
      check(r.cText.includes('mul127(') && r.cText.includes('add127(') && r.cText.includes('if (P >= M127) P -= M127;') &&
            r.cText.includes('static const __uint128_t P_alpha[') && r.cText.includes('__uint128_t eval_P(__uint128_t x)'), `p127 n=${n}: shape`);
    if (n === 14) check(/2\*x/.test(r.cText.replace(/\/\/.*$/gm, '')) || /add127\(x, x\)/.test(r.cText), `${mode} n=14: doubled x term`);
    check(r.cTextFraction === null, `${mode}: no fraction variant`);
    const fcs = cs.map(c => Fq.fromRat(c));
    const xs = [...edge, ...Array.from({ length: 5 }, randX)];
    const want = xs.map(x => fmt(P.evalAt(Fq, fcs, x % prime)));      // x is reduced on entry
    const outs = buildAndRun(r.cText, mode, xs, `ours_${mode}_n${n}`);
    compare(outs, want, `ours ${mode} n=${n}`, (a, b) => a === b);
    for (const [nm, fn] of [['Horner', compileHorner], ['RW', compileRW], ['Estrin', compileEstrin]]) {
      const m = fn(fcs, Fq);
      const c = methodChainC(m.lines, mode, Fq, { name: nm, mults: m.mults, preprocessing: m.preprocessing });
      const o = buildAndRun(c, mode, xs, `${nm}_${mode}_n${n}`);
      compare(o, want, `${nm} ${mode} n=${n}`, (a, b) => a === b);
    }
  }
  // direct char0C on a hand-made chain (coefficient-2 terms, negative wires)
  const core = await import('../js/char0/core.js');
  const field = core.GF(prime);
  const params = Array.from({ length: 9 }, (_, i) => field.coerce(BigInt(i * 1234567 + 89)));
  const chain = core.compile_paper_params_chain(params, prime);
  const c = char0C(chain, mode);
  const xs = [5n, 123456789n, ...edge];
  const outs = buildAndRun(c, mode, xs, `char0C_${mode}`);
  compare(outs, xs.map(x => fmt(chain.eval(field.coerce(x)))), `char0C ${mode} chain`, (a, b) => a === b);
}

// ---------- keyed entry point of the hashing fields: the same circuit with a second key ----------
// eval_P_key(a, x) reads every constant from a[]; eval_P(x) = eval_P_key(P_a / P_alpha, x).
// A second polynomial of the same degree compiles to the same circuit, so its
// table, passed as the key, must evaluate it.  Over the Mersenne fields a
// parameter that happens to be 0 (x^n + 1) keeps its slot.
{
  const tableOf = (text, tbl) => {
    const m = new RegExp(`static const (\\S+) ${tbl}\\[(\\d+)\\] = \\{\\n([\\s\\S]*?)\\n\\};`).exec(text);
    return m ? { T: m[1], n: Number(m[2]), body: m[3] } : null;
  };
  const keyedMain = (kind, T, table, xs) => `    static const ${T} key2[${table.n}] = {\n${table.body}\n    };\n` +
    MAINS[kind](xs).replace('eval_P(xs[i])', 'eval_P_key(key2, xs[i])');
  const headerOf = text => text.slice(0, text.indexOf('*/')).replace(/\n \* +/g, ' ');   // the doc block, unwrapped
  const keyedBody = text => text.slice(text.indexOf('eval_P_key(const'));            // from the keyed function on
  // Mersenne primes: random monic pairs, x^n + 1 (a zero parameter), a non-monic input
  for (const [mode, prime, fmt, randX] of [['p61', MERSENNE61, hex16, () => rnd()], ['p89', MERSENNE89, hex128, () => rnd()],
                                          ['p127', MERSENNE127, hex128, () => (rnd() << 64n) | rnd()]]) {
    const Fq = Fp(prime);
    const kind = KINDS[mode];
    for (const [n, lead] of [[4, Rat.ONE], [7, Rat.ONE], [9, new Rat(5n)], [12, Rat.ONE]]) {
      const mk = () => [...Array.from({ length: n }, () => new Rat(rnd() % 1000n - 500n)), lead];
      const cs1 = mk(), cs2 = mk(), csZ = [Rat.ONE, ...Array(n - 1).fill(Rat.ZERO), Rat.ONE];   // x^n + 1
      const r1 = await compileChar0(ratSrc(cs1), mode), r2 = await compileChar0(ratSrc(cs2), mode), rz = await compileChar0(ratSrc(csZ), mode);
      const t1 = tableOf(r1.cText, 'P_alpha'), t2 = tableOf(r2.cText, 'P_alpha'), tz = tableOf(rz.cText, 'P_alpha');
      check(t1 && t2 && tz && t1.n === n && t2.n === n && tz.n === n, `${mode} n=${n}: one key slot per parameter (${t1?.n}, ${t2?.n}, ${tz?.n})`);
      check(new RegExp(`static inline \\S+ eval_P_key\\(const \\S+ a\\[${n}\\], \\S+ x\\)`).test(r1.cText) && /eval_P_key\(P_alpha, x\)/.test(r1.cText) &&
            !/P_alpha\[\d+\]/.test(keyedBody(r1.cText)), `${mode} n=${n}: keyed entry point, the table only through the wrapper`);
      check(new RegExp(`degree-${n} polynomial, i\\.e\\. ${n === 8 || n === 11 || n === 18 ? 'an' : 'a'} ${n}-wise independent hash`).test(headerOf(r1.cText)) &&
            /bijection/.test(headerOf(r1.cText)), `${mode} n=${n}: header note on the key map`);
      if (lead.isOne()) check(!/leading coefficient/.test(r1.cText.slice(r1.cText.indexOf('eval_P('))), `${mode} n=${n}: monic wrapper has no scale`);
      else check(/eval_P_key\(P_alpha, x\);\n[^\n]*leading coefficient/.test(r1.cText), `${mode} n=${n}: the scale stays outside eval_P_key`);
      const xs = [0n, 1n, mode === 'p89' ? (1n << 64n) - 1n : prime - 1n, ...Array.from({ length: 5 }, randX)];   // x: a 64-bit word over 2^89-1
      const want = coeffs => xs.map(x => fmt(P.evalAt(Fq, coeffs.map(c => Fq.fromRat(c)), x % prime)));
      // r1's file with r2's (and x^n + 1's) constants as the key: the second polynomial —
      // its monic part (the key is the chain of P/lc; the wrapper applies lc)
      compare(buildAndRun(r1.cText, mode, xs, `keyed_${mode}_n${n}`, keyedMain(kind, t1.T, t2, xs)), want(cs2.map(c => c.div(lead))), `keyed ${mode} n=${n} (second key)`, (a, b) => a === b);
      compare(buildAndRun(r1.cText, mode, xs, `keyedZ_${mode}_n${n}`, keyedMain(kind, t1.T, tz, xs)), want(csZ), `keyed ${mode} n=${n} (x^n + 1 as the key)`, (a, b) => a === b);
      // and the wrapper still evaluates its own polynomial (leading coefficient applied)
      compare(buildAndRun(r1.cText, mode, xs, `keyedSelf_${mode}_n${n}`), want(cs1), `keyed ${mode} n=${n} (eval_P)`, (a, b) => a === b);
    }
  }
  // GF(2^k): the char-2 circuits, including an even (lifted) degree
  for (const [k, mode, fmt] of [[64, 'gf64', hex16], [32, 'gf32', hex8]]) {
    const F = GF2k(k);
    const randK = () => rnd() & ((1n << BigInt(k)) - 1n);
    const kind = KINDS[mode];
    for (const [n, monic] of [[7, true], [8, true], [13, true], [9, false]]) {
      const mk = () => [...Array.from({ length: n }, randK), monic ? 1n : (randK() | 2n)];
      const c1 = mk(), c2 = mk();
      const r1 = compileChar2(c1, F), r2 = compileChar2(c2, F);
      const t1 = tableOf(r1.cText, 'P_a'), t2 = tableOf(r2.cText, 'P_a');
      check(t1 && t2 && t1.n === t2.n && t1.n === n, `gf${k} n=${n}: one key slot per parameter (${t1?.n}, ${t2?.n})`);
      check(new RegExp(`static inline \\S+ eval_P_key\\(const \\S+ a\\[${n}\\], \\S+ x\\)`).test(r1.cText) && /eval_P_key\(P_a, x\)/.test(r1.cText), `gf${k} n=${n}: keyed entry point`);
      // the article agrees with the spoken degree ("an 8-wise", "a 13-wise")
      check(new RegExp(`degree-${n} polynomial, i\\.e\\. ${n === 8 ? 'an' : 'a'} ${n}-wise independent hash`).test(headerOf(r1.cText)) &&
            /bijection/.test(headerOf(r1.cText)), `gf${k} n=${n}: header note on the key map`);
      const xs = [0n, 1n, (1n << BigInt(k)) - 1n, ...Array.from({ length: 5 }, randK)];
      const want = coeffs => xs.map(x => fmt(P.evalAt(F, coeffs, x)));
      const inv2 = F.inv(c2[n]);   // the key is the chain of the monic part P/lc
      compare(buildAndRun(r1.cText, mode, xs, `keyed_gf${k}_n${n}`, keyedMain(kind, t1.T, t2, xs)), want(c2.map(c => F.mul(c, inv2))), `keyed gf${k} n=${n} (second key)`, (a, b) => a === b);
      compare(buildAndRun(r1.cText, mode, xs, `keyedSelf_gf${k}_n${n}`), want(c1), `keyed gf${k} n=${n} (eval_P)`, (a, b) => a === b);
    }
  }
}

// ---------- ours: R (doubles; exact preprocessing, constants rounded) ----------
{
  const src = '2x^9 - 4x^8 + 4x^7 - 7x^6 - 4x^5 - 11/2x^4 - 11x^3 + 5x^2 - 9/3x - 7';
  const cs = parsePoly(src, { char2: false }).coeffs;
  const r = await compileChar0(src, 'R');
  const q = await compileChar0(src, 'Q');
  check(typeof r.cText === 'string' && r.cTextFraction === null && r.fieldId === 'R' && r.exact === false && r.status === '≈ numeric', 'R: C variant / status');
  check(/double P = /.test(r.cText) && /static const double P_alpha\[/.test(r.cText) && /preprocessed exactly/.test(r.cText) && !/\(double\)/.test(r.cText), 'R: header / constants');
  check(/return P \* 2\.0;/.test(r.cText), 'R: leading coefficient as a double literal');
  // the header repeats compile0's measured rounding (one doc block, lines within 88 columns)
  check(new RegExp(`Double rounding: max relative error ${r.maxRelError.toExponential(1).replace('+', '\\+')} at the sample points`).test(r.cText) &&
        r.cText.slice(0, r.cText.indexOf('*/')).split('\n').every(l => l.length <= 88), `R: rounding remark in the header (${r.maxRelError})`);
  check(r.cMissing === undefined && /Compile: cc -O3 -march=native <this file>/.test(r.cText) && !/\.\.\./.test(r.cText.slice(0, r.cText.indexOf('*/'))), 'R: compile line names the file');
  check(/^y += /m.test(r.mathText) && /^z += /m.test(r.mathText) && !/\by0\b/.test(r.mathText), 'R: math view uses the letter wire names of the C');
  // the chain is Q's exact chain: below the banner the C code is identical to Q's float
  // style (only Q's table comments carry the exact fractions)
  const body = t => t.slice(t.indexOf('/* preprocessed constants')).replace(/[ \t]*\/\/.*$/gm, '');
  check(body(r.cText) === body(q.cText) && !/computed numerically/.test(r.cText) && /\/\/ alpha0 = /.test(q.cText) && /\/\/ alpha0$/m.test(r.cText), 'R: C code identical to Q (float constants)');
  check(!/\d\/\d/.test(r.mathText) && r.mathText.split('\n').length === q.mathText.split('\n').length, 'R: math view shows doubles, same chain as Q');
  const xs = [-1.5, -0.7, 0.3, 0.9, 1.7, 2.5];
  const dc = cs.map(c => ratToDouble(c.n, c.d));
  const horner = x => { let a = 0; for (let i = dc.length - 1; i >= 0; i--) a = a * x + dc[i]; return a; };
  const want = xs.map(horner);
  compare(buildAndRun(r.cText, 'R', xs, 'oursR'), want, 'ours R', (a, b) => relClose(Number(a), b));
  // the comparison methods run on the exact coefficients; the field prints doubles
  for (const [nm, fn] of [['Horner', compileHorner], ['RW', compileRW], ['Estrin', compileEstrin]]) {
    const m = fn(cs, R);
    const c = methodChainC(m.lines, 'R', R, { name: nm, mults: m.mults, preprocessing: m.preprocessing });
    if (nm === 'RW') check(c.includes('static const double P_c[') && !/\(double\)\d+\/\d+/.test(c) && !/\d\/\d/.test(c), 'RW R: constants table of plain doubles');
    check(!/\d\/\d/.test(m.lines.map(l => l.rhs).join(' ')), `${nm} R: rendered constants are doubles`);
    compare(buildAndRun(c, 'R', xs, `${nm}R`), want, `${nm} R`, (a, b) => relClose(Number(a), b));
  }
  // small magnitudes: shortest round-trip decimals, scientific when needed (1e-7),
  // in the C and in the math view; the chain itself stays exact
  const tiny = await compileChar0('0.0000001x^5 + x^3 + 0.5x + 3', 'R');
  check(/return P \* 1e-7;/.test(tiny.cText) && /1e-7 \* P̃/.test(tiny.mathText), 'R: tiny constant rendering');
  compare(buildAndRun(tiny.cText, 'R', xs, 'tinyR'), xs.map(x => 1e-7 * x ** 5 + x ** 3 + 0.5 * x + 3), 'tiny R', (a, b) => relClose(Number(a), b));
  const tiny2 = await compileChar0('x^5 + 0.0000001x^3 + 0.5x + 3', 'R');
  check(/1\.0000001,/.test(tiny2.cText) && tiny2.mathText.includes('1.0000001'), 'R: 1 + 1e-7 rendering');
  compare(buildAndRun(tiny2.cText, 'R', xs, 'tiny2R'), xs.map(x => ((x * x + 1e-7) * x * x + 0.5) * x + 3), 'tiny2 R', (a, b) => relClose(Number(a), b));
  // beyond the double range the C is dropped (as over Q) while the chain survives
  const big = await compileChar0(Array.from({ length: 32 }, (_, i) => (i === 31 ? 'x^31' : `${((i * 37 + 11) % 19 - 9) || 3}x^${i}`)).join(' + ').replace(/\+ -/g, '- '), 'R');
  check(big.cText === null && /no C rendering: constant -?Infinity/.test(big.note) && big.mults === 16 && /\de\+3\d\d/.test(big.mathText), 'R beyond double range: no C, math view survives');
  check(/^an exact constant exceeds the double range/.test(big.cMissing ?? '') && big.maxRelError === Infinity, `R beyond double range: cMissing (${big.cMissing})`);
}

// ---------- ours: C (C99 double complex; exact preprocessing over Q(i), constants rounded) ----------
{
  const zs = [{ re: -1.5, im: 0.5 }, { re: -0.7, im: -0.3 }, { re: 0.3, im: 1.1 }, { re: 0.9, im: -0.4 }, { re: 1.7, im: 0.2 }, { re: 2.5, im: -1 }];
  const toC = g => ({ re: ratToDouble(g.re.n, g.re.d), im: ratToDouble(g.im.n, g.im.d) });
  const cmul = (a, b) => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re });
  const hornerC = (dc, z) => dc.reduceRight((v, c) => { const p = cmul(v, z); return { re: p.re + c.re, im: p.im + c.im }; }, { re: 0, im: 0 });
  const coefScale = (dc, z) => dc.reduce((s, c, i) => s + Math.hypot(c.re, c.im) * Math.pow(Math.max(1, Math.hypot(z.re, z.im)), i), 0);
  const runC = (text, tag) => buildAndRun(text, 'C', zs, tag);
  const shape = (text, tag) => {
    check(text.includes('#include <complex.h>') && text.includes('#pragma STDC CX_LIMITED_RANGE ON') && /double complex eval_P\(double complex x\)/.test(text) &&
          /Field: C, evaluated in complex double precision/.test(text) && /-lm/.test(text), `${tag}: complex C shape`);
  };
  const src = '(1+2i)x^7 - ix^5 + 3x^4 - (1/2-3/4i)x^2 + x + i';
  const cs = parsePoly(src, { complex: true }).coeffs, dc = cs.map(toC);
  const want = zs.map(z => hornerC(dc, z));
  const r = await compileChar0(src, 'C');
  check(typeof r.cText === 'string' && r.cTextFraction === null && r.fieldId === 'C' && r.exact === false && r.status === '≈ numeric', 'C: C variant / status');
  shape(r.cText, 'ours C');
  check(/static const double complex P_alpha\[/.test(r.cText) && /return P \* \(1\.0 \+ 2\.0\*I\);/.test(r.cText) && /preprocessed exactly/.test(r.cText) &&
        /\d\.\d+ [-+] \d\.\d+\*I,/.test(r.cText) && !/\(double\)/.test(r.cText) && !/\di\)/.test(r.cText.replace(/\/\/.*$/gm, '').replace(/\/\*[\s\S]*?\*\//g, '')),
        'C: complex table, complex leading coefficient, re ± im*I literals (the (re±imi) tokens only in comments)');
  check(new RegExp(`Double rounding: max relative error ${r.maxRelError.toExponential(1).replace('+', '\\+')} at the sample points`).test(r.cText), `C: rounding remark in the header (${r.maxRelError})`);
  compare(runC(r.cText, 'oursC'), want, 'ours C', cxClose);
  // the classical methods over ℂ: complex tokens in the chain, double complex in the C
  for (const [nm, fn] of [['Horner', compileHorner], ['RW', compileRW], ['Estrin', compileEstrin]]) {
    const m = fn(cs.map(c => Cx.fromRat(c)), Cx);
    const c = methodChainC(m.lines, 'C', Cx, { name: nm, mults: m.mults, preprocessing: m.preprocessing, poly: src });
    shape(c, `${nm} C`);
    // the ℂ constants note is 97 columns unwrapped: the whole doc block stays within 88
    {
      const hl = c.slice(0, c.indexOf('*/')).split('\n');
      check(hl.every(l => l.length <= 88) && hl.join('\n').replace(/\n \* {3}/g, ' ')
              .includes('rounded to the nearest complex double (each part a shortest round-trip decimal).'),
            `${nm} C: the complex constants note is wrapped inside the 88-column doc block`);
    }
    if (nm === 'RW') check(c.includes('static const double complex P_c[') && /\d\*I,/.test(c), 'RW C: constants table of complex doubles');
    if (nm === 'Horner') check(!c.includes('static const') && /\(1\.0 \+ 2\.0\*I\) \* x/.test(c), 'Horner C: inline complex coefficients, parenthesised');
    compare(runC(c, `${nm}C`), want, `${nm} C`, cxClose);
  }
  // the numeric rows as the page builds them: Knuth–Eve and Belaga at degree 7
  // (Pan's complex scheme starts at degree 11 and says so), all three at degree 13
  for (const [srcN, wantRows, notPan] of [
    [src, ['Knuth–Eve', 'Belaga'], /^Pan's complex schemes start at degree 11 \(scheme \(4\); family \(3\) from 13\) and this polynomial has degree 7; below degree 11, Knuth–Eve and Belaga already give ⌊n\/2⌋\+1 multiplications for a monic polynomial\.$/],
    ['(0+1i)x^13 + 2x^11 - ix^3 + (1-1i)x + 1', ['Knuth–Eve', 'Pan', 'Belaga'], null],
  ]) {
    const csN = parsePoly(srcN, { complex: true }).coeffs, dcN = csN.map(toC);
    const wantN = zs.map(z => hornerC(dcN, z));
    const rows = buildComparisons(csN.map(c => Cx.fromRat(c)), Cx, 'C', { poly: srcN });
    if (notPan) check(!rows.find(r => r.name === 'Pan').ok && notPan.test(rows.find(r => r.name === 'Pan').note), `Pan C degree ${csN.length - 1}: refused with its note`);
    for (const nm of wantRows) {
      const row = rows.find(r => r.name === nm);
      check(!!row?.ok && typeof row.cText === 'string' && row.cTextFraction === row.cText && row.exact === false, `${nm} C: the page has C for it (${row?.note?.slice(0, 60)})`);
      if (!row?.cText) continue;
      shape(row.cText, `${nm} C`);
      check(row.cText.includes(' * Reference: ') && /Knuth|Pan|Belaga/.test(row.cText.split('Reference: ')[1] ?? ''), `${nm} C: header cites its reference`);
      if (nm === 'Belaga') check(/Reference: E\. G\. Belaga/.test(row.cText) && /Pt = /.test(row.cText) && /P = P_c\[\d+\] \* Pt;/.test(row.cText), 'Belaga C: cited; the scale line restores the leading coefficient');
      const o = runC(row.cText, `${cIdent(nm)}C_n${csN.length - 1}`);
      compare(o, wantN, `${nm} C n=${csN.length - 1} (numeric preprocessing)`, (a, b) => {
        const z = zs[wantN.indexOf(b)], g = parseCx(a);
        return Math.hypot(g.re - b.re, g.im - b.im) <= 1e-6 * (1 + Math.hypot(b.re, b.im) + coefScale(dcN, z));
      });
    }
  }
  // a real input over ℂ: ℝ's chain typed double complex, every literal a plain double
  const rsrc = '2x^9 - 4x^8 + 4x^7 - 7x^6 - 4x^5 - 11/2x^4 - 11x^3 + 5x^2 - 9/3x - 7';
  const rr = await compileChar0(rsrc, 'C'), qq = await compileChar0(rsrc, 'R');
  shape(rr.cText, 'ours C (real input)');
  const body = t => t.slice(t.indexOf('/* preprocessed constants')).replace(/[ \t]*\/\/.*$/gm, '');
  check(!/\*I/.test(rr.cText) && /return P \* 2\.0;/.test(rr.cText) && body(rr.cText) === body(qq.cText).replace(/\bdouble\b/g, 'double complex'),
        'C real input: R\'s code with double complex in place of double');
  const rdc = parsePoly(rsrc).coeffs.map(c => ({ re: ratToDouble(c.n, c.d), im: 0 }));
  compare(runC(rr.cText, 'oursC_real'), zs.map(z => hornerC(rdc, z)), 'ours C (real input)', cxClose);
}

// ---------- header width: a long P(x) line is wrapped, not left to overflow ----------
{
  const fact = n => { let f = 1n; for (let i = 2n; i <= BigInt(n); i++) f *= i; return f; };
  // the degree-12 truncation of e^x — its P(x) line is over 150 columns unwrapped
  const src = Array.from({ length: 13 }, (_, i) => 12 - i).map(i => (i === 0 ? '1' : `1/${fact(i)}x^${i}`)).join(' + ');
  const r = await compileChar0(src, 'R');
  const hl = r.cText.slice(0, r.cText.indexOf('*/')).split('\n');
  check(hl.every(l => l.length <= 88), `R deg 12: every header line within 88 columns (widest ${Math.max(...hl.map(l => l.length))})`);
  const poly = hl.join('\n').replace(/\n \* {3}/g, ' ').split('\n').find(l => l.includes('P(x) = '));
  check(poly && poly.includes('1/479001600*x^12') && poly.trim().endsWith('+ 1') && poly.length > 88,
        'R deg 12: the P(x) line is complete once the continuations are joined');
  check(hl.filter(l => /^ \* {3}\S/.test(l)).length >= 1, 'R deg 12: the P(x) line uses the doc-block continuation indent');
}

// ---------- mode aliases ----------
{
  const F32 = GF2k(32);
  const m = compileHorner([3n, 5n, 7n, 1n], F32);
  check(methodChainC(m.lines, 'gf2k', F32, { name: 'H' }).includes('gf32_mul('), "methodChainC 'gf2k' follows F.k");
  let threw = false; try { methodChainC(m.lines, 'gf64', F32, { name: 'H' }); } catch (e) { threw = true; } check(threw, 'methodChainC mode/field mismatch throws');
  const chain9 = await compileChar0('x^9 + 2x^3 - 5x + 1', 'p89');
  check(char0C(chain9.chain, 'p').includes('extra_large_mult_mod(') && char0C(chain9.chain, 'p89') === char0C(chain9.chain, 'p'), "char0C 'p' = 'p89'");
  threw = false; try { char0C(chain9.chain, 'p61'); } catch (e) { threw = true; } check(threw, 'char0C refuses a chain over another prime');
}

// ---------- char2C direct: rejects other fields ----------
{
  let threw = false;
  try { char2C(GF2k(8), { n: 1, gates: [], out: { t: ['x'], k: null } }, []); } catch (e) { threw = true; }
  check(threw, 'char2C rejects GF(2^8)');
}

// ---------- methodChainC: the radix (ldexp) path and out-of-range constants ----------
{
  const radix = [{ lhs: 'z', rhs: '0.5·x', mul: false, radixShift: -1 }, { lhs: 'P', rhs: 'z * z', mul: true }];
  const cR = methodChainC(radix, 'R', R, { name: 't', preprocessing: 'numeric' });
  check(/double z = ldexp\(x, -1\);/.test(cR) && /#include <math.h>/.test(cR), 'R: a radix line is a free ldexp');
  const cC = methodChainC(radix, 'C', Cx, { name: 't', preprocessing: 'numeric' });
  check(!/ldexp\(x/.test(cC) && /double complex z = [^;]*\* x;/.test(cC), 'C: a radix line is a plain product, never ldexp(double complex)');
  compare(buildAndRun(cC, 'C', [{ re: 2, im: 4 }, { re: -1, im: 0.5 }], 'radixC'), [{ re: -3, im: 4 }, { re: 0.1875, im: -0.25 }], 'C radix line', cxClose);
  // a constant beyond the double range is refused (no inf literal), as char0C does
  const huge = compileHorner([Rat.ZERO, Rat.ONE, Rat.ZERO, new Rat(10n ** 400n)], R);
  let msg = null;
  try { methodChainC(huge.lines, 'R', R, { name: 'Horner', preprocessing: 'none' }); } catch (e) { msg = e.message; }
  check(msg !== null && /1e\+400 is not representable as a double/.test(msg), `R: 1e+400 constant refused (${msg})`);
  const hugeC = compileHorner([Rat.ZERO, Rat.ONE, Rat.ZERO, new Rat(10n ** 400n)].map(c => Cx.fromRat(c)), Cx);
  msg = null;
  try { methodChainC(hugeC.lines, 'C', Cx, { name: 'Horner', preprocessing: 'none' }); } catch (e) { msg = e.message; }
  check(msg !== null && /not representable as a double/.test(msg), `C: 1e+400 constant refused (${msg})`);
}

console.log(`${checks} checks, ${fails} failures (targets: ${targets.map(t => t.label).join(', ')})`);
if (fails) process.exit(1);
console.log('CGEN PASSES');
