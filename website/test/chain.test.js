// chain.test.js — paper-format rendering (letter wire names, gadget headings)
// and gate-label provenance invariants of the char-0 chain builder.
import { decode, rationals, GF, compile_paper_params_chain } from '../js/char0/core.js';
import { renderAffineChain, renderGateChain, chainToText, paperWireNames, gateGroups, wireLetter, countOps,
         formatConstants, toSigDigits, foldConstants, factorize } from '../js/chain.js';
import { CIRCUITS } from '../js/char2.js';
import { GF2k } from '../js/field.js';
import { Rat } from '../js/rat.js';

let fails = 0, checks = 0;
const check = (c, m) => { checks++; if (!c) { fails++; console.error('FAIL: ' + m); } };
const M61 = (1n << 61n) - 1n;
const toRat = c => Rat.of(typeof c === 'number' ? BigInt(c) : c);
const QDisplay = { isZero: c => toRat(c).isZero(), toDisplay: c => toRat(c).toString() };
const FpDisplay = { isZero: c => BigInt(c) === 0n, toDisplay: c => BigInt(c).toString() };

check(wireLetter(0) === 'y' && wireLetter(19) === 'b' && wireLetter(20) === 'g20', 'wireLetter scheme');

function chainFor(n, useQ) {
  const field = useQ ? rationals() : GF(M61);
  const cs = [];
  for (let i = 0; i < n; i++) cs.push(field.coerce(useQ ? ((i * 7 + 3) % 11) - 5 : BigInt((i * 13 + 5) % 97)));
  cs.push(field.one());
  return compile_paper_params_chain(decode(n, cs, field), useQ ? null : M61);
}

for (const [n, useQ] of [[7, true], [9, true], [15, true], [31, true], [27, false], [63, false], [64, false], [127, false]]) {
  const chain = chainFor(n, useQ);
  const F = useQ ? QDisplay : FpDisplay;
  check(chain.gate_labels.length === chain.gates.length, `n=${n}: gate_labels parallel to gates`);
  check(chain.gate_labels.every(l => typeof l === 'string' && l.length), `n=${n}: every gate labeled`);
  check(chain.gate_label_paths.every((p, i) => p[p.length - 1] === chain.gate_labels[i]), `n=${n}: label path ends in innermost label`);
  check(chain.gates.every((g, i) => g.label === chain.gate_labels[i]), `n=${n}: MulGate.label mirrors gate_labels`);

  const idx = renderAffineChain(F, chain);
  const let_ = renderAffineChain(F, chain, { names: 'letters' });
  const grp = renderAffineChain(F, chain, { names: 'letters', group: true });
  check(idx.length === chain.gates.length + 1 && idx[0].lhs === 'y0', `n=${n}: index naming default`);
  check(let_.length === idx.length && let_[0].lhs === 'y' && let_[chain.gates.length].lhs === 'P', `n=${n}: letters naming`);
  check(let_.every((l, i) => i === let_.length - 1 || l.lhs === wireLetter(i)), `n=${n}: letters follow appendix order`);
  const heads = grp.filter(l => l.heading !== undefined);
  const runs = chain.gate_labels.filter((l, i) => i === 0 || l !== chain.gate_labels[i - 1]).length;
  check(heads.length === runs, `n=${n}: one heading per label run (${heads.length} vs ${runs})`);
  check(grp.filter(l => l.heading === undefined).length === idx.length, `n=${n}: grouping adds only headings`);
  check(grp[0].heading === chain.gate_labels[0], `n=${n}: first heading is first label`);
  const txt = chainToText({ lines: grp });
  check(txt.startsWith(`── ${chain.gate_labels[0]} ──\n`), `n=${n}: chainToText prints headings`);
  // renaming must not change the right-hand sides beyond wire names
  const rename = paperWireNames(chain);
  const idxToLet = s => s.replace(/\by(\d+)\b/g, (_, k) => rename[Number(k) + 2]);
  check(idx.every((l, i) => idxToLet(l.rhs) === let_[i].rhs), `n=${n}: rhs identical up to renaming`);
  const groups = gateGroups(chain);
  check(groups.size === chain.gates.length && groups.get(2) === chain.gate_labels[0], `n=${n}: gateGroups map`);
}

// specific expected labels (documented emission points)
const c7 = chainFor(7, true);
check(c7.gate_labels.every(l => l === 'P_7 base'), 'n=7: all gates from P_7 base');
const c15 = chainFor(15, true);
check(JSON.stringify(c15.gate_labels) === JSON.stringify([
  'H_2 base', 'H_4 known power', 'Q_7 known-power block', 'Q_7 known-power block', 'Q_7 known-power block',
  'splittable pair (T⁽¹⁾_15, T⁽²⁾_15)', 'splittable pair (T⁽¹⁾_15, T⁽²⁾_15)', 'P_15 = x·T⁽¹⁾ + T⁽²⁾']), 'n=15 labels');
const c64 = chainFor(64, false);
check(c64.gate_labels[c64.gate_labels.length - 1] === 'even lift P_64 = x·P_63 + α_0', 'n=64: even lift label');
const c9 = chainFor(9, true);
check(c9.gate_label_paths[2].includes('T-recursion T_{2,4} (l=2)') && c9.gate_labels[2] === 'H_8 known power', 'n=9: nested T path');

// char-2 gate chain: letters are native; index renames to y0..; group is a no-op without labels
const F2 = GF2k(64);
const spec = CIRCUITS[15];
const keys = []; for (let i = 0; i < spec.keys; i++) keys.push(F2.fromInt(i + 1));
const a = renderGateChain(F2, spec, keys);
const b = renderGateChain(F2, spec, keys, { names: 'index' });
const c = renderGateChain(F2, spec, keys, { names: 'letters', group: true });
check(a[0].lhs === 'y' && b[0].lhs === 'y0' && b[1].rhs.includes('y0') && !b[1].rhs.includes('(y +'), 'char2 index renaming');
check(JSON.stringify(a) === JSON.stringify(c), 'char2 group without labels is a no-op');
check(a.length === spec.gates.length + 1 && a[a.length - 1].lhs === 'P', 'char2 output line');

// ---- factorize folds the constants an inlined affine wire brings along ---------
{
  const ke = factorize([
    { lhs: 'y', rhs: 'x + 0.6277364', mul: false },
    { lhs: 'w', rhs: 'y * y', mul: true },
    { lhs: 'f0', rhs: '(y - 4.392765911111) * (w + 7.564986624894)', mul: true },
    { lhs: 'P', rhs: 'f0 + 0.2256435388577', mul: false },
  ]);
  check(ke[1].rhs === '(x − 3.765029511111) * (w + 7.564986624894)', `decimal constants fold after inlining: ${ke[1].rhs}`);
  const ex = factorize([
    { lhs: 'y', rhs: 'x + 3/2', mul: false },
    { lhs: 'z', rhs: '(y - 1/2) * (y + 1)', mul: true },
    { lhs: 'P', rhs: 'z + 2 - 2', mul: false },
  ]);
  check(ex[0].rhs === '(x + 1) * (x + 5/2)' && ex[1].rhs === 'z', `exact constants fold as rationals; a zero sum vanishes: ${ex.map(l => l.rhs).join(' | ')}`);
  check(JSON.stringify(foldConstants([{ neg: false, t: [{ tok: 'x' }] }, { neg: true, t: [{ tok: '3' }] }])) ===
        JSON.stringify([{ neg: false, t: [{ tok: 'x' }] }, { neg: true, t: [{ tok: '3' }] }]), 'a single constant is left alone');
  // complex doubles fold into one canonical (re±imi) token, kept parenthesised and last
  const cx = foldConstants([{ neg: false, t: [{ tok: '(1.5+2i)' }] }, { neg: false, t: [{ tok: 'x' }] }, { neg: true, t: [{ tok: '(0.25-0.5i)' }] }]);
  check(JSON.stringify(cx) === JSON.stringify([{ neg: false, t: [{ tok: 'x' }] }, { neg: false, t: [{ tok: '(1.25+2.5i)' }] }]), `foldConstants complex: ${JSON.stringify(cx)}`);
  const cr = foldConstants([{ neg: false, t: [{ tok: '(1+2i)' }] }, { neg: false, t: [{ tok: '1/2' }] }, { neg: true, t: [{ tok: '(0+2i)' }] }]);
  check(JSON.stringify(cr) === JSON.stringify([{ neg: false, t: [{ tok: '1.5' }] }]), `foldConstants complex parts cancelling to a real token: ${JSON.stringify(cr)}`);
  const cn = foldConstants([{ neg: false, t: [{ tok: '(0+1i)' }] }, { neg: true, t: [{ tok: '(2+3i)' }] }]);
  check(JSON.stringify(cn) === JSON.stringify([{ neg: false, t: [{ tok: '(-2-2i)' }] }]), `foldConstants negative real part stays inside the literal: ${JSON.stringify(cn)}`);
  const cf = factorize([
    { lhs: 'y', rhs: 'x + (0.5+1.25i)', mul: false },
    { lhs: 'P', rhs: '(y − (1+0.25i)) * (x + (0-1i))', mul: true },
  ]);
  check(cf[0].rhs === '(x + (-0.5+1i)) * (x + (0-1i))', `factorize keeps complex literals atomic: ${cf[0].rhs}`);
}

// ---- countOps: the footer counts exactly what the displayed form shows -----------
// (displayed-form count; integer multiples charged by double-and-add, the
// hardware variant of the paper's accounting — the paper's A_n treats fixed
// integer multiples as free, see tools/polychain.py add_count)
{
  const ex = [
    'y   = x * (x + 65342529/16384)',
    'z   = (x + y + 4268043425794177/268435456) * (x − 65301569/16384)',
    'w   = (z + 278709932825554996974785/4398046511104) * x',
    'v   = (x + z + 278709932164679789204673/4398046511104) * (w + 15899/64)',
    'P_7 = y + w + v + 87474275/8192',
    'P   = 1/5040 * P_7   (leading-coefficient scale)',
  ].join('\n');
  const o = countOps(ex);
  check(o.adds === 11 && o.mults === 4 && o.scalar === 1, `countOps degree-7 example: ${JSON.stringify(o)}`);
  const f = countOps('f0 = (1/5040) * (x)\nf1 = (f0 + 1/720) * (x)\nP  = f1 + 1');
  check(f.adds === 2 && f.mults === 1 && f.scalar === 1, `countOps parenthesised scalar: ${JSON.stringify(f)}`);
  const h = countOps('── layer 1 ──\nP = x^4 + 2·x + 1');
  check(h.adds === 3 && h.mults === 2 && h.scalar === 0, `countOps hidden powers + integer multiple by double-and-add (hardware variant): ${JSON.stringify(h)}`);
  const q = countOps('P = 4·y + 3·z');
  check(q.adds === 1 + 2 + 2 && q.scalar === 0, `countOps double-and-add for 4 and 3 (hardware variant, not the paper's free multiples): ${JSON.stringify(q)}`);
  const wrapped = countOps('P = y + w\n      + v + 3');
  check(wrapped.adds === 3 && wrapped.mults === 0, `countOps wrapped continuation: ${JSON.stringify(wrapped)}`);
  check(countOps('').adds === 0 && countOps(undefined).mults === 0, 'countOps empty');
  const c1 = countOps('P = (1+2i) * y');
  check(c1.scalar === 1 && c1.mults === 0 && c1.adds === 0, `countOps complex literal is one scalar: ${JSON.stringify(c1)}`);
  const c2 = countOps('P = x + (0+1i)');
  check(c2.adds === 1 && c2.mults === 0 && c2.scalar === 0, `countOps complex literal is one summand: ${JSON.stringify(c2)}`);
  const c3 = countOps('y = (x + (1.5-0.25i)) * (x − (1e-7+3.2e+5i))\nP = y * (0-1i)');
  check(c3.adds === 2 && c3.mults === 1 && c3.scalar === 1, `countOps complex factors: ${JSON.stringify(c3)}`);
}

// ---- formatConstants: readable constants are a display-only rewrite ------------
{
  check(toSigDigits(3988.19) === '3988.19' && toSigDigits(1.5) === '1.5' && toSigDigits(0) === '0' && toSigDigits(-7) === '-7',
        'toSigDigits fixed notation');
  check(toSigDigits(1 / 5040) === '0.000198413' && toSigDigits(15899 / 64) === '248.422', `toSigDigits six digits: ${toSigDigits(1 / 5040)} ${toSigDigits(15899 / 64)}`);
  check(toSigDigits(4268043425794177 / 268435456) === '1.58997e7' && toSigDigits(2.5e-7) === '2.5e-7' && toSigDigits(-1e21) === '-1e21',
        `toSigDigits scientific: ${toSigDigits(4268043425794177 / 268435456)} ${toSigDigits(2.5e-7)} ${toSigDigits(-1e21)}`);
  check(toSigDigits(999999.7) === '1e6' && toSigDigits(123456) === '123456', `toSigDigits rounding into the next decade: ${toSigDigits(999999.7)}`);
  const ex = [
    '── H_2 base ──',
    'y   = x * (x + 65342529/16384)',
    'z   = (x + y + 4268043425794177/268435456) * (x − 65301569/16384)',
    'v   = (x2 + 2·z − 1/5040) * (w + 15899/64)',
    'P_7 = y + w + v + 87474275/8192 + x^4 + g20 + f0',
    'P   = 1/5040 * P_7   (leading-coefficient scale)',
    '      + 3',
  ].join('\n');
  const dec = formatConstants(ex, 'decimal');
  check(dec.split('\n')[0] === '── H_2 base ──', 'formatConstants leaves headings alone');
  check(dec.includes('y   = x * (x + 3988.19)') && dec.includes('(x + y + 1.58997e7) * (x − 3985.69)'), `formatConstants decimals: ${dec.split('\n')[2]}`);
  check(dec.includes('(x2 + 2·z − 0.000198413) * (w + 248.422)'), `formatConstants keeps wire names and integer multiples: ${dec.split('\n')[3]}`);
  check(dec.includes('P_7 = y + w + v + 10678 + x^4 + g20 + f0'), `formatConstants keeps P_7, x^4, g20, f0: ${dec.split('\n')[4]}`);
  check(dec.includes('P   = 0.000198413 * P_7   (leading-coefficient scale)') && dec.endsWith('+ 3'), 'formatConstants scale row + continuation line');
  check(formatConstants(ex, null) === ex && formatConstants('', 'decimal') === '', 'formatConstants without a style is the identity');
  check(countOps(ex).mults === countOps(dec).mults && countOps(ex).adds === countOps(dec).adds && countOps(ex).scalar === countOps(dec).scalar,
        'the rewrite preserves the operation counts');
  const gf = 'y = (x + 5) * (x + 0x1f3a)\nP = y + 0xdeadbeef + 1 + x2';
  check(formatConstants(gf, 'hex') === 'y = (x + 0x5) * (x + 0x1f3a)\nP = y + 0xdeadbeef + 0x1 + x2', `formatConstants hex: ${formatConstants(gf, 'hex')}`);
  check(formatConstants('P = 0.3333333333333333 * x + 1234567', 'decimal') === 'P = 0.333333 * x + 1.23457e6', `formatConstants doubles + long integers: ${formatConstants('P = 0.3333333333333333 * x + 1234567', 'decimal')}`);
  const huge = `P = ${'9'.repeat(400)}/7 * x`;
  check(formatConstants(huge, 'decimal') === huge, 'out-of-double-range constants keep their exact token');
  const cx = formatConstants('P = y + (1.234567890123+2.345678901234i)', 'decimal');
  check(cx === 'P = y + (1.23457+2.34568i)', `formatConstants rounds both parts of a complex literal: ${cx}`);
  const cx2 = formatConstants('y = (x − (0-1i)) * (x + (-2.000000001+1e-7i))', 'decimal');
  check(cx2 === 'y = (x − (0-1i)) * (x + (-2+1e-7i))', `formatConstants keeps the complex form: ${cx2}`);
  check(formatConstants('P = y + (1.5+2i)', 'hex') === 'P = y + (1.5+2i)', 'hex style leaves complex literals alone');
  check(countOps('P = y + (1.234567890123+2.345678901234i)').adds === countOps(cx).adds, 'the complex rewrite preserves the counts');
}

if (fails) { console.error(`${fails} failure(s) out of ${checks} checks`); process.exit(1); }
console.log(`CHAIN RENDER PASSES (${checks} checks)`);
