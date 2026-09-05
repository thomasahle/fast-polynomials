// mathview.test.js — the display-only plain-chain -> TeX adapter and the
// vendored KaTeX runtime. Besides focused token checks, render every equation
// produced by representative fields and every available comparison method.
import { readFileSync } from 'node:fs';
import vm from 'node:vm';
import { handleMessage } from '../js/worker.js';
import {
  nameToTex, tokenToTex, expressionToTex, chainMathRows, renderLatex,
} from '../js/mathview.js';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };
const eq = (got, want, msg) => check(got === want, `${msg}: got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`);

eq(nameToTex('P_7'), 'P_{7}', 'explicit subscript');
eq(nameToTex('P̃'), '\\widetilde{P}', 'combining tilde');
eq(nameToTex('H̃_8'), '\\widetilde{H}_{8}', 'tilde before a subscript');
eq(nameToTex('T⁽¹⁾'), 'T^{(1)}', 'paper superscript');
eq(nameToTex('Q_3′′'), 'Q_{3}^{\\prime\\prime}', 'primed paper gadget');
eq(nameToTex('y12'), 'y_{12}', 'indexed wire');
eq(nameToTex('x4'), 'x^{4}', 'power wire');
eq(nameToTex('alpha3'), '\\alpha_{3}', 'named Greek parameter');
eq(tokenToTex('-7/3'), '-\\frac{7}{3}', 'rational constant');
eq(tokenToTex('0x1f'), '\\mathtt{0x1f}', 'binary-field constant');
eq(tokenToTex('1e-7'), '1\\mathbin{\\times}10^{-7}', 'scientific notation');
eq(tokenToTex('2·y'), '2\\,y', 'integer multiple');
eq(expressionToTex('(x + 1/2) * (P̃ − 0x1f)'),
  '\\left(x + \\frac{1}{2}\\right) \\mathbin{\\cdot} ' +
  '\\left(\\widetilde{P} - \\mathtt{0x1f}\\right)', 'factored expression');

const sample = chainMathRows([
  '── H̃_8 ──',
  'y0  = (x + 1/2) * (P̃ − 0x1f)',
  'P_7 = y0 + 2·x^4',
  '      + 1e-7   (boundary correction)',
].join('\n'));
eq(sample.length, 3, 'wrapped RHS is folded into its equation');
eq(sample[0].tex, '\\widetilde{H}_{8}', 'heading TeX');
eq(sample[2].annotation, 'boundary correction', 'annotation separated from math');
check(sample[2].rhsTex.includes('10^{-7}'), 'wrapped scientific term converted');

// Load the exact browser asset in a `self` sandbox: no npm install or browser
// global is required by the test suite.
const katexSource = readFileSync(new URL('../js/vendor/katex/katex.min.js', import.meta.url), 'utf8');
const pageCss = readFileSync(new URL('../style.css', import.meta.url), 'utf8');
const sandbox = { self: {} };
vm.runInNewContext(katexSource, sandbox);
globalThis.katex = sandbox.self.katex;
eq(globalThis.katex.version, '0.18.5', 'pinned KaTeX runtime');
check(renderLatex(sample[2].rhsTex)?.includes('class="katex-mathml"'),
  'KaTeX emits accessible MathML and HTML');
const tableRule = (/\.math-table\s*\{([^}]*)\}/.exec(pageCss)?.[1] ?? '')
  .replace(/\/\*[\s\S]*?\*\//g, '');
check(tableRule.includes('width: max-content') && tableRule.includes('margin-inline: auto') &&
      !/\bmin-width\s*:/.test(tableRule),
  'the alignment table keeps intrinsic column widths instead of distributing spare pane width');

const CASES = [
  { lane: 'char2', fieldMode: 'gf64',
    src: 'x^15 + 4x^14 + 0x14x^13 + 0xfx^12 + 3x^11 + 2x^10 + 4x^9 + 8x^8 + 9x^7 + 0x12x^6 + 0x15x^5 + 2x^4 + 0x13x^3 + 8x^2 + 0x18x + 0x16' },
  { lane: 'char0', fieldMode: 'Q',
    src: 'x^7 - 2x^6 - 8x^5 - 6x^4 - 11x^3 + 10/3x^2 + 2x - 7/3' },
  { lane: 'char0', fieldMode: 'R',
    src: '1/6x^6 + 1/5x^5 + 1/4x^4 + 1/3x^3 + 1/2x^2 + x + 1' },
  { lane: 'char0', fieldMode: 'p89',
    src: 'x^15 - 5x^14 - 17x^13 + 18x^12 - 12x^11 + 19x^10 - 12x^9 + 17x^8 + 17x^7 - 18x^6 + 3x^5 + 14x^4 + 8x^3 + 7x^2 + 11x + 9' },
];

let equations = 0;
for (const request of CASES) {
  const result = await handleMessage(request);
  const texts = [result.mathText, result.mathTextOriginal,
    ...result.comparisons.flatMap(row => row.ok ? [row.mathText, row.mathTextOriginal] : [])]
    .filter(Boolean);
  for (const text of texts) for (const row of chainMathRows(text)) {
    if (row.kind === 'heading') check(!!renderLatex(row.tex), `heading renders: ${row.text}`);
    if (row.kind !== 'equation') continue;
    equations++;
    check(!!row.rhsTex, `equation parses: ${row.lhs} = ${row.expression}`);
    check(!!renderLatex(row.lhsTex), `lhs renders: ${row.lhs}`);
    check(!!renderLatex(row.rhsTex), `rhs renders: ${row.expression}`);
  }
}
check(equations > 300, `broad generated-chain coverage (${equations} equations)`);

delete globalThis.katex;
console.log(fails ? `MATH VIEW FAILED (${fails}/${checks})` : `MATH VIEW PASSES (${checks} checks, ${equations} generated equations)`);
process.exit(fails ? 1 : 0);
