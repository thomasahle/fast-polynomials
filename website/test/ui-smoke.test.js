// ui-smoke.test.js — drives the worker's message handler (handleMessage) under
// node for one example per UI mode (char 0 / Mersenne / char 2) and checks
// that every field the page's views rely on is present and structured-clone
// safe: mathText, mathTextOriginal, cText, cTextFraction (char 0 only), graph +
// graphSvg + graphText, and the same fields on every comparison row.  Also
// unit-checks the C highlighter (token round-trip, HTML escaping) and, since
// ui.js needs a DOM, structurally checks the automatic-compilation wiring
// (no Compile button, debounced edits, cancel-while-busy, compile on load).
import { readFileSync } from 'node:fs';
import { handleMessage } from '../js/worker.js';
import { tokenizeC, highlightC } from '../js/highlight.js';
import { graphStats } from '../js/graph.js';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };

// plain-JSON check: strings / numbers / booleans / null / arrays / plain objects only
function isPlain(v, path = '$') {
  if (v === null) return true;
  const t = typeof v;
  if (t === 'string' || t === 'number' || t === 'boolean') return true;
  if (Array.isArray(v)) return v.every((x, i) => isPlain(x, `${path}[${i}]`));
  if (t === 'object' && Object.getPrototypeOf(v) === Object.prototype)
    return Object.entries(v).every(([k, x]) => isPlain(x, `${path}.${k}`));
  console.log(`  non-plain value at ${path}: ${t} ${v?.constructor?.name ?? ''}`);
  return false;
}

const MODES = [
  ['char 0',   { lane: 'char0', fieldMode: 'Q',
                 src: 'x^7 - 2x^6 - 8x^5 - 6x^4 - 11x^3 + 10/3x^2 + 4/2x - 7/3' }],
  ['Mersenne', { lane: 'char0', fieldMode: 'p',
                 src: 'x^15 - 5x^14 - 17x^13 + 18x^12 - 12x^11 + 19x^10 - 12x^9 + 17x^8 + 17x^7 - 18x^6 + 3x^5 + 14x^4 + 8x^3 + 7x^2 + 11x + 9' }],
  ['char 2',   { lane: 'char2', fieldMode: null,
                 src: 'x^15 + 4x^14 + 0x14x^13 + 0xfx^12 + 3x^11 + 2x^10 + 4x^9 + 8x^8 + 9x^7 + 0x12x^6 + 0x15x^5 + 2x^4 + 0x13x^3 + 8x^2 + 0x18x + 0x16' }],
];

const checkRow = (tag, r, { isQ, ours }) => {
  for (const f of ['mathText', 'cText', 'graph', 'graphSvg', 'graphText', 'mults', 'adds', 'height'])
    check(r[f] !== undefined && r[f] !== null, `${tag}: field ${f} missing`);
  check('mathTextOriginal' in r, `${tag}: mathTextOriginal key missing`);
  check('cTextFraction' in r, `${tag}: cTextFraction key missing`);
  if (ours) check(typeof r.mathTextOriginal === 'string' && r.mathTextOriginal.length > 0, `${tag}: mathTextOriginal text`);
  if (isQ) check(typeof r.cTextFraction === 'string' && r.cTextFraction.length > 0, `${tag}: cTextFraction (char 0) text`);
  else check(r.cTextFraction === null || r.cTextFraction === r.cText, `${tag}: cTextFraction must be null (or == cText) outside char 0`);
  if (r.graph) {
    const st = graphStats(r.graph);
    check(st.mul === r.mults, `${tag}: graph mul nodes ${st.mul} != mults ${r.mults}`);
    check(typeof r.graphSvg === 'string' && r.graphSvg.startsWith('<svg') && r.graphSvg.endsWith('</svg>'), `${tag}: graphSvg well-formed`);
    check(typeof r.graphText === 'string' && r.graphText.includes('# '), `${tag}: graphText footer`);
  }
  check(r.cText.includes('eval_P'), `${tag}: cText has eval_P`);
};

for (const [label, msg] of MODES) {
  const t0 = Date.now();
  const result = await handleMessage(msg);
  const isQ = msg.lane === 'char0' && msg.fieldMode === 'Q';
  console.log(`${label}: ${Date.now() - t0} ms, mults=${result.mults}, field=${result.fieldName}, ` +
              `comparisons=${result.comparisons.map(c => `${c.name}${c.ok ? '' : '✗'}`).join(', ')}`);
  check(!result.oursFailed, `${label}: our compiler failed: ${result.oursFailed}`);
  check(isPlain(result), `${label}: result is plain JSON (structured-clone safe)`);
  let cloned = null;
  try { cloned = structuredClone(result); } catch (e) { check(false, `${label}: structuredClone threw ${e.message}`); }
  check(cloned && cloned.mults === result.mults, `${label}: structuredClone round trip`);
  checkRow(label, result, { isQ, ours: true });
  check(typeof result.fieldName === 'string' && result.fieldName.length > 0, `${label}: fieldName`);
  const expectField = isQ ? 'ℚ' : (msg.fieldMode === 'p' ? 'GF(2^89−1)' : 'GF(2^64)');
  check(result.fieldName === expectField, `${label}: fieldName ${result.fieldName} != ${expectField}`);
  // original form: char 2 uses the appendix letter names; char 0 follows sections/constructions
  // (named gadget rows H_2, H_4, Q_k, T⁽¹⁾, T⁽²⁾ …, last row P_n, no per-gate headings)
  if (msg.lane === 'char2') check(/^y\s*=/m.test(result.mathTextOriginal), `${label}: paper text starts wires at y`);
  if (msg.lane === 'char0') {
    const rows = result.mathTextOriginal.split('\n');
    check(!result.mathTextOriginal.includes('──'), `${label}: constructions form has no headings`);
    check(/^P(_\d+)?\s+=|^P̃?\s*=|^P\s*=/.test(rows[rows.length - 1]), `${label}: constructions form ends with P_n (${rows[rows.length - 1].slice(0, 20)})`);
    check(/^(H_2|y|P_\d+)\s+=/.test(rows[0]), `${label}: constructions form starts with a paper name (${rows[0].slice(0, 20)})`);
  }
  if (msg.fieldMode === 'p') check(result.cText.includes('M89') && result.cText.includes('__uint128_t'), `${label}: Mersenne C`);
  if (msg.lane === 'char2') check(result.cText.includes('lemul') || result.cText.includes('gf64_mul'), `${label}: GF(2^64) C uses the hardware carryless path`);
  if (isQ) {
    check(result.cTextFraction.includes('(double)'), `${label}: fraction C uses (double)NUM/DEN`);
    check(result.cTextFraction !== result.cText, `${label}: fraction C differs from float C`);
  }
  // comparisons: Horner, Estrin, Rabin–Winograd (+ numerical methods in Q)
  const names = result.comparisons.map(c => c.name);
  for (const n of ['Horner', 'Estrin', 'Rabin–Winograd']) check(names.includes(n), `${label}: comparison ${n} present`);
  if (isQ) for (const n of ['Knuth–Eve', 'Pan']) check(names.includes(n), `${label}: ${n} present in Q mode`);
  for (const c of result.comparisons) {
    check('ok' in c && 'name' in c, `${label}/${c.name}: ok/name`);
    if (!c.ok) { console.log(`  note: ${c.name} not ok: ${c.note}`); continue; }
    for (const f of ['preprocessing', 'exact', 'note']) check(f in c, `${label}/${c.name}: ${f}`);
    checkRow(`${label}/${c.name}`, c, { isQ: isQ && !['Knuth–Eve', 'Pan'].includes(c.name), ours: false });
  }
}

// error path: a char-2 degree above 26 (27 is the paper's open frontier) must throw a readable message
for (const [src, n] of [['x^27 + x + 1', 27], ['x^30 + 1', 30]]) {
  try {
    await handleMessage({ lane: 'char2', src, fieldMode: null });
    check(false, `char 2 ${src} should throw`);
  } catch (e) {
    check(new RegExp(`characteristic-2 chains exist for every degree up to 26 \\(you entered degree ${n}\\); degree 27 is the open frontier of the paper`).test(e.message),
          `char 2 unsupported-degree message: ${e.message}`);
  }
}
// every degree 1..26 compiles through the worker path: odd degrees by their circuits,
// even ones by the x-lift of the degree below (one extra multiplication), 1 and 2 directly
{
  const r = await handleMessage({ lane: 'char2', src: 'x^5 + 3x + 1', fieldMode: null });
  check(r.mults === 3 && r.hornerMults === 4 && !r.oursFailed, 'char 2 degree 5 compiles with 3 multiplications');
  const r4 = await handleMessage({ lane: 'char2', src: 'x^4 + 3x + 1', fieldMode: null });
  check(r4.mults === 3 && r4.hornerMults === 3 && !r4.oursFailed, 'char 2 degree 4 compiles with 3 multiplications');
  check(/^P_3 = /m.test(r4.mathText) && /^P +=\s+x \* P_3 \+ 1   \(even-degree lift\)$/m.test(r4.mathText), 'char 2 degree 4: lift row P = x * P_3 + c0');
  check(r4.cText.includes('even-degree lift') && graphStats(r4.graph).mul === 3, 'char 2 degree 4: lift in the C and graph views');
  const r1 = await handleMessage({ lane: 'char2', src: 'x + 1', fieldMode: null });
  check(r1.mults === 0 && r1.hornerMults === 0 && /^P = x \+ 1$/m.test(r1.mathText) && graphStats(r1.graph).mul === 0, 'char 2 degree 1: P = x + 1, no multiplication');
  const r2 = await handleMessage({ lane: 'char2', src: 'x^2 + 3x + 1', fieldMode: null });
  check(r2.mults === 1 && /^y = x \* \(x \+ 3\)$/m.test(r2.mathText) && /^P = y \+ 1$/m.test(r2.mathText), 'char 2 degree 2: y = x * (x + 3), P = y + 1');
  const r26 = await handleMessage({ lane: 'char2', src: 'x^26 + 0x1fx^13 + x + 1', fieldMode: null });
  check(r26.mults === 14 && r26.hornerMults === 25 && /P_25/.test(r26.mathTextOriginal), 'char 2 degree 26 compiles with 14 multiplications (degree-25 circuit + lift)');
}

// ---- highlighter ----
const sample = `#include <stdint.h>
#if defined(__x86_64__) && defined(__PCLMUL__)
/* block
   comment */
static const uint64_t a[2] = {0x1234ULL, 42u}; // keys
__uint128_t eval_P(uint64_t x) { double d = 1.5e-3; char *s = "a\\"b<c>"; if (P >= M89) P -= M89; return gf64_mul(P, 0xffULL); }
`;
const toks = tokenizeC(sample);
check(toks.map(t => t.text).join('') === sample, 'tokenizer round-trips the source');
const types = new Set(toks.map(t => t.type));
for (const t of ['comment', 'preproc', 'string', 'number', 'keyword', 'type', 'fn', 'ident', 'op', 'space'])
  check(types.has(t), `tokenizer produces ${t} tokens`);
check(toks.find(t => t.text === '0x1234ULL')?.type === 'number', 'hex ULL literal is one number token');
check(toks.find(t => t.text === '1.5e-3')?.type === 'number', 'float literal with exponent');
check(toks.find(t => t.text === '__uint128_t')?.type === 'type', '__uint128_t is a type');
check(toks.find(t => t.text === 'gf64_mul')?.type === 'fn', 'call site is fn');
check(toks.find(t => t.text === '#include <stdint.h>')?.type === 'preproc', 'preprocessor line');
const html = highlightC(sample);
check(!/<(?!\/?span)/.test(html.replace(/<span class="hl-[a-z]+">/g, '<span>')), 'highlighter output has only span tags');
check(html.includes('&lt;stdint.h&gt;'), 'highlighter escapes < >');
check(html.includes('class="hl-keyword">return<'), 'return highlighted as keyword');
check(html.includes('class="hl-string">"a\\"b&lt;c&gt;"<'), 'string with escapes stays one token');
// idempotence under theme: the generated C for every mode highlights without throwing
for (const [label, msg] of MODES) {
  const r = await handleMessage(msg);
  for (const c of [r.cText, r.cTextFraction, ...r.comparisons.map(x => x.cText)]) {
    if (!c) continue;
    check(tokenizeC(c).map(t => t.text).join('') === c, `${label}: generated C round-trips through the tokenizer`);
  }
}

// ---- automatic compilation: structural checks on the UI layer --------------
// ui.js needs a DOM to execute, so assert its wiring textually: the Compile
// button is gone, edits are debounced in ui.js (never in the pure reducer), a
// cancel affordance is dispatched while busy, and the first load compiles.
const uiSrc = readFileSync(new URL('../js/ui.js', import.meta.url), 'utf8');
const stateSrc = readFileSync(new URL('../js/uistate.js', import.meta.url), 'utf8');
const githubStarsSrc = readFileSync(new URL('../js/github-stars.js', import.meta.url), 'utf8');
check(!uiSrc.includes('id="go"') && !uiSrc.includes('goLabel'), 'no Compile button (#go) or goLabel in ui.js');
check(!stateSrc.includes('goLabel'), 'goLabel selector removed from uistate.js');
check(/DEBOUNCE_MS = 500\b/.test(uiSrc), 'edit debounce constant (~500 ms) present in ui.js');
check(uiSrc.includes('setTimeout(') && uiSrc.includes('clearTimeout('), 'debounce timer is set and reset in ui.js');
check(!/set(Timeout|Interval)\(/.test(stateSrc), 'uistate.js stays pure: no timers');
check(uiSrc.includes("dispatch({ type: 'compile' })"), 'ui.js dispatches compile (debounce / load / Cmd+Enter)');
check(uiSrc.includes('id="cancel"') && uiSrc.includes("dispatch({ type: 'cancel' })"), 'cancel affordance dispatches cancel while busy');
check(/useEffect\(\(\) => \{ compileNow\(\); \}, \[\]\)/.test(uiSrc), 'initial example compiles on first load');

// ---- redesign layout: structural checks ------------------------------------
const indexSrc = readFileSync(new URL('../index.html', import.meta.url), 'utf8');
check(indexSrc.includes('id="paper-card"') && indexSrc.includes('title="arXiv link to follow"'),
  'header paper card exposes the intentional pre-publication placeholder');
check(indexSrc.includes('Read the paper'), 'paper card heading');
check(indexSrc.includes('id="github-star"') &&
      indexSrc.includes('href="https://github.com/thomasahle/fast-polynomials"') &&
      indexSrc.includes('aria-label="Star fast-polynomials on GitHub"'),
      'header links to the public GitHub repository with an accessible label');
check(indexSrc.includes('id="github-star-count"') && indexSrc.includes('viewBox="0 0 16 16"') &&
      indexSrc.includes('js/github-stars.js'),
      'GitHub button contains a star icon and loads its live count');
check(githubStarsSrc.includes('https://api.github.com/repos/thomasahle/fast-polynomials') &&
      githubStarsSrc.includes('stargazers_count'),
      'star count comes from the public GitHub repository API');
const outputFn = uiSrc.slice(uiSrc.indexOf('function Output'), uiSrc.indexOf('function FooterBar'));
check(outputFn.length > 0 && !outputFn.includes('id="methods"') && !outputFn.includes('setMethod'),
      'output card (#out) no longer holds the method seg');
check(uiSrc.includes('id="methods"') && uiSrc.indexOf('id="methods"') < uiSrc.indexOf('function Output'),
      'method chips render in the input card');
for (const id of ['monic', 'degree', 'deg-minus', 'deg-plus', 'share', 'copy', 'footer-stats'])
  check(uiSrc.includes(`id="${id}"`), `#${id} present in ui.js`);
check(uiSrc.includes('navigator.clipboard') && uiSrc.includes("execCommand('copy')"),
      'clipboard write has an execCommand fallback');
check(uiSrc.includes('stateFromHash(s, location.hash)'), 'boot state seeded from the URL hash');
check(uiSrc.includes('hashFromState'), 'Share builds its hash in the pure layer');
check(uiSrc.includes("dispatch({ type: 'setExDegree', delta })"), 'degree stepper dispatches setExDegree');
check(uiSrc.includes("dispatch({ type: 'example', key })"), 'example chips dispatch by key');
check(uiSrc.includes("dispatch({ type: 'setExMonic' })"), 'monic selector dispatches setExMonic');

console.log(fails ? `UI SMOKE FAILED (${fails}/${checks})` : `UI SMOKE PASSES (${checks} checks)`);
process.exit(fails ? 1 : 0);
