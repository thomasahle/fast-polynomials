// ui-smoke.test.js — drives the worker's message handler (handleMessage) under
// node for one example per UI mode (char 0 / Mersenne / char 2) and checks
// that every field the page's views rely on is present and structured-clone
// safe: mathText, mathTextOriginal, cText, cTextFraction (char 0 only), graph +
// graphSvg + graphText, and the same fields on every comparison row.  Also
// unit-checks the C highlighter (token round-trip, HTML escaping) and, since
// ui.js needs a DOM, structurally checks the automatic-compilation wiring
// (no Compile button, debounced edits, cancel-while-busy, compile on load).
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { dirname, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { handleMessage, replyNumeric } from '../js/worker.js';
import { parsePoly } from '../js/polyparse.js';
import { resolveField } from '../js/field.js';
import { numericMethodsFor } from '../js/compare.js';
import { tokenizeC, highlightC } from '../js/highlight.js';
import { graphStats } from '../js/graph.js';
import { installDom, settle, ShimWorker } from './dom-shim.js';
import { initialState, initialStateFor, examplesFor, defaultExample, tokenizePoly } from '../js/uistate.js';
import { PAPER_URL, PAPER_TITLE, REFERENCES, referenceFor } from '../js/references.js';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };
const eq = (a, b, msg) => check(JSON.stringify(a) === JSON.stringify(b), `${msg}: ${JSON.stringify(a)} != ${JSON.stringify(b)}`);

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
  ['complex',  { lane: 'char0', fieldMode: 'C',
                 src: '(1+2i)x^7 - ix^5 + 3x^4 - (1/2-3/4i)x^2 + x + i' }],
  ['Mersenne', { lane: 'char0', fieldMode: 'p',
                 src: 'x^15 - 5x^14 - 17x^13 + 18x^12 - 12x^11 + 19x^10 - 12x^9 + 17x^8 + 17x^7 - 18x^6 + 3x^5 + 14x^4 + 8x^3 + 7x^2 + 11x + 9' }],
  ['char 2',   { lane: 'char2', fieldMode: null,
                 src: 'x^15 + 4x^14 + 0x14x^13 + 0xfx^12 + 3x^11 + 2x^10 + 4x^9 + 8x^8 + 9x^7 + 0x12x^6 + 0x15x^5 + 2x^4 + 0x13x^3 + 8x^2 + 0x18x + 0x16' }],
];

// cCode: the registry's flag — a field without a C emitter would ship cText null (every field has one now)
const checkRow = (tag, r, { isQ, ours, cCode = true }) => {
  for (const f of ['mathText', ...(cCode ? ['cText'] : []), 'graph', 'graphSvg', 'graphText', 'mults', 'adds', 'height'])
    check(r[f] !== undefined && r[f] !== null, `${tag}: field ${f} missing`);
  if (!cCode) check(r.cText === null && r.cTextFraction === null, `${tag}: no C for a field without an emitter`);
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
  if (cCode) check(r.cText.includes('eval_P'), `${tag}: cText has eval_P`);
};

for (const [label, msg] of MODES) {
  const t0 = Date.now();
  const result = await handleMessage(msg);
  const isQ = msg.lane === 'char0' && msg.fieldMode === 'Q';
  const { cCode } = resolveField(msg.lane, msg.fieldMode);
  console.log(`${label}: ${Date.now() - t0} ms, mults=${result.mults}, field=${result.fieldName}, ` +
              `comparisons=${result.comparisons.map(c => `${c.name}${c.ok ? '' : '✗'}`).join(', ')}`);
  check(!result.oursFailed, `${label}: our compiler failed: ${result.oursFailed}`);
  check(isPlain(result), `${label}: result is plain JSON (structured-clone safe)`);
  let cloned = null;
  try { cloned = structuredClone(result); } catch (e) { check(false, `${label}: structuredClone threw ${e.message}`); }
  check(cloned && cloned.mults === result.mults, `${label}: structuredClone round trip`);
  checkRow(label, result, { isQ, ours: true, cCode });
  check(typeof result.fieldName === 'string' && result.fieldName.length > 0, `${label}: fieldName`);
  const expectField = isQ ? 'ℚ' : msg.fieldMode === 'C' ? 'ℂ' : (msg.fieldMode === 'p' ? 'GF(2^89−1)' : 'GF(2^64)');
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
  if (msg.fieldMode === 'C') check(/\(1\+2i\) \* P̃/.test(result.mathText) && result.exact === false && result.status === '≈ numeric' && typeof result.maxRelError === 'number',
                                   `${label}: complex scale line, ≈ numeric, rounding error`);
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
    checkRow(`${label}/${c.name}`, c, { isQ: isQ && !['Knuth–Eve', 'Pan'].includes(c.name), ours: false, cCode });
  }
  // the numeric part answers one method at a time (`only`), as the browser worker does
  if (msg.fieldMode === 'C') {
    for (const only of numericMethodsFor('C')) {
      const nr = await handleMessage({ ...msg, part: 'numeric', only });
      check(nr.comparisons.length === 1 && nr.comparisons[0].name === only, `${label}: numeric part with only=${only} yields that row alone`);
    }
  }
}

// the browser worker's numeric loop (worker.js replyNumeric): one reply per method
// over ℂ — Knuth–Eve, Pan, Belaga — and a single failure reply for an unknown field
{
  const out = [];
  await replyNumeric({ id: 9, lane: 'char0', fieldMode: 'C', src: MODES[1][1].src, part: 'numeric' }, m => out.push(m));
  check(out.length === 3 && out.every(m => m.ok === true && m.id === 9 && m.part === 'numeric'), `replyNumeric over ℂ posts three ok replies (${out.length})`);
  eq(out.map(m => m.result.comparisons.map(c => c.name)), [['Knuth–Eve'], ['Pan'], ['Belaga']], 'replyNumeric over ℂ: one row per reply, in method order');
  const bad = [];
  await replyNumeric({ id: 10, lane: 'char0', fieldMode: 'nope', src: 'x + 1', part: 'numeric' }, m => bad.push(m));
  check(bad.length === 1 && bad[0].ok === false && bad[0].id === 10 && /unknown field/.test(bad[0].message), 'replyNumeric with an unknown field posts a single failure');
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
  check(r2.mults === 1 && /^y = x \* \(x \+ 0x3\)$/m.test(r2.mathText) && /^P = y \+ 1$/m.test(r2.mathText), 'char 2 degree 2: y = x * (x + 0x3), P = y + 1');
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

// ---- the page itself, rendered under a minimal DOM ------------------------
// ui.js is imported under test/dom-shim.js — a fresh module instance per
// layout (query string) — and driven through the rendered elements: what a
// browser test would click, without a browser.  The Worker stand-in records
// the compile messages; a real compiler result is delivered back through it.
const uiSrc = readFileSync(new URL('../js/ui.js', import.meta.url), 'utf8');
const stateSrc = readFileSync(new URL('../js/uistate.js', import.meta.url), 'utf8');
const githubStarsSrc = readFileSync(new URL('../js/github-stars.js', import.meta.url), 'utf8');
check(!/set(Timeout|Interval)\(/.test(stateSrc), 'uistate.js stays pure: no timers');
check(uiSrc.includes('cBundleArchive') && uiSrc.includes('URL.createObjectURL'),
      'Download builds and saves the C benchmark archive');
check(uiSrc.includes('navigator.clipboard') && uiSrc.includes("execCommand('copy')"),
      'clipboard write has an execCommand fallback');

const indexSrc = readFileSync(new URL('../index.html', import.meta.url), 'utf8');
// the paper's link has one source, references.js PAPER_URL: the phone intro and the
// "This paper" reference read it, and the static paper card in index.html carries the same URL
check(/^https:\/\/arxiv\.org\/abs\//.test(PAPER_URL) && referenceFor('ours').url === PAPER_URL &&
      indexSrc.includes(`href="${PAPER_URL}"`) && uiSrc.includes('href=${PAPER_URL}') && !uiSrc.includes('arxiv.org/abs/'),
  'the paper card, the phone Paper link and reference [1] share PAPER_URL from references.js');
// the tooltips too: PAPER_TITLE is derived from PAPER_URL (it names the submission / the arXiv id), so the
// announcement flip is that one constant — no literal id survives in ui.js, and index.html's static copy is checked equal
check(PAPER_TITLE.includes(PAPER_URL.split('/').pop()) && uiSrc.includes('title=${PAPER_TITLE}') && !/arXiv submission \d+/.test(uiSrc) &&
      indexSrc.includes(`title="${PAPER_TITLE}"`),
  'the Paper links\' tooltips come from PAPER_TITLE, derived from PAPER_URL');
check(Object.values(REFERENCES).every(r => typeof r.blurb === 'string' && r.blurb.length > 20 && !/verif/i.test(r.blurb)),
  'every method has a fixed one-line blurb (no verification wording)');
// ui.js no longer pulls the compilers onto the page thread: only the dependency-free method list
check(uiSrc.includes("from './methodlist.js'") && !uiSrc.includes("from './compare.js'"),
  'ui.js imports the method names from methodlist.js, not compare.js');
check(indexSrc.includes('<b>Fast Evaluation of Polynomials with Rational Preprocessing</b>'),
      'paper card heading');
check(indexSrc.includes('js/vendor/katex/katex.min.css') &&
      indexSrc.includes('js/vendor/katex/katex.min.js'),
      'the self-hosted KaTeX stylesheet and runtime are loaded');
check(!indexSrc.includes('All arithmetic is exact'),
      'field-specific implementation notes are not repeated in a global footer');
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
// page metadata: description / Open Graph / Twitter card (text only: no image exists
// in the tree), canonical, a theme-color per theme, a <main> landmark, and GA4
// reporting the page without the hash fragment (which carries the polynomial)
check(/<meta name="description"\s+content="[^"]{60,}"/.test(indexSrc) && /<meta property="og:title" content="Fast Polynomial Evaluation/.test(indexSrc) &&
      /<meta property="og:description"/.test(indexSrc) && /<meta property="og:url" content="https:\/\/thomasahle\.com\/fast-polynomials\/"/.test(indexSrc) &&
      /<link rel="canonical" href="https:\/\/thomasahle\.com\/fast-polynomials\/"/.test(indexSrc) &&
      /<meta name="twitter:card" content="summary"/.test(indexSrc) && !/og:image/.test(indexSrc),
      'index.html carries description, Open Graph and Twitter card metas (no fabricated image)');
check(/<meta name="theme-color" media="\(prefers-color-scheme: light\)" content="#f7f6f2"/.test(indexSrc) &&
      /<meta name="theme-color" media="\(prefers-color-scheme: dark\)" content="#191817"/.test(indexSrc),
      'theme-color metas match style.css --bg for both themes');
check(indexSrc.includes('<main id="app"></main>') && !indexSrc.includes('<div id="app">'), 'the app renders into a <main> landmark');
check(/gtag\('config', 'G-40XB6Q54CE', \{ page_location: location\.origin \+ location\.pathname \}\)/.test(indexSrc),
      'GA4 page_location omits the hash fragment');
check(indexSrc.includes('Simply type a polynomial below') && !indexSrc.includes('Simple type') &&
      indexSrc.includes('&lfloor;<i>n</i>/2&rfloor;+1</span> multiplications suffice for any monic') &&
      indexSrc.includes('one more for a general one') && indexSrc.includes('<i>n</i>−1</span> if it is monic'),
      'the desktop intro counts agree with the table (n / n−1 monic for Horner, ⌊n/2⌋+1 monic / one more general)');
check(indexSrc.includes('data-paper-link href="') &&
      /import \{ PAPER_URL, PAPER_TITLE \} from '\.\/js\/references\.js';\s*for \(const a of document\.querySelectorAll\('\[data-paper-link\]'\)\) \{ a\.href = PAPER_URL; a\.title = PAPER_TITLE; \}/.test(indexSrc),
      'the paper card takes its href and title from references.js at load (the static copies are the fallback)');
// modulepreload hints: exactly the worker's module closure minus what the page itself imports
{
  const site = resolve(fileURLToPath(new URL('..', import.meta.url)));
  const closure = entry => {
    const seen = new Set(), stack = [resolve(site, entry)];
    while (stack.length) {
      const f = stack.pop();
      if (seen.has(f)) continue;
      seen.add(f);
      const src = readFileSync(f, 'utf8');
      const re = /(?:import|export)\s*(?:[^'"]*?\s*from\s*)?['"](\.[^'"]+)['"]|import\(\s*['"](\.[^'"]+)['"]\s*\)/g;
      let m;
      while ((m = re.exec(src))) stack.push(resolve(dirname(f), m[1] ?? m[2]));
    }
    return [...seen].map(f => relative(site, f));
  };
  const pageScripts = [...indexSrc.matchAll(/<script type="module" src="([^"]+)"/g)].map(m => m[1]);
  const page = new Set(pageScripts.flatMap(closure));
  const workerOnly = closure('js/worker.js').filter(f => !page.has(f)).sort();
  const preloads = [...indexSrc.matchAll(/<link rel="modulepreload" href="([^"]+)">/g)].map(m => m[1]).sort();
  eq(preloads, workerOnly, 'index.html modulepreloads exactly the worker-only module closure');
  check(pageScripts.includes('js/ui.js') && workerOnly.includes('js/worker.js') && workerOnly.includes('js/char0/core.js') &&
        !workerOnly.includes('js/methodlist.js') && !page.has('js/compare.js'),
        'the page thread loads methodlist.js but no compiler; the workers load compare.js and core.js');
}
// the vendored Preact + htm bundle: its provenance header names the version, and the
// bundle below the header still hashes to the recorded sha256 (an upgrade must update both)
{
  const vendored = readFileSync(new URL('../js/vendor/preact-htm.module.js', import.meta.url), 'utf8');
  const header = /^(?:\/\/[^\n]*\n)+/.exec(vendored)?.[0] ?? '';
  const recorded = /sha256[^\n]*\n\/\/ ([0-9a-f]{64})/.exec(header)?.[1];
  const actual = createHash('sha256').update(vendored.slice(header.length)).digest('hex');
  check(header.includes('htm@3.1.1') && header.includes('preact/standalone.module.js') && recorded === actual,
        `vendored bundle provenance: htm@3.1.1 recorded, body sha256 ${actual.slice(0, 12)}… matches the header`);
}
// the input highlighter's number grammar (uistate.tokenizePoly) agrees with the parser
// on every literal below: one 'num' token iff parsePoly accepts `<lit>*x`
{
  const literals = ['3', '1/2', '0.25', '.5', '1.5e-3', '2e3', '1e-3', '3.', '3.e2', '0x1f',
    'i', '2i', '1/2i', '0.5i', '(1+2i)', '(1/2-3/4i)', '(2-i)', '(-i)', '(1/2)i', '(-1/2)*i', '(0+1i)'];
  for (const lit of literals) {
    const toks = tokenizePoly(lit);
    const oneNum = toks.length === 1 && toks[0].type === 'num';
    let parses = true;
    try { parsePoly(`${lit}*x`, { complex: /i/.test(lit) }); } catch { parses = false; }
    check(oneNum && parses, `highlighter and parser both accept the literal ${lit}`);
  }
  for (const bad of ['1.5.2', 'x', '0x', '1//2', '0X1F']) {
    const toks = tokenizePoly(bad);
    check(!(toks.length === 1 && toks[0].type === 'num'), `highlighter does not paint ${bad} as one number`);
  }
}

const typeInto = async (ta, text) => { ta.value = text; ta.dispatch('input'); };
// the messages of the most recent job (highest id), its main part first
const allMessages = () => ShimWorker.instances.flatMap(w => w.messages);
const latestJob = () => { const id = Math.max(0, ...allMessages().map(m => m.id)); return allMessages().filter(m => m.id === id); };
const lastMessage = () => latestJob().find(m => m.part === 'main') ?? null;
const messageCount = () => allMessages().filter(m => m.part === 'main').length;   // jobs posted
/** Answer the latest compile message of one worker part (main by default —
 *  over ℚ / ℝ / ℂ the numeric methods come from a second worker) with the real
 *  compiler's result; the numeric part is answered as the browser worker does,
 *  one reply per method; `replyToLatest` answers every part. */
const replyPart = async part => {
  const w = ShimWorker.instances.find(x => x.messages.at(-1)?.part === part && !x.terminated);
  if (!w) return null;
  const m = w.messages.at(-1);
  if (part === 'numeric') {
    const results = [];
    await replyNumeric(m, reply => { results.push(reply.result); w.onmessage({ data: reply }); });
    await settle();
    return results;
  }
  const result = await handleMessage(m);
  w.onmessage({ data: { id: m.id, part, ok: true, result } });
  await settle();
  return result;
};
/** One method's numeric reply (the browser worker's per-method message). */
const replyNumericOnly = async only => {
  const w = ShimWorker.instances.find(x => x.messages.at(-1)?.part === 'numeric' && !x.terminated);
  const m = w.messages.at(-1);
  const result = await handleMessage({ ...m, only });
  w.onmessage({ data: { id: m.id, part: 'numeric', ok: true, result } });
  await settle();
  return { w, result };
};
const replyToLatest = async () => { const r = await replyPart('main'); await replyPart('numeric'); return r; };

// desktop ------------------------------------------------------------------
{
  const { app, history: shimHistory } = installDom({ compact: false });
  await import('../js/ui.js?layout=desktop');
  await settle();
  const $ = s => app.querySelector(s), $$ = s => app.querySelectorAll(s);
  check($('#poly-in').value === initialState.src && $('#mode button.on')?.dataset.mode === 'Q',
        'desktop boots on the initial example (He_7 over ℚ) with its field pill on');
  eq($$('#examples button.chip').map(c => c.dataset.ex), ['exp', 'ln', 'sqrt', 'hermite'], 'desktop shows every chip');
  check($$('#examples .chip').every(c => c.localName === 'button' && c.getAttribute('type') === 'button') &&
        $('#examples').getAttribute('role') === 'group', 'example chips are real buttons (keyboard reachable) in a labelled group');
  // ARIA state on the pill rows and the stepper (screen readers hear which is on)
  check($('#mode').getAttribute('role') === 'group' && $('#mode').getAttribute('aria-label') === 'Field' &&
        $('#mode button[data-mode="Q"]').getAttribute('aria-pressed') === 'true' &&
        $('#mode button[data-mode="R"]').getAttribute('aria-pressed') === 'false' &&
        $('#mode button[data-mode="gf64"]').getAttribute('aria-label') === 'GF(2^64)' &&
        $('#mode button[data-mode="p61"]').getAttribute('aria-label') === 'GF(2^61−1)',
        'field pills carry aria-pressed and spelled-out accessible names');
  check($('#deg-minus').getAttribute('aria-label') === 'decrease degree' && $('#deg-plus').getAttribute('aria-label') === 'increase degree' &&
        /extra scalar multiplication/.test($('#monic').getAttribute('title')),
        'the degree stepper is named and the monic toggle explains the non-monic cost');
  check($('#error') && $('#error').getAttribute('aria-live') === 'polite' && $('#error').textContent === '' &&
        $('#poly-in').getAttribute('aria-invalid') === null,
        'the error line is an always-mounted polite live region, empty while the input is fine');
  check($('#main h2.sr-only')?.textContent === 'Your polynomial', 'the input card has a (visually hidden) heading');
  check($('#monic') && $('#degree') && $('.head-row #share') && !$('#pickers') && !$('.intro-compact'),
        'desktop has the monic toggle, degree stepper and Share in the head row; no dropdowns or phone intro');
  check(ShimWorker.instances.length === 2 && messageCount() === 1 && allMessages().length === 2 &&
        ShimWorker.instances.map(w => w.messages[0].part).join(',') === 'main,numeric' &&
        JSON.stringify(ShimWorker.instances[0].messages[0]) === JSON.stringify({ id: 1, src: initialState.src, lane: 'char0', fieldMode: 'Q', part: 'main' }),
        'the first load over ℚ compiles the initial example through a main and a numeric worker');
  check($('#busy') && $('#busy #cancel') && !$('#out'), 'while the first job runs with nothing to show, a busy row offers Cancel');
  check($('#job-status').getAttribute('role') === 'status' && $('#job-status').getAttribute('aria-live') === 'polite' && $('#job-status #busy') &&
        $('#busy').getAttribute('role') === null && $('#busy .spinner').getAttribute('aria-hidden') === 'true' && $('#busy').textContent.includes('compiling'),
        'the busy row sits in the always-mounted job-status region (only its text changes); its spinner is decorative');
  const firstWorkers = ShimWorker.instances.slice();
  // a click the reducer ignores (the field pill that is already on) must not touch the workers
  $('#mode button[data-mode="Q"]').click(); await settle();
  check(firstWorkers.every(w => !w.terminated) && ShimWorker.instances.length === 2 && messageCount() === 1 && $('#busy'),
        'a no-op click while a job runs leaves its workers running (no stuck stale page)');
  $('button.chip[data-ex="ln"]').click(); await settle();
  check(firstWorkers.every(w => w.terminated) && ShimWorker.instances.length === 4, 'a new job while one runs terminates its workers and starts fresh ones');
  check($('#poly-in').value === examplesFor('Q', 7, 0, true).find(e => e.key === 'ln').src &&
        lastMessage()?.src === $('#poly-in').value, 'a chip fills the input and compiles it');
  const before = messageCount();
  $('#deg-plus').click(); await settle();
  check($('.deg-n').textContent === 'degree 8' && messageCount() === before + 1 &&
        lastMessage().src === examplesFor('Q', 8, 0, true).find(e => e.key === 'ln').src,
        'the degree stepper regenerates the held chip and compiles');
  // the stepper's ends: at degree 3 the − button is aria-disabled (dimmed, still focusable so its tooltip says why) and inert
  check($('#deg-minus').getAttribute('aria-disabled') === 'false' && $('#deg-plus').getAttribute('aria-disabled') === 'false', 'mid-range both stepper buttons are live');
  for (let i = 0; i < 5; i++) { $('#deg-minus').click(); await settle(); }
  const atMin = messageCount();
  check($('.deg-n').textContent === 'degree 3' && $('#deg-minus').getAttribute('aria-disabled') === 'true' && $('#deg-plus').getAttribute('aria-disabled') === 'false' &&
        /smallest/.test($('#deg-minus').getAttribute('title')), 'at the smallest degree the − button is aria-disabled and says so');
  $('#deg-minus').click(); await settle();
  check(messageCount() === atMin && $('.deg-n').textContent === 'degree 3', 'clicking it posts nothing');
  for (let i = 0; i < 5; i++) { $('#deg-plus').click(); await settle(); }
  check($('.deg-n').textContent === 'degree 8' && $('#deg-minus').getAttribute('aria-disabled') === 'false', 'stepping back up re-enables it');
  $('#monic').click(); await settle();
  check(!$('#monic').classList.contains('on') && $('#monic').getAttribute('aria-pressed') === 'false' &&
        $('#poly-in').value === examplesFor('Q', 8, 0, false).find(e => e.key === 'ln').src,
        'the monic toggle regenerates the held chip with monic off');
  $('#monic').click(); await settle();

  const n0 = messageCount();
  await typeInto($('#poly-in'), 'x^3 + x + 1'); await settle(200);
  check(messageCount() === n0 && !$('#degree').querySelector('.deg-n').textContent.includes('NaN'), 'typing does not compile before the debounce');
  await settle(450);
  check(messageCount() === n0 + 1 && lastMessage().src === 'x^3 + x + 1', 'an edit compiles after the debounce');
  await typeInto($('#poly-in'), 'x^4 + 1');
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();
  check(lastMessage().src === 'x^4 + 1', 'Cmd/Ctrl+Enter compiles at once');
  // Cancel retires the job: its workers are terminated (in the job effect), nothing new is posted
  const cancelled = ShimWorker.instances.filter(w => !w.terminated), nCancel = messageCount();
  $('#cancel').click(); await settle();
  check(cancelled.length === 2 && cancelled.every(w => w.terminated) && !$('#busy') && !$('#cancel') && messageCount() === nCancel,
        'Cancel terminates the running workers and posts no job');
  check(!$('#out') && $('#job-status').textContent.includes('compilation cancelled') && /Ctrl\+Enter or edit/.test($('#job-status').textContent) &&
        $('#error').textContent === '' && $('#poly-in').getAttribute('aria-invalid') === null,
        'with nothing mounted the status line explains the empty page after Cancel — not as an error');
  // an edit that is reverted within the debounce still recompiles: the cancelled text is not the mounted output's
  await typeInto($('#poly-in'), 'x^4 + 1 '); await typeInto($('#poly-in'), 'x^4 + 1'); await settle(650);
  check(messageCount() === nCancel + 1 && lastMessage().src === 'x^4 + 1' && $('#busy') && !$('#job-status').textContent.includes('cancelled'),
        'after Cancel an edit-and-revert compiles the same text again (a fresh job) and drops the note');
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();
  check(messageCount() === nCancel + 2 && lastMessage().src === 'x^4 + 1' && $('#busy'), 'Cmd/Ctrl+Enter compiles again after Cancel too');

  // over ℚ the numeric methods arrive from their own worker: spinners meanwhile
  await replyPart('main');
  check($('#out') && $$('#methods button.pending').length === 2 && $$('#methods button.pending .spinner').length === 2 &&
        $$('#compare td.pending').length === 2, 'after the main reply the two numeric methods show spinners on their chips and rows');
  $('#methods button[data-m="Pan"]').click(); await settle();
  check($('#methods button.on')?.dataset.m === 'Pan' && $('#chain.pending-pane') && !$('#copy'), 'a pending method can be selected: the pane spins, nothing to copy');
  // one method's reply fills only its row; the numeric worker is still computing the
  // rest, so a superseding job must terminate it (the idle main worker is kept)
  const { w: numW, result: keOnly } = await replyNumericOnly('Knuth–Eve');
  check(keOnly.comparisons.length === 1 && keOnly.comparisons[0].name === 'Knuth–Eve' &&
        $$('#methods button.pending').length === 1 && $$('#compare td.pending').length === 1 && $('#chain.pending-pane'),
        'a per-method reply fills only its row');
  const mainW = ShimWorker.instances.find(x => x.messages.at(-1)?.part === 'main' && !x.terminated);
  const jobBefore = lastMessage().id;
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();
  check(numW.terminated && !mainW.terminated && lastMessage().id === jobBefore + 1 && mainW.messages.at(-1).id === jobBefore + 1,
        'a new job terminates a numeric worker that has replied for some methods but is still computing the rest; the idle main worker takes the new job');
  const freshNum = ShimWorker.instances.filter(x => !x.terminated && x.messages.some(m => m.part === 'numeric'));
  check(freshNum.length === 1 && freshNum[0] !== numW && freshNum[0].messages.length === 1 && freshNum[0].messages[0].id === jobBefore + 1,
        'the new job posts its numeric part to a fresh worker, not to the abandoned one');
  await replyPart('main');
  check($$('#methods button.pending').length === 2 && $$('#compare td.pending').length === 2, 'the new job starts with both numeric rows pending again');
  const numReplies = await replyPart('numeric');
  check(numReplies.length === 2 && !$('#methods button.pending') && !$('#compare td.pending') && !$('.pending-pane'), 'the per-method numeric replies remove every spinner');
  const doneNum = ShimWorker.instances.find(x => !x.terminated && x.messages.some(m => m.part === 'numeric'));
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();
  check(doneNum && !doneNum.terminated && doneNum.messages.length === 2, 'a numeric worker whose every reply arrived is idle: a new job reuses it');
  await replyPart('main'); await replyPart('numeric');
  check(!$('#methods button.pending') && !$('#compare td.pending') && !$('.pending-pane'), 'the reused worker\'s replies land');
  check(!$('#out').classList.contains('stale') && !$('#cancel') && $('#job-status').textContent === '' && $('#job-status').getAttribute('role') === 'status',
        'an idle page with every row filled is neither stale nor cancellable; the job-status region stays mounted, empty');
  // stale-while-revalidate for a numeric method: its last chain stays mounted and dims
  // while the new job's numeric worker computes, instead of collapsing to a spinner
  $('#methods button[data-m="Knuth–Eve"]').click(); await settle();
  const keChain = $('#chain')?.textContent;
  check($('#methods button.on')?.dataset.m === 'Knuth–Eve' && keChain && !$('.pending-pane'), 'Knuth–Eve is selected with its chain shown');
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();
  check($('#out').classList.contains('stale') && $('.pane-actions #cancel') && $('#chain')?.textContent === keChain,
        'a running job dims the mounted output and offers Cancel in the pane corner');
  await replyPart('main');
  check($$('#compare td.pending').length === 2 && $('#out').classList.contains('stale') && !$('.pending-pane') &&
        $('#chain')?.textContent === keChain && !$('#cancel'),
        'after the main reply the selected numeric method keeps its previous chain, dimmed, while its row is pending');
  check(!$('#download'), 'Download is withheld while the pane shows the previous chain (the archive would hold another polynomial\'s selected.c)');
  await replyPart('numeric');
  check(!$('#out').classList.contains('stale') && !$('#compare td.pending') && $('#chain')?.textContent === keChain && $('#download'),
        'the numeric reply fills the row and the output is current again (Download back)');
  // Cancel after a superseding job: the kept result's pending rows settle (their worker is gone), and
  // every view of the result — pane, chips, table — dims under a status note until the next job
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();
  await replyPart('main');
  check($$('#compare td.pending').length === 2 && $('#methods.stale') && $('#footer-stats.stale') && $('#out.stale'),
        'a pending phase dims the chips and the table along with the pane');
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();   // job B: the numeric worker of job A is terminated
  $('#cancel').click(); await settle();
  check(!$('#methods button.pending') && !$('#compare td.pending') && !$('.pending-pane') && !$('#cancel') && !$('#busy'),
        'after Cancel no spinner is left: the orphaned numeric rows are settled');
  check($('#out').classList.contains('stale') && $('#methods').classList.contains('stale') && $('#footer-stats').classList.contains('stale') &&
        $('#job-status').textContent.includes('compilation cancelled') && $('#error').textContent === '',
        'the kept output reads as stale everywhere and the status line says the compilation was cancelled');
  check($('#methods button.on')?.dataset.m === 'ours' && $('#compare tr[data-m="Knuth–Eve"]')?.classList.contains('off') &&
        /cancelled/.test($('#compare tr[data-m="Knuth–Eve"] .why')?.textContent ?? ''),
        'the selected numeric method, now not computed, is deselected in favour of ours; its row says why');
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();
  await replyPart('main'); await replyPart('numeric');
  $('#methods button[data-m="Knuth–Eve"]').click(); await settle();
  check(!$('#out').classList.contains('stale') && !$('#methods').classList.contains('stale') && $('#job-status').textContent === '' &&
        $('#methods button.on')?.dataset.m === 'Knuth–Eve' && $('#chain')?.textContent === keChain,
        'the next compile clears the note and the dimming; Knuth–Eve is back');
  check($('#compare tr[data-m="Knuth–Eve"] td .rel-err') && /e-\d+$/.test($('#compare tr[data-m="Knuth–Eve"] td .rel-err').textContent) &&
        !$('#compare tr[data-m="Knuth–Eve"] td.warn') && !$('#compare tr[data-m="Horner"] .rel-err'),
        'a ≈ numeric row shows its measured rounding error in the exact column (not flagged when tiny); exact rows show none');
  check($('#cmp-caption')?.textContent.includes('scalar') && $('#cmp-caption').textContent.includes('depth') &&
        $$('#cmp-notes li').some(li => li.textContent.startsWith('Knuth–Eve') && li.textContent.includes('coefficient adaptation')) &&
        !$('#cmp-notes').textContent.includes('verified'),
        'the caption explains the columns and the rows\' notes are listed under the table, without verification wording');
  check($('#compare tr[data-m="Horner"] td.m').getAttribute('title')?.includes('n multiplications') &&
        $('#methods button[data-m="Horner"]').getAttribute('title') === referenceFor('Horner').blurb,
        'method cells and chips carry the one-line blurb as their tooltip');
  $('#methods button[data-m="ours"]').click(); await settle();

  $('#mode button[data-mode="gf64"]').click(); await settle();
  check($('#mode button.on')?.dataset.mode === 'gf64' && lastMessage().lane === 'char2' && lastMessage().fieldMode === 'gf64' &&
        $('#poly-in').value === 'x^4 + 1', 'a field pill switches the field and recompiles typed text as typed');
  eq(latestJob().map(m => m.part), ['main'], 'a GF(2^k) job posts no numeric part');

  // a real result through the worker: the output, its tabs and the table appear
  await replyToLatest();
  check($('#out') && $$('#view button').length === 3 && $('#view button.on')?.dataset.view === 'math' && $('#chain'),
        'a compile reply mounts the output with the math view');
  check($$('#methods button').length >= 4 && $('#methods button.on')?.dataset.m === 'ours' && $$('#compare tbody tr').length >= 4,
        'method chips and the comparison table follow the result');
  check($$('#compare a.ref').length >= 4 && $('#compare tr[data-m="Horner"] a.ref')?.getAttribute('href')?.includes('doi.org') &&
        $$('#references li').length === $$('#compare a.ref').length && $('#references li').textContent.includes('Ahle'),
        'method names link to their references and the list under the table numbers them');
  check($('#copy') && $('#download') && !$('.pane-actions #share'), 'desktop pane: Copy and Download, Share stays in the head row');
  $('#methods button[data-m="Horner"]').click(); await settle();
  check($('#methods button.on')?.dataset.m === 'Horner' && $('#compare tr.on')?.dataset.m === 'Horner', 'a method chip selects the method and its row');
  check($('#methods').getAttribute('role') === 'group' && $('#methods button[data-m="Horner"]').getAttribute('aria-pressed') === 'true' &&
        $('#methods button[data-m="ours"]').getAttribute('aria-pressed') === 'false', 'method chips carry aria-pressed');
  $('#compare tr[data-m="Estrin"]').click(); await settle();
  check($('#methods button.on')?.dataset.m === 'Estrin', 'a table row selects its method');
  // rows are keyboard-selectable: focusable, Enter / Space select, aria-selected follows
  check($('#compare tr[data-m="Horner"]').getAttribute('tabindex') === '0' && $('#compare tr[data-m="Estrin"]').getAttribute('aria-selected') === 'true' &&
        $('#compare tr[data-m="Horner"]').getAttribute('aria-selected') === 'false' && $('#compare tr[data-m="Pan"]')?.getAttribute('tabindex') === null,
        'enabled comparison rows are focusable with aria-selected; rejected rows are not');
  $('#compare tr[data-m="Horner"]').dispatch('keydown', { key: 'Enter' }); await settle();
  check($('#methods button.on')?.dataset.m === 'Horner', 'Enter on a focused row selects its method');
  $('#compare tr[data-m="Estrin"]').dispatch('keydown', { key: ' ' }); await settle();
  check($('#methods button.on')?.dataset.m === 'Estrin', 'Space on a focused row selects its method');
  check($('#compare caption.sr-only')?.textContent.includes('Comparison') && $('#references').getAttribute('aria-label') === 'references' &&
        $$('#compare th .abbr').every(a => a.getAttribute('aria-hidden') === 'true'),
        'the table has a caption, the references a label, and the phone header abbreviations are hidden from AT');
  check($('#view').getAttribute('role') === 'tablist' && $$('#view button').every(b => b.getAttribute('role') === 'tab') &&
        $('#view button[data-view="math"]').getAttribute('aria-selected') === 'true' && $('#view button[data-view="c"]').getAttribute('aria-selected') === 'false',
        'the view tabs are a tablist with aria-selected on the current view');
  // the complete tab pattern: ids + aria-controls to the pane (a tabpanel labelled by the selected tab), a roving tabindex
  check($$('#view button').every(b => b.getAttribute('aria-controls') === 'pane' && b.getAttribute('id') === `tab-${b.dataset.view}`) &&
        $('#view button[data-view="math"]').getAttribute('tabindex') === '0' && $('#view button[data-view="c"]').getAttribute('tabindex') === '-1' &&
        $('#pane').getAttribute('role') === 'tabpanel' && $('#pane').getAttribute('aria-labelledby') === 'tab-math' && $('#pane').getAttribute('tabindex') === '0' &&
        $('#pane #chain'), 'each tab controls the pane (tabpanel); only the selected tab is in the Tab order');
  $('#view').dispatch('keydown', { key: 'ArrowRight' }); await settle();
  check($('#view button.on')?.dataset.view === 'c' && $('#view button[data-view="c"]').getAttribute('tabindex') === '0' &&
        $('#view button[data-view="math"]').getAttribute('tabindex') === '-1' && $('#pane').getAttribute('aria-labelledby') === 'tab-c',
        'ArrowRight moves the selection (and the tab stop) to the next view');
  $('#view').dispatch('keydown', { key: 'End' }); await settle();
  check($('#view button.on')?.dataset.view === 'graph', 'End selects the last view');
  $('#view').dispatch('keydown', { key: 'ArrowRight' }); await settle();
  check($('#view button.on')?.dataset.view === 'math', 'ArrowRight wraps around');
  $('#view').dispatch('keydown', { key: 'ArrowLeft' }); await settle();
  check($('#view button.on')?.dataset.view === 'graph', 'ArrowLeft wraps the other way');
  $('#view').dispatch('keydown', { key: 'Home' }); await settle();
  check($('#view button.on')?.dataset.view === 'math', 'Home selects the first view');
  $('#view').dispatch('keydown', { key: 'Tab' }); await settle();
  check($('#view button.on')?.dataset.view === 'math', 'other keys leave the selection alone');
  $('#view button[data-view="c"]').click(); await settle();
  check($('#view button.on')?.dataset.view === 'c' && $('#chain').innerHTML.includes('Code generated from'), 'the C tab shows the generated source with its header');
  check($('#view button[data-view="c"]').getAttribute('aria-selected') === 'true' && $('#view button[data-view="math"]').getAttribute('aria-selected') === 'false',
        'aria-selected follows the view');
  $('#view button[data-view="graph"]').click(); await settle();
  check($('#graph') && $('#graph-legend') && $('.graph-pane-wrap #graph') && !$('#graph-scroll-cue'),
        'the graph tab shows the SVG pane and legend (no scroll cue without a layout to measure)');
  $('#view button[data-view="math"]').click(); await settle();
  check($$('#view-sub .strip').every(st => st.getAttribute('role') === 'group' && st.getAttribute('aria-label')) &&
        $$('#view-sub button').every(b => b.getAttribute('type') === 'button' && /^(true|false)$/.test(b.getAttribute('aria-pressed'))) &&
        $('#view-sub button[data-opt="factor"]').getAttribute('aria-pressed') === 'true',
        'sub-option strips are labelled groups of buttons with aria-pressed');
  $('#view-sub button[data-opt="original"]').click(); await settle();
  check($('#view-sub button[data-opt="original"]').classList.contains('on') && $('#view-sub button[data-opt="original"]').getAttribute('aria-pressed') === 'true' &&
        $('#view-sub button[data-opt="factor"]').getAttribute('aria-pressed') === 'false', 'a sub-option toggles (class and aria-pressed)');
  $('#share').click(); await settle();
  check(location.hash.startsWith('#src=') && location.hash.includes('mode=gf64') && $('#share').textContent.includes('copied') &&
        shimHistory.entries === 0,
        'Share writes the state hash to the URL in place (replaceState, no history entry) and flashes "copied"');

  // ℂ: the pill regenerates a held example in the new field and its chips take over
  $('button.chip[data-ex="sparse"]').click(); await settle();
  check($('#poly-in').value === examplesFor('gf64', 8, 0, true).find(e => e.key === 'sparse').src, 'a GF(2^64) chip is held before switching');
  $('#mode button[data-mode="C"]').click(); await settle();
  check($('#mode button.on')?.dataset.mode === 'C' && lastMessage().fieldMode === 'C' && lastMessage().lane === 'char0' &&
        $('#poly-in').value === defaultExample('C', 8, 0, true).src && $('#poly-in').value.includes('(0+1i)x'),
        'the ℂ pill regenerates the held example (e^{ix} with Gaussian coefficients) and compiles it');
  eq($$('#examples button.chip').map(c => c.dataset.ex), ['expi', 'binomi', 'exp1i', 'gauss'], 'ℂ shows its own chips');
  check($$('.poly-hl .in-num').some(t => t.textContent === '(0+1i)'), 'the input backdrop paints the Gaussian literal as a number');
  await replyPart('main');
  check($$('#methods button.pending').length === 3 && $$('#compare td.pending').length === 3 && $('#compare tr[data-m="Belaga"] td.pending'),
        'over ℂ the main reply leaves Knuth–Eve, Pan and Belaga pending');
  let left = 3;
  for (const only of numericMethodsFor('C')) {
    const { result } = await replyNumericOnly(only);
    left--;
    check(result.comparisons.length === 1 && result.comparisons[0].name === only &&
          $$('#methods button.pending').length === left && $$('#compare td.pending').length === left, `${only} reply clears its spinner (${left} left)`);
  }
  check($('#compare tr[data-m="Belaga"]') && !$('#compare tr[data-m="Belaga"] td.pending'), 'the Belaga row is filled in');
  check($('#out') && $('#compare tr[data-m="ours"]') && $$('#compare tbody tr').length >= 4, 'a ℂ compile reply mounts the output and the table');
  check($('#compare tr[data-m="ours"]').textContent.includes('≈ numeric') && $('#compare tr[data-m="Horner"]').textContent.includes('yes'),
        'over ℂ the table reports ours as ≈ numeric and Horner as exact');
  check($('#compare tr[data-m="ours"] .rel-err') && $('#compare tr[data-m="ours"] td[title*="Gaussian-rational"]'),
        'over ℂ the paper\'s row shows its rounding error with the complex-double note');

  // a failed compile keeps the last output mounted (dimmed under the error) and
  // retires the job, terminating the numeric worker still computing it
  await typeInto($('#poly-in'), 'x^^2 +');
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();
  const failW = ShimWorker.instances.find(x => x.messages.at(-1)?.part === 'main' && !x.terminated);
  const failNum = ShimWorker.instances.find(x => x.messages.at(-1)?.part === 'numeric' && !x.terminated);
  failW.onmessage({ data: { id: failW.messages.at(-1).id, part: 'main', ok: false, message: 'cannot read the polynomial over ℂ: the polynomial ends with a sign' } });
  await settle();
  check($('#error')?.textContent.includes('ends with a sign') && $('#out') && $('#out').classList.contains('stale') &&
        $('#methods').classList.contains('stale') && $('#footer-stats').classList.contains('stale') &&
        $$('#compare tbody tr').length >= 4 && !$('#busy') && !$('#cancel'),
        'a parse error keeps the output, chips and table mounted, all dimmed under the error');
  check(!$('#methods button.pending') && !$('#compare td.pending') && !$('.pending-pane'),
        'the pending numeric rows of the kept result are settled (their worker was terminated): no frozen spinners under the error');
  check(failNum.terminated && !failW.terminated, 'the failed job\'s numeric worker is terminated; the idle main worker stays');
  const nFail = messageCount();
  await settle(650);
  check(messageCount() === nFail && !$('#busy') && !$('#cancel'), 'the debounce still pending from the typing does not re-run the compile that just failed');
  check($('#poly-in').getAttribute('aria-invalid') === 'true' && $('#poly-in').getAttribute('aria-describedby') === 'error',
        'the textarea is marked invalid and described by the error line while an error stands');
}

// phones --------------------------------------------------------------------
{
  const { app, fire } = installDom({ compact: true });
  await import('../js/ui.js?layout=compact');
  await settle();
  const $ = s => app.querySelector(s), $$ = s => app.querySelectorAll(s);
  const boot = initialStateFor({ compact: true });
  check($('#poly-in').value === boot.src && $('#mode-select')?.value === 'Q', 'phones boot on the ℚ e^x example with the field dropdown');
  const optC = $$('#mode-select option').find(o => o.value === 'C');
  check(optC && !optC.disabled && optC.textContent.trim() === 'ℂ  complex' &&
        $$('#mode-select option').map(o => o.value).slice(0, 3).join(',') === 'Q,R,C',
        'the phone field dropdown lists ℂ after ℚ and ℝ, enabled, as "ℂ  complex"');
  check($$('#examples button.chip').length === 3 && !$('#degree') && !$('#monic') && !$('#share') && !$('#mode') && $('.intro-compact'),
        'phones: three chips, no stepper / monic / Share yet, dropdowns instead of pills, the intro');
  const intro = $('.intro-compact .sub').textContent.replace(/\s+/g, ' ');
  check(intro.includes('once and ⌊n/2⌋+1 suffice for any monic polynomial') && intro.includes('(n−1 if it is monic)') &&
        intro.includes('one more for a general one'), 'the phone intro states the same counts as the desktop intro');
  eq($$('.quick-links a').map(a => a.textContent.trim().replace(/\s+/g, ' ')), ['Paper', 'GitHub'], 'phone intro links');
  const toggle = $('.quick-links .theme-toggle');
  check(toggle && /switch to the dark theme/.test(toggle.getAttribute('aria-label') ?? ''), 'the phone intro has the day / night toggle, offering dark while light');
  toggle.click(); await settle();
  check(document.documentElement.dataset.theme === 'dark' && /light theme/.test(toggle.getAttribute('aria-label')), 'the toggle switches to dark and offers light');
  toggle.click(); await settle();
  check(document.documentElement.dataset.theme === 'light', 'and back to an explicit light');
  check(indexSrc.includes('data-theme-toggle') && indexSrc.includes('js/theme.js') && indexSrc.includes("localStorage.getItem('theme')"),
        'the desktop header has the static toggle, loads theme.js, and applies a remembered theme before first paint');
  check(lastMessage()?.src === boot.src && lastMessage().lane === 'char0', 'phones compile the boot example');
  const sel = $('#mode-select'); sel.value = 'gf64'; sel.dispatch('change'); await settle();
  check($('#poly-in').value === defaultExample('gf64', 5, 0, true).src && lastMessage().fieldMode === 'gf64',
        'the field dropdown regenerates the held example in the new field and compiles');
  sel.value = 'Q'; sel.dispatch('change'); await settle();
  await replyToLatest();
  check($('.out-card #out') && $('.pane-actions #share') && $('.pane-actions #copy') && !$('#download'),
        'phone output card: Share floats beside Copy, no Download');
  check(/^3 multiplications(?: \(\d scalar\))? · \d+ additions · mult\. depth \d+$/.test($('#stats-line').textContent) &&
        $('#cmp-card') && !$('#cmp-card').open && $$('#compare tbody tr').length >= 4,
        `phone stats line in words and the collapsed comparison card (${$('#stats-line').textContent})`);
  eq($$('#method-select option').map(o => o.textContent).slice(0, 4), ['Paper (3)', 'Horner (4)', 'Estrin (5)', 'R–W (5)'],
     'the phone Method dropdown uses short names so the count stays visible');
  // Copy hands out ASCII: the displayed chain keeps U+2212 / U+00B7
  const shown = $('#chain').textContent;
  let copiedText = null;
  globalThis.navigator.clipboard = { writeText: t => { copiedText = t; return Promise.resolve(); } };
  $('#copy').click(); await settle();
  check(shown.includes('−') && copiedText === shown.replace(/−/g, '-').replace(/·/g, '*') && !/[−·]/.test(copiedText),
        'Copy in the math view writes an ASCII minus and asterisk');
  delete globalThis.navigator.clipboard;
  eq($$('#view-sub .strip').map(s => s.dataset.strip), ['form'], 'phones hide the constants strip');
  const msel = $('#method-select'); msel.value = 'Knuth–Eve'; msel.dispatch('change'); await settle();
  check($('#compare tr.on')?.dataset.m === 'Knuth–Eve' && /\d\.\d{2,5}\b/.test($('#chain').textContent) && !/\d\.\d{7,}/.test($('#chain').textContent),
        'the method dropdown selects a method; a numeric row shows six-digit constants on phones');
  check(/· ≈ real roots \(numeric\)$/.test($('#stats-line').textContent), `the stats line ends with the row's own inexact reason (${$('#stats-line').textContent})`);
  // Share links the state as chosen: the phone's readable-constants presentation (numfmt=decimal) never travels in the link
  $('.pane-actions #share').click(); await settle();
  check(location.hash.includes('method=Knuth%E2%80%93Eve') && location.hash.includes('numfmt=exact') && !location.hash.includes('numfmt=decimal'),
        `phone Share writes the un-presented state (${location.hash})`);
  // while a job runs the phone's other views of the result dim with the pane
  $('#poly-in').dispatch('keydown', { key: 'Enter', metaKey: true }); await settle();
  check($('#out').classList.contains('stale') && $('#stats-line').classList.contains('stale') && $('#method-picker').classList.contains('stale'),
        'while the job runs the phone stats line and Method dropdown dim with the output');
  await replyToLatest();
  check(!$('#out').classList.contains('stale') && !$('#stats-line').classList.contains('stale') && !$('#method-picker').classList.contains('stale'),
        'and are current again once the replies land');
  // a hash change after boot restores the shared state and compiles it
  const nBefore = messageCount();
  location.hash = '#mode=p89&deg=7';
  fire('hashchange'); await settle();
  check($('#mode-select').value === 'p89' && $('#poly-in').value === defaultExample('p89', 7, 0, true).src &&
        messageCount() === nBefore + 1 && lastMessage().fieldMode === 'p89' && lastMessage().src === $('#poly-in').value,
        'a hashchange after boot restores the state from the URL and compiles it');
  check(!$('#input-hint'), 'no input hint for a held example');
  await typeInto($('#poly-in'), 'x^30 + 1'); await settle();
  check(!$('#input-hint'), 'no degree hint over a Mersenne field');
  const fsel = $('#mode-select'); fsel.value = 'R'; fsel.dispatch('change'); await settle();
  check($('#input-hint')?.textContent.includes('degree 30') && $('#input-hint').textContent.includes('minutes') && !$('#input-hint').textContent.includes('Cancel'),
        'typed input of degree > 26 over ℝ shows the slow-preprocessing hint under the input');
  await typeInto($('#poly-in'), 'x^40 + 1'); await settle();
  check(!$('#input-hint'), 'no hint for a degree the worker refuses at once (the error line will say so)');
}

// a shared link boots the shared state -------------------------------------
{
  const { app } = installDom({ compact: true, hash: '#mode=p89&deg=7' });
  await import('../js/ui.js?layout=hash');
  await settle();
  check(app.querySelector('#mode-select').value === 'p89' && app.querySelector('#poly-in').value === defaultExample('p89', 7, 0, true).src,
        'location.hash seeds the boot state');
}

console.log(fails ? `UI SMOKE FAILED (${fails}/${checks})` : `UI SMOKE PASSES (${checks} checks)`);
process.exit(fails ? 1 : 0);
