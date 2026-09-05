// uistate.test.js — invariants of the page's pure state (js/uistate.js): the
// reducer and the selectors the Preact UI renders from.  No DOM, no worker.
import {
  initialStateFor, presentedState, COMPACT_MODE, COMPACT_DEGREE, compileMessages, pendingRow,
  reduce, initialState, examplesFor, defaultExample, exampleHeld, clampDegree, stepDegree, exampleDegree,
  hashFromState, stateFromHash, MODE_MSG, MODES, LEGACY_MODES, VIEWS, showOutput,
  compileMessage, comparisonRow, selectedRow, methodTabs, comparisonTable, rowOps, stats,
  availableSubOptions, subOptionStrips, paneContent, effectiveForm, effectiveCstyle, effectiveNumfmt,
  defaultMethod, methodAvailable, FIELDS, FIELD_GROUPS, fieldChooser, fieldTitle, tokenizePoly,
} from '../js/uistate.js';
import { FIELDS as REGISTRY, FIELD_IDS } from '../js/field.js';
import { parsePoly } from '../js/polyparse.js';
import { countOps, formatConstants } from '../js/chain.js';
import { Rat } from '../js/rat.js';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };
const eq = (a, b, msg) => check(JSON.stringify(a) === JSON.stringify(b),
  `${msg}: got ${JSON.stringify(a)}, want ${JSON.stringify(b)}`);
const run = (state, ...actions) => actions.reduce(reduce, state);

function deepFreeze(o) {
  if (o && typeof o === 'object' && !Object.isFrozen(o)) { Object.freeze(o); Object.values(o).forEach(deepFreeze); }
  return o;
}

// ---- fixtures: result objects shaped like worker.js replies ----------------
const row = (name, extra = {}) => ({
  name, ok: true, mults: 7, adds: 7, height: 4, preprocessing: 'none', exact: true,
  mathText: `${name} math`, mathTextOriginal: null, cText: `${name} c`, cTextFraction: null,
  graph: {}, graphSvg: `<svg>${name}</svg>`, graphText: '', note: '', ...extra,
});
const RESULT = deepFreeze({
  mathText: 'ours math', mathTextOriginal: 'ours paper', cText: 'ours c', cTextFraction: 'ours frac',
  graph: {}, graphSvg: '<svg>ours</svg>', graphText: '', mults: 4, adds: 7, height: 3,
  fieldName: 'ℚ', note: '', comparisons: [
    row('Horner'),
    row('Estrin', { exact: false, cTextFraction: 'estrin frac' }),
    { name: 'Motzkin–Eve', ok: false, note: 'no real roots' },
    row('NoC', { cText: null, graphSvg: null }),
  ],
});
const FAILED = deepFreeze({
  oursFailed: 'degree too small', mathText: null, mathTextOriginal: null, cText: null, cTextFraction: null,
  graph: null, graphSvg: null, graphText: null, mults: null, adds: null, height: null,
  fieldName: 'GF(2^64)', note: '', comparisons: [
    { name: 'Horner', ok: false, note: 'nope' },
    row('Estrin'),
  ],
});
// a result with real chain text, so the counts are taken on the rendering
const OURS_TEXT = [
  'y   = x * (x + 65342529/16384)',
  'z   = (x + y + 4268043425794177/268435456) * (x − 65301569/16384)',
  'w   = (z + 278709932825554996974785/4398046511104) * x',
  'v   = (x + z + 278709932164679789204673/4398046511104) * (w + 15899/64)',
  'P_7 = y + w + v + 87474275/8192',
  'P   = 1/5040 * P_7   (leading-coefficient scale)',
].join('\n');
const HORNER_TEXT = 'b5 = (1/5040) * (x)\nb4 = (b5 + 1/720) * (x)\nP  = b4 + 1';
const COUNTED = deepFreeze({
  ...RESULT, mathText: OURS_TEXT, mults: 5, adds: 11, height: 3, exact: true, fieldId: 'Q', fieldName: 'ℚ',
  comparisons: [row('Horner', { mathText: HORNER_TEXT, mults: 2, adds: 2, height: 2 }), row('Estrin', { exact: false, mathText: 'P = 2·x + 4·y' }),
                { name: 'Belaga', ok: false, note: 'needs complex parameters' }],
});
const withResult = (state, result = RESULT) => {
  const s = reduce(state, { type: 'compile' });
  return reduce(s, { type: 'reply', id: s.jobId, ok: true, result });
};
// A fixture that is NOT in any of the modes the switch tests target (switching
// to the current mode is a no-op): the old GF(2^64) degree-10 boot, but over p61.
const BASE = Object.freeze({ ...initialState, mode: 'p61', exDegree: 10, exKey: 'dense', src: defaultExample('p61', 10, 0, true).src });
const inMode = mode => reduce(BASE, { type: 'setMode', mode });

// ---- initial state ---------------------------------------------------------
eq(Object.keys(initialState).sort(),
   ['busy', 'cstyle', 'error', 'exDegree', 'exKey', 'exMonic', 'exSeed', 'form', 'jobId', 'lateNumeric', 'method', 'mode', 'numfmt', 'result', 'src', 'view'], 'state keys');
eq([initialState.mode, initialState.view, initialState.form, initialState.cstyle, initialState.numfmt, initialState.method,
    initialState.exDegree, initialState.exKey, initialState.exSeed, initialState.exMonic],
   ['Q', 'math', 'factor', 'float', 'exact', 'ours', 7, 'hermite', 0, true], 'initial selections');
check(initialState.src === 'x^7 - 21x^5 + 105x^3 - 105x' && initialState.src === examplesFor('Q', 7).find(e => e.key === 'hermite').src,
      'the desktop opens on the Hermite polynomial He_7 over ℚ (small preprocessed constants)');
eq(examplesFor('Q', 5).find(e => e.key === 'hermite').src, 'x^5 - 10x^3 + 15x', 'He_5');
eq(examplesFor('Q', 3).find(e => e.key === 'hermite').src, 'x^3 - 3x', 'He_3');
check(examplesFor('R', 8).find(e => e.key === 'hermite').src.startsWith('x^8 - 28x^6') && examplesFor('R', 8).find(e => e.key === 'hermite').labelTex === '\\mathrm{He}_{8}',
      'Hermite chips are monic at every degree, over ℝ too');
check(!initialState.busy && initialState.jobId === 0 && initialState.result === null && initialState.error === null, 'initial idle');
check(!showOutput(initialState) && paneContent(initialState) === null && availableSubOptions(initialState) === null
      && selectedRow(initialState) === null && methodTabs(initialState).length === 0 && stats(initialState).length === 0
      && comparisonTable(initialState).length === 0 && subOptionStrips(initialState).length === 0,
      'nothing to show without a result');
eq(MODES, FIELD_IDS, 'modes = the registry ids'); eq(VIEWS, ['math', 'c', 'graph'], 'views');
for (const m of MODES) {
  const exs = examplesFor(m, 10);
  check(exs.length > 0 && exs.every(e =>
    typeof e.key === 'string' && e.key.length > 0 &&
    typeof e.label === 'string' && e.label.length > 0 &&
    typeof e.title === 'string' && e.title.length > 0 &&
    typeof e.src === 'string' && e.src.length > 0), `examples for ${m}`);
  eq(MODE_MSG[m], REGISTRY.find(f => f.id === m).worker, `worker message fields for ${m}`);
  check(MODE_MSG[m].fieldMode === m && ['char0', 'char2'].includes(MODE_MSG[m].lane), `worker message id for ${m}`);
}
eq(MODE_MSG.Q, { lane: 'char0', fieldMode: 'Q' }, 'MODE_MSG Q');
eq(MODE_MSG.p89, { lane: 'char0', fieldMode: 'p89' }, 'MODE_MSG p89');
eq(MODE_MSG.gf64, { lane: 'char2', fieldMode: 'gf64' }, 'MODE_MSG gf64');

// ---- purity ----------------------------------------------------------------
const frozen = deepFreeze({ ...initialState });
for (const a of [{ type: 'setMode', mode: 'Q' }, { type: 'compile' }, { type: 'setSrc', src: 'x' },
                 { type: 'setView', view: 'c' }, { type: 'example', key: 'dense' }, { type: 'example', key: 'random' },
                 { type: 'setExDegree', delta: 1 }, { type: 'setExMonic' }, { type: 'setNumfmt', numfmt: 'decimal' }]) {
  try { reduce(frozen, a); check(true, ''); } catch (e) { check(false, `reducer mutates state on ${a.type}: ${e.message}`); }
}
check(reduce(initialState, { type: 'bogus' }) === initialState, 'unknown action is a no-op (same reference)');
check(reduce(initialState, { type: 'setMode', mode: 'nope' }) === initialState, 'unknown mode ignored');
check(reduce(initialState, { type: 'setMode', mode: 'char2' }) === initialState, 'legacy mode ids are not modes');
check(reduce(initialState, { type: 'setView', view: 'nope' }) === initialState, 'unknown view ignored');
check(reduce(initialState, { type: 'setSrc', src: initialState.src }) === initialState, 'setSrc with same text is a no-op');
check(reduce(initialState, { type: 'cancel' }) === initialState, 'cancel while idle is a no-op');

// ---- mode switch -----------------------------------------------------------
{
  const s0 = run(withResult(BASE), { type: 'setView', view: 'c' }, { type: 'setForm', form: 'original' }, { type: 'setCstyle', cstyle: 'fraction' });
  const typed = reduce(s0, { type: 'setSrc', src: 'x^3 + 1' });
  const s1 = reduce(typed, { type: 'setMode', mode: 'Q' });
  check(s1.mode === 'Q' && s1.result !== null && s1.error === null && showOutput(s1), 'mode switch keeps the last output visible while recompiling (stale)');
  check(s1.src === 'x^3 + 1', 'mode switch keeps the textarea contents');
  check(s1.busy && s1.jobId === typed.jobId + 1, 'mode switch immediately starts a job for the current source');
  eq(compileMessage(s1), { id: s1.jobId, src: 'x^3 + 1', lane: 'char0', fieldMode: 'Q' }, 'auto-compile message reads the new mode');
  check(s1.view === 'c' && s1.form === 'original' && s1.cstyle === 'fraction', 'mode switch keeps view preferences');
  for (const m of MODES) {
    const sm = reduce(typed, { type: 'setMode', mode: m });
    eq(compileMessage(sm), { id: sm.jobId, src: 'x^3 + 1', ...MODE_MSG[m] }, `compile message in ${m} carries the registry worker ids`);
  }
  // method stickiness: the chosen method survives a mode switch and a reply that supports it
  const sh = reduce(run(withResult(BASE), { type: 'setMethod', method: 'Horner' }), { type: 'setMode', mode: 'Q' });
  check(sh.method === 'Horner', 'mode switch keeps the chosen method');
  const shr = reduce(sh, { type: 'reply', id: sh.jobId, ok: true, result: RESULT });
  check(shr.method === 'Horner', 'reply keeps the chosen method when the new result has it');
  const noM = { ...RESULT, comparisons: RESULT.comparisons.filter(r => r.name !== 'Horner') };
  const shf = reduce(sh, { type: 'reply', id: sh.jobId, ok: true, result: noM });
  check(shf.method === 'ours', 'reply falls back when the chosen method is unavailable');
  eq(examplesFor('Q', 10).map(e => e.key), ['exp', 'ln', 'sqrt', 'hermite'], 'ℚ example chips');
  eq(examplesFor('R', 10).map(e => e.key), ['exp', 'ln', 'sqrt', 'hermite'], 'ℝ example chips (the same polynomials)');
  eq(examplesFor('Q', 10).map(e => e.labelTex), ['e^x', '\\ln(1+x)', '\\sqrt{1+x}', '\\mathrm{He}_{10}'],
    'ℚ example chips carry TeX labels');
  for (const m of ['p61', 'p89', 'p127', 'gf32', 'gf64', 'gf128'])
    eq(examplesFor(m, 10).map(e => e.key), ['random', 'sparse', 'dense', 'fixed'], `${m} hashing example chips`);
  const exM = reduce(reduce(s1, { type: 'setMode', mode: 'p89' }), { type: 'example', key: 'dense' });
  check(exM.src === defaultExample('p89', 10).src, 'example chips follow the mode (Mersenne)');
  const err = reduce(reduce(initialState, { type: 'compile' }), { type: 'reply', id: 1, ok: false, message: 'bad input' });
  check(err.error === 'bad input' && !err.busy && err.result === null, 'error reply shows the message');
  check(reduce(err, { type: 'setMode', mode: 'gf32' }).error === null, 'mode switch clears the error');
  // a held example follows the field; typed text does not
  const heldG = reduce(initialState, { type: 'setMode', mode: 'gf64' });
  check(heldG.src === defaultExample('gf64', 7, 0, true).src && heldG.exKey === 'dense' && heldG.busy,
        'mode switch regenerates a held example in the new field (ℚ He_7 → gf64 dense)');
  const heldBack = reduce(heldG, { type: 'setMode', mode: 'Q' });
  check(heldBack.src === defaultExample('Q', 7, 0, true).src && heldBack.exKey === 'exp', 'and back (gf64 dense → the ℚ default, e^x)');
  const sparse = reduce(inMode('gf64'), { type: 'example', key: 'sparse' });
  check(reduce(sparse, { type: 'setMode', mode: 'p89' }).exKey === 'sparse', 'the same chip is kept when the new field has it');
  check(reduce(typed, { type: 'setMode', mode: 'gf32' }).src === 'x^3 + 1', 'typed text survives a mode switch unchanged');
  check(reduce(initialState, { type: 'setMode', mode: 'Q' }) === initialState, 'switching to the current mode is a no-op');
  check(reduce(err, { type: 'setSrc', src: '  ' }).error === null && reduce(err, { type: 'setSrc', src: 'x' }).error === 'bad input',
        'emptying the input clears a stale error; other edits keep it until the next compile');
  check(/0x[0-9a-f]+ x\^/.test(defaultExample('gf64', 10).src) && !/0x[0-9a-f]+x/.test(defaultExample('gf64', 10).src),
        'hex example coefficients are separated from x by a space');
  // setMode while busy supersedes cleanly: busy stays true under a NEW job id,
  // the superseded job's reply is ignored, the new job's reply lands
  const busy = reduce(BASE, { type: 'compile' });
  const sw = reduce(busy, { type: 'setMode', mode: 'Q' });
  check(sw.busy && sw.jobId === busy.jobId + 1 && sw.mode === 'Q', 'setMode while busy starts a NEW job (busy, fresh id)');
  check(reduce(sw, { type: 'reply', id: busy.jobId, ok: true, result: RESULT }) === sw, 'superseded job reply is ignored (same reference)');
  const landed = reduce(sw, { type: 'reply', id: sw.jobId, ok: true, result: RESULT });
  check(!landed.busy && landed.result === RESULT, 'the new job reply lands');
  // blank source: switching mode starts no job (and compile is a no-op)
  const blank = reduce(BASE, { type: 'setSrc', src: '   \n\t' });
  const bsw = reduce(blank, { type: 'setMode', mode: 'Q' });
  check(!bsw.busy && bsw.jobId === blank.jobId && bsw.mode === 'Q' && bsw.result === null, 'setMode with blank source starts no job');
  check(reduce(blank, { type: 'compile' }) === blank, 'compile with blank source is a no-op');
  const refs = comparisonTable(withResult(BASE)).map(r => [r.name, r.ref?.short ?? null]);
  eq(refs.slice(0, 3), [['This paper', 'Ahle & Knudsen 2026'], ['Horner', 'Horner 1819'], ['Estrin', 'Estrin 1960']],
     'comparison rows carry their references');
  check(comparisonTable(withResult(BASE)).every(r => !r.ref || (typeof r.ref.cite === 'string' && r.ref.cite.length > 20)), 'every reference has a citation line');
  const bres = reduce(reduce(withResult(BASE), { type: 'setSrc', src: ' ' }), { type: 'setMode', mode: 'Q' });
  check(!bres.busy && bres.result === null && !showOutput(bres), 'blank-source mode switch still clears the output');
}

// ---- examples / compile / cancel / replies ---------------------------------
{
  const s0 = run(BASE, { type: 'setMode', mode: 'Q' });   // auto-starts job 1
  check(s0.busy && s0.jobId === 1, 'mode switch auto-compiles (job 1)');
  const ex = examplesFor('Q', 10, 0, true)[0];
  const s1 = reduce(s0, { type: 'example', key: ex.key });
  check(s1.src === ex.src && s1.exKey === 'exp' && s1.busy && s1.jobId === 2 && s1.result === null && s1.error === null, 'example sets src and starts a job');
  eq(compileMessage(s1), { id: 2, src: ex.src, lane: 'char0', fieldMode: 'Q' }, 'compile message for ℚ');
  check(reduce(s1, { type: 'reply', id: 1, ok: true, result: RESULT }) === s1, 'stale reply (old id) ignored');
  check(reduce(s1, { type: 'reply', id: 3, ok: true, result: RESULT }) === s1, 'reply for an unknown id ignored');
  const s2 = reduce(s1, { type: 'reply', id: 2, ok: true, result: RESULT });
  check(!s2.busy && s2.result === RESULT && s2.error === null && showOutput(s2), 'matching reply lands');
  const s3 = reduce(s2, { type: 'compile' });
  check(s3.jobId === 3 && s3.busy && showOutput(s3) === (s3.result !== null), 'compile keeps any previous output while running (stale)');
  check(reduce(s3, { type: 'reply', id: 2, ok: true, result: RESULT }) === s3, 'reply from the superseded job ignored');
  const s4 = reduce(s3, { type: 'cancel' });
  check(!s4.busy && s4.jobId === 3 && s4.result === RESULT, 'cancel keeps the stale output (idle, last result shown)');
  check(reduce(s4, { type: 'reply', id: 3, ok: true, result: RESULT }) === s4, 'reply after cancel ignored');
  check(reduce(s4, { type: 'reply', id: 3, ok: false, message: 'x' }) === s4, 'error reply after cancel ignored');
  const s5 = reduce(s4, { type: 'compile' });
  check(s5.jobId === 4 && s5.busy, 'compile after cancel uses a fresh id');
  eq(compileMessage(reduce(inMode('p89'), { type: 'compile' })).lane, 'char0', 'Mersenne lane');
  eq(compileMessage(reduce(inMode('p127'), { type: 'compile' })).fieldMode, 'p127', 'Mersenne fieldMode is the registry id');
  eq(compileMessage(reduce(initialState, { type: 'compile' })), { id: 1, src: initialState.src, lane: 'char0', fieldMode: 'Q' }, 'ℚ message');
  eq(compileMessage(reduce(inMode('gf64'), { type: 'compile' })), { id: 2, src: defaultExample('gf64', 10, 0, true).src, lane: 'char2', fieldMode: 'gf64' }, 'GF(2^64) message');
  const we = reduce(s5, { type: 'workerError', message: 'worker failed to load: boom' });
  check(!we.busy && we.error === 'worker failed to load: boom' && we.result === null, 'worker error surfaces and returns to idle');
  check(reduce(we, { type: 'reply', id: 4, ok: true, result: RESULT }) === we, 'reply after worker error ignored');
}

// ---- result → method selection --------------------------------------------
{
  const s = withResult(initialState);
  check(s.method === 'ours' && selectedRow(s) === RESULT && comparisonRow(s) === null, 'fresh result selects ours');
  eq(methodTabs(s).map(t => [t.key, t.enabled, t.on]),
     [['ours', true, true], ['Horner', true, false], ['Estrin', true, false], ['Motzkin–Eve', false, false], ['NoC', true, false]], 'method tabs');
  check(methodTabs(s)[0].label === 'This paper (4)' && methodTabs(s)[1].label === 'Horner (7)' && methodTabs(s)[3].label === 'Motzkin–Eve',
        'chips carry their multiplication counts');
  check(methodTabs(s)[3].title === 'no real roots', 'failed comparison carries its note as title');
  const h = run(s, { type: 'setMethod', method: 'Horner' }, { type: 'setView', view: 'graph' }, { type: 'setForm', form: 'original' }, { type: 'setCstyle', cstyle: 'fraction' });
  check(h.method === 'Horner' && selectedRow(h).name === 'Horner' && comparisonRow(h).name === 'Horner', 'comparison selected');
  eq(methodTabs(h).filter(t => t.on).map(t => t.key), ['Horner'], 'exactly one tab is on');
  const h2 = withResult(h);
  check(h2.method === 'Horner', 'new result keeps the chosen method (sticky)');
  check(h2.view === 'graph' && h2.form === 'original' && h2.cstyle === 'fraction', 'new result keeps view/form/cstyle');
  check(reduce(s, { type: 'setMethod', method: 'Motzkin–Eve' }) === s, 'cannot select a failed comparison');
  check(reduce(s, { type: 'setMethod', method: 'Nonexistent' }) === s, 'cannot select an unknown method');
  check(reduce(initialState, { type: 'setMethod', method: 'Horner' }) === initialState, 'cannot select without a result');
  const f = withResult(initialState, FAILED);
  check(f.method === 'Estrin' && selectedRow(f).name === 'Estrin', 'oursFailed selects the first ok comparison');
  eq(methodTabs(f).map(t => [t.key, t.enabled, t.on]), [['ours', false, false], ['Horner', false, false], ['Estrin', true, true]], 'tabs when ours failed');
  check(methodTabs(f)[0].title === 'degree too small', 'ours failure shown as title');
  check(reduce(f, { type: 'setMethod', method: 'ours' }) === f, 'cannot select ours when it failed');
  check(defaultMethod(RESULT) === 'ours' && defaultMethod(FAILED) === 'Estrin', 'defaultMethod');
  check(methodAvailable(RESULT, 'ours') && !methodAvailable(FAILED, 'ours') && methodAvailable(RESULT, 'NoC') && !methodAvailable(null, 'ours'), 'methodAvailable');
  eq(stats(f).map(x => x.value), [7, 7, 4, 'GF(2^64)', 'yes'], 'stats for the selected comparison use the result fieldName');
}

// ---- stats + comparison table ---------------------------------------------
{
  const s = withResult(initialState);
  eq(stats(s).map(x => [x.label, x.value]),
     [['multiplications', 4], ['additions', 7], ['mult. depth', 3], ['field', 'ℚ'], ['exact', 'yes']], 'stats for ours');
  eq(stats(reduce(s, { type: 'setMethod', method: 'Estrin' })).map(x => x.value), [7, 7, 4, 'ℚ', '≈ numeric'], 'stats: inexact comparison');
  const noCounts = withResult(initialState, deepFreeze({ ...RESULT, mults: null }));
  eq(stats(noCounts), [], 'no stats without counts');
  check(stats(withResult(initialState, deepFreeze({ ...RESULT, exact: false })))[4].value === '≈ numeric', 'ours over ℝ is ≈ numeric');
  // the table: one row per method in worker order, the selected one on, counts from countOps
  const t = comparisonTable(s);
  eq(t.map(r => [r.key, r.name, r.ok, r.on]),
     [['ours', 'This paper', true, true], ['Horner', 'Horner', true, false], ['Estrin', 'Estrin', true, false],
      ['Motzkin–Eve', 'Motzkin–Eve', false, false], ['NoC', 'NoC', true, false]], 'table rows: every method, ours first, selected on');
  eq(t.map(r => [r.mults, r.scalar, r.adds, r.height, r.exact]),
     [[4, 0, 7, 3, true], [7, 0, 7, 4, true], [7, 0, 7, 4, false], [null, 0, null, null, null], [7, 0, 7, 4, true]],
     'table counts fall back to the row counts when the rendering shows no operation; failed rows have none');
  check(t[3].note === 'no real roots' && t[0].note === '' && t[1].note === '', 'failed rows carry their reason');
  eq(comparisonTable(reduce(s, { type: 'setMethod', method: 'Estrin' })).filter(r => r.on).map(r => r.key), ['Estrin'], 'the table highlights the selected method');
  // clicking a row is the chip's action: setMethod (refused for failed rows)
  check(reduce(s, { type: 'setMethod', method: t[3].key }) === s && reduce(s, { type: 'setMethod', method: t[1].key }).method === 'Horner', 'row click = setMethod');
  // counts are taken on the factored rendering with countOps: scalar multiplications counted, integer multiples as additions
  const c = withResult(inMode('Q'), COUNTED);
  const ct = comparisonTable(c);
  const ours = countOps(OURS_TEXT), horner = countOps(HORNER_TEXT), estrin = countOps('P = 2·x + 4·y');
  eq([ct[0].mults, ct[0].scalar, ct[0].adds, ct[0].height], [ours.mults + ours.scalar, ours.scalar, ours.adds, 3], 'ours counted on its rendering (4 + 1 scalar)');
  check(ct[0].mults === 5 && ct[0].scalar === 1 && ct[0].adds === 11, `ours: ${ct[0].mults} mults (${ct[0].scalar} scalar), ${ct[0].adds} adds`);
  eq([ct[1].mults, ct[1].scalar, ct[1].adds], [horner.mults + horner.scalar, horner.scalar, horner.adds], 'Horner counted on its rendering');
  eq([ct[2].mults, ct[2].scalar, ct[2].adds], [estrin.mults, 0, estrin.adds], 'integer multiples charged as additions (2·x = 1, 4·y = 2, plus the sum)');
  check(ct[2].adds === 4 && ct[2].mults === 0, `Estrin fixture: ${ct[2].mults} mults ${ct[2].adds} adds`);
  eq(ct.map(r => r.exact), [true, true, false, null], 'exact column');
  check(ct[3].key === 'Belaga' && ct[3].note === 'needs complex parameters', 'Belaga row reports why it did not run');
  // the chips show the same totals as the table
  eq(methodTabs(c).map(x => x.label), ['This paper (5)', 'Horner (2)', 'Estrin (0)', 'Belaga'], 'chip counts = table totals');
  eq(rowOps(null), null, 'rowOps without a row');
  eq(rowOps({ mults: 3, adds: 2, mathText: 'P = 5' }), { mults: 3, adds: 2, scalar: 0 }, 'rowOps: a constant rendering keeps the row counts');
  eq(rowOps({ mults: 0, adds: 1, radixShifts: 1, radixExponent: 3, mathText: 'P = y + 8·q2' }),
    { adds: 1, mults: 0, scalar: 0, radix: 1 }, 'rowOps: 2^N is charged as one radix shift, not N additions');
  // ℝ: the field's own status is ≈ numeric — the same exact-column cell Motzkin–Eve's
  // numeric rows show — with a hover note saying only the constants are rounded (the
  // preprocessing is exact, so there is no accuracy warning anywhere)
  const rres = deepFreeze({ ...RESULT, exact: false, status: '≈ numeric', fieldId: 'R', fieldName: 'ℝ', comparisons: [
    row('Horner', { preprocessing: 'none', exact: true }),
    row('Rabin–Winograd', { preprocessing: 'numeric', exact: false }),
    row('Motzkin–Eve', { preprocessing: 'real roots (numeric)', exact: false, note: 'max rel. error 1.2e-16' }),
    { name: 'Belaga', ok: false, note: 'no real parameters' },
  ] });
  const rt = comparisonTable(withResult(inMode('R'), rres));
  eq(rt.map(r => [r.key, r.exact]), [['ours', false], ['Horner', true], ['Rabin–Winograd', false], ['Motzkin–Eve', false], ['Belaga', null]],
     'ℝ: ours is ≈ numeric like the numeric methods; Horner (no preprocessing) stays exact');
  check(/exact rational preprocessing/.test(rt[0].exactNote) && /rounded to doubles/.test(rt[0].exactNote), `ℝ: ours' note says only the constants are rounded (${rt[0].exactNote})`);
  check(rt[1].exactNote === null && rt[4].exactNote === null, 'exact and failed rows carry no numeric note');
  check(rt[2].exactNote === rt[0].exactNote, 'Rabin–Winograd over ℝ: the same rounding note (its preprocessing is exact too)');
  check(rt[3].exactNote === 'real roots (numeric), max rel. error 1.2e-16', `Motzkin–Eve note: ${rt[3].exactNote}`);
  const long = row('Belaga', { preprocessing: 'complex roots', exact: false, note: 'Belaga 1958 (Pan 1966): the constants are roots of B max rel. error 3.2e-11' });
  check(comparisonTable(withResult(inMode('R'), deepFreeze({ ...rres, comparisons: [long] })))[1].exactNote === 'complex roots, max rel. error 3.2e-11',
        'a method description in the note is left out of the hover text');
  check(stats(withResult(inMode('R'), rres))[4].value === '≈ numeric', 'ℝ stats agree with the table');
  check(comparisonTable(withResult(inMode('Q'), COUNTED)).every(r => (r.exactNote === null) === (r.exact !== false)), 'ℚ: notes only on inexact rows');
  // failed ours: its row is off with the reason, the rest still count
  const ft = comparisonTable(withResult(initialState, FAILED));
  eq(ft.map(r => [r.key, r.ok, r.on, r.mults]), [['ours', false, false, null], ['Horner', false, false, null], ['Estrin', true, true, 7]], 'table when ours failed');
  check(ft[0].note === 'degree too small', 'ours failure in the table');
}

// ---- sub-option visibility -------------------------------------------------
{
  const q = withResult(inMode('Q'));
  const sub = availableSubOptions(q);
  check(sub.kind === 'form' && sub.label === 'form:', 'math view shows the form strip first');
  eq(sub.options.map(o => [o.key, o.on, o.enabled]), [['factor', true, true], ['original', false, true]], 'form options for ours');
  eq(subOptionStrips(q).map(st => st.kind), ['form', 'numfmt'], 'math view: form + constant-format strips');
  const c = reduce(q, { type: 'setView', view: 'c' });
  const csub = availableSubOptions(c);
  check(csub.kind === 'constants' && csub.label === 'constants:', 'C view over ℚ shows the constants strip');
  eq(subOptionStrips(c).map(st => st.kind), ['constants'], 'C view over ℚ: only the constants strip');
  eq(csub.options.map(o => [o.key, o.on, o.enabled]), [['float', true, true], ['fraction', false, true]], 'constants options for ours');
  check(availableSubOptions(reduce(q, { type: 'setView', view: 'graph' })) === null, 'graph view has no sub-options');
  for (const m of ['R', 'p89', 'gf64']) {
    const s = reduce(withResult(inMode(m)), { type: 'setView', view: 'c' });
    check(availableSubOptions(s) === null, `C constants strip hidden in ${m}`);
    eq(subOptionStrips(reduce(s, { type: 'setView', view: 'math' })).map(st => st.kind), ['form', 'numfmt'], `form + numfmt strips shown in ${m}`);
  }
  const hp = run(q, { type: 'setForm', form: 'original' });
  eq(availableSubOptions(hp).options.map(o => [o.key, o.on, o.enabled]), [['factor', false, true], ['original', true, true]], 'original selected for ours');
  const hh = reduce(hp, { type: 'setMethod', method: 'Horner' });
  eq(availableSubOptions(hh).options.map(o => [o.key, o.on, o.enabled]), [['factor', true, true], ['original', false, false]], 'original unavailable for Horner: factor on, original off');
  check(effectiveForm(hh) === 'factor' && hh.form === 'original', 'preference kept, effective value falls back');
  check(paneContent(hh).text === 'Horner math', 'pane falls back to the factored text');
  check(paneContent(reduce(hh, { type: 'setMethod', method: 'ours' })).text === 'ours paper', 'preference resumes on a row that has original text');
  const cf = run(c, { type: 'setCstyle', cstyle: 'fraction' });
  eq(availableSubOptions(cf).options.map(o => [o.key, o.on, o.enabled]), [['float', false, true], ['fraction', true, true]], 'fraction on for ours');
  eq(paneContent(cf), { kind: 'c', code: 'ours frac' }, 'fraction C for ours');
  const cfh = reduce(cf, { type: 'setMethod', method: 'Horner' });
  eq(availableSubOptions(cfh).options.map(o => [o.key, o.on, o.enabled]), [['float', true, true], ['fraction', false, false]], 'fraction off for Horner');
  eq(paneContent(cfh), { kind: 'c', code: 'Horner c' }, 'float C for Horner');
  eq(paneContent(reduce(cf, { type: 'setMethod', method: 'Estrin' })), { kind: 'c', code: 'estrin frac' }, 'fraction C for a row that has it');
  const mf = run(withResult(inMode('p89')), { type: 'setView', view: 'c' }, { type: 'setCstyle', cstyle: 'fraction' });
  check(effectiveCstyle(mf) === 'float' && paneContent(mf).code === 'ours c', 'fraction ignored outside ℚ');
  check(reduce(q, { type: 'setSubOption', key: 'original' }).form === 'original', 'setSubOption → form in math view');
  check(reduce(c, { type: 'setSubOption', key: 'fraction' }).cstyle === 'fraction', 'setSubOption → cstyle in C view');
  check(reduce(hh, { type: 'setSubOption', key: 'original' }) === hh, 'setSubOption ignores a disabled option');
  const g = reduce(q, { type: 'setView', view: 'graph' });
  check(reduce(g, { type: 'setSubOption', key: 'original' }) === g, 'setSubOption is a no-op without a strip');
  check(reduce(q, { type: 'setForm', form: 'bogus' }) === q && reduce(q, { type: 'setCstyle', cstyle: 'bogus' }) === q
        && reduce(q, { type: 'setNumfmt', numfmt: 'bogus' }) === q, 'invalid sub-option values ignored');
}

// ---- readable constants (numfmt) -------------------------------------------
{
  const q = withResult(inMode('Q'), COUNTED);
  const strip = subOptionStrips(q)[1];
  check(strip.kind === 'numfmt' && strip.label === 'constants:', 'constant-format strip on the math row');
  eq(strip.options.map(o => [o.key, o.label, o.on, o.enabled]), [['exact', 'exact', true, true], ['decimal', 'decimal', false, true]], 'ℚ defaults to exact');
  check(paneContent(q).text === OURS_TEXT && effectiveNumfmt(q) === 'exact', 'exact shows the chain as produced');
  const d = reduce(q, { type: 'setSubOption', key: 'decimal' });
  check(d.numfmt === 'decimal' && effectiveNumfmt(d) === 'decimal', 'setSubOption routes decimal to numfmt');
  check(paneContent(d).text === formatConstants(OURS_TEXT, 'decimal') && paneContent(d).text.includes('x * (x + 3988.19)')
        && paneContent(d).text.includes('0.000198413 * P_7'), `decimal pane: ${paneContent(d).text.split('\n')[0]}`);
  eq(subOptionStrips(d)[1].options.map(o => o.on), [false, true], 'decimal option on');
  eq(comparisonTable(d).map(r => [r.mults, r.adds]), comparisonTable(q).map(r => [r.mults, r.adds]), 'counts never change with the display format');
  check(d.result === q.result && selectedRow(d).mathText === OURS_TEXT, 'the underlying chain is untouched');
  check(paneContent(reduce(d, { type: 'setView', view: 'c' })).code === 'ours c', 'the C view ignores numfmt');
  const dh = reduce(d, { type: 'setMethod', method: 'Horner' });
  check(paneContent(dh).text === 'b5 = (0.000198413) * (x)\nb4 = (b5 + 0.00138889) * (x)\nP  = b4 + 1', `decimal applies to comparison rows too: ${paneContent(dh).text}`);
  // the original form is reformatted as well
  const dor = reduce(d, { type: 'setForm', form: 'original' });
  check(paneContent(dor).text === 'ours paper', 'original form without constants passes through');
  // binary fields: the readable style is hex (every constant a bit pattern)
  const gfr = deepFreeze({ ...RESULT, mathText: 'y = (x + 5) * (x + 0x1f3a)\nP = y + 1', fieldId: 'gf64', fieldName: 'GF(2^64)' });
  const g = withResult(inMode('gf64'), gfr);
  eq(subOptionStrips(g)[1].options.map(o => [o.key, o.label, o.enabled]), [['exact', 'exact', true], ['decimal', 'hex', true]], 'GF(2^k): the readable option is hex');
  check(paneContent(reduce(g, { type: 'setNumfmt', numfmt: 'decimal' })).text === 'y = (x + 0x5) * (x + 0x1f3a)\nP = y + 0x1', 'hex rendering');
  // Mersenne fields: constants are decimal residues already — the option is offered but disabled
  const p = withResult(inMode('p89'), deepFreeze({ ...RESULT, mathText: 'y = (x + 309485009821345068724781055) * x\nP = y + 5', fieldId: 'p89' }));
  const ps = subOptionStrips(p)[1];
  eq(ps.options.map(o => [o.key, o.on, o.enabled]), [['exact', true, true], ['decimal', false, false]], 'Mersenne: decimal disabled');
  check(/decimal residues/.test(ps.options[1].title), 'Mersenne: the disabled option says why');
  const pd = reduce(p, { type: 'setNumfmt', numfmt: 'decimal' });
  check(effectiveNumfmt(pd) === 'exact' && paneContent(pd).text === selectedRow(pd).mathText, 'a decimal preference has no effect in a Mersenne field');
  check(reduce(p, { type: 'setSubOption', key: 'decimal' }) === p, 'setSubOption refuses the disabled option');
  // ℝ: the constants are doubles; 'full' / 'decimal'
  const r = withResult(inMode('R'), deepFreeze({ ...RESULT, mathText: 'y = (x + 0.3333333333333333) * x\nP = y + 1', exact: false, fieldId: 'R' }));
  eq(subOptionStrips(r)[1].options.map(o => o.label), ['full', 'decimal'], 'ℝ labels');
  check(paneContent(reduce(r, { type: 'setNumfmt', numfmt: 'decimal' })).text === 'y = (x + 0.333333) * x\nP = y + 1', 'ℝ decimal rendering');
  // a rendering without constants offers nothing to reformat
  const none = withResult(inMode('Q'), deepFreeze({ ...RESULT, mathText: 'y = x * x\nP = y + x' }));
  check(subOptionStrips(none)[1].options[1].enabled === false && effectiveNumfmt(reduce(none, { type: 'setNumfmt', numfmt: 'decimal' })) === 'exact',
        'decimal disabled when nothing changes');
  // the preference is sticky across methods, views and results
  const back = withResult(run(d, { type: 'setView', view: 'graph' }), COUNTED);
  check(back.numfmt === 'decimal' && effectiveNumfmt(reduce(back, { type: 'setView', view: 'math' })) === 'decimal', 'numfmt preference survives');
}

// ---- pane content ----------------------------------------------------------
{
  const s = withResult(initialState);
  eq(paneContent(s), { kind: 'math', text: 'ours math' }, 'math pane');
  eq(paneContent(reduce(s, { type: 'setForm', form: 'original' })), { kind: 'math', text: 'ours paper' }, 'original math pane');
  eq(paneContent(reduce(s, { type: 'setView', view: 'c' })), { kind: 'c', code: 'ours c' }, 'C pane');
  eq(paneContent(reduce(s, { type: 'setView', view: 'graph' })), { kind: 'graph', svg: '<svg>ours</svg>', dash: false, kx: false }, 'graph pane');
  const noc = run(s, { type: 'setMethod', method: 'NoC' }, { type: 'setView', view: 'c' });
  eq(paneContent(noc), { kind: 'c-missing', text: 'NoC math', note: '/* no C rendering for this method */' }, 'null cText shows the math text with a note line');
  eq(paneContent(reduce(noc, { type: 'setView', view: 'graph' })), { kind: 'graph-missing', note: 'no graph for this method' }, 'null graphSvg');
  eq(paneContent(reduce(s, { type: 'setMethod', method: 'Horner' })), { kind: 'math', text: 'Horner math' }, 'math pane follows the method');
  // a field without C rendering says so (registry cCode / the reply's cCode)
  const nofield = withResult(initialState, deepFreeze({ ...RESULT, cText: null, cTextFraction: null, cCode: false }));
  check(paneContent(reduce(nofield, { type: 'setView', view: 'c' })).note === '/* no C rendering for this field yet */', 'field-level C note');
  check(REGISTRY.every(f => f.cCode), 'every registry field renders C today');
  const e = run(s, { type: 'setMethod', method: 'Estrin' });
  check(selectedRow(e).name === 'Estrin' && paneContent(e).text === 'Estrin math' && stats(e)[4].value === '≈ numeric'
        && methodTabs(e).find(t => t.on).key === 'Estrin' && comparisonTable(e).find(r => r.on).key === 'Estrin', 'one source of truth for the selected method');
}

// ---- example generators ----------------------------------------------------
{
  // exact Taylor coefficients, checked through the real parser against Rat values
  const fact = k => { let f = 1n; for (let i = 2n; i <= BigInt(k); i++) f *= i; return f; };
  const { coeffs: ec } = parsePoly(examplesFor('Q', 7)[0].src);
  check(ec.length === 8, 'exp generator reaches x^7');
  for (let k = 0; k <= 7; k++) check(ec[k].eq(new Rat(1n, fact(k))), `exp coeff x^${k} = 1/${k}!`);
  const { coeffs: lc } = parsePoly(examplesFor('Q', 9)[1].src);
  check(lc.length === 10 && lc[0].isZero(), 'ln generator reaches x^9 with no constant term');
  for (let k = 1; k <= 9; k++) check(lc[k].eq(new Rat(k % 2 ? 1n : -1n, BigInt(k))), `ln coeff x^${k} = ±1/${k}`);
  const { coeffs: sc } = parsePoly(examplesFor('R', 8)[2].src);
  let b = Rat.ONE;
  for (let k = 0; k <= 8; k++) {
    if (k > 0) b = b.mul(new Rat(1n, 2n).sub(new Rat(BigInt(k - 1)))).div(new Rat(BigInt(k)));
    check(sc[k].eq(b), `sqrt coeff x^${k} = binom(1/2,${k})`);
  }
  check(examplesFor('Q', 10)[0].src === '1/3628800x^10 + 1/362880x^9 + 1/40320x^8 + 1/5040x^7 + 1/720x^6 + 1/120x^5 + 1/24x^4 + 1/6x^3 + 1/2x^2 + x + 1',
        'exp(x) at degree 10 matches the old example');
  check(examplesFor('Q', 15)[1].src === '1/15x^15 - 1/14x^14 + 1/13x^13 - 1/12x^12 + 1/11x^11 - 1/10x^10 + 1/9x^9 - 1/8x^8 + 1/7x^7 - 1/6x^6 + 1/5x^5 - 1/4x^4 + 1/3x^3 - 1/2x^2 + x',
        'ln(1+x) at degree 15 matches the old example');
  check(examplesFor('Q', 12)[2].src === '-29393/4194304x^12 + 4199/524288x^11 - 2431/262144x^10 + 715/65536x^9 - 429/32768x^8 + 33/2048x^7 - 21/1024x^6 + 7/256x^5 - 5/128x^4 + 1/16x^3 - 1/8x^2 + 1/2x + 1',
        '√(1+x) at degree 12 matches the old example');
  eq(examplesFor('Q', 12).map(e => e.src), examplesFor('R', 12).map(e => e.src), 'ℝ shares the ℚ examples');
  // hashing fields: the same four presets over every Mersenne prime / binary field
  const abs = c => (c.n < 0n ? -c.n : c.n);
  for (const m of ['p61', 'p89', 'p127']) {
    const f = REGISTRY.find(x => x.id === m);
    eq(examplesFor(m, 20), examplesFor(m, 20), `${m} generators are deterministic`);
    for (const n of [3, 20, 63]) {
      const ex = Object.fromEntries(examplesFor(m, n).map(e => [e.key, parsePoly(e.src)]));
      check(ex.dense.degree === n && ex.dense.coeffs[n].isOne() && ex.dense.coeffs.every(c => c.isInt() && !c.isZero() && abs(c) <= 20n),
            `${m} dense degree ${n}: monic, every coefficient in ±[1,20]`);
      const sparseNZ = ex.sparse.coeffs.filter(c => !c.isZero()).length;
      check(ex.sparse.degree === n && ex.sparse.coeffs[n].isOne() && !ex.sparse.coeffs[0].isZero() && sparseNZ <= Math.max(3, n / 4 + 2)
            && sparseNZ < n + 1 && ex.sparse.coeffs.every(c => c.isInt() && abs(c) <= 20n),
            `${m} sparse degree ${n}: monic, ${sparseNZ} nonzero terms`);
      for (const k of ['random', 'fixed']) {
        const p = ex[k];
        check(p.degree === n && p.coeffs.every(c => c.isInt() && c.n >= 0n && c.n < f.prime), `${m} ${k} key degree ${n}: residues in [0, p)`);
        check(p.coeffs.filter(c => c.n > (f.prime >> 8n)).length >= n / 2, `${m} ${k} key degree ${n}: full-width coefficients`);
        check(!p.coeffs[n].isOne(), `${m} ${k} key degree ${n}: random leading coefficient (non-monic)`);
      }
    }
    check(examplesFor(m, 64)[2].src.startsWith('x^63'), `${m} degree clamps down to 63`);
    check(examplesFor(m, 1)[2].src.startsWith('x^3'), `${m} degree clamps up to 3`);
  }
  check(examplesFor('p61', 20)[2].src === examplesFor('p89', 20)[2].src && examplesFor('p61', 20)[1].src === examplesFor('p127', 20)[1].src,
        'small-coefficient presets agree across the Mersenne fields (only the keys depend on the width)');
  check(examplesFor('p61', 20)[3].src !== examplesFor('p89', 20)[3].src, 'fixed keys are field-width specific');
  for (const m of ['gf32', 'gf64', 'gf128']) {
    const f = REGISTRY.find(x => x.id === m);
    eq([0, 3, 13, 14, 16, 17, 21, 40].map(d => clampDegree(m, d)), [1, 3, 13, 14, 16, 17, 21, 26], `${m} degree clamping: every degree 1..26`);
    for (const n of [13, 14, 21]) {
      const ex = Object.fromEntries(examplesFor(m, n).map(e => [e.key, parsePoly(e.src, { char2: true })]));
      check(ex.dense.degree === n && ex.dense.coeffs[n] === 1n && ex.dense.coeffs.every(c => c !== 0n && c <= 29n), `${m} dense degree ${n}: monic, small hex coefficients`);
      check(ex.sparse.degree === n && ex.sparse.coeffs[n] === 1n && ex.sparse.coeffs[0] !== 0n && ex.sparse.coeffs.filter(c => c !== 0n).length <= 8, `${m} sparse degree ${n}`);
      for (const k of ['random', 'fixed']) {
        const p = ex[k];
        check(p.degree === n && p.coeffs.every(c => c >= 0n && c < (1n << BigInt(f.bits))), `${m} ${k} key degree ${n}: ${f.bits}-bit patterns`);
        check(p.coeffs.filter(c => c > (1n << BigInt(f.bits - 8))).length >= n / 2 && p.coeffs[n] !== 1n, `${m} ${k} key degree ${n}: full-width, non-monic`);
      }
    }
    check(/^0x[0-9a-f]+ x\^13 \+ 0x/.test(examplesFor(m, 13)[0].src), `${m} keys are written in hex (a space before x)`);
    check(examplesFor(m, 14)[2].src.startsWith('x^14') && examplesFor(m, 27)[2].src.startsWith('x^26'), `${m} even degrees are their own; 27 clamps to 26`);
  }
  // the random key reseeds; the fixed key does not
  check(examplesFor('p89', 20, 0)[0].src !== examplesFor('p89', 20, 1)[0].src, 'random key differs per seed');
  check(examplesFor('p89', 20, 0)[3].src === examplesFor('p89', 20, 1)[3].src, 'fixed key ignores the seed');
  check(examplesFor('p89', 20, 5)[0].src === examplesFor('p89', 20, 5)[0].src, 'random key reproducible per seed');
  check(examplesFor('p89', 20, 0)[0].reseed === true && examplesFor('p89', 20)[3].reseed === undefined, 'only the random chip reseeds');
  check(/independent hashing/.test(examplesFor('gf64', 13)[0].title) && /21-independent/.test(examplesFor('p89', 20)[0].title), 'random key chip explains k-independence');
  // stepping
  eq([stepDegree('Q', 10, 1), stepDegree('Q', 24, 1), stepDegree('Q', 3, -1), stepDegree('R', 24, 1)], [11, 24, 3, 24], 'ℚ/ℝ stepping clamps at [3,24]');
  eq([stepDegree('p89', 62, 1), stepDegree('p89', 63, 1)], [63, 63], 'Mersenne stepping clamps at 63');
  eq([stepDegree('gf64', 13, 1), stepDegree('gf64', 15, -1), stepDegree('gf64', 26, 1), stepDegree('gf64', 1, -1)],
     [14, 14, 26, 1], 'GF(2^k) stepping walks every degree 1..26 and clamps at the ends');
  check(clampDegree('nope', 7) === 7 && examplesFor('nope', 7).length === 0, 'unknown mode: no examples, degree untouched');
}

// ---- degree chooser (setExDegree) ------------------------------------------
{
  const hermite = (n, monic = true) => examplesFor('Q', n, 0, monic).find(e => e.key === 'hermite').src;
  check(exampleDegree(initialState) === 7, 'the ℚ default exDegree 7 is compiled as is');
  const up = reduce(initialState, { type: 'setExDegree', delta: 1 });
  check(up.exDegree === 8 && up.exKey === 'hermite' && up.busy && up.jobId === initialState.jobId + 1
        && up.src === hermite(8), 'stepping + regenerates the held example and compiles');
  const down = reduce(up, { type: 'setExDegree', delta: -1 });
  check(down.exDegree === 7 && down.src === initialState.src && down.jobId === up.jobId + 1, 'stepping − regenerates back');
  const lowest = { ...initialState, exDegree: 1 };
  check(reduce(lowest, { type: 'setExDegree', delta: -1 }) === lowest, 'stepping below the smallest supported degree is a no-op');
  check(reduce(up, { type: 'setExDegree' }) === up && reduce(up, { type: 'setExDegree', degree: 'x' }) === up,
        'setExDegree without a valid target is a no-op');
  const abs = reduce(initialState, { type: 'setExDegree', degree: 99 });
  check(abs.exDegree === 24 && abs.src === hermite(24) && abs.busy, 'absolute degree clamps (ℚ: 24) and regenerates');
  // every example (random key included) regenerates when the stepper moves, in every field
  for (const m of MODES) for (const ex of examplesFor(m, 10)) {
    const s = reduce(inMode(m), { type: 'example', key: ex.key });
    check(exampleHeld(s) && s.exKey === ex.key, `${m}/${ex.key}: chip click holds the example`);
    const st = reduce(s, { type: 'setExDegree', delta: 1 });
    const want = examplesFor(m, st.exDegree, st.exSeed, true).find(e => e.key === ex.key).src;
    check(st.exDegree !== s.exDegree && st.src === want && st.src !== s.src && st.busy && st.jobId === s.jobId + 1,
          `${m}/${ex.key}: stepping regenerates at degree ${st.exDegree}`);
    check(exampleHeld(st), `${m}/${ex.key}: still held after stepping`);
  }
  // the random chip draws a fresh key on every click and keeps it across stepping
  const r1 = reduce(inMode('p89'), { type: 'example', key: 'random' });
  const r2 = reduce(r1, { type: 'example', key: 'random' });
  check(r1.exSeed === 1 && r2.exSeed === 2 && r1.src !== r2.src && r2.exKey === 'random' && r2.busy, 'random key: every click reseeds');
  const r3 = reduce(r2, { type: 'setExDegree', delta: 1 });
  check(r3.exSeed === 2 && r3.src === examplesFor('p89', 11, 2, true)[0].src, 'stepping keeps the seed');
  const f1 = reduce(reduce(inMode('p89'), { type: 'example', key: 'fixed' }), { type: 'example', key: 'fixed' });
  check(f1.exSeed === 0 && f1.src === examplesFor('p89', 10, 0, true)[3].src, 'fixed key: clicking again reproduces the same polynomial');
  // typing custom text detaches the stepper from the example
  const typed = reduce(initialState, { type: 'setSrc', src: 'x^13 + x + 1' });
  check(typed.exKey === null && !exampleHeld(typed), 'setSrc clears exKey');
  const t2 = reduce(typed, { type: 'setExDegree', delta: 1 });
  check(t2.exDegree === 8 && t2.src === 'x^13 + x + 1' && !t2.busy && t2.jobId === typed.jobId,
        'stepping over custom text only changes the setting');
  const back = reduce(t2, { type: 'example', key: 'exp' });
  check(back.src === defaultExample('Q', 8, 0, true).src && back.exKey === 'exp' && back.busy,
        'chip click regenerates at the current degree');
  check(reduce(t2, { type: 'example', key: 'nope' }) === t2, 'unknown example key ignored');
  // after a mode switch with typed text the textarea holds foreign text: stepping must not overwrite it
  const sw = reduce(reduce(initialState, { type: 'setSrc', src: 'x^3 + 1' }), { type: 'setMode', mode: 'p89' });
  const st = reduce(sw, { type: 'setExDegree', delta: 1 });
  check(st.exDegree === 8 && st.src === sw.src && st.jobId === sw.jobId,
        "stepping after a mode switch doesn't overwrite typed text");
  // ... whereas a held example was regenerated in the new field, so stepping regenerates it again
  const swHeld = inMode('p89');
  const stHeld = reduce(swHeld, { type: 'setExDegree', delta: 1 });
  check(stHeld.src === defaultExample('p89', 11, 0, true).src && stHeld.busy, 'stepping after a held mode switch regenerates in the new field');

  // monic is an example-generation setting: held examples regenerate, custom text does not
  const q = reduce(inMode('Q'), { type: 'example', key: 'exp' });
  check(parsePoly(q.src).coeffs.at(-1).isOne(), 'monic selector is on by default for generated examples');
  const raw = reduce(q, { type: 'setExMonic', value: false });
  check(!raw.exMonic && raw.busy && raw.jobId === q.jobId + 1 &&
        raw.src === examplesFor('Q', 10, 0, false)[0].src && !parsePoly(raw.src).coeffs.at(-1).isOne(),
        'turning monic off regenerates and compiles the held example');
  const normalized = reduce(raw, { type: 'setExMonic' });
  check(normalized.exMonic && parsePoly(normalized.src).coeffs.at(-1).isOne(),
        'toggling monic back on normalizes the leading coefficient');
  const customMonic = reduce(typed, { type: 'setExMonic', value: false });
  check(!customMonic.exMonic && customMonic.src === typed.src && !customMonic.busy,
        'monic selector leaves custom text untouched');
  check(reduce(customMonic, { type: 'setExMonic', value: false }) === customMonic,
        'setting monic to its current value is a no-op');
}

// ---- URL-hash sharing (hashFromState / stateFromHash) ----------------------
{
  const s = run(withResult(inMode('gf64')), { type: 'setMethod', method: 'Horner' }, { type: 'setView', view: 'c' },
                { type: 'setForm', form: 'original' }, { type: 'setCstyle', cstyle: 'fraction' }, { type: 'setNumfmt', numfmt: 'decimal' });
  const typed = reduce(s, { type: 'setSrc', src: 'x^4 + x + 1' });
  const h = hashFromState(typed);
  check(h.startsWith('#src=x%5E4') && h.includes('&deg=10') && h.includes('&mode=gf64') && h.includes('&numfmt=decimal') && !h.includes('seed='),
        'hash encodes src, mode, the clamped degree and the constant format (seed only when used)');
  const r = stateFromHash(initialState, h);
  eq([r.src, r.mode, r.method, r.view, r.form, r.cstyle, r.numfmt, r.exDegree, r.exKey, r.exSeed, r.exMonic],
     ['x^4 + x + 1', 'gf64', 'Horner', 'c', 'original', 'fraction', 'decimal', 10, null, 0, true], 'hash roundtrip restores every shared field');
  check(!r.busy && r.result === null && r.error === null && r.jobId === 0, 'hash seeds an idle state (the load auto-compile runs on it)');
  check(stateFromHash(initialState, '') === initialState && stateFromHash(initialState, '#') === initialState, 'empty hash → defaults');
  eq(stateFromHash(initialState, '#!!%%&==junk&deg=frog&seed=-1'), initialState, 'junk hash → defaults');
  eq(stateFromHash(initialState, '#mode=klingon&view=x&form=y&cstyle=z&numfmt=w&method='), initialState, 'invalid params ignored');
  check(stateFromHash(initialState, '#mode=Q&deg=99').exDegree === 24, 'deg clamps to the ℚ maximum');
  check(stateFromHash(initialState, '#mode=gf128&deg=14').exDegree === 14 && stateFromHash(initialState, '#mode=gf128&deg=40').exDegree === 26,
        'GF(2^k) deg: even degrees kept, clamped to the largest compiled degree');
  check(stateFromHash(initialState, '#deg=17').src === defaultExample('Q', 17, 0, true).src, "degree-only hash reseeds the field's default example at that degree");
  const m = stateFromHash(initialState, '#mode=p89&deg=20');
  check(m.mode === 'p89' && m.src === defaultExample('p89', 20).src && m.exKey === 'dense', 'src-less hash seeds the dense example');
  for (const [legacy, id] of Object.entries(LEGACY_MODES))
    check(stateFromHash(initialState, `#mode=${legacy}&deg=20`).mode === id, `legacy mode ${legacy} → ${id}`);
  check(stateFromHash(initialState, '#mode=mersenne&src=x%5E3%2B1').src === 'x^3+1', 'legacy Mersenne link keeps its source');
  const g = stateFromHash(initialState, hashFromState(reduce(initialState, { type: 'setExDegree', delta: 1 })));
  check(g.exDegree === 8 && g.exKey === 'hermite' && g.src === examplesFor('Q', 8).find(e => e.key === 'hermite').src, 'shared example round-trips with exKey');
  // a shared random key carries its seed, so the stepper still regenerates it
  const rk = run(inMode('p89'), { type: 'example', key: 'random' }, { type: 'example', key: 'random' }, { type: 'example', key: 'random' });
  const rh = hashFromState(rk);
  check(rh.includes('&seed=3'), 'hash carries the seed of a random key');
  const rr = stateFromHash(initialState, rh);
  check(rr.exSeed === 3 && rr.exKey === 'random' && rr.src === rk.src && exampleHeld(rr), 'shared random key round-trips as a held example');
  const rs = reduce(rr, { type: 'setExDegree', delta: 1 });
  check(rs.src === examplesFor('p89', 11, 3, true)[0].src, 'the stepper regenerates the shared random key at the new degree');
  const unmonic = reduce(initialState, { type: 'setExMonic', value: false });
  const ur = stateFromHash(initialState, hashFromState(unmonic));
  check(!ur.exMonic && hashFromState(unmonic).includes('&monic=0'), 'Share links preserve an unselected monic toggle');
}

// ---- field registry → chooser ----------------------------------------------
{
  check(FIELDS === REGISTRY, 'uistate re-exports the js/field.js registry');
  const groupIds = FIELD_GROUPS.map(g => g.id);
  check(FIELDS.every(f => typeof f.id === 'string' && f.id && typeof f.label === 'string' && f.label && groupIds.includes(f.group)),
        'every registry field has id, label and a known group');
  eq(MODES, FIELD_IDS, 'MODES = the registry fields the pipeline compiles for (registry order)');
  check(MODES.every(id => id in MODE_MSG), 'MODES ⊆ MODE_MSG');
  eq(groupIds, ['exact', 'mersenne', 'binary'], 'three groups: exact (ℚ, ℝ together), Mersenne primes, binary fields');
  const ch = fieldChooser(initialState);
  eq(ch.map(g => g.id), groupIds.filter(g => FIELDS.some(f => f.group === g)), 'chooser lists the non-empty groups in order');
  eq(ch.flatMap(g => g.fields.map(f => f.id)), FIELD_GROUPS.flatMap(g => FIELDS.filter(f => f.group === g.id).map(f => f.id)),
     'chooser fields = registry fields, grouped');
  check(ch.every(g => typeof g.label === 'string' && g.label), 'each group carries a display label');
  check(ch.every(g => g.fields.every(f => typeof f.label === 'string' && typeof f.labelHtml === 'string' && typeof f.name === 'string' && typeof f.title === 'string' && f.title)),
        'each field carries label, labelHtml, name + title');
  const on = ch.flatMap(g => g.fields).filter(f => f.on);
  eq(on.map(f => f.id), ['Q'], 'exactly one field is on: the initial mode');
  eq(fieldChooser(inMode('Q')).flatMap(g => g.fields).filter(f => f.on).map(f => f.id), ['Q'], 'selection follows state.mode');
  const all = ch.flatMap(g => g.fields);
  eq(all.filter(f => f.enabled).map(f => f.id), MODES, 'enabled fields are exactly MODES');
  check(all.every(f => f.enabled), 'every registry field is selectable (no placeholders left)');
  check(all.every(f => f.title !== 'coming soon'), 'enabled fields keep their own title');
  for (const f of all) check(reduce(initialState, { type: 'setMode', mode: f.id }).mode === f.id, `setMode(${f.id}) selects the field`);
  const byGroup = Object.fromEntries(ch.map(g => [g.id, g.fields.map(f => f.label)]));
  eq(byGroup.exact, ['ℚ', 'ℝ'], 'exact group: ℚ and ℝ together (ℝ is the same exact preprocessing shown in doubles)');
  eq(byGroup.mersenne, ['2⁶¹−1', '2⁸⁹−1', '2¹²⁷−1'], 'Mersenne group: short labels, the caption supplies the GF(…) context');
  eq(byGroup.binary, ['GF(2³²)', 'GF(2⁶⁴)', 'GF(2¹²⁸)'], 'binary group');
  eq(ch.map(g => [g.label, g.fields.length]), [['exact', 2], ['Mersenne primes', 3], ['binary fields', 3]], 'group captions + sizes');
  check(ch.every(g => typeof g.title === 'string' && g.title.length > 0), 'each group caption carries a hover title');
  check(/rational/.test(ch[0].title) && /doubles/.test(ch[0].title), 'the exact group\'s title explains ℝ');
  check(all.every(f => f.label.length <= 8), `chooser labels are short: ${all.map(f => f.label).join(' ')}`);
  check(REGISTRY.filter(f => f.char === 'p').every(f => f.name === `GF(2^${f.bits}−1)` && f.labelHtml === `2<sup>${f.bits}</sup>−1`),
        'Mersenne fields keep their GF(2^k−1) name for results');
  eq(fieldChooser(inMode('R')).flatMap(g => g.fields).filter(f => f.on).map(f => f.id), ['R'], 'ℝ is selectable inside the exact group');
  check(/paper's experiments/.test(fieldTitle(REGISTRY.find(f => f.id === 'p89'))) && /paper's experiments/.test(fieldTitle(REGISTRY.find(f => f.id === 'gf64')))
        && !/paper's experiments/.test(fieldTitle(REGISTRY.find(f => f.id === 'p61'))), 'the paper\'s fields are marked in their titles');
  check(/≈ numeric/.test(fieldTitle(REGISTRY.find(f => f.id === 'R'))) && /exact rational preprocessing/.test(fieldTitle(REGISTRY.find(f => f.id === 'R'))),
        'ℝ title: exact preprocessing, reported as ≈ numeric');
  check((() => { try { fieldChooser(deepFreeze({ ...initialState })); return true; } catch { return false; } })(), 'fieldChooser is pure');
}

// ---- a field that cannot read the text (fractions in GF(2^k)) ---------------
{
  // the ℚ examples carry fractions; read as binary-field polynomials they must fail
  // with a message a person can act on — not BigInt's "Cannot convert 1/3628800 to a BigInt"
  for (const ex of examplesFor('Q', 10)) {
    let msg = null;
    try { parsePoly(ex.src, { char2: true }); } catch (e) { msg = e.message; }
    if (ex.key === 'hermite')       // integers with signs: the objection is the minus, not a fraction
      check(msg !== null && /no negatives/.test(msg), `${ex.key} over GF(2^k): readable message (${msg})`);
    else
    check(msg !== null && !/BigInt|Cannot convert/.test(msg) && /fraction/.test(msg) && /ℚ/.test(msg) && /bit pattern/.test(msg) && /"\d+\/\d+"/.test(msg),
          `${ex.key} over GF(2^k): readable message (${msg})`);
  }
  let msg = null;
  try { parsePoly('0.5x^3 + x', { char2: true }); } catch (e) { msg = e.message; }
  check(msg !== null && /"0.5" is a decimal/.test(msg) && !/BigInt/.test(msg), `decimal over GF(2^k): ${msg}`);
  msg = null; try { parsePoly('2e3x + 1', { char2: true }); } catch (e) { msg = e.message; }
  check(msg !== null && !/BigInt|Cannot convert/.test(msg), `exponent literal over GF(2^k): ${msg}`);
  msg = null; try { parsePoly('x^3 - x', { char2: true }); } catch (e) { msg = e.message; }
  check(msg !== null && /−1 = 1/.test(msg), `minus over GF(2^k): ${msg}`);
  check(parsePoly('0xdeadx^2 + 0x1e', { char2: true }).coeffs[0] === 0x1en, 'hex literals containing an e digit still parse in GF(2^k)');
  check(parsePoly('1/2x^2 + 0.5x + 2e1', { char2: false }).coeffs[1].eq(new Rat(1n, 2n)), 'the same literals read fine in characteristic 0');
  // the worker's failure reply is what the page shows, verbatim; the stale output is dropped
  const s = reduce(reduce(withResult(inMode('Q')), { type: 'setSrc', src: examplesFor('Q', 10)[0].src }), { type: 'setMode', mode: 'gf64' });
  check(s.busy && s.mode === 'gf64' && s.result !== null, 'switching field recompiles the fractional text over GF(2^64)');
  const bad = 'cannot read the polynomial over GF(2^64): binary-field coefficients are bit patterns (integers or 0x… hex), but "1/3628800" is a fraction — choose ℚ, ℝ or a Mersenne-prime field for it, or rewrite the polynomial';
  const e = reduce(s, { type: 'reply', id: s.jobId, ok: false, message: bad });
  check(e.error === bad && e.result === null && !e.busy && !showOutput(e), 'the failure reply is shown as the error, the stale output dropped');
  const back = reduce(e, { type: 'setMode', mode: 'Q' });
  check(back.error === null && back.busy && back.src === examplesFor('Q', 10)[0].src, 'switching back to ℚ clears the message and recompiles the same text');
}

// ---- input tokenizer (highlight backdrop) ----------------------------------
{
  const join = toks => toks.map(t => t.text).join('');
  const types = toks => toks.map(t => `${t.type}:${t.text}`);
  const srcs = ['1/2x^2 + 0x1f*x - 3', ' x^13 +  X\n- 7/3', '', '0xdeadbeef', 'x^^2 ?? 1e5', examplesFor('Q', 10)[0].src,
                ...examplesFor('gf64', 13).map(e => e.src), ...examplesFor('p89', 20).map(e => e.src)];
  for (const s of srcs) check(join(tokenizePoly(s)) === s, `tokens concatenate back: ${JSON.stringify(s.slice(0, 40))}`);
  eq(types(tokenizePoly('1/2x^2 + 0x1f*x - 3')),
     ['num:1/2', 'var:x^2', 'space: ', 'op:+', 'space: ', 'num:0x1f', 'op:*', 'var:x', 'space: ', 'op:-', 'space: ', 'num:3'],
     'fractions, powers, hex, operators');
  eq(types(tokenizePoly('X^3-x')), ['var:X^3', 'op:-', 'var:x'], 'upper-case variable, no spaces');
  eq(types(tokenizePoly('0x1f')), ['num:0x1f'], 'the x inside a hex literal is not a variable');
  eq(types(tokenizePoly('2 x ^ 2')), ['num:2', 'space: ', 'var:x', 'space: ', 'op:^', 'space: ', 'num:2'], 'spaced caret stays an operator');
  eq(types(tokenizePoly('ab ?? 1')), ['text:ab', 'space: ', 'text:??', 'space: ', 'num:1'], 'unknown characters merge into plain text runs');
  eq(tokenizePoly(''), [], 'empty input has no tokens');
  const many = tokenizePoly(examplesFor('p89', 63)[2].src);
  check(many.filter(t => t.type === 'var').length === 63 && many.filter(t => t.type === 'num').length >= 60, 'dense degree-63 example: 63 powers, 60+ numbers');
  check(!tokenizePoly('1/2x^2').some(t => t.type === 'text'), 'valid syntax produces no plain-text tokens');
  check(!tokenizePoly(examplesFor('gf64', 13)[0].src).some(t => t.type === 'text'), 'hex key polynomials produce no plain-text tokens');
}

// ---- the numeric methods in their own worker --------------------------------
{
  eq(compileMessages(inMode('Q')).map(m => m.part), ['main', 'numeric'], 'ℚ compiles in two workers');
  eq(compileMessages(inMode('R')).map(m => m.part), ['main', 'numeric'], 'ℝ compiles in two workers');
  eq(compileMessages(inMode('gf64')).map(m => m.part), ['main'], 'GF(2^k) needs only the main worker');
  eq(compileMessages(inMode('p89')).map(m => m.part), ['main'], 'Mersenne needs only the main worker');
  const pend = name => ({ name, ok: false, pending: true, note: 'computing…' });
  const MAIN = deepFreeze({ ...RESULT, comparisons: [row('Horner'), row('Estrin'), pend('Knuth–Eve'), pend('Pan')] });
  const NUMERIC = deepFreeze({ comparisons: [row('Knuth–Eve', { exact: false }), { name: 'Pan', ok: false, note: 'degree too low' }] });
  const started = reduce(inMode('Q'), { type: 'compile' });          // job 2
  const main = reduce(started, { type: 'reply', id: started.jobId, part: 'main', ok: true, result: MAIN });
  check(!main.busy && main.result === MAIN && methodTabs(main).find(t => t.key === 'Pan').pending && methodTabs(main).find(t => t.key === 'Pan').enabled,
        'the main reply lands with the numeric rows pending (and selectable)');
  eq(comparisonTable(main).filter(r => r.pending).map(r => r.name), ['Knuth–Eve', 'Pan'], 'pending rows in the table');
  const onPan = reduce(main, { type: 'setMethod', method: 'Pan' });
  check(onPan.method === 'Pan' && pendingRow(onPan)?.name === 'Pan' && selectedRow(onPan) === null && paneContent(onPan).kind === 'pending' &&
        stats(onPan).length === 0, 'a pending method can be selected: the pane shows it is computing, no stats');
  const filled = reduce(onPan, { type: 'reply', id: started.jobId, part: 'numeric', ok: true, result: NUMERIC });
  check(!filled.result.comparisons.some(r => r.pending) && comparisonRow({ ...filled, method: 'Knuth–Eve' })?.exact === false &&
        filled.result.comparisons.find(r => r.name === 'Pan').note === 'degree too low' && filled.result.comparisons[0] === MAIN.comparisons[0],
        'the numeric reply fills the placeholders and keeps the other rows');
  check(filled.method === 'Pan' && paneContent(filled) !== null && paneContent(filled).kind !== 'pending' && selectedRow(filled) === filled.result,
        'a selected method that turned out unavailable falls through to ours in the pane');
  check(reduce(main, { type: 'reply', id: started.jobId - 1, part: 'numeric', ok: true, result: NUMERIC }) === main, 'a stale numeric reply is ignored');
  const failedNum = reduce(main, { type: 'reply', id: started.jobId, part: 'numeric', ok: false, message: 'boom' });
  eq(failedNum.result.comparisons.slice(2).map(r => [r.ok, r.note]), [[false, 'boom'], [false, 'boom']], 'a failed numeric worker leaves explained rows');
  // numeric first, main second: the rows wait in lateNumeric
  const early = reduce(started, { type: 'reply', id: started.jobId, part: 'numeric', ok: true, result: NUMERIC });
  check(early.busy && JSON.stringify(early.lateNumeric) === JSON.stringify(NUMERIC.comparisons) && early.result === started.result, 'an early numeric reply waits for the main one');
  const early2 = reduce(reduce(started, { type: 'reply', id: started.jobId, part: 'numeric', ok: true, result: { comparisons: [NUMERIC.comparisons[0]] } }),
                        { type: 'reply', id: started.jobId, part: 'numeric', ok: true, result: { comparisons: [NUMERIC.comparisons[1]] } });
  check(early2.lateNumeric.length === 2 && !reduce(early2, { type: 'reply', id: started.jobId, part: 'main', ok: true, result: MAIN }).result.comparisons.some(r => r.pending),
        'per-method numeric replies accumulate while waiting');
  const one = reduce(main, { type: 'reply', id: started.jobId, part: 'numeric', ok: true, result: { comparisons: [NUMERIC.comparisons[0]] } });
  check(one.result.comparisons[2].ok && one.result.comparisons[3].pending, 'a per-method numeric reply fills only its row');
  const both = reduce(early, { type: 'reply', id: started.jobId, part: 'main', ok: true, result: MAIN });
  check(!both.busy && both.lateNumeric === null && !both.result.comparisons.some(r => r.pending) && both.result.comparisons[2].exact === false,
        'the main reply merges the waiting numeric rows');
  check(reduce(early, { type: 'cancel' }).lateNumeric === null, 'cancel drops waiting numeric rows');
  check(methodAvailable(MAIN, 'Pan') && !methodAvailable(NUMERIC.comparisons && { comparisons: NUMERIC.comparisons }, 'Pan'), 'pending counts as available; a failed row does not');
}

// ---- boot state per layout, and what the panes render from ----------------
{
  check(initialStateFor() === initialState && initialStateFor({ compact: false }) === initialState, 'desktop boots on initialState');
  const c = initialStateFor({ compact: true });
  check(c.mode === COMPACT_MODE && c.exDegree === COMPACT_DEGREE && c.exMonic && c.exKey === 'exp' &&
        c.src === defaultExample(COMPACT_MODE, COMPACT_DEGREE, 0, true).src && Object.isFrozen(c),
        'phones boot on the ℚ e^x example at the compact degree, monic');
  check(exampleHeld(c) && c.result === null && !c.busy && c.view === 'math', 'the compact boot state is a held example with the default view');
  const q = { ...withResult(initialState), mode: 'Q' };
  check(presentedState(q) === q && presentedState(q, { compact: true }) === q, 'exact rows are presented as they are');
  const ke = reduce(q, { type: 'setMethod', method: 'Estrin' });     // the fixture's inexact row
  check(presentedState(ke, { compact: true }).numfmt === 'decimal' && presentedState(ke).numfmt === 'exact',
        'phones present an inexact row with readable constants; desktop does not');
  const r = { ...q, mode: 'R' };
  check(presentedState(r, { compact: true }).numfmt === 'decimal', 'phones present ℝ with readable constants');
  const already = { ...ke, numfmt: 'decimal' };
  check(presentedState(already, { compact: true }) === already, 'an explicit readable choice is left alone');
}

console.log(fails ? `UISTATE FAILED (${fails}/${checks})` : `UISTATE PASSES (${checks} checks)`);
process.exit(fails ? 1 : 0);
