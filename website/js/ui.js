// Page UI as a Preact app (vendored preact + htm, no build step).
//
// Every control is rendered from the single state object in uistate.js
// (pure reducer + selectors), so the field chooser, method chips, comparison
// table, view tabs, sub-options and the pane can never disagree.  This file
// owns only the markup and the side effects: the Web Workers that keep
// unbounded exact-rational preprocessing off the UI thread — a main worker
// for our chain and the classical methods, and over ℚ / ℝ / ℂ a second one for
// the numeric methods (Knuth–Eve, Pan; Belaga over ℂ), whose rows arrive later and show as
// spinners meanwhile.  Workers are created lazily and terminated in exactly
// one place: the effect keyed on state.jobId, which runs whenever the reducer
// retires a job id — a new job, Cancel, a failed compile — and drops the
// workers still computing the old one (a computation cannot be interrupted
// otherwise); the action wrappers never second-guess the reducer.  Also the
// timers that make compilation automatic — the initial example compiles on
// load, a mode switch recompiles immediately (the reducer starts that job
// itself), and edits recompile after DEBOUNCE_MS of no typing — plus the
// clipboard behind Copy / Share, the URL hash (stateFromHash seeds the boot
// state; Share rewrites the hash in place with history.replaceState; a
// hashchange after boot — a share link pasted into a tab already on the site,
// Back — dispatches 'restore') and the scroll sync of the input's highlight
// backdrop.  The worker posts every variant up front, so switching views /
// methods / constant formats never recompiles.
//
// Stale-while-revalidate: the last output stays mounted and dims — the pane,
// the method chips, the comparison table and the phone stats line all carry
// the `stale` class (uistate.isStale) — while a job runs, while a parse error
// stands over it, after a Cancel (a status note says so until the next job),
// and while the selected numeric method is still computing but a previous
// chain of it exists (uistate.staleRow); the pending spinner pane appears only
// when there is nothing to show.  A Cancel button accompanies every running
// job: in the status row while no output is mounted yet, in the pane's action
// corner otherwise.
//
// Two layouts render the same state (App → DesktopLayout | CompactLayout;
// style.css shares the breakpoint COMPACT_QUERY):
//   desktop  ONE card: heading row (label + example chips + monic + degree
//            stepper + Share) → the polynomial input → field pill groups (from
//            the js/field.js registry) → method chips → error → view
//            tabs attached to the output pane; the comparison table below.
//   phones   a short intro with Paper / GitHub links, then three cards: the
//            input (three chips beside the label, Field / Method dropdowns),
//            the output (underline tabs, a Copy + Share row at the top of the
//            pane — static, so it never covers an equation — no Download,
//            numeric constants to six digits, a stats line) and a collapsed
//            "Compare methods" disclosure.  Boot state:
//            uistate.initialStateFor({ compact: true }).
//
// Every control is a real <button> (chips, pills, sub-options, tabs, rows via
// tabindex) with its state in ARIA: aria-pressed on toggles and pills, the view
// switcher as a complete tab widget (role=tablist, tabs with aria-controls and
// a roving tabindex moved by the arrow keys, the pane as their tabpanel),
// role=group labels on the pill rows, two always-mounted polite live regions —
// the error line and a job status line ("compiling…", "compilation
// cancelled …") — sr-only headings and a table caption for landmark
// navigation.  Decorative spinners are aria-hidden; the text beside them says
// "computing".
import { html, render, useReducer, useState, useEffect, useMemo, useRef } from './vendor/preact-htm.module.js';
import { highlightC } from './highlight.js';
import { cBundleArchive, hasCBundle } from './cbundle.js';
import { fetchStars } from './github-stars.js';
import { toggleTheme, label as labelThemeToggle } from './theme.js';
import { chainMathRows, renderLatex } from './mathview.js';
import {
  reduce, initialStateFor, presentedState, stateFromHash, hashFromState, VIEWS, examplesFor,
  exampleDegree, stepDegree, showOutput, compileMessages, methodTabs, comparisonTable,
  subOptionStrips, paneContent, fieldChooser, tokenizePoly, stats, staleRow, isStale, inputHint,
  hasPending,
} from './uistate.js';
// dependency-free: the page thread never loads the compilers (they run in the workers)
import { numericMethodsFor, REL_ERROR_WARN } from './methodlist.js';
import { PAPER_URL, PAPER_TITLE, referenceFor } from './references.js';

const DEBOUNCE_MS = 500;   // quiet time after an edit before the chain recompiles
const COPIED_MS = 1200;    // how long Copy / Share show their transient "copied"
const COMPACT_QUERY = '(max-width: 640px)';
const COMPACT_CHIPS = 3;   // example chips shown beside the label on phones

const VIEW_LABEL = { math: 'mathematical', c: 'C code', graph: 'graph' };
const VIEW_LABEL_COMPACT = { math: 'Math', c: 'C code', graph: 'Graph' };
// the phone Method dropdown has ~100px of text: short names keep the count visible
const SHORT_METHOD = { 'This paper': 'Paper', 'Rabin–Winograd': 'R–W', 'Knuth–Eve': 'K–E' };

const isCompact = () => typeof matchMedia === 'function' && matchMedia(COMPACT_QUERY).matches;

// ---- hooks -----------------------------------------------------------------

/** True while the media query matches (re-renders on resize / rotation). */
function useMediaQuery(query) {
  const mq = useMemo(() => (typeof matchMedia === 'function' ? matchMedia(query) : null), [query]);
  const [matches, setMatches] = useState(!!mq?.matches);
  useEffect(() => {
    if (!mq) return undefined;
    const on = e => setMatches(e.matches);
    mq.addEventListener('change', on);
    setMatches(mq.matches);
    return () => mq.removeEventListener('change', on);
  }, [mq]);
  return matches;
}

/** The GitHub star count once fetched (null until then / when unavailable). */
function useStars() {
  const [stars, setStars] = useState(null);
  useEffect(() => {
    let live = true;
    fetchStars().then(count => { if (live) setStars(count); });
    return () => { live = false; };
  }, []);
  return stars;
}

/** Transient "copied" flag for Copy / Share (persistent state stays in the reducer). */
function useCopied() {
  const [copied, setCopied] = useState(false);
  const flash = () => { setCopied(true); setTimeout(() => setCopied(false), COPIED_MS); };
  return [copied, flash];
}

// ---- small helpers ---------------------------------------------------------

/** Clipboard write with an execCommand fallback for clipboard-less contexts. */
function copyText(text) {
  if (navigator.clipboard?.writeText)
    return navigator.clipboard.writeText(text).catch(() => execCopy(text));
  return Promise.resolve().then(() => execCopy(text));
}
function execCopy(text) {
  const ta = document.createElement('textarea');
  ta.value = text;
  ta.style.cssText = 'position:fixed;opacity:0';
  document.body.appendChild(ta);
  ta.select();
  try { document.execCommand('copy'); } finally { ta.remove(); }
}

/** One trusted, generated TeX fragment. KaTeX supplies accessible MathML;
 *  `fallback` remains visible if the runtime or a particular render fails. */
function Typeset({ tex, fallback = tex, className = null }) {
  const markup = useMemo(() => renderLatex(tex), [tex]);   // unchanged rows cost nothing per render
  return markup
    ? html`<span class=${className} dangerouslySetInnerHTML=${{ __html: markup }} />`
    : html`<span class=${className}>${fallback}</span>`;
}

function ExampleLabel({ example }) {
  return example.labelTex
    ? html`<${Typeset} tex=${example.labelTex} fallback=${example.label} />`
    : example.label;
}

/** Typeset a registry label: `^k` exponents and Unicode superscript runs
 *  ("GF(2^64)", "GF(2⁶⁴)") both become real superscripts. */
const SUP_DIGITS = '⁰¹²³⁴⁵⁶⁷⁸⁹';
function fieldLabel(label) {
  const plain = label.replace(/[⁰¹²³⁴⁵⁶⁷⁸⁹]+/g, run => '^' + [...run].map(c => SUP_DIGITS.indexOf(c)).join(''));
  const out = [];
  const re = /\^(\d+)/g;
  let last = 0, m;
  while ((m = re.exec(plain))) {
    if (m.index > last) out.push(plain.slice(last, m.index));
    out.push(html`<sup key=${m.index}>${m[1]}</sup>`);
    last = m.index + m[0].length;
  }
  if (last < plain.length) out.push(plain.slice(last));
  return out;
}

/** Dropdown text of a registry field: the exact fields say what they are. */
function fieldOptionLabel(f) {
  if (f.id === 'Q') return 'ℚ  rational';
  if (f.id === 'R') return 'ℝ  real (doubles)';
  if (f.id === 'C') return 'ℂ  complex';
  return f.name;
}

/** "5 multiplications (1 scalar) · 11 additions · mult. depth 4[ · ≈ constants
 *  rounded to doubles]" for the compact output card: the paper's words, and
 *  the shown row's own reason for being inexact (never a hard-coded one). */
function statsLine(state) {
  const s = stats(state);
  if (!s.length) return '';
  const get = label => s.find(x => x.label === label)?.value;
  // the multiplications value is "5" or "5 (1 scalar)": the noun goes after the count
  const parts = [String(get('multiplications')).replace(/^(\d+)/, '$1 multiplications'), `${get('additions')} additions`];
  if (get('mult. depth') !== undefined && get('mult. depth') !== null) parts.push(`mult. depth ${get('mult. depth')}`);
  if (get('exact') !== 'yes') parts.push(`≈ ${shortExactNote(comparisonTable(state).find(r => r.on)?.exactNote)}`);
  return parts.join(' · ');
}

/** A row's exactNote in a few words: "constants rounded to doubles" /
 *  "constants exceed the double range" / "real roots (numeric)" — the
 *  measured error is dropped (the table shows it) and the exact-preprocessing
 *  clause too; a missing note reads "numeric". */
function shortExactNote(note) {
  if (!note) return 'numeric';
  const dbl = /rounded to (complex doubles|doubles)/.exec(note);
  if (dbl) return `constants rounded to ${dbl[1]}`;
  if (/exceed the double range/.test(note)) return 'constants exceed the double range';
  return note.replace(/,?\s*max rel\. error \S+\s*$/, '').trim() || 'numeric';
}

/** The fixed one-line description of a method (references.js), for tooltips. */
const blurbOf = key => referenceFor(key)?.blurb ?? null;

/** Copy hands out ASCII: the chain grammar writes U+2212 for a binary minus and
 *  U+00B7 for a scaled wire, which Python and C reject when pasted (the same
 *  rewrite cgen.js applies to the P(x) header).  Display and tests keep the text. */
const asciiChain = text => text.replace(/−/g, '-').replace(/·/g, '*');

/** The measured rounding error for the table's exact column. */
const fmtRelError = err => (Number.isFinite(err) ? err.toExponential(1) : 'overflow');

// ---- the app: state, worker, timers ---------------------------------------

function App() {
  const compact = useMediaQuery(COMPACT_QUERY);
  // the layout at boot picks the initial example; location.hash then seeds the
  // state (pure helper; junk falls back to the defaults)
  const [state, dispatch] = useReducer(reduce, initialStateFor({ compact: isCompact() }),
    s => stateFromHash(s, location.hash));
  const workersRef = useRef({});          // part ('main' | 'numeric') -> Worker
  const runningRef = useRef({});          // part -> true while a job is in flight there
  const repliesLeftRef = useRef({});      // part -> replies the running job still owes (numeric: one per method)
  const stateRef = useRef(state);          // latest state, for timer callbacks
  stateRef.current = state;
  const postedSrcRef = useRef(null);       // src of the most recently posted job
  const editedSinceRef = useRef(false);    // an edit since the last job was posted (or cancelled)

  const dropWorker = part => { workersRef.current[part]?.terminate(); delete workersRef.current[part]; runningRef.current[part] = false; };
  const ensureWorker = part => {
    if (!workersRef.current[part]) {
      const w = new Worker(new URL('worker.js', import.meta.url), { type: 'module' });
      w.onmessage = e => {                 // the part is idle only after its job's LAST reply (stale ids never flip the flag;
        if (e.data.id === stateRef.current.jobId &&   // the reducer drops them too); a numeric ok:false reply is that worker's only one
            (!e.data.ok || --repliesLeftRef.current[part] <= 0)) runningRef.current[part] = false;
        dispatch({ type: 'reply', ...e.data });
      };
      w.onerror = e => {
        dropWorker(part);
        if (part === 'main') dispatch({ type: 'workerError', message: `worker failed to load: ${e.message ?? e}` });
        else dispatch({ type: 'reply', id: stateRef.current.jobId, part, ok: false, message: `worker failed to load: ${e.message ?? e}` });
      };
      workersRef.current[part] = w;
    }
    return workersRef.current[part];
  };

  const compileNow = () => dispatch({ type: 'compile' });   // the reducer skips blank input

  // The job id changed: the reducer retired the previous job (a new one started,
  // Cancel, or a failed compile), so the workers still computing it are
  // terminated here — the one place that happens — and, when a job was
  // started, each part is posted to its (fresh or idle) worker.  The posted
  // source is remembered as it is even when the job ends without a result: a
  // pending debounce must not re-run a compile that just failed, and after a
  // Cancel the debounce recompiles on `state.cancelled` instead (below).
  useEffect(() => {
    for (const part of Object.keys(runningRef.current)) if (runningRef.current[part]) dropWorker(part);
    if (!state.busy) return;
    postedSrcRef.current = state.src;
    editedSinceRef.current = false;
    for (const m of compileMessages(state)) {
      ensureWorker(m.part).postMessage(m);
      runningRef.current[m.part] = true;
      repliesLeftRef.current[m.part] = m.part === 'numeric' ? numericMethodsFor(state.mode).length : 1;
    }
  }, [state.jobId]);

  // Auto-compile edits after DEBOUNCE_MS of no typing (the cleanup resets the
  // timer on every keystroke).  Blank input and text whose job was already
  // posted (an example click, a mode switch, an earlier flush) start nothing —
  // unless that job was cancelled: then any edit made after the cancel, an
  // edit-and-revert included, compiles the text the mounted output does not
  // answer (a timer armed before the cancel must not restart the job).
  useEffect(() => {
    const t = setTimeout(() => {
      const s = stateRef.current;
      if (s.src.trim() && (s.src !== postedSrcRef.current || (s.cancelled && editedSinceRef.current))) compileNow();
    }, DEBOUNCE_MS);
    return () => clearTimeout(t);
  }, [state.src]);

  // First visit: the initial example compiles with no interaction.
  useEffect(() => { compileNow(); }, []);

  // A hash change after boot (a share link pasted into this tab, Back) rebuilds
  // the state from the URL, as a fresh load would; Share itself uses
  // history.replaceState, which fires no hashchange.
  useEffect(() => {
    const on = () => dispatch({ type: 'restore', hash: location.hash, compact: isCompact() });
    addEventListener('hashchange', on);
    return () => removeEventListener('hashchange', on);
  }, []);

  // Everything the controls can do: plain dispatches — the reducer alone
  // decides whether an action starts a job (the effect above then handles the workers).
  const actions = {
    runExample: key => dispatch({ type: 'example', key }),
    setMode: mode => dispatch({ type: 'setMode', mode }),
    toggleMonic: () => dispatch({ type: 'setExMonic' }),
    stepDeg: delta => dispatch({ type: 'setExDegree', delta }),
    setSrc: e => { editedSinceRef.current = true; dispatch({ type: 'setSrc', src: e.currentTarget.value }); },
    onKeyDown: e => {                      // Cmd/Ctrl+Enter skips the debounce
      if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) { e.preventDefault(); compileNow(); }
    },
  };

  const Layout = compact ? CompactLayout : DesktopLayout;
  return html`<${Layout} state=${state} dispatch=${dispatch} actions=${actions} />`;
}

// ---- layouts ---------------------------------------------------------------

function DesktopLayout({ state, dispatch, actions }) {
  const tabs = methodTabs(state);
  const out = showOutput(state);
  const stale = isStale(state);
  const extras = html`<${DegreeControls} state=${state} actions=${actions} /><${ShareButton} state=${state} />`;
  return html`<${InputCard} state=${state} actions=${actions} extras=${extras}
      chips=${examplesFor(state.mode, state.exDegree, state.exSeed, state.exMonic)}>
      <${FieldPills} state=${state} setMode=${actions.setMode} />
      ${tabs.length > 0 && html`<${MethodPills} tabs=${tabs} stale=${stale} dispatch=${dispatch} />`}
      <${Status} state=${state} dispatch=${dispatch} />
      ${out && html`<${Output} key="out" state=${state} dispatch=${dispatch} />`}
    <//>
    <div>${out && html`<${FooterBar} key="foot" state=${state} stale=${stale} dispatch=${dispatch} />`}</div>`;
}

function CompactLayout({ state, dispatch, actions }) {
  const tabs = methodTabs(state);
  const out = showOutput(state);
  const stale = isStale(state);
  const chips = examplesFor(state.mode, state.exDegree, state.exSeed, state.exMonic).slice(0, COMPACT_CHIPS);
  // the output renders the presented state (readable constants); Share links
  // the state as chosen, so a presentation-only format never travels in a link
  return html`<${CompactIntro} />
    <${InputCard} state=${state} actions=${actions} chips=${chips}>
      <${FieldMethodPickers} state=${state} tabs=${tabs} stale=${stale} setMode=${actions.setMode} dispatch=${dispatch} />
      <${Status} state=${state} dispatch=${dispatch} />
    <//>
    ${out && html`<div class="card out-card">
      <${Output} key="out" state=${presentedState(state, { compact: true })} shareState=${state} dispatch=${dispatch} compact />
      <div class=${stale ? 'stats-line stale' : 'stats-line'} id="stats-line">${statsLine(state)}</div>
    </div>`}
    ${out && html`<details class="card cmp-card" id="cmp-card"><summary>Compare methods</summary>
      <${FooterBar} key="foot" state=${state} stale=${stale} dispatch=${dispatch} />
    </details>`}`;
}

// ---- the input card and its controls --------------------------------------

/** The card with the heading row (label, example chips, `extras`), the
 *  polynomial input, and whatever the layout puts below (`children`). */
function InputCard({ state, actions, chips, extras = null, children }) {
  return html`<div class="card" id="main">
    <h2 class="sr-only">Your polynomial</h2>
    <div class="head-row">
      <label class="head" for="poly-in">Your polynomial</label>
      <span class="ex-row">
        <span class="examples" id="examples" role="group" aria-label="examples">
          ${chips.map(ex => html`<button type="button" key=${ex.key} class="chip"
            data-ex=${ex.key} title=${ex.title || null} onClick=${() => actions.runExample(ex.key)}
            ><${ExampleLabel} example=${ex} /></button>`)}
        </span>
        ${extras}
      </span>
    </div>
    <${PolyInput} src=${state.src} invalid=${state.error !== null} onKeyDown=${actions.onKeyDown} onInput=${actions.setSrc} />
    ${inputHint(state) !== null && html`<div class="input-hint" id="input-hint">${inputHint(state)}</div>`}
    ${children}
  </div>`;
}

/** Desktop only: the monic toggle and the − N + degree stepper for the chips.
 *  At either end of the field's range (stepDegree is a fixed point there) the
 *  button is aria-disabled — still focusable, so its tooltip says why — and
 *  style.css dims it; a click on it is the reducer's no-op. */
function DegreeControls({ state, actions }) {
  const d = exampleDegree(state);
  const atMin = stepDegree(state.mode, d, -1) === d, atMax = stepDegree(state.mode, d, +1) === d;
  return html`<button id="monic" class=${`monic-toggle${state.exMonic ? ' on' : ''}`}
      aria-pressed=${state.exMonic}
      title="generate examples with leading coefficient 1 (a non-monic input costs one extra scalar multiplication)"
      onClick=${actions.toggleMonic}>monic</button>
    <span class="degree" id="degree">
      <button type="button" id="deg-minus" aria-label="decrease degree" aria-disabled=${atMin}
        title=${atMin ? `degree ${d} is the smallest example degree` : 'lower example degree'}
        onClick=${atMin ? null : () => actions.stepDeg(-1)}>−</button>
      <span class="deg-n">degree ${d}</span>
      <button type="button" id="deg-plus" aria-label="increase degree" aria-disabled=${atMax}
        title=${atMax ? `degree ${d} is the largest example degree in this field` : 'raise example degree'}
        onClick=${atMax ? null : () => actions.stepDeg(+1)}>+</button>
    </span>`;
}

/** A control row: the pills, then a small-caps legend to their right — shown
 *  only while it fits on the pills' line (seven method chips over ℂ fill the
 *  card; a legend wrapping under them read as a stray word). Measured with a
 *  ResizeObserver; where none exists (tests) the legend simply stays. */
function PillRow({ id, legend, children }) {
  const rowRef = useRef(null), lblRef = useRef(null), lblWidth = useRef(0);
  const [fits, setFits] = useState(true);
  useEffect(() => {
    const row = rowRef.current, lbl = lblRef.current;
    if (!row || !lbl || typeof ResizeObserver === 'undefined') return undefined;
    const measure = () => {
      if (lbl.offsetWidth) lblWidth.current = lbl.offsetWidth;       // remember it while visible
      const pills = [...row.children].filter(el => el !== lbl).reduce((w, el) => w + el.offsetWidth, 0);
      const gap = parseFloat(getComputedStyle(row).columnGap) || 0;
      setFits(pills + gap + lblWidth.current <= row.clientWidth);
    };
    const ro = new ResizeObserver(measure);
    ro.observe(row);
    for (const el of row.children) ro.observe(el);
    measure();
    return () => ro.disconnect();
  });
  return html`<div class="controls" id=${id} ref=${rowRef}>
    ${children}
    <span class=${fits ? 'lbl' : 'lbl tight'} ref=${lblRef} aria-hidden=${!fits}>${legend}</span>
  </div>`;
}

/** The field chooser: one pill group per registry group, FIELD legend to the right. */
function FieldPills({ state, setMode }) {
  return html`<${PillRow} id="field-row" legend="Field">
    <div class="field-groups" id="mode" role="group" aria-label="Field">
      ${fieldChooser(state).map(g => html`<div class="seg" key=${g.id} data-group=${g.id}>
        ${g.fields.map(f => html`<button type="button" key=${f.id} data-mode=${f.id} title=${f.title || null}
          aria-label=${f.name} aria-pressed=${!!f.on}
          class=${f.on ? 'on' : null} disabled=${!f.enabled}
          onClick=${f.enabled ? () => setMode(f.id) : null}>${fieldLabel(f.label)}</button>`)}
      </div>`)}
    </div>
  <//>`;
}

/** The method chips (bold reserve keeps their width stable), METHOD legend to
 *  the right; dimmed with the output (`stale`) — still clickable, since
 *  switching method is how the previous result is inspected meanwhile. */
function MethodPills({ tabs, stale = false, dispatch }) {
  return html`<${PillRow} id="method-row" legend="Method">
    <div class=${stale ? 'seg methods stale' : 'seg methods'} id="methods" role="group" aria-label="Method">
      ${tabs.map(t => t.enabled
    ? html`<button type="button" key=${t.key} data-m=${t.key} data-label=${t.label} class=${[t.on && 'on', t.pending && 'pending'].filter(Boolean).join(' ') || null}
            aria-pressed=${!!t.on} title=${t.pending ? t.title || 'computing\u2026' : blurbOf(t.key)}
            onClick=${() => dispatch({ type: 'setMethod', method: t.key })}><span>${t.label}${t.pending && html`<${Spinner} />`}</span></button>`
    : html`<button type="button" key=${t.key} data-label=${t.label} disabled title=${t.title || null}><span>${t.label}</span></button>`)}
    </div>
  <//>`;
}

/** A method chip's label for the phone dropdown: "Paper (5)", "R–W (5)",
 *  "K–E (5)", and "Pan …" while computing (the count is the payload; the
 *  dropdown ellipsizes anything longer). */
function compactMethodLabel(t) {
  const name = t.key === 'ours' ? 'This paper' : t.key;
  const label = t.label.startsWith(name) ? (SHORT_METHOD[name] ?? name) + t.label.slice(name.length) : t.label;
  return t.pending ? `${label} \u2026` : label;
}

/** Phones: the same field and method choices as two labelled dropdowns (the
 *  Method one dims with the output it describes). */
function FieldMethodPickers({ state, tabs, stale = false, setMode, dispatch }) {
  return html`<div class="pickers" id="pickers">
    <label class="picker"><span class="lbl">Field</span>
      <select id="mode-select" value=${state.mode} onChange=${e => setMode(e.currentTarget.value)}>
        ${fieldChooser(state).map(g => html`<optgroup key=${g.id} label=${g.label}>
          ${g.fields.map(f => html`<option key=${f.id} value=${f.id} disabled=${!f.enabled}>${fieldOptionLabel(f)}</option>`)}
        </optgroup>`)}
      </select></label>
    ${tabs.length > 0 && html`<label class=${stale ? 'picker stale' : 'picker'} id="method-picker"><span class="lbl">Method</span>
      <select id="method-select" value=${state.method}
        onChange=${e => dispatch({ type: 'setMethod', method: e.currentTarget.value })}>
        ${tabs.map(t => html`<option key=${t.key} value=${t.key} disabled=${!t.enabled}>${compactMethodLabel(t)}</option>`)}
      </select></label>`}
  </div>`;
}

/** Two live regions that stay mounted (empty when silent), so screen readers
 *  announce what appears in them: the error line, and the job status line —
 *  while a job runs with no output mounted yet (the first load, a share link, a
 *  mode switch after an error) a busy row with Cancel, since there is nothing
 *  else to show and nothing to shift; after a Cancel the note that the mounted
 *  output is not the current input's, until the next job starts.  Once an
 *  output exists a running job dims it instead (stale-while-revalidate) and
 *  Cancel sits in the pane's action corner (Pane): a row here would shift the
 *  layout and flicker on every quick recompile. */
const CANCELLED_NOTE = 'compilation cancelled — press ⌘/Ctrl+Enter or edit to run it again';
function Status({ state, dispatch }) {
  const busyRow = state.busy && !showOutput(state);
  return html`<div id="error" role="status" aria-live="polite">${state.error !== null ? state.error : ''}</div>
    <div id="job-status" class=${state.cancelled ? 'job-status cancelled' : 'job-status'} role="status" aria-live="polite">
      ${busyRow ? html`<span class="busy-row" id="busy"><${Spinner} /> compiling\u2026 <${CancelButton} dispatch=${dispatch} /></span>`
      : state.cancelled ? CANCELLED_NOTE : ''}</div>`;
}

/** Cancel the running job: the reducer retires it, the job effect terminates its workers. */
const CancelButton = ({ dispatch }) => html`<button class="cancel" id="cancel" type="button"
  title="stop the running compilation" onClick=${() => dispatch({ type: 'cancel' })}>Cancel</button>`;

/** Phone header under the title: a short intro and the Paper / GitHub (with
 *  star count) links; the desktop intro and paper card are hidden.  (htm drops
 *  a line break between text and an inline tag, so " <b>" stays on one line.) */
function CompactIntro() {
  const stars = useStars();
  return html`<div class="intro-compact">
    <p class="sub">Horner's rule evaluates a degree-<i>n</i> polynomial with <i>n</i> multiplications
      (<span class="nowrap"><i>n</i>−1</span> if it is monic). Preprocess the coefficients once and <b><span class="nowrap">⌊<i>n</i>/2⌋+1</span> suffice for any monic polynomial</b>, one more for a
      general one — for approximating functions like exp, sin and cos, or for the polynomials of
      hashing, cryptography and coding theory. Type a polynomial, pick a field, and read off the
      evaluation chain.</p>
    <nav class="quick-links" aria-label="paper and source">
      <a href=${PAPER_URL} target="_blank" rel="noopener noreferrer" title=${PAPER_TITLE}>
        <svg class="doc-icon" viewBox="0 0 24 24" width="20" height="20" aria-hidden="true" fill="none"
          stroke="currentColor" stroke-width="1.5" stroke-linejoin="round">
          <path d="M5.5 2.5h9l4 4v15h-13z" /><path d="M14.5 2.5v4h4" />
          <path stroke-width="1.2" stroke-linecap="round" d="M8.5 11h7M8.5 14.5h7M8.5 18h4.5" />
        </svg>Paper</a>
      <a href="https://github.com/thomasahle/fast-polynomials" target="_blank" rel="noopener noreferrer"
        aria-label=${stars !== null ? `fast-polynomials on GitHub (${stars} stars)` : 'fast-polynomials on GitHub'}>
        <svg viewBox="0 0 24 24" width="18" height="18" aria-hidden="true" fill="currentColor">
          <path d=${GITHUB_MARK} />
        </svg>GitHub
        ${stars !== null && html`<span class="stars">
          <svg viewBox="0 0 16 16" width="13" height="13" aria-hidden="true" fill="currentColor"><path d=${STAR_MARK} /></svg>
          ${new Intl.NumberFormat().format(stars)}</span>`}</a>
      <${ThemeToggle} />
    </nav>
  </div>`;
}

/** Day / night button (phones); the desktop header has the static twin in index.html. */
function ThemeToggle() {
  const ref = useRef(null);
  useEffect(() => { if (ref.current) labelThemeToggle(ref.current); }, []);
  return html`<button class="theme-toggle" type="button" ref=${ref} data-theme-toggle onClick=${toggleTheme}>
    <svg class="sun" viewBox="0 0 24 24" width="16" height="16" aria-hidden="true" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"><circle cx="12" cy="12" r="4" /><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4" /></svg>
    <svg class="moon" viewBox="0 0 24 24" width="16" height="16" aria-hidden="true" fill="none" stroke="currentColor" stroke-width="2" stroke-linejoin="round"><path d="M20.5 14.5A8.5 8.5 0 0 1 9.5 3.5a8.5 8.5 0 1 0 11 11z" /></svg>
  </button>`;
}

// the GitHub mark and star, as in the desktop header (index.html)
const GITHUB_MARK = 'M12 .7a11.3 11.3 0 0 0-3.6 22c.6.1.8-.2.8-.6v-2.2c-3.4.7-4.1-1.4-4.1-1.4-.5-1.4-1.3-1.8-1.3-1.8-1.1-.7.1-.7.1-.7 1.2.1 1.8 1.2 1.8 1.2 1.1 1.8 2.8 1.3 3.5 1 .1-.8.4-1.3.8-1.6-2.7-.3-5.5-1.3-5.5-5.6 0-1.2.4-2.3 1.2-3.1-.1-.3-.5-1.6.1-3.1 0 0 1-.3 3.1 1.2a10.7 10.7 0 0 1 5.7 0c2.2-1.5 3.1-1.2 3.1-1.2.6 1.5.2 2.8.1 3.1.8.8 1.2 1.9 1.2 3.1 0 4.3-2.8 5.3-5.5 5.6.4.4.8 1.1.8 2.2v3.3c0 .4.2.7.8.6A11.3 11.3 0 0 0 12 .7Z';
const STAR_MARK = 'M8 .25a.75.75 0 0 1 .673.418l1.882 3.815 4.21.612a.75.75 0 0 1 .416 1.279l-3.046 2.97.719 4.192a.75.75 0 0 1-1.088.791L8 12.347l-3.766 1.98a.75.75 0 0 1-1.088-.79l.72-4.194L.818 6.374a.75.75 0 0 1 .416-1.28l4.21-.611L7.327.668A.75.75 0 0 1 8 .25Z';

/** Share: the URL hash encodes the state; the link is copied to the clipboard.
 *  The address bar is updated in place (no history entry, no hashchange). */
function ShareButton({ state }) {
  const [copied, flash] = useCopied();
  const share = () => {
    const url = new URL(location.href);
    url.hash = hashFromState(state);
    history.replaceState(null, '', url.hash);
    copyText(url.href).then(flash);
  };
  return html`<button type="button" class="share" id="share" title="copy a link to this chain" onClick=${share}>
    <svg viewBox="0 0 24 24" width="14" height="14" aria-hidden="true" fill="none"
      stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
      <path d="M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71" />
      <path d="M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71" />
    </svg>
    ${copied ? 'copied' : 'Share'}</button>`;
}

/** The polynomial input: a transparent textarea over a highlighted backdrop
 *  (same font, padding and wrapping; scroll-synced), so numbers and x-powers
 *  are coloured while the textarea keeps native editing.  The backdrop ends in
 *  a newline + zero-width space so a trailing empty line keeps its height. */
function PolyInput({ src, invalid = false, onInput, onKeyDown }) {
  const hlRef = useRef(null), taRef = useRef(null);
  const sync = () => {
    const h = hlRef.current, t = taRef.current;
    if (!h || !t) return;
    // grow to fit the polynomial (up to half the viewport; beyond that it scrolls)
    t.style.minHeight = '';
    t.style.minHeight = `${Math.min(t.scrollHeight + 2, Math.round(innerHeight * 0.5))}px`;
    h.scrollTop = t.scrollTop; h.scrollLeft = t.scrollLeft;
  };
  useEffect(sync);   // after every render too: a programmatic value change may move the scroll
  return html`<div class="poly-edit">
    <pre class="poly-hl" aria-hidden="true" ref=${hlRef}>${tokenizePoly(src).map(t =>
    t.type === 'num' ? html`<span class="in-num">${t.text}</span>`
      : t.type === 'var' ? html`<span class="in-var">${t.text}</span>`
        : t.text)}${'\n​'}</pre>
    <textarea id="poly-in" ref=${taRef} spellcheck=${false} autocomplete="off" autocorrect="off"
      autocapitalize="off" aria-invalid=${invalid || null} aria-describedby=${invalid ? 'error' : null}
      value=${src} onInput=${onInput} onKeyDown=${onKeyDown} onScroll=${sync}></textarea>
  </div>`;
}

// ---- the output: view tabs, pane, comparison table ------------------------

/** View tabs (+ the sub-option strips: form and constant format in the math
 *  view, constant style in the ℚ C view) attached to the pane.  Phones hide
 *  the constants strip (presentedState decides the format there).  The tabs
 *  are a complete tab widget: each controls the pane (its tabpanel), only the
 *  selected one is in the Tab order, and Left / Right / Home / End move the
 *  selection and the focus (the roving tabindex of the ARIA tabs pattern).
 *  `shareState` is the state Share links — the un-presented one on phones. */
function Output({ state, shareState = null, dispatch, compact = false }) {
  const strips = subOptionStrips(state).filter(sub => !compact || sub.kind !== 'numfmt');
  const labels = compact ? VIEW_LABEL_COMPACT : VIEW_LABEL;
  const tabsRef = useRef(null);
  const onTabKey = e => {
    const i = VIEWS.indexOf(state.view), n = VIEWS.length;
    const next = e.key === 'ArrowRight' ? VIEWS[(i + 1) % n] : e.key === 'ArrowLeft' ? VIEWS[(i + n - 1) % n]
      : e.key === 'Home' ? VIEWS[0] : e.key === 'End' ? VIEWS[n - 1] : null;
    if (!next) return;
    e.preventDefault();
    dispatch({ type: 'setView', view: next });
    tabsRef.current?.querySelector(`[data-view="${next}"]`)?.focus();   // focus follows the selection
  };
  // dimmed while the shown chain is not (yet) the one for the current input
  const stale = isStale(state);
  return html`<div class=${stale ? 'out stale' : 'out'} id="out">
    <h2 class="sr-only">Evaluation chain</h2>
    <div class="viewbar">
      <div class="views" id="view" role="tablist" aria-label="output view" ref=${tabsRef} onKeyDown=${onTabKey}>
        ${VIEWS.map(v => html`<button type="button" key=${v} id=${`tab-${v}`} data-view=${v} role="tab"
          aria-selected=${v === state.view} aria-controls="pane" tabindex=${v === state.view ? 0 : -1}
          class=${v === state.view ? 'on' : null}
          onClick=${() => dispatch({ type: 'setView', view: v })}>${labels[v]}</button>`)}
      </div>
      <div class="subopts" id="view-sub">
        ${strips.map(sub => html`<span class="strip" key=${sub.kind} data-strip=${sub.kind} role="group" aria-label=${sub.label}>
          <span class="lbl" aria-hidden="true">${sub.label}</span>
          ${sub.options.map(o => html`<button type="button" key=${o.key} data-opt=${o.key} title=${o.title || null}
            aria-pressed=${!!o.on} disabled=${!o.enabled} class=${o.on ? 'on' : null}
            onClick=${o.enabled ? () => dispatch({ type: 'setSubOption', key: o.key }) : null}>${o.label}</button>`)}
        </span>`)}
      </div>
    </div>
    <${Pane} content=${paneContent(state)} state=${state} shareState=${shareState} dispatch=${dispatch} compact=${compact} />
  </div>`;
}

/** The comparison table: one row per method; the selected method's row is
 *  bold and clicking a row selects it, like its chip.  Each method name links
 *  to its reference (numbered as in the list under the table); its cell's
 *  tooltip says what the method is (references.js).  A ≈ numeric row shows
 *  the measured max relative rounding error beside the mark (flagged above
 *  REL_ERROR_WARN, and "overflow" when no double chain exists).  Under the
 *  table a caption explains the columns and the rows' notes are listed in
 *  full, so nothing is hover-only. */
function FooterBar({ state, stale = false, dispatch }) {
  const rows = comparisonTable(state);
  const mults = r => (r.scalar ? `${r.mults} (${r.scalar} scalar)` : r.mults);
  const refs = rows.filter(r => r.ref).map(r => r.ref);
  const refNo = r => refs.indexOf(r.ref) + 1;
  const exactCell = r => html`<td key="ex" title=${r.exactNote || null}
      class=${r.maxRelError !== null && r.maxRelError > REL_ERROR_WARN ? 'warn' : null}>${r.exact ? 'yes' : '≈ numeric'}${
        r.maxRelError !== null && html` <span class="rel-err" title=${`measured max relative error of the double-precision chain: ${fmtRelError(r.maxRelError)}`}>${fmtRelError(r.maxRelError)}</span>`}</td>`;
  // each ran method's own note (its inexact reason when it has no other)
  const notes = rows.filter(r => r.ok && (r.note || r.exactNote)).map(r => ({ key: r.key, name: r.name, text: r.note || r.exactNote }));
  // rows select their method from the keyboard too (Enter / Space), like the chips
  const select = key => dispatch({ type: 'setMethod', method: key });
  const onRowKey = key => e => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); select(key); } };
  return html`<div class=${stale ? 'foot stale' : 'foot'} id="footer-stats">
    <div class="cmp-wrap"><table class="cmp" id="compare">
      <caption class="sr-only">Comparison of evaluation methods (select a row to show its chain)</caption>
      <thead><tr>
        <th class="m">method</th>
        <th title="multiplications in total (scalar ones, by a constant, in parentheses)"><span class="full">multiplications</span><span class="abbr" aria-hidden="true">mult.</span></th>
        <th title="additions (integer multiples charged as additions)"><span class="full">additions</span><span class="abbr" aria-hidden="true">add.</span></th>
        <th title="multiplicative depth: the longest chain of multiplications"><span class="full">mult. depth</span><span class="abbr" aria-hidden="true">depth</span></th>
        <th title="exact preprocessing, or numeric (≈)">exact</th>
      </tr></thead>
      <tbody>${rows.map(r => html`<tr key=${r.key} data-m=${r.key}
          class=${r.on ? 'on' : r.ok ? null : 'off'} title=${r.ok ? null : r.note}
          tabindex=${r.ok ? 0 : null} aria-selected=${r.ok ? !!r.on : null}
          onClick=${r.ok ? () => select(r.key) : null} onKeyDown=${r.ok ? onRowKey(r.key) : null}>
        <td class="m" title=${blurbOf(r.key)}>${r.ref
      ? html`<a class="ref" href=${r.ref.url ?? `#ref-${refNo(r)}`} title=${r.ref.cite}
            target=${r.ref.url ? '_blank' : null} rel=${r.ref.url ? 'noopener noreferrer' : null}
            onClick=${e => e.stopPropagation()}>${r.name}</a><sup class="ref-no">${refNo(r)}</sup>`
      : r.name}</td>
        ${r.ok
      ? [html`<td key="mu">${mults(r)}</td>`, html`<td key="ad">${r.adds}</td>`,
      html`<td key="de">${r.height ?? '—'}</td>`, exactCell(r)]
      : r.pending ? html`<td colspan="4" class="na pending"><${Spinner} /> computing the numerical preprocessing\u2026</td>`
      : html`<td colspan="4" class="na">— <span class="why">${r.note}</span></td>`}
      </tr>`)}</tbody>
    </table>
    <p class="cmp-caption" id="cmp-caption">Counts are for the chain shown: <i>scalar</i> multiplications are
      by a constant (a leading-coefficient scale included); integer multiples are charged as additions; <i>mult. depth</i> is
      the longest chain of multiplications. ≈ numeric: the chain constants are rounded to doubles, or the
      preprocessing itself is numeric — the figure is the measured max relative error.</p>
    ${notes.length > 0 && html`<ul class="cmp-notes" id="cmp-notes">
      ${notes.map(n => html`<li key=${n.key}><b>${n.name}</b> — ${n.text}</li>`)}
    </ul>`}
    <ol class="refs" id="references" aria-label="references">
      ${refs.map((ref, i) => html`<li key=${i} id=${`ref-${i + 1}`}>${ref.url
        ? html`<a href=${ref.url} target="_blank" rel="noopener noreferrer">${ref.cite}</a>`
        : ref.cite}</li>`)}
    </ol></div>
  </div>`;
}

/** Copy button pinned to the pane's top-right corner (math and C views); it
 *  copies exactly the text shown, readable constants included. */
function CopyButton({ text }) {
  const [copied, flash] = useCopied();
  return html`<button type="button" class="copy" id="copy" title="copy to clipboard"
    onClick=${() => copyText(text).then(flash)}>${copied ? 'copied' : 'Copy'}</button>`;
}

/** Download the selected source plus every C method and a comparison harness. */
function DownloadButton({ state }) {
  const [busy, setBusy] = useState(false);
  const download = async () => {
    if (busy) return;
    setBusy(true);
    try {
      const { name, blob } = await cBundleArchive(state);
      const url = URL.createObjectURL(blob), a = document.createElement('a');
      a.href = url; a.download = name; a.style.display = 'none';
      document.body.appendChild(a); a.click(); a.remove();
      setTimeout(() => URL.revokeObjectURL(url), 1000);
    } finally { setBusy(false); }
  };
  return html`<button type="button" class="download" id="download"
    title="download this source, all C methods, and benchmark scripts" disabled=${busy}
    onClick=${download}>${busy ? 'packing…' : 'Download'}</button>`;
}

/** The pane below the view bar — the tabpanel of the view tabs, keyed per kind
 *  so switching kinds remounts the element.  Download is withheld while the
 *  pane shows a numeric method's previous chain (staleRow): the archive is
 *  built from the current result, and a stale selected.c would not match it. */
function Pane({ content, state, shareState = null, dispatch, compact }) {
  // Copy receives ASCII for the chain grammar (asciiChain); the C source already is
  const text = content?.kind === 'math' ? asciiChain(content.text)
    : content?.kind === 'c' ? content.code
      : content?.kind === 'c-missing' ? asciiChain(`${content.note}\n\n${content.text}`) : null;
  // phones: Share sits here beside Copy (no Download) in a static row above the
  // pane body (style.css), never over an equation; desktop keeps Share in the head row
  return html`<div class="pane-wrap" id="pane" role="tabpanel" aria-labelledby=${`tab-${state.view}`} tabindex="0">
    ${(text !== null || compact || state.busy) && html`<div class="pane-actions">
      ${state.busy && html`<${CancelButton} dispatch=${dispatch} />`}
      ${text !== null && html`<${CopyButton} text=${text} />`}
      ${!compact && hasCBundle(state) && staleRow(state) === null && !hasPending(state.result) && html`<${DownloadButton} state=${state} />`}
      ${compact && html`<${ShareButton} state=${shareState ?? state} />`}
    </div>`}
    ${paneBody(content)}
  </div>`;
}

function paneBody(content) {
  switch (content?.kind) {
    case 'pending':
      return html`<div class="chain pending-pane" id="chain" key="pending" role="status"><${Spinner} /> ${content.note}</div>`;
    case 'math':
      return html`<${MathChain} text=${content.text} />`;
    case 'c':
      return html`<pre class="chain code" id="chain" key="c"
        dangerouslySetInnerHTML=${{ __html: highlightC(content.code) }} />`;
    case 'c-missing':
      return html`<pre class="chain code" id="chain" key="c-missing"><span class="none">${content.note}</span>${'\n\n' + content.text}</pre>`;
    case 'graph':
      return html`<${GraphPane} key="graph" svg=${content.svg} dash=${content.dash} kx=${content.kx} />`;
    case 'graph-missing':
      return [
        html`<div class="graph-pane" id="graph" key="graph"><div class="none">${content.note}</div></div>`,
        html`<${Legend} key="legend" />`,
      ];
    default:
      return null;
  }
}

/** The plain-text chain rendered as an equals-aligned mathematical display.
 *  Copy receives the same text from Pane, in ASCII (asciiChain). */
function MathChain({ text }) {
  if (!globalThis.katex) return html`<pre class="chain" id="chain" key="math">${text}</pre>`;
  const rows = chainMathRows(text);
  let lastEquation = -1;
  rows.forEach((row, i) => { if (row.kind === 'equation') lastEquation = i; });
  return html`<div class="chain math-chain" id="chain" key="math"
    role="region" aria-label="mathematical evaluation chain">
    <table class="math-table"><tbody>
      ${rows.map((row, i) => {
        if (row.kind === 'heading') return html`<tr class="math-section" key=${i}>
          <th colspan="3"><span class="math-section-rule"></span>
            <${Typeset} tex=${row.tex} fallback=${row.text} />
            <span class="math-section-rule"></span></th></tr>`;
        if (row.kind === 'note') return html`<tr class="math-note" key=${i}>
          <td colspan="3">${row.text}</td></tr>`;
        if (row.kind === 'gap') return html`<tr class="math-gap" aria-hidden="true" key=${i}>
          <td colspan="3"></td></tr>`;
        return html`<tr class=${i === lastEquation ? 'math-equation result' : 'math-equation'} key=${i}>
          <td class="math-lhs"><${Typeset} tex=${row.lhsTex} fallback=${row.lhs} /></td>
          <td class="math-rel"><${Typeset} tex="=" fallback="=" /></td>
          <td class="math-rhs"><${Typeset} tex=${row.rhsTex} fallback=${row.expression} />
            ${row.annotation && html`<span class="math-annotation">${row.annotation}</span>`}</td>
        </tr>`;
      })}
    </tbody></table>
  </div>`;
}

/** A small ring beside text that says "computing": decorative for assistive tech
 *  (a bare span cannot carry a name; the pending pane / busy row are role=status). */
const Spinner = () => html`<span class="spinner" aria-hidden="true" />`;

/** The circuit SVG in a sideways-scrolling pane.  The worker emits it at its
 *  natural width (12px labels); a graph up to FIT_RATIO times the pane's width
 *  shrinks to fit (class `fit`: labels stay ≥ 9px) so the output node P is in
 *  view; a wider one keeps its size and scrolls, with a right-edge fade while
 *  more of it lies beyond the edge (class `more`) and a legend note saying so —
 *  iOS hides the scrollbar until touched.  Measured with a ResizeObserver;
 *  without one (tests) the pane simply scrolls. */
const FIT_RATIO = 1.35;
function GraphPane({ svg, dash, kx }) {
  const ref = useRef(null);
  const natural = useMemo(() => Number(/<svg[^>]*\swidth="(\d+(?:\.\d+)?)"/.exec(svg)?.[1]) || 0, [svg]);
  const [fit, setFit] = useState(false);
  const [scroll, setScroll] = useState({ overflow: false, atEnd: true });
  const measure = () => {
    const el = ref.current;
    if (!el) return;
    setFit(natural > el.clientWidth && natural <= FIT_RATIO * el.clientWidth);
    setScroll({ overflow: el.scrollWidth > el.clientWidth + 1, atEnd: el.scrollLeft + el.clientWidth >= el.scrollWidth - 1 });
  };
  useEffect(() => {
    const el = ref.current;
    if (!el || typeof ResizeObserver === 'undefined') return undefined;
    const ro = new ResizeObserver(measure);
    ro.observe(el);
    measure();
    return () => ro.disconnect();
  }, [svg, natural, fit]);   // `fit` changes the scroll width: measure again once applied
  const more = scroll.overflow && !scroll.atEnd;
  return html`<div class=${more ? 'graph-pane-wrap more' : 'graph-pane-wrap'}>
      <div class=${fit ? 'graph-pane fit' : 'graph-pane'} id="graph" ref=${ref} onScroll=${measure}
        dangerouslySetInnerHTML=${{ __html: svg }} />
    </div>
    <${Legend} dash=${dash} kx=${kx} scrolls=${scroll.overflow} />`;
}

// only the edge decorations that actually occur in the shown graph are listed
const Legend = ({ dash, kx, scrolls = false }) => html`<div class="graph-legend" id="graph-legend">
  <span><i class="lg-mul">×</i> multiplication</span>
  <span><i class="lg-add">+</i> addition</span>
  <span><i class="lg-const">c</i> constant</span>
  ${dash ? html`<span><i class="lg-dash"></i> subtracted input</span>` : null}
  ${kx ? html`<span><i class="lg-k">k×</i> integer multiple</span>` : null}
  ${scrolls ? html`<span class="lg-scroll" id="graph-scroll-cue">wider than the pane — scroll sideways →</span>` : null}
</div>`;

render(html`<${App} />`, document.getElementById('app'));
