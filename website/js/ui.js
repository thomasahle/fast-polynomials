// Page UI as a Preact app (vendored preact + htm, no build step).
//
// Every control is rendered from the single state object in uistate.js
// (pure reducer + selectors), so the field chooser, method chips, comparison
// table, view tabs, sub-options and the pane can never disagree.  This file
// owns only the markup and the side effects: the Web Worker that keeps
// unbounded exact-rational preprocessing off the UI thread (created lazily,
// terminated on Cancel and whenever a newer job supersedes a running one), the
// timers that make compilation automatic — the initial example compiles on
// load, a mode switch recompiles immediately (the reducer starts that job
// itself), and edits recompile after DEBOUNCE_MS of no typing — plus the
// clipboard behind Copy / Share, the boot-time URL-hash seeding
// (stateFromHash) and the scroll sync of the input's highlight backdrop.  The
// worker posts every variant up front, so switching views / methods /
// constant formats never recompiles.
//
// Two layouts render the same state (App → DesktopLayout | CompactLayout;
// style.css shares the breakpoint COMPACT_QUERY):
//   desktop  ONE card: heading row (label + example chips + monic + degree
//            stepper + Share) → the polynomial input → field pill groups (from
//            the js/field.js registry) → method chips → busy / error → view
//            tabs attached to the output pane; the comparison table below.
//   phones   a short intro with Paper / GitHub links, then three cards: the
//            input (three chips beside the label, Field / Method dropdowns),
//            the output (underline tabs, Copy + Share floating in the pane,
//            no Download, numeric constants to six digits, a stats line) and
//            a collapsed "Compare methods" disclosure.  Boot state:
//            uistate.initialStateFor({ compact: true }).
import { html, render, useReducer, useState, useEffect, useMemo, useRef } from './vendor/preact-htm.module.js';
import { highlightC } from './highlight.js';
import { cBundleArchive, hasCBundle } from './cbundle.js';
import { fetchStars } from './github-stars.js';
import { toggleTheme, label as labelThemeToggle } from './theme.js';
import { chainMathRows, renderLatex } from './mathview.js';
import {
  reduce, initialStateFor, presentedState, stateFromHash, hashFromState, VIEWS, examplesFor,
  exampleHeld, exampleDegree, showOutput, compileMessage, methodTabs, comparisonTable,
  subOptionStrips, paneContent, fieldChooser, tokenizePoly, stats,
} from './uistate.js';

const DEBOUNCE_MS = 500;   // quiet time after an edit before the chain recompiles
const COPIED_MS = 1200;    // how long Copy / Share show their transient "copied"
const COMPACT_QUERY = '(max-width: 640px)';
const COMPACT_CHIPS = 3;   // example chips shown beside the label on phones

const VIEW_LABEL = { math: 'mathematical', c: 'C code', graph: 'graph' };
const VIEW_LABEL_COMPACT = { math: 'Math', c: 'C code', graph: 'Graph' };

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
  const markup = renderLatex(tex);
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
  return f.name;
}

/** "6 mul · 13 add · depth 5" for the compact output card. */
function statsLine(state) {
  const s = stats(state);
  if (!s.length) return '';
  const get = label => s.find(x => x.label === label)?.value;
  const parts = [`${get('multiplications')} mul`, `${get('additions')} add`];
  if (get('mult. depth') !== undefined && get('mult. depth') !== null) parts.push(`depth ${get('mult. depth')}`);
  if (get('exact') !== 'yes') parts.push('≈ numeric');
  return parts.join(' · ');
}

// ---- the app: state, worker, timers ---------------------------------------

function App() {
  const compact = useMediaQuery(COMPACT_QUERY);
  // the layout at boot picks the initial example; location.hash then seeds the
  // state (pure helper; junk falls back to the defaults)
  const [state, dispatch] = useReducer(reduce, initialStateFor({ compact: isCompact() }),
    s => stateFromHash(s, location.hash));
  const workerRef = useRef(null);
  const stateRef = useRef(state);          // latest state, for timer callbacks
  stateRef.current = state;
  const postedSrcRef = useRef(null);       // src of the most recently posted job

  const dropWorker = () => { workerRef.current?.terminate(); workerRef.current = null; };
  const ensureWorker = () => {
    if (!workerRef.current) {
      const w = new Worker(new URL('worker.js', import.meta.url), { type: 'module' });
      w.onmessage = e => dispatch({ type: 'reply', ...e.data });   // stale ids are dropped by the reducer
      w.onerror = e => {
        dropWorker();
        dispatch({ type: 'workerError', message: `worker failed to load: ${e.message ?? e}` });
      };
      workerRef.current = w;
    }
    return workerRef.current;
  };

  const abandonJob = () => { if (stateRef.current.busy) dropWorker(); };
  const compileNow = () => {               // immediate compile, superseding any running job
    if (!stateRef.current.src.trim()) return;
    abandonJob();
    dispatch({ type: 'compile' });
  };

  // A new job id means a job was started: post it (the reducer already set busy).
  useEffect(() => {
    if (state.busy) { postedSrcRef.current = state.src; ensureWorker().postMessage(compileMessage(state)); }
  }, [state.jobId]);

  // Auto-compile edits after DEBOUNCE_MS of no typing (the cleanup resets the
  // timer on every keystroke).  Blank input and text whose job was already
  // posted (an example click, a mode switch, an earlier flush) start nothing.
  useEffect(() => {
    const t = setTimeout(() => {
      const s = stateRef.current;
      if (s.src.trim() && s.src !== postedSrcRef.current) compileNow();
    }, DEBOUNCE_MS);
    return () => clearTimeout(t);
  }, [state.src]);

  // First visit: the initial example compiles with no interaction.
  useEffect(() => { compileNow(); }, []);

  // Everything the controls can do; a running job is abandoned only when the
  // action will start a new one (the reducer's conditions, mirrored here).
  const actions = {
    cancel: () => { dropWorker(); dispatch({ type: 'cancel' }); },
    runExample: key => { abandonJob(); dispatch({ type: 'example', key }); },
    setMode: mode => { abandonJob(); dispatch({ type: 'setMode', mode }); },
    toggleMonic: () => { if (exampleHeld(stateRef.current)) abandonJob(); dispatch({ type: 'setExMonic' }); },
    stepDeg: delta => { if (exampleHeld(stateRef.current)) abandonJob(); dispatch({ type: 'setExDegree', delta }); },
    setSrc: e => dispatch({ type: 'setSrc', src: e.currentTarget.value }),
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
  const extras = html`<${DegreeControls} state=${state} actions=${actions} /><${ShareButton} state=${state} />`;
  return html`<${InputCard} state=${state} actions=${actions} extras=${extras}
      chips=${examplesFor(state.mode, state.exDegree, state.exSeed, state.exMonic)}>
      <${FieldPills} state=${state} setMode=${actions.setMode} />
      ${tabs.length > 0 && html`<${MethodPills} tabs=${tabs} dispatch=${dispatch} />`}
      <${Status} state=${state} cancel=${actions.cancel} />
      ${out && html`<${Output} key="out" state=${state} dispatch=${dispatch} />`}
    <//>
    <div>${out && html`<${FooterBar} key="foot" state=${state} dispatch=${dispatch} />`}</div>`;
}

function CompactLayout({ state, dispatch, actions }) {
  const tabs = methodTabs(state);
  const out = showOutput(state);
  const chips = examplesFor(state.mode, state.exDegree, state.exSeed, state.exMonic).slice(0, COMPACT_CHIPS);
  return html`<${CompactIntro} />
    <${InputCard} state=${state} actions=${actions} chips=${chips}>
      <${FieldMethodPickers} state=${state} tabs=${tabs} setMode=${actions.setMode} dispatch=${dispatch} />
      <${Status} state=${state} cancel=${actions.cancel} />
    <//>
    ${out && html`<div class="card out-card">
      <${Output} key="out" state=${presentedState(state, { compact: true })} dispatch=${dispatch} compact />
      <div class="stats-line" id="stats-line">${statsLine(state)}</div>
    </div>`}
    ${out && html`<details class="card cmp-card" id="cmp-card"><summary>Compare methods</summary>
      <${FooterBar} key="foot" state=${state} dispatch=${dispatch} />
    </details>`}`;
}

// ---- the input card and its controls --------------------------------------

/** The card with the heading row (label, example chips, `extras`), the
 *  polynomial input, and whatever the layout puts below (`children`). */
function InputCard({ state, actions, chips, extras = null, children }) {
  return html`<div class="card" id="main">
    <div class="head-row">
      <label class="head" for="poly-in">Your polynomial</label>
      <span class="ex-row">
        <span class="examples" id="examples">
          ${chips.map(ex => html`<a key=${ex.key} class="chip"
            data-ex=${ex.key} title=${ex.title || null} onClick=${() => actions.runExample(ex.key)}
            ><${ExampleLabel} example=${ex} /></a>`)}
        </span>
        ${extras}
      </span>
    </div>
    <${PolyInput} src=${state.src} onKeyDown=${actions.onKeyDown} onInput=${actions.setSrc} />
    ${children}
  </div>`;
}

/** Desktop only: the monic toggle and the − N + degree stepper for the chips. */
function DegreeControls({ state, actions }) {
  return html`<button id="monic" class=${`monic-toggle${state.exMonic ? ' on' : ''}`}
      aria-pressed=${state.exMonic} title="normalize generated examples to leading coefficient 1"
      onClick=${actions.toggleMonic}>monic</button>
    <span class="degree" id="degree">
      <button id="deg-minus" title="lower example degree" onClick=${() => actions.stepDeg(-1)}>−</button>
      <span class="deg-n">degree ${exampleDegree(state)}</span>
      <button id="deg-plus" title="raise example degree" onClick=${() => actions.stepDeg(+1)}>+</button>
    </span>`;
}

/** The field chooser: one pill group per registry group, FIELD legend to the right. */
function FieldPills({ state, setMode }) {
  return html`<div class="controls" id="field-row">
    <div class="field-groups" id="mode">
      ${fieldChooser(state).map(g => html`<div class="seg" key=${g.id} data-group=${g.id}>
        ${g.fields.map(f => html`<button key=${f.id} data-mode=${f.id} title=${f.title || null}
          class=${f.on ? 'on' : null} disabled=${!f.enabled}
          onClick=${f.enabled ? () => setMode(f.id) : null}>${fieldLabel(f.label)}</button>`)}
      </div>`)}
    </div>
    <span class="lbl">Field</span>
  </div>`;
}

/** The method chips (bold reserve keeps their width stable), METHOD legend to the right. */
function MethodPills({ tabs, dispatch }) {
  return html`<div class="controls" id="method-row">
    <div class="seg methods" id="methods">
      ${tabs.map(t => t.enabled
    ? html`<button key=${t.key} data-m=${t.key} data-label=${t.label} class=${t.on ? 'on' : null}
            onClick=${() => dispatch({ type: 'setMethod', method: t.key })}><span>${t.label}</span></button>`
    : html`<button key=${t.key} data-label=${t.label} disabled title=${t.title || null}><span>${t.label}</span></button>`)}
    </div>
    <span class="lbl">Method</span>
  </div>`;
}

/** Phones: the same field and method choices as two labelled dropdowns. */
function FieldMethodPickers({ state, tabs, setMode, dispatch }) {
  return html`<div class="pickers" id="pickers">
    <label class="picker"><span class="lbl">Field</span>
      <select id="mode-select" value=${state.mode} onChange=${e => setMode(e.currentTarget.value)}>
        ${fieldChooser(state).map(g => html`<optgroup key=${g.id} label=${g.label}>
          ${g.fields.map(f => html`<option key=${f.id} value=${f.id} disabled=${!f.enabled}>${fieldOptionLabel(f)}</option>`)}
        </optgroup>`)}
      </select></label>
    ${tabs.length > 0 && html`<label class="picker"><span class="lbl">Method</span>
      <select id="method-select" value=${state.method}
        onChange=${e => dispatch({ type: 'setMethod', method: e.currentTarget.value })}>
        ${tabs.map(t => html`<option key=${t.key} value=${t.key} disabled=${!t.enabled}>${t.label}</option>`)}
      </select></label>`}
  </div>`;
}

/** The busy row (with Cancel) and the error line. */
function Status({ state, cancel }) {
  return html`${state.busy && html`<div class="controls"><span id="busy" style="color:var(--muted)">preprocessing…
      <button class="cancel" id="cancel" onClick=${cancel}>cancel</button></span></div>`}
    ${state.error !== null && html`<div id="error">${state.error}</div>`}`;
}

/** Phone header under the title: a short intro and the Paper / GitHub (with
 *  star count) links; the desktop intro and paper card are hidden. */
function CompactIntro() {
  const stars = useStars();
  return html`<div class="intro-compact">
    <p class="sub">Horner's rule evaluates a degree-<i>n</i> polynomial with <i>n</i> multiplications.
      Preprocess the coefficients once and about <b><i>n</i>/2</b> suffice — for approximating
      functions like exp, sin and cos, or for the polynomials of hashing, cryptography and
      coding theory. Type a polynomial, pick a field, and read off the evaluation chain.</p>
    <nav class="quick-links" aria-label="paper and source">
      <a href="https://arxiv.org/abs/submit/8036575" target="_blank" rel="noopener noreferrer"
        title="arXiv submission 8036575 (the permanent identifier follows on announcement)">
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

/** Share: the URL hash encodes the state; the link is copied to the clipboard. */
function ShareButton({ state }) {
  const [copied, flash] = useCopied();
  const share = () => {
    const url = new URL(location.href);
    url.hash = hashFromState(state);
    location.hash = url.hash;
    copyText(url.href).then(flash);
  };
  return html`<button class="share" id="share" title="copy a link to this chain" onClick=${share}>
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
function PolyInput({ src, onInput, onKeyDown }) {
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
      autocapitalize="off" value=${src} onInput=${onInput} onKeyDown=${onKeyDown} onScroll=${sync}></textarea>
  </div>`;
}

// ---- the output: view tabs, pane, comparison table ------------------------

/** View tabs (+ the sub-option strips: form and constant format in the math
 *  view, constant style in the ℚ C view) attached to the pane.  Phones hide
 *  the constants strip (presentedState decides the format there). */
function Output({ state, dispatch, compact = false }) {
  const strips = subOptionStrips(state).filter(sub => !compact || sub.kind !== 'numfmt');
  const labels = compact ? VIEW_LABEL_COMPACT : VIEW_LABEL;
  return html`<div class=${state.busy ? 'out stale' : 'out'} id="out">
    <div class="viewbar">
      <div class="views" id="view">
        ${VIEWS.map(v => html`<button key=${v} data-view=${v} class=${v === state.view ? 'on' : null}
          onClick=${() => dispatch({ type: 'setView', view: v })}>${labels[v]}</button>`)}
      </div>
      <div class="subopts" id="view-sub">
        ${strips.map(sub => html`<span class="strip" key=${sub.kind} data-strip=${sub.kind}>
          <span class="lbl">${sub.label}</span>
          ${sub.options.map(o => html`<a key=${o.key} data-opt=${o.key} title=${o.title || null}
            class=${!o.enabled ? 'off' : (o.on ? 'on' : null)}
            onClick=${o.enabled ? () => dispatch({ type: 'setSubOption', key: o.key }) : null}>${o.label}</a>`)}
        </span>`)}
      </div>
    </div>
    <${Pane} content=${paneContent(state)} state=${state} compact=${compact} />
  </div>`;
}

/** The comparison table: one row per method; the selected method's row is
 *  bold and clicking a row selects it, like its chip. */
function FooterBar({ state, dispatch }) {
  const rows = comparisonTable(state);
  const mults = r => (r.scalar ? `${r.mults} (${r.scalar} scalar)` : r.mults);
  return html`<div class="foot" id="footer-stats">
    <div class="cmp-wrap"><table class="cmp" id="compare">
      <thead><tr>
        <th class="m">method</th>
        <th title="multiplications in total (scalar ones, by a constant, in parentheses)"><span class="full">multiplications</span><span class="abbr">mult.</span></th>
        <th title="additions (integer multiples charged as additions)"><span class="full">additions</span><span class="abbr">add.</span></th>
        <th title="multiplicative depth: the longest chain of multiplications"><span class="full">mult. depth</span><span class="abbr">depth</span></th>
        <th title="exact preprocessing, or numeric (≈)">exact</th>
      </tr></thead>
      <tbody>${rows.map(r => html`<tr key=${r.key} data-m=${r.key}
          class=${r.on ? 'on' : r.ok ? null : 'off'} title=${r.ok ? null : r.note}
          onClick=${r.ok ? () => dispatch({ type: 'setMethod', method: r.key }) : null}>
        <td class="m">${r.name}</td>
        ${r.ok
      ? [html`<td key="mu">${mults(r)}</td>`, html`<td key="ad">${r.adds}</td>`,
      html`<td key="de">${r.height ?? '—'}</td>`,
      html`<td key="ex" title=${r.exactNote || null}>${r.exact ? 'yes' : '≈ numeric'}</td>`]
      : html`<td colspan="4" class="na">— <span class="why">${r.note}</span></td>`}
      </tr>`)}</tbody>
    </table></div>
  </div>`;
}

/** Copy button pinned to the pane's top-right corner (math and C views); it
 *  copies exactly the text shown, readable constants included. */
function CopyButton({ text }) {
  const [copied, flash] = useCopied();
  return html`<button class="copy" id="copy" title="copy to clipboard"
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
  return html`<button class="download" id="download"
    title="download this source, all C methods, and benchmark scripts" disabled=${busy}
    onClick=${download}>${busy ? 'packing…' : 'Download'}</button>`;
}

/** The pane below the view bar; keyed per kind so switching kinds remounts the element. */
function Pane({ content, state, compact }) {
  const text = content?.kind === 'math' ? content.text
    : content?.kind === 'c' ? content.code
      : content?.kind === 'c-missing' ? `${content.note}\n\n${content.text}` : null;
  // phones: Share floats here beside Copy (no Download); desktop keeps Share in the head row
  return html`<div class="pane-wrap">
    ${(text !== null || compact) && html`<div class="pane-actions">
      ${text !== null && html`<${CopyButton} text=${text} />`}
      ${!compact && hasCBundle(state) && html`<${DownloadButton} state=${state} />`}
      ${compact && html`<${ShareButton} state=${state} />`}
    </div>`}
    ${paneBody(content)}
  </div>`;
}

function paneBody(content) {
  switch (content?.kind) {
    case 'math':
      return html`<${MathChain} text=${content.text} />`;
    case 'c':
      return html`<pre class="chain code" id="chain" key="c"
        dangerouslySetInnerHTML=${{ __html: highlightC(content.code) }} />`;
    case 'c-missing':
      return html`<pre class="chain code" id="chain" key="c-missing"><span class="none">${content.note}</span>${'\n\n' + content.text}</pre>`;
    case 'graph':
      return [
        html`<div class="graph-pane" id="graph" key="graph" dangerouslySetInnerHTML=${{ __html: content.svg }} />`,
        html`<${Legend} key="legend" dash=${content.dash} kx=${content.kx} />`,
      ];
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
 *  Copy still receives the untouched text from Pane. */
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

// only the edge decorations that actually occur in the shown graph are listed
const Legend = ({ dash, kx }) => html`<div class="graph-legend" id="graph-legend">
  <span><i class="lg-mul">×</i> multiplication</span>
  <span><i class="lg-add">+</i> addition</span>
  <span><i class="lg-const">c</i> constant</span>
  ${dash ? html`<span><i class="lg-dash"></i> subtracted input</span>` : null}
  ${kx ? html`<span><i class="lg-k">k×</i> integer multiple</span>` : null}
</div>`;

render(html`<${App} />`, document.getElementById('app'));
