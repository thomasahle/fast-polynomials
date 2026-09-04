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
// Layout: ONE card.  Heading row (label + example chips + degree stepper) →
// the polynomial input → field chooser (three pill groups from the js/field.js
// registry — exact ℚ ℝ · Mersenne primes · binary fields — with the FIELD
// legend on the same line at the card's full width) → method chips → busy /
// error → view tabs attached to the output pane → the comparison table (one
// row per method) + Share.
import { html, render, useReducer, useState, useEffect, useRef } from './vendor/preact-htm.module.js';
import { highlightC } from './highlight.js';
import {
  reduce, initialState, stateFromHash, hashFromState, VIEWS, examplesFor, exampleHeld,
  exampleDegree, showOutput, compileMessage, methodTabs, comparisonTable, subOptionStrips,
  paneContent, fieldChooser, tokenizePoly,
} from './uistate.js';

const DEBOUNCE_MS = 500;   // quiet time after an edit before the chain recompiles
const COPIED_MS = 1200;    // how long Copy / Share show their transient "copied"

const VIEW_LABEL = { math: 'mathematical', c: 'C code', graph: 'graph' };

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

/** Transient "copied" flag for Copy / Share (persistent state stays in the reducer). */
function useCopied() {
  const [copied, setCopied] = useState(false);
  const flash = () => { setCopied(true); setTimeout(() => setCopied(false), COPIED_MS); };
  return [copied, flash];
}

function App() {
  // location.hash seeds the boot state (pure helper; junk falls back to defaults)
  const [state, dispatch] = useReducer(reduce, initialState, s => stateFromHash(s, location.hash));
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

  const cancel = () => { dropWorker(); dispatch({ type: 'cancel' }); };
  const runExample = key => { abandonJob(); dispatch({ type: 'example', key }); };
  const setMode = mode => { abandonJob(); dispatch({ type: 'setMode', mode }); };
  const toggleMonic = () => {
    if (exampleHeld(stateRef.current)) abandonJob();
    dispatch({ type: 'setExMonic' });
  };
  const stepDeg = delta => {
    // terminate a running job only when stepping will actually regenerate the
    // example and recompile (the reducer's setExDegree condition)
    if (exampleHeld(stateRef.current)) abandonJob();
    dispatch({ type: 'setExDegree', delta });
  };
  const onKeyDown = e => {                 // Cmd/Ctrl+Enter skips the debounce
    if (e.key === 'Enter' && (e.metaKey || e.ctrlKey)) { e.preventDefault(); compileNow(); }
  };
  const name = t => t.label;
  const tabs = methodTabs(state);

  const [copied, flash] = useCopied();
  const share = () => {
    const url = new URL(location.href);
    url.hash = hashFromState(state);
    location.hash = url.hash;
    copyText(url.href).then(flash);
  };

  return html`<div class="card" id="main">
    <div class="head-row">
      <label class="head" for="poly-in">Your polynomial</label>
      <span class="ex-row">
        <span class="examples" id="examples">
          ${examplesFor(state.mode, state.exDegree, state.exSeed, state.exMonic).map(ex => html`<a key=${ex.key} class="chip"
            data-ex=${ex.key} title=${ex.title || null} onClick=${() => runExample(ex.key)}
            dangerouslySetInnerHTML=${{ __html: ex.labelHtmlSpec }}></a>`)}
        </span>
        <button id="monic" class=${`monic-toggle${state.exMonic ? ' on' : ''}`}
          aria-pressed=${state.exMonic} title="normalize generated examples to leading coefficient 1"
          onClick=${toggleMonic}>monic</button>
        <span class="degree" id="degree">
          <button id="deg-minus" title="lower example degree" onClick=${() => stepDeg(-1)}>−</button>
          <span class="deg-n">degree ${exampleDegree(state)}</span>
          <button id="deg-plus" title="raise example degree" onClick=${() => stepDeg(+1)}>+</button>
        </span>
        <button class="share" id="share" title="copy a link to this chain" onClick=${share}>
          <svg viewBox="0 0 24 24" width="14" height="14" aria-hidden="true" fill="none"
            stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
            <path d="M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71" />
            <path d="M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71" />
          </svg>
          ${copied ? 'copied' : 'Share'}</button>
      </span>
    </div>
    <${PolyInput} src=${state.src} onKeyDown=${onKeyDown}
      onInput=${e => dispatch({ type: 'setSrc', src: e.currentTarget.value })} />
    <div class="controls" id="field-row">
      <div class="field-groups" id="mode">
        ${fieldChooser(state).map(g => html`<div class="seg" key=${g.id} data-group=${g.id}>
          ${g.fields.map(f => html`<button key=${f.id} data-mode=${f.id} title=${f.title || null}
            class=${f.on ? 'on' : null} disabled=${!f.enabled}
            onClick=${f.enabled ? () => setMode(f.id) : null}>${fieldLabel(f.label)}</button>`)}
        </div>`)}
      </div>
      <span class="lbl">Field</span>
    </div>
    ${tabs.length > 0 && html`<div class="controls" id="method-row">
      <div class="seg methods" id="methods">
        ${tabs.map(t => t.enabled
    ? html`<button key=${t.key} data-m=${t.key} data-label=${t.label} class=${t.on ? 'on' : null}
              onClick=${() => dispatch({ type: 'setMethod', method: t.key })}><span>${name(t)}</span></button>`
    : html`<button key=${t.key} data-label=${t.label} disabled title=${t.title || null}><span>${name(t)}</span></button>`)}
      </div>
      <span class="lbl">Method</span>
    </div>`}
    ${state.busy && html`<div class="controls"><span id="busy" style="color:var(--muted)">preprocessing…
      <button class="cancel" id="cancel" onClick=${cancel}>cancel</button></span></div>`}
    ${state.error !== null && html`<div id="error">${state.error}</div>`}
    ${showOutput(state) && html`<${Output} key="out" state=${state} dispatch=${dispatch} />`}
  </div>
  <div>
    ${showOutput(state) && html`<${FooterBar} key="foot" state=${state} dispatch=${dispatch} />`}
  </div>`;
}

/** The polynomial input: a transparent textarea over a highlighted backdrop
 *  (same font, padding and wrapping; scroll-synced), so numbers and x-powers
 *  are coloured while the textarea keeps native editing.  The backdrop ends in
 *  a newline + zero-width space so a trailing empty line keeps its height. */
function PolyInput({ src, onInput, onKeyDown }) {
  const hlRef = useRef(null), taRef = useRef(null);
  const sync = () => {
    const h = hlRef.current, t = taRef.current;
    if (h && t) { h.scrollTop = t.scrollTop; h.scrollLeft = t.scrollLeft; }
  };
  useEffect(sync);   // after every render too: a programmatic value change may move the scroll
  return html`<div class="poly-edit">
    <pre class="poly-hl" aria-hidden="true" ref=${hlRef}>${tokenizePoly(src).map(t =>
    t.type === 'num' ? html`<span class="in-num">${t.text}</span>`
      : t.type === 'var' ? html`<span class="in-var">${t.text}</span>`
        : t.text)}${'\n\u200b'}</pre>
    <textarea id="poly-in" ref=${taRef} spellcheck=${false} autocomplete="off" autocorrect="off"
      autocapitalize="off" value=${src} onInput=${onInput} onKeyDown=${onKeyDown} onScroll=${sync}></textarea>
  </div>`;
}

/** Output section of the card: view tabs (+ the sub-option strips: form and
 *  constant format in the math view, constant style in the ℚ C view) attached
 *  to the pane.  Methods and the comparison table live elsewhere. */
function Output({ state, dispatch }) {
  const strips = subOptionStrips(state);
  return html`<div class=${state.busy ? 'out stale' : 'out'} id="out">
    <div class="viewbar">
      <div class="views" id="view">
        ${VIEWS.map(v => html`<button key=${v} data-view=${v} class=${v === state.view ? 'on' : null}
          onClick=${() => dispatch({ type: 'setView', view: v })}>${VIEW_LABEL[v]}</button>`)}
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
    <${Pane} content=${paneContent(state)} />
  </div>`;
}

/** Below the pane: the comparison table (one row per method; the selected
 *  method's row is bold and clicking a row selects it, like its chip)
 *  and a Share button (URL hash + clipboard) on the right. */
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

/** The pane below the view bar; keyed per kind so switching kinds remounts the element. */
function Pane({ content }) {
  const text = content?.kind === 'math' ? content.text
    : content?.kind === 'c' ? content.code
      : content?.kind === 'c-missing' ? `${content.note}\n\n${content.text}` : null;
  return html`<div class="pane-wrap">
    ${text !== null && html`<${CopyButton} text=${text} />`}
    ${paneBody(content)}
  </div>`;
}

function paneBody(content) {
  switch (content?.kind) {
    case 'math':
      return html`<pre class="chain" id="chain" key="math">${content.text}</pre>`;
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

// only the edge decorations that actually occur in the shown graph are listed
const Legend = ({ dash, kx }) => html`<div class="graph-legend" id="graph-legend">
  <span><i class="lg-mul">×</i> multiplication</span>
  <span><i class="lg-add">+</i> addition</span>
  <span><i class="lg-const">c</i> constant</span>
  ${dash ? html`<span><i class="lg-dash"></i> subtracted input</span>` : null}
  ${kx ? html`<span><i class="lg-k">k×</i> integer multiple</span>` : null}
</div>`;

render(html`<${App} />`, document.getElementById('app'));
