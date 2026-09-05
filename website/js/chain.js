// Straight-line-program rendering: turn a circuit spec + concrete key values
// into display lines, and package compile results for the UI.
//
// Every renderer returns an array of "lines":
//   { lhs, rhs, mul }   — one assignment (mul: true for a multiplication gate)
//   { heading }         — a gadget heading (only when rendered with group:true)
// Two wire-naming schemes are supported:
//   'index'   — the compiler's own names (char 0: y0, y1, …; char 2: the circuit's letters)
//   'letters' — the paper's appendix scheme y, z, t, u, v, w, s, r, q, p, o, m, j, h, g, f,
//               e, d, c, b, then g20, g21, … (tools/polychain.py:_WIRE_LETTERS)

/** Appendix wire letters, in order of multiplication output (tools/polychain.py). */
export const WIRE_LETTERS = ['y', 'z', 't', 'u', 'v', 'w', 's', 'r', 'q', 'p',
                             'o', 'm', 'j', 'h', 'g', 'f', 'e', 'd', 'c', 'b'];

/** Name of the i-th multiplication output in the paper's scheme (i = 0 → 'y'). */
export function wireLetter(i) {
  return i < WIRE_LETTERS.length ? WIRE_LETTERS[i] : `g${i}`;
}

/**
 * Wire-name array (index = wire) for a char-0 PolynomialChain in the paper's
 * letter scheme: ['1', 'x', 'y', 'z', 't', …].  Suitable for graph.js `opts.names`.
 */
export function paperWireNames(chain) {
  const names = ['1', 'x'];
  for (let i = 0; i < chain.gates.length; i++) names.push(wireLetter(i));
  return names;
}

/**
 * Gadget provenance of a char-0 chain as Map<outputWire, label> (null-free).
 * Reads chain.gate_labels (parallel to chain.gates) or gate.label.  Suitable
 * for graph.js `opts.groups`.
 */
export function gateGroups(chain) {
  const m = new Map();
  chain.gates.forEach((g, i) => {
    const label = chain.gate_labels?.[i] ?? g.label ?? null;
    if (label != null) m.set(g.out_wire, label);
  });
  return m;
}

/** Insert {heading} lines wherever the label of consecutive gate lines changes. */
function withHeadings(gateLines, labels) {
  const out = [];
  let last = null;
  gateLines.forEach((line, i) => {
    const label = labels[i] ?? null;
    if (label !== null && label !== last) out.push({ heading: label });
    if (label !== null) last = label;
    out.push(line);
  });
  return out;
}

function fmtFactor(F, f, keys, nameOf) {
  const parts = f.t.map(nameOf);
  if (f.k !== null && !F.isZero(keys[f.k])) parts.push(F.toDisplay(keys[f.k]));
  const body = parts.join(' + ');
  return parts.length > 1 ? `(${body})` : body;
}

/**
 * Render a char-2 style gate circuit with concrete keys.
 * opts.names: 'letters' (default — the circuit's own wire letters, which already
 *             follow the appendix scheme) or 'index' (y0, y1, … in gate order).
 * opts.group: insert {heading} lines from gate.label / spec.gate_labels (if any).
 */
export function renderGateChain(F, spec, keys, { names = 'letters', group = false } = {}) {
  const rename = new Map();
  if (names === 'index') spec.gates.forEach((g, i) => rename.set(g.w, `y${i}`));
  const nameOf = w => rename.get(w) ?? w;
  const lines = [];
  for (const gate of spec.gates)
    lines.push({
      lhs: nameOf(gate.w),
      rhs: `${fmtFactor(F, gate.l, keys, nameOf)} * ${fmtFactor(F, gate.r, keys, nameOf)}`,
      mul: true,
    });
  const labels = spec.gates.map((g, i) => spec.gate_labels?.[i] ?? g.label ?? null);
  const body = group ? withHeadings(lines, labels) : lines;
  const o = spec.out;
  const parts = o.t.map(nameOf);
  if (o.k !== null && !F.isZero(keys[o.k])) parts.push(F.toDisplay(keys[o.k]));
  body.push({ lhs: 'P', rhs: parts.join(' + '), mul: false });
  return body;
}

/** Uniform result object consumed by the UI. */
export function makeResult({ field, n, lines, mults, adds, height, note, scaleStep }) {
  if (scaleStep) lines = [...lines, scaleStep];
  return { field, n, lines, mults, adds, height, note,
           hornerMults: n - 1 };
}

/** Text form of a line list: aligned `lhs = rhs`, headings as `── label ──`. */
export function chainToText(result) {
  const lines = result.lines;
  const w = Math.max(0, ...lines.filter(l => l.lhs !== undefined).map(l => l.lhs.length));
  return lines
    .map(l => (l.heading !== undefined ? `── ${l.heading} ──` : `${l.lhs.padEnd(w)} = ${l.rhs}`))
    .join('\n');
}

/**
 * Render a char-0 PolynomialChain (AffineForm/MulGate) with wire names.
 * opts.names: 'index' (default — chain.wire_names: y0, y1, …) or 'letters'
 *             (appendix scheme y, z, t, …).
 * opts.group: insert {heading} lines when chain.gate_labels changes between gates.
 * Constants are printed with F.toDisplay exactly as before.
 */
export function renderAffineChain(F, chain, { names = 'index', group = false } = {}) {
  const wn = names === 'letters'
    ? paperWireNames(chain)
    : (chain.wire_names && chain.wire_names.length ? chain.wire_names : null);
  const nameOf = w => (wn ? wn[w] : (w === 1 ? 'x' : w === 0 ? '1' : `y${w - 2}`));
  const entries = t => (t instanceof Map ? [...t.entries()] : Object.entries(t).map(([a, b]) => [Number(a), b]));
  const fmtAffine = (form, paren) => {
    const parts = [];
    const idxs = entries(form.terms).sort((a, b) => a[0] - b[0]);
    for (const [w, k] of idxs) {
      if (k === 0) continue;
      const nm = nameOf(w);
      if (k === 1) parts.push(nm);
      else if (k === -1) parts.push(`-${nm}`);
      else parts.push(`${k}·${nm}`);
    }
    if (!F.isZero(form.const)) parts.push(F.toDisplay(form.const));
    if (!parts.length) parts.push('0');
    let body = parts.join(' + ').replace(/\+ -/g, '− ');
    return paren && parts.length > 1 ? `(${body})` : body;
  };
  const lines = [];
  for (const gate of chain.gates)
    lines.push({
      lhs: nameOf(gate.out_wire),
      rhs: `${fmtAffine(gate.left, true)} * ${fmtAffine(gate.right, true)}`,
      mul: true,
    });
  const labels = chain.gates.map((g, i) => chain.gate_labels?.[i] ?? g.label ?? null);
  const body = group ? withHeadings(lines, labels) : lines;
  body.push({ lhs: 'P', rhs: fmtAffine(chain.output, false), mul: false });
  return body;
}

// ---- "original" form: each method's own presentation --------------------------
// Inline single-use wires into their consumers so that Horner reads as its
// nested form, Estrin as its grouped tree, Rabin–Winograd as its recursive
// split and Eve as its peels; wires used more than once keep their name, and
// power wires x2, x4, … are written x^2, x^4, ….
function topLevelHasSum(s) {
  let d = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === '(') d++; else if (ch === ')') d--;
    else if (d === 0 && (s.startsWith(' + ', i) || s.startsWith(' − ', i) || s.startsWith(' - ', i))) return true;
  }
  return false;
}
function stripOuterParens(s) {
  while (s.startsWith('(') && s.endsWith(')')) {
    let d = 0, ok = true;
    for (let i = 0; i < s.length - 1; i++) { if (s[i] === '(') d++; else if (s[i] === ')') d--; if (d === 0) { ok = false; break; } }
    if (!ok) break;
    s = s.slice(1, -1);
  }
  return s;
}
export function inlineOriginal(lines, { maxWidth = 88 } = {}) {
  const uses = new Map();
  const ident = /[A-Za-z_][A-Za-z0-9_]*/g;
  for (const l of lines) for (const m of l.rhs.matchAll(ident)) uses.set(m[0], (uses.get(m[0]) ?? 0) + 1);
  const expr = new Map();                       // wire -> inlined expression (single-use only)
  const out = [];
  const render = rhs => rhs.replace(ident, tok => {
    if (expr.has(tok)) { const e = expr.get(tok); return topLevelHasSum(e) ? `(${e})` : e; }
    const pw = /^x(\d+)$/.exec(tok);
    return pw && !expr.has(tok) && !lines.some(l => l.lhs === tok && !/^x\d+ = /.test(l.lhs + ' = ' + l.rhs)) ? `x^${pw[1]}` : tok;
  });
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    const rhs = stripOuterParens(render(l.rhs));
    const last = i === lines.length - 1;
    const isPower = /^x\d+$/.test(l.lhs) && /^(x|x\^\d+|x\d+) \* (x|x\^\d+|x\d+)$/.test(l.rhs);
    if (!last && (uses.get(l.lhs) ?? 0) === 1 && !isPower) { expr.set(l.lhs, rhs); continue; }
    if (isPower) { expr.set(l.lhs, `x^${l.lhs.slice(1)}`); continue; }
    out.push({ lhs: l.lhs, rhs: wrapAtSums(rhs, maxWidth, l.lhs.length + 3) });
  }
  return out.map(l => `${l.lhs} = ${l.rhs}`).join('\n');
}
function wrapAtSums(s, maxWidth, indent) {
  if (s.length <= maxWidth) return s;
  const parts = [];
  let d = 0, start = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === '(') d++; else if (ch === ')') d--;
    else if (d === 0 && (s.startsWith(' + ', i) || s.startsWith(' − ', i) || s.startsWith(' - ', i))) {
      parts.push(s.slice(start, i)); start = i;
    }
  }
  parts.push(s.slice(start));
  const pad = ' '.repeat(indent);
  let lines = [], cur = '';
  for (const p of parts) {
    if (cur && (cur + p).length > maxWidth) { lines.push(cur); cur = pad + p.trimStart(); }
    else cur += p;
  }
  lines.push(cur);
  return lines.join('\n');
}

// ---- operation counts of a rendered form ---------------------------------------
const isNumTok = t => /^-?(\d+(\.\d+)?([eE][+-]?\d+)?(\/\d+)?)$/.test(t);
/**
 * Count the operations of a rendered line list exactly as displayed:
 *   adds   — binary + / − between terms (unary minus is free),
 *   mults  — `*` between two non-constant operands,
 *   scalar — `*` with a constant operand (a genuine scalar multiplication);
 *            integer multiples `k·w` are charged as additions (double-and-add:
 *            ×2 = 1, ×4 = 2, ×3 = 2), as in the paper's accounting.
 * Hidden powers `x^k` (k ≥ 2, as shown in some methods' original form) count
 * one multiplication each (one squaring per ladder step).  Continuation lines
 * of a wrapped right-hand side are joined to their statement; headings and
 * trailing comments are ignored.
 */
const constSum = sum => sum.length === 1 && sum[0].t.length === 1 &&
  (sum[0].t[0].tok !== undefined ? isNumTok(sum[0].t[0].tok) : constSum(sum[0].t[0].sum));
export function countOps(text) {
  const stmts = [];
  for (const raw of String(text ?? '').split('\n')) {
    if (/^── .* ──$/.test(raw.trim()) || !raw.trim()) continue;
    const eq = raw.indexOf(' = ');
    if (eq > 0 && !/^\s/.test(raw)) stmts.push(raw.slice(eq + 3));
    else if (stmts.length) stmts[stmts.length - 1] += ' ' + raw.trim();
  }
  let adds = 0, mults = 0, scalar = 0;
  const powers = new Set();
  const walkSum = sum => {
    adds += Math.max(0, sum.length - 1);
    for (const { t } of sum) {
      let wires = 0, consts = 0;
      for (const f of t) {
        if (f.sum !== undefined) {
          if (constSum(f.sum)) { consts++; continue; }       // a parenthesised constant, e.g. (1/5040)
          wires++; walkSum(f.sum); continue;
        }
        const tok = f.tok;
        if (isNumTok(tok)) { consts++; continue; }
        const im = /^-?(\d+)·/.exec(tok);              // integer multiple k·w: repeated addition
        if (im) { const k = Number(im[1]); if (k >= 2) adds += Math.floor(Math.log2(k)) + (k.toString(2).split('1').length - 2); }
        const pw = /^-?x\^(\d+)$/.exec(tok);
        if (pw && Number(pw[1]) >= 2) powers.add(Number(pw[1]));
        wires++;
      }
      mults += Math.max(0, wires - 1);
      scalar += wires ? consts : Math.max(0, consts - 1);
    }
  };
  for (const rhs of stmts) {
    try { walkSum(parseRhs(rhs.replace(/\s{2,}\([A-Za-z][A-Za-z -]*\)\s*$/, '')).sum); } catch (e) { /* unparsable row: skip */ }
  }
  // hidden powers: a squaring ladder up to the largest power of two, plus one
  // multiplication for each exponent that is not a power of two (lower bound)
  let ladder = 0;
  if (powers.size) {
    const kmax = Math.max(...powers);
    ladder = Math.floor(Math.log2(kmax)) + [...powers].filter(k => (k & (k - 1)) !== 0).length;
  }
  return { adds, mults: mults + ladder, scalar };
}

// ---- readable constants: a display-only rewrite of a rendered chain --------------
// formatConstants(text, style) rewrites every constant token of a chain text and
// nothing else: wire names (y0, x2, g20, P_7), integer multiples (2·y), hidden
// powers (x^4), headings and comments are left alone.  The chain itself is never
// changed — the UI shows the rewritten text (and copies it) while every count is
// still taken on the exact rendering.
//   'decimal'  rationals a/b, integers and doubles → about six significant digits,
//              scientific notation (1.59e7, 2.5e-7) when the exponent is far out
//   'hex'      every field constant as a 0x… bit pattern (binary fields)
import { ratToDouble } from './field.js';
const CONST_TOKEN_RE = /(?<![A-Za-z0-9_^\/.·⁻⁽])(-?)(0x[0-9a-fA-F]+|\d+(?:\.\d+)?(?:[eE][+-]?\d+)?(?:\/\d+)?)(?![A-Za-z0-9_·.\/^])/g;

/** x to about `digits` significant digits: fixed notation when the decimal
 *  exponent is in [-4, digits), otherwise mantissa e exponent; trailing zeros
 *  are dropped (1.500000 → 1.5, 3988.19, 0.000198413, 1.58999e7, 2.5e-7). */
export function toSigDigits(x, digits = 6) {
  if (!Number.isFinite(x)) throw new Error(`non-finite constant ${x}`);
  if (x === 0) return '0';
  const trim = s => (s.includes('.') ? s.replace(/\.?0+$/, '') : s);
  const e = Math.floor(Math.log10(Math.abs(x)));
  const fixed = e < -4 || e >= digits ? null : x.toPrecision(digits);
  if (fixed !== null && !/e/.test(fixed)) return trim(fixed);
  const [m, ex] = x.toExponential(digits - 1).split('e');   // rounding may carry into the next decade: re-derive
  return `${trim(m)}e${Number(ex)}`;
}

function formatConstToken(tok, style) {
  try {
    if (style === 'hex') {
      if (/[\/.eE]/.test(tok) && !/^0x/.test(tok)) return tok;   // not a field element pattern
      return '0x' + BigInt(tok).toString(16);
    }
    if (/^0x/.test(tok)) return tok;
    if (tok.includes('/')) { const [a, b] = tok.split('/'); return toSigDigits(ratToDouble(BigInt(a), BigInt(b))); }
    if (/[.eE]/.test(tok)) return toSigDigits(Number(tok));
    return tok.length <= 6 ? tok : toSigDigits(ratToDouble(BigInt(tok), 1n));
  } catch (e) {
    return tok;                                                   // out of double range etc.: keep the exact token
  }
}

export function formatConstants(text, style) {
  if (!style) return text;
  return String(text ?? '').split('\n').map(line => {
    if (/^── .* ──$/.test(line.trim())) return line;               // gadget headings carry indices, not constants
    return line.replace(CONST_TOKEN_RE, (m, sign, tok) => sign + formatConstToken(tok, style));
  }).join('\n');
}

// ---- strict factored form: every row is  v = (affine) * (affine)  ------------
// Rows whose right-hand side is not a pure two-factor product are rewritten:
// products become their own rows, additive remainders are folded (flattened)
// into every consumer's affine form, and the final row P is an affine combination.
import { parseRhs } from './cgen.js';
import { Rat } from './rat.js';
const negTerm = ({ neg, t }) => ({ neg: !neg, t });
/** Expand a sum AST: references to eliminated wires are spliced in (sign-aware). */
function expandSum(sum, subst) {
  const out = [];
  for (const term of sum) {
    if (term.t.length === 1 && term.t[0].tok !== undefined) {
      const tok = term.t[0].tok, neg0 = tok.startsWith('-'), base = neg0 ? tok.slice(1) : tok;
      if (subst.has(base)) {
        for (const tt of expandSum(subst.get(base), subst)) out.push((term.neg !== neg0) ? negTerm(tt) : tt);
        continue;
      }
    }
    out.push({ neg: term.neg, t: term.t.map(f => expandFactor(f, subst)) });
  }
  return out;
}
function expandFactor(f, subst) {
  if (f.tok !== undefined) {
    const neg0 = f.tok.startsWith('-'), base = neg0 ? f.tok.slice(1) : f.tok;
    if (subst.has(base)) {
      const sum = expandSum(subst.get(base), subst);
      return { sum: neg0 ? sum.map(negTerm) : sum };
    }
    return f;
  }
  return { sum: expandSum(f.sum, subst) };
}
function sumStr(sum) {
  return sum.map(({ neg, t }, i) => (i === 0 ? (neg ? '-' : '') : (neg ? ' − ' : ' + ')) + t.map(factorStr).join(' * ')).join('');
}
function factorStr(f) {
  if (f.tok !== undefined) return f.tok;
  const s = sumStr(f.sum);
  return f.sum.length === 1 && f.sum[0].t.length === 1 && !f.sum[0].neg ? s : `(${s})`;
}
/** Annotate + order a method's lines by multiplicative layer (depth): each line's
 * layer is max(layer of the wires it reads) + 1 if it multiplies.  A stable sort
 * by layer is a valid evaluation order (a line's layer >= its operands'; ties
 * keep the original, already-valid order).  Gives Estrin/RW the layered
 * presentation `layer 1: x2 = x*x; layer 2: ...` in the C output. */
export function layerLines(lines) {
  const depth = new Map([['x', 0]]);
  for (const l of lines) {
    let d = 0;
    for (const m of l.rhs.matchAll(/[A-Za-z_][A-Za-z0-9_]*/g)) d = Math.max(d, depth.get(m[0]) ?? 0);
    d += l.mul ? 1 : 0;
    depth.set(l.lhs, d);
    l.layer = d;
  }
  return lines.map((l, i) => [l.layer, i, l]).sort((a, b) => a[0] - b[0] || a[1] - b[1]).map(t => t[2]);
}

const paren = s => (s.startsWith('(') && s.endsWith(')') ? s : `(${s})`);
/** Flatten nested sums: a term whose only factor is a parenthesized sum is
 * spliced into its parent (sign-aware), recursively — so factors and affine
 * rows never carry redundant inner brackets like (w2 + (x − 61)) — and fold
 * the constant terms a splice brings together into one (x + 3/2 − 1/2 → x + 1). */
function flattenSum(sum) {
  const out = [];
  for (const term of sum) {
    const t = term.t.map(f => (f.sum !== undefined ? { sum: flattenSum(f.sum) } : f));
    if (t.length === 1 && t[0].sum !== undefined) {
      for (const inner of t[0].sum) out.push(term.neg ? negTerm(inner) : inner);
    } else out.push({ neg: term.neg, t });
  }
  return foldConstants(out);
}
/** One constant term per sum: exact literals (integers, fractions) add as
 *  rationals; once a decimal is involved the sum is a double printed to 13
 *  significant digits, as the numeric methods print theirs.  The folded
 *  constant goes last, where the rows keep their constants. */
export function foldConstants(sum) {
  const isConst = term => term.t.length === 1 && term.t[0].tok !== undefined && isNumTok(term.t[0].tok);
  const consts = sum.filter(isConst), rest = sum.filter(t => !isConst(t));
  if (consts.length < 2) return sum;
  const exact = consts.every(({ t }) => !/[.eE]/.test(t[0].tok));
  let tok;
  if (exact) {
    let acc = new Rat(0n);
    for (const { neg, t } of consts) {
      const [a, b] = t[0].tok.split('/');
      const r = new Rat(BigInt(a), b ? BigInt(b) : 1n);
      acc = acc.add(neg ? r.neg() : r);
    }
    tok = acc.toString();
  } else {
    let v = 0;
    for (const { neg, t } of consts) {
      const [a, b] = t[0].tok.split('/');
      const x = b ? Number(a) / Number(b) : Number(a);
      v += neg ? -x : x;
    }
    tok = String(Number(v.toPrecision(13)));
  }
  if (/^-?0$/.test(tok)) return rest.length ? rest : [{ neg: false, t: [{ tok: '0' }] }];
  const neg = tok.startsWith('-');
  return [...rest, { neg, t: [{ tok: neg ? tok.slice(1) : tok }] }];
}
export function factorize(lines) {
  const subst = new Map();                       // eliminated wire -> sum AST (unexpanded)
  const out = [];
  let tmp = 0;
  const fresh = () => `f${tmp++}`;
  const emitProduct = (name, factors) => {       // factors: expanded factor nodes (>= 2)
    let acc = factors[0];
    for (let i = 1; i < factors.length; i++) {
      const nm = i === factors.length - 1 ? name : fresh();
      const flat = f => (f.sum !== undefined ? { sum: flattenSum(f.sum) } : f);
      out.push({ lhs: nm, rhs: `${paren(factorStr(flat(acc)))} * ${paren(factorStr(flat(factors[i])))}`, mul: true });
      acc = { tok: nm };
    }
  };
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i], last = i === lines.length - 1;
    const terms = flattenSum(expandSum(parseRhs(l.rhs).sum, subst));
    if (!last && terms.length === 1 && terms[0].t.length >= 2 && !terms[0].neg) { emitProduct(l.lhs, terms[0].t); continue; }
    const parts = terms.map(({ neg, t }) => {
      if (t.length >= 2) { const nm = fresh(); emitProduct(nm, t); return { neg, t: [{ tok: nm }] }; }
      return { neg, t };
    });
    if (last) out.push({ lhs: l.lhs, rhs: sumStr(parts), mul: false });
    else subst.set(l.lhs, parts);
  }
  return out;
}

// ---- constructions.tex form for the paper's chains ----------------------------
// Rows as in sections/constructions: gadget outputs carry the paper's names (H_2,
// H_4, H_8, H̃_8, Q_k, T⁽¹⁾, T⁽²⁾, P_n), products used once are inlined into their
// consumer (so a row may hold several products), products used more than once get
// the paper's working letters (y, z, w, v, …), and the last row is
// P_n = x·(T⁽¹⁾ + …) + T⁽²⁾ + … rather than a separate product gate.
const WORKING_LETTERS = ['y', 'z', 'w', 'v', 'u', 't', 's', 'r', 'q', 'p'];
function groupName(label) {
  if (/^even/.test(label)) return /P_[0-9]+/.exec(label)?.[0] ?? 'P';
  const m = /^([A-Za-zH̃]+(?:_[0-9]+)?(?:⁽[¹²]⁾)?)/u.exec(label);
  return m ? m[1] : label;
}
export function renderConstructionsForm(F, chain, extraRow = null) {
  const lines = renderAffineChain(F, chain);          // index names y0.., last row P
  const labels = chain.gate_labels ?? [];
  const ng = chain.gates.length;
  if (!labels.length || labels.length !== ng) return chainToText({ lines });
  // consecutive gates with the same label form a gadget; the output row joins the last gadget
  const groups = [];
  for (let i = 0; i < ng; i++) {
    const g = groups[groups.length - 1];
    // known powers H_k and the one-gate Q_3 block are one gadget per gate; other
    // repeated labels (Q_7 block, T pairs) are one multi-gate gadget
    const single = /^(H_|H̃_|Q_3 )/u.test(labels[i]);
    if (g && g.label === labels[i] && !single) g.rows.push(i); else groups.push({ label: labels[i], rows: [i] });
  }
  groups[groups.length - 1].rows.push(ng);            // output row index
  const finalRows = groups.filter(g => /^(P_[0-9]+ =|even)/.test(g.label)).flatMap(g => g.rows);
  const uses = new Map();
  for (const l of lines) for (const m of l.rhs.matchAll(/[A-Za-z_][A-Za-z0-9_]*/g)) uses.set(m[0], (uses.get(m[0]) ?? 0) + 1);
  const name = new Map();                             // wire -> displayed name
  const subst = new Map();                            // inlined wire -> sum AST
  const out = [];
  const taken = new Set();
  const unique = nm => { while (taken.has(nm)) nm += '′'; taken.add(nm); return nm; };
  let letter = 0, deferredT2 = null;
  const nextLetter = () => WORKING_LETTERS[letter++] ?? `y${letter}`;
  // P_n = x·(…) + T⁽²⁾: the x-product first; a deferred T⁽²⁾ gate absorbs the additive rest
  const presentP = ast => {
    const xi = ast.findIndex(t => !t.neg && t.t.length === 2 && t.t.some(f => f.tok === 'x'));
    if (xi < 0) return ast;
    const xt = ast[xi]; xt.t.sort((f, g) => (g.tok === 'x') - (f.tok === 'x'));
    const rest = ast.filter((_, i) => i !== xi);
    if (!deferredT2 || !rest.length) return [xt, ...rest];
    const t2 = unique('T⁽²⁾'); name.set(deferredT2, t2); deferredT2 = null;
    out.push({ lhs: t2, rhs: renameWires(sumStr(rest), name) });
    return [xt, { neg: false, t: [{ tok: t2 }] }];
  };
  for (const [gi, grp] of groups.entries()) {
    const gname = groupName(grp.label);
    const isLast = gi === groups.length - 1;
    const isPair = /splittable pair|T-recursion/.test(grp.label) && grp.rows.length === 2;
    const isBase = /^P_[0-9]+ base$/.test(grp.label);
    const isEven = /^even/.test(grp.label);
    const last = grp.rows[grp.rows.length - 1];
    for (const ri of grp.rows) {
      const row = lines[ri];
      let ast = expandSum(parseRhs(row.rhs).sum, subst);
      const isOut = ri === last || (isPair && ri === grp.rows[0]);
      let nm;
      if (ri === ng) { nm = gname; ast = presentP(ast); }  // the output row of the final gadget
      else if (isPair && ri === grp.rows[0]) nm = 'T⁽¹⁾';
      else if (isPair) {
        // T⁽²⁾ absorbs the additive tail of P_n = x·T⁽¹⁾ + T⁽²⁾ (as in the paper); when it
        // feeds only the output row, defer it and emit it there together with that tail
        if ((uses.get(row.lhs) ?? 0) === 1 && finalRows.some(r => lines[r].rhs.includes(row.lhs))) { subst.set(row.lhs, ast); deferredT2 = row.lhs; continue; }
        nm = 'T⁽²⁾';
      }
      else if (isEven && ast.length === 1 && ast[0].t.length === 2 && ast[0].t.some(f => f.tok === 'x')) {
        // even lift  P_n = x·P_{n-1} + α_0: the non-x factor is the odd polynomial P_{n-1}
        const inner = ast[0].t.find(f => f.tok !== 'x');
        const prev = `P_${Number(gname.slice(2)) - 1}`;
        out.push({ lhs: prev, rhs: renameWires(sumStr(presentP(inner.sum ?? [{ neg: false, t: [inner] }])), name) });
        ast = [{ neg: ast[0].neg, t: [{ tok: prev }, { tok: 'x' }] }];
        subst.set(row.lhs, ast); continue;
      }
      else if (isOut && (isLast || !/^P_/.test(gname))) nm = gname;
      else if (isBase || (uses.get(row.lhs) ?? 0) !== 1) nm = nextLetter();
      else { subst.set(row.lhs, ast); continue; }     // used once: inline into its consumer
      nm = unique(nm);
      name.set(row.lhs, nm);
      out.push({ lhs: nm, rhs: renameWires(sumStr(ast), name) });
    }
  }
  if (extraRow) out.push({ lhs: extraRow.lhs, rhs: extraRow.rhs.replace('P̃', out[out.length - 1].lhs) });
  const w = Math.max(...out.map(l => l.lhs.length));
  return out.map(l => `${l.lhs.padEnd(w)} = ${l.rhs}`).join('\n');
}
function renameWires(s, name) {
  return s.replace(/[A-Za-z_][A-Za-z0-9_]*/g, tok => name.get(tok) ?? tok);
}
