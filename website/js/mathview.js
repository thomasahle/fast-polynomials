// TeX presentation for the mathematical-chain pane.
//
// The compilers deliberately keep their canonical output as plain text: it is
// what Copy exports, what the operation counter reads, and what tests compare.
// This module is a display-only adapter for that small, controlled grammar.  It
// never feeds user input to KaTeX as TeX; only identifiers, constants and the
// operators parsed below are translated.

import { parseRhs } from './cgen.js';

const SUPERSCRIPT_DIGIT = new Map([
  ['⁰', '0'], ['¹', '1'], ['²', '2'], ['³', '3'], ['⁴', '4'],
  ['⁵', '5'], ['⁶', '6'], ['⁷', '7'], ['⁸', '8'], ['⁹', '9'],
]);

const GREEK = new Map([
  ['alpha', '\\alpha'], ['beta', '\\beta'], ['gamma', '\\gamma'],
  ['delta', '\\delta'], ['epsilon', '\\varepsilon'], ['theta', '\\theta'],
  ['lambda', '\\lambda'], ['mu', '\\mu'], ['rho', '\\rho'],
  ['sigma', '\\sigma'], ['phi', '\\phi'], ['psi', '\\psi'], ['omega', '\\omega'],
  ['α', '\\alpha'], ['β', '\\beta'], ['γ', '\\gamma'],
  ['δ', '\\delta'], ['ε', '\\varepsilon'], ['θ', '\\theta'],
  ['λ', '\\lambda'], ['μ', '\\mu'], ['ρ', '\\rho'],
  ['σ', '\\sigma'], ['φ', '\\phi'], ['ψ', '\\psi'], ['ω', '\\omega'],
]);

/** Escape literal text placed inside a TeX text command. */
export function escapeTexText(text) {
  return String(text).replace(/[\\{}$&#_%^~]/g, ch => ({
    '\\': '\\textbackslash{}', '{': '\\{', '}': '\\}', '$': '\\$', '&': '\\&',
    '#': '\\#', '_': '\\_', '%': '\\%', '^': '\\textasciicircum{}',
    '~': '\\textasciitilde{}',
  })[ch]);
}

const superscriptDigits = s => [...s].map(ch => SUPERSCRIPT_DIGIT.get(ch) ?? ch).join('');

/** A compiler wire/name token (P_7, P̃, H̃_8, T⁽¹⁾, y12, x^4) -> TeX. */
export function nameToTex(raw) {
  let name = String(raw).trim().normalize('NFD');
  let sign = '';
  if (name.startsWith('-')) { sign = '-'; name = name.slice(1); }

  // Paper names use both ASCII apostrophes and U+2032 primes (Q_3′, Q_3′′).
  const primeMatch = /(['′]+)$/.exec(name);
  const primes = primeMatch ? [...primeMatch[1]].length : 0;
  if (primeMatch) name = name.slice(0, primeMatch.index);

  let superscript = null;
  let m = /\^(-?\d+)$/.exec(name);
  if (m) { superscript = m[1]; name = name.slice(0, m.index); }
  else {
    m = /⁽([⁰¹²³⁴-⁹]+)⁾$/u.exec(name);
    if (m) { superscript = `(${superscriptDigits(m[1])})`; name = name.slice(0, m.index); }
  }

  let subscript = null;
  m = /_(\d+)$/.exec(name);
  if (m) { subscript = m[1]; name = name.slice(0, m.index); }
  else {
    m = /^(x)(\d+)$/.exec(name);
    if (m) { superscript ??= m[2]; name = m[1]; }
    else {
      m = /^(.+?)(\d+)$/.exec(name);
      if (m) { subscript = m[2]; name = m[1]; }
    }
  }

  const hasTilde = name.includes('\u0303');
  name = name.replace(/\u0303/g, '');
  let base = GREEK.get(name);
  if (!base) {
    if (/^[A-Za-z]$/.test(name)) base = name;
    else if (/^[A-Za-z]+$/.test(name)) base = `\\mathrm{${name}}`;
    else base = `\\mathrm{${escapeTexText(name)}}`;
  }
  if (hasTilde) base = `\\widetilde{${base}}`;
  if (subscript !== null) base += `_{${subscript}}`;
  const superTex = (superscript !== null ? superscript : '') + '\\prime'.repeat(primes);
  if (superTex) base += `^{${superTex}}`;
  return sign + base;
}

const NUMBER = /^-?\d+(?:\.\d+)?$/;

// The class commands are emitted only by this parser, never copied from user
// input.  CSS then gives mathematical variables and constants the same theme-
// aware colours as the polynomial editor.
const highlighted = (kind, tex, on) => on ? `\\htmlClass{math-${kind}}{${tex}}` : tex;

/** One non-parenthesized token from the chain grammar -> TeX. */
export function tokenToTex(token, { highlight = false } = {}) {
  const t = String(token);
  let m = /^(-?)(\d+)\/(\d+)$/.exec(t);
  if (m) return highlighted('const', `${m[1]}\\frac{${m[2]}}{${m[3]}}`, highlight);
  m = /^(-?)(0x[0-9a-fA-F]+)$/.exec(t);
  if (m) return highlighted('const', `${m[1]}\\mathtt{${m[2]}}`, highlight);
  m = /^(-?\d+(?:\.\d+)?)[eE]([+-]?\d+)$/.exec(t);
  if (m) return highlighted('const', `${m[1]}\\mathbin{\\times}10^{${Number(m[2])}}`, highlight);
  if (NUMBER.test(t)) return highlighted('const', t, highlight);
  m = /^(.+)·(.+)$/.exec(t);
  if (m) return `${tokenToTex(m[1], { highlight })}\\,${highlighted('var', nameToTex(m[2]), highlight)}`;
  return highlighted('var', nameToTex(t), highlight);
}

const simpleSum = sum => sum.length === 1 && !sum[0].neg && sum[0].t.length === 1;

function factorToTex(factor, options) {
  if (factor.tok !== undefined) return tokenToTex(factor.tok, options);
  const inside = sumToTex(factor.sum, options);
  return simpleSum(factor.sum) ? inside : `\\left(${inside}\\right)`;
}

function termToTex(factors, options) {
  return factors.map(factor => factorToTex(factor, options)).join(' \\mathbin{\\cdot} ');
}

function sumToTex(sum, options) {
  return sum.map(({ neg, t }, i) => {
    const sign = i === 0 ? (neg ? '-' : '') : (neg ? ' - ' : ' + ');
    return sign + termToTex(t, options);
  }).join('');
}

/** A generated right-hand side -> TeX, or null if it falls outside the grammar. */
export function expressionToTex(rhs, { highlight = false } = {}) {
  try {
    const normalized = String(rhs).trim().replace(/\s+/g, ' ');
    return normalized ? sumToTex(parseRhs(normalized).sum, { highlight }) : null;
  } catch (_) {
    return null;
  }
}

function splitAnnotation(rhs) {
  const m = /^(.*\S)\s{2,}\(([^()]*)\)\s*$/.exec(rhs);
  return m ? { expression: m[1], annotation: m[2] } : { expression: rhs.trim(), annotation: null };
}

/**
 * Parse chainToText/inlineOriginal output into display rows. Wrapped RHS lines
 * are rejoined before conversion. The original strings stay on every row so a
 * failed or unavailable KaTeX render has a readable fallback.
 */
export function chainMathRows(text) {
  const rawRows = [];
  for (const raw of String(text ?? '').split('\n')) {
    const trimmed = raw.trim();
    if (!trimmed) { rawRows.push({ kind: 'gap' }); continue; }
    const heading = /^─{2,}\s*(.*?)\s*─{2,}$/.exec(trimmed);
    if (heading) { rawRows.push({ kind: 'heading', text: heading[1] }); continue; }

    // inlineOriginal wraps only a right-hand side, indenting continuation rows.
    const previous = rawRows[rawRows.length - 1];
    if (/^\s/.test(raw) && previous?.kind === 'equation') {
      previous.rhs += ` ${trimmed}`;
      continue;
    }

    const equation = /^(\S+)\s+=\s+(.*)$/.exec(raw);
    if (equation) {
      rawRows.push({ kind: 'equation', lhs: equation[1], rhs: equation[2] });
      continue;
    }
    rawRows.push({ kind: 'note', text: trimmed.replace(/^#\s*/, '') });
  }

  // Collapse repeated blank lines and avoid empty padding at either edge.
  const compact = rawRows.filter((row, i) => row.kind !== 'gap' ||
    (i > 0 && i + 1 < rawRows.length && rawRows[i - 1].kind !== 'gap'));
  return compact.map(row => {
    if (row.kind === 'equation') {
      const { expression, annotation } = splitAnnotation(row.rhs);
      return { ...row, expression, annotation,
        lhsTex: nameToTex(row.lhs), rhsTex: expressionToTex(expression, { highlight: true }) };
    }
    if (row.kind === 'heading') {
      const oneName = /^\S+$/.test(row.text);
      return { ...row, tex: oneName ? nameToTex(row.text) : `\\text{${escapeTexText(row.text)}}` };
    }
    return row;
  });
}

/** Safe synchronous KaTeX rendering. null means the plain-text fallback should be used. */
export function renderLatex(tex) {
  const katex = globalThis.katex;
  if (!katex || !tex) return null;
  try {
    return katex.renderToString(tex, {
      displayMode: false,
      output: 'htmlAndMathml',
      throwOnError: true,
      // Only the parser-generated colour hooks above use KaTeX's HTML
      // extension.  No user-authored TeX reaches this function.
      trust: context => context.command === '\\htmlClass',
      strict: code => code === 'htmlExtension' ? 'ignore' : 'error',
    });
  } catch (_) {
    return null;
  }
}
