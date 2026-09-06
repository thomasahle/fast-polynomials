// Minimal C syntax highlighter for the generated code pane (no dependencies).
//
//   tokenizeC(src) -> [{ type, text }]   (concatenating the texts gives back src)
//   highlightC(src) -> HTML string with <span class="hl-<type>"> wrappers
//
// Token types: comment, preproc, string, number, keyword, type, fn (identifier
// followed by '('), ident, op, space.  Styled by style.css (.hl-*), which
// carries both light and dark palettes.

const KEYWORDS = new Set([
  'auto', 'break', 'case', 'const', 'continue', 'default', 'do', 'else', 'enum', 'extern',
  'for', 'goto', 'if', 'inline', 'register', 'restrict', 'return', 'sizeof', 'static',
  'struct', 'switch', 'typedef', 'union', 'volatile', 'while', '_Static_assert',
  'constexpr', 'template', 'typename', 'namespace', 'using', 'class', 'public', 'private',
]);
const TYPES = new Set([
  'void', 'char', 'short', 'int', 'long', 'float', 'double', 'signed', 'unsigned', 'bool',
  '_Bool', 'size_t', 'ssize_t', 'ptrdiff_t', 'uintptr_t', 'intptr_t',
  'int8_t', 'int16_t', 'int32_t', 'int64_t', 'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t',
  '__uint128_t', '__int128_t', '__int128', '__m128i', '__m256i', 'uint8x16_t', 'uint64x2_t',
  'poly64_t', 'poly64x1_t', 'poly64x2_t', 'poly128_t', 'U128',
  'complex', '_Complex',
]);

const NUM_RE = /^(?:0[xX][0-9a-fA-F']+|(?:\d[\d']*\.?\d*|\.\d+)(?:[eE][+-]?\d+)?)(?:[uU]?[lL]{0,2}|[lL]{0,2}[uU]?|[fF])?/;
const IDENT_RE = /^[A-Za-z_$][\w$]*/;
const OP_RE = /^(?:->|\+\+|--|<<=|>>=|<<|>>|<=|>=|==|!=|&&|\|\||[-+*/%&|^~!<>=?:;,.(){}\[\]#\\])/;

/** Split C source into tokens; texts concatenate back to `src`. */
export function tokenizeC(src) {
  const toks = [];
  let i = 0;
  const n = src.length;
  let lineStart = true;                   // for preprocessor detection
  while (i < n) {
    const ch = src[i];
    // line comment
    if (ch === '/' && src[i + 1] === '/') {
      let j = src.indexOf('\n', i); if (j < 0) j = n;
      toks.push({ type: 'comment', text: src.slice(i, j) }); i = j; continue;
    }
    // block comment
    if (ch === '/' && src[i + 1] === '*') {
      let j = src.indexOf('*/', i + 2); j = j < 0 ? n : j + 2;
      toks.push({ type: 'comment', text: src.slice(i, j) }); i = j; continue;
    }
    // whitespace
    if (ch === ' ' || ch === '\t' || ch === '\r' || ch === '\n') {
      let j = i; while (j < n && (src[j] === ' ' || src[j] === '\t' || src[j] === '\r' || src[j] === '\n')) j++;
      const text = src.slice(i, j);
      if (text.includes('\n')) lineStart = true;
      toks.push({ type: 'space', text }); i = j; continue;
    }
    // preprocessor line (a '#' as the first non-blank of a line, up to the end of the line;
    // comments inside are still tokenized separately)
    if (ch === '#' && lineStart) {
      let j = i;
      while (j < n && src[j] !== '\n') {
        if (src[j] === '/' && (src[j + 1] === '/' || src[j + 1] === '*')) break;
        if (src[j] === '\\' && src[j + 1] === '\n') { j += 2; continue; }
        j++;
      }
      toks.push({ type: 'preproc', text: src.slice(i, j) }); i = j; lineStart = false; continue;
    }
    lineStart = false;
    // string / char literal
    if (ch === '"' || ch === "'") {
      let j = i + 1;
      while (j < n && src[j] !== ch && src[j] !== '\n') { if (src[j] === '\\') j++; j++; }
      if (j < n && src[j] === ch) j++;
      toks.push({ type: 'string', text: src.slice(i, j) }); i = j; continue;
    }
    const rest = src.slice(i, i + 64);
    let m;
    if ((ch >= '0' && ch <= '9') || (ch === '.' && src[i + 1] >= '0' && src[i + 1] <= '9')) {
      m = NUM_RE.exec(rest);
      if (m) { toks.push({ type: 'number', text: m[0] }); i += m[0].length; continue; }
    }
    if ((m = IDENT_RE.exec(rest))) {
      const word = m[0];
      let type = 'ident';
      if (KEYWORDS.has(word)) type = 'keyword';
      else if (TYPES.has(word)) type = 'type';
      else {
        let j = i + word.length;
        while (j < n && (src[j] === ' ' || src[j] === '\t')) j++;
        if (src[j] === '(') type = 'fn';
      }
      toks.push({ type, text: word }); i += word.length; continue;
    }
    if ((m = OP_RE.exec(rest))) { toks.push({ type: 'op', text: m[0] }); i += m[0].length; continue; }
    // anything else (unicode in comments is already consumed above): single char
    toks.push({ type: 'op', text: ch }); i++;
  }
  return toks;
}

const esc = s => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');

/** HTML with <span class="hl-…"> per token (whitespace and plain identifiers unwrapped). */
export function highlightC(src) {
  return tokenizeC(src).map(t =>
    (t.type === 'space' || t.type === 'ident' || t.type === 'op')
      ? esc(t.text)
      : `<span class="hl-${t.type}">${esc(t.text)}</span>`).join('');
}
