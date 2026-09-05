// Estrin's scheme: P = A(x) + x^(2^k) * B(x), recursively; same multiplication
// count as Horner (plus the power ladder) but depth O(log n).
import * as P from '../poly.js';
import { layerLines } from '../chain.js';

/** Rename the e-wires to follow the printed order.  The recursion numbers
 *  them in post-order, but layerLines groups the lines by multiplicative
 *  layer, so an affine wire from the right half (a leading coefficient 1,
 *  no product) would read e4 above e3.  Hex constants and exponents such as
 *  0x1e5 / 1e-7 have no word boundary before the e and are left alone. */
function renumber(lines) {
  const names = new Map();
  for (const l of lines) if (/^e\d+$/.test(l.lhs)) names.set(l.lhs, `e${names.size}`);
  const ren = s => s.replace(/\be\d+\b/g, m => names.get(m) ?? m);
  return lines.map(l => ({ ...l, lhs: ren(l.lhs), rhs: ren(l.rhs) }));
}

export function compileEstrin(coeffs, F) {
  const n = P.deg(coeffs);
  const lines = [];
  let mults = 0, adds = 0, wid = 0;
  const disp = c => F.toDisplay(c);
  // power ladder x^2, x^4, ...
  const powers = { 1: 'x' };
  let p = 1;
  while (2 * p <= n) {
    const nm = `x${2 * p}`;
    lines.push({ lhs: nm, rhs: `${powers[p]} * ${powers[p]}`, mul: true });
    mults++;
    powers[2 * p] = nm;
    p *= 2;
  }
  const depths = { x: 0 };
  for (let q = 2; q <= n; q *= 2) depths[`x${q}`] = Math.log2(q);
  // recursive splitting; returns [wireName|literal, depth]
  function go(lo, hi) {                    // inclusive degree range
    if (lo === hi) {
      const c = coeffs[lo];
      return F.isZero(c) ? null : [disp(c), 0, F.isOne(c)];
    }
    if (hi - lo === 0) return null;
    let span = 1;
    while (lo + 2 * span <= hi) span *= 2;  // largest 2^k with lo+2^k <= hi
    const low = go(lo, lo + span - 1);
    const high = go(lo + span, hi);
    if (!high) return low;
    const px = powers[span];
    // t = high * x^span (+ low)
    const t = `e${wid++}`;
    let rhs;
    const highExpr = high[2] ? px : `${high[0]} * ${px}`;
    if (!high[2]) mults++;
    if (low) {
      const neg = typeof low[0] === 'string' && low[0].startsWith('-') && !low[0].includes(' ');
      rhs = neg ? `${highExpr} \u2212 ${low[0].slice(1)}` : `${highExpr} + ${low[0]}`;
      adds++;
    }
    else rhs = highExpr;
    const d = Math.max(high[1] + (high[2] ? 0 : 1), depths[px], low ? low[1] : 0);
    lines.push({ lhs: t, rhs, mul: !high[2] });
    return [t, d, false];
  }
  const root = go(0, n);
  lines.push({ lhs: 'P', rhs: root[0], mul: false });
  // depth: structural
  const height = Math.max(root[1], Math.ceil(Math.log2(Math.max(n, 2))));
  return {
    name: "Estrin's scheme", lines: renumber(layerLines(lines)), mults, adds, height,
    preprocessing: 'none', exact: true,
    note: 'same multiplications as Horner, but log-depth (parallel-friendly)',
  };
}
