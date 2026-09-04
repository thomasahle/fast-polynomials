// Horner's rule as a chain: acc = c_n; acc = acc*x + c_{n-1}; ...
// n multiplications for general degree-n input (n-1 if monic — the leading
// multiply by 1 is skipped), n additions, depth n-ish. The baseline.
import * as P from '../poly.js';

export function compileHorner(coeffs, F) {
  const n = P.deg(coeffs);
  const lines = [];
  let mults = 0, adds = 0;
  const disp = c => F.toDisplay(c);
  const plus = c => {
    if (F.isZero(c)) return '';
    const d = disp(c); adds++;
    return F.char !== 2 && d.startsWith('-') ? ` \u2212 ${d.slice(1)}` : ` + ${d}`;
  };
  // b_n = a_n; b_k = b_{k+1} * x + a_k; P = b_0  (leading multiply skipped when monic)
  let acc;
  const top = coeffs[n];
  if (F.isOne(top)) { acc = 'x' + plus(coeffs[n - 1]); }
  else { lines.push({ lhs: `b${n - 1}`, rhs: `${disp(top)} * x${plus(coeffs[n - 1])}`, mul: true }); mults++; acc = `b${n - 1}`; }
  if (acc !== `b${n - 1}`) { lines.push({ lhs: `b${n - 1}`, rhs: acc, mul: false }); acc = `b${n - 1}`; }
  for (let i = n - 2; i >= 0; i--) {
    const lhs = i === 0 ? 'P' : `b${i}`;
    lines.push({ lhs, rhs: `${acc} * x${plus(coeffs[i])}`, mul: true });
    mults++;
    acc = lhs;
  }
  if (lines[lines.length - 1].lhs !== 'P') lines.push({ lhs: 'P', rhs: acc, mul: false });
  return {
    name: "Horner's rule", lines, mults, adds, height: mults,
    preprocessing: 'none', exact: true,
    note: 'sequential; every step depends on the previous one',
  };
}
