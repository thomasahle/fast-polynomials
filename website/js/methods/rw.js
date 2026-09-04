// Rabin–Winograd-style balanced splitting with rational preprocessing.
// At balanced nodes (deg = 2s−1, s a power of two) the split
//     P = Q·(x^s + a) + R
// absorbs one coefficient per multiplication (a is solved with a UNIT pivot —
// Q is monic — so no division is even needed there); other nodes plain-split
// P = Q·x^s + L, and non-monic remainders are normalized by their leading
// coefficient (one division + one extra multiplication, on O(log n) nodes).
// Total: ⌈n/2⌉ + O(log n) multiplications, exact over any field.
import * as P from '../poly.js';
import { layerLines } from '../chain.js';

export function compileRW(coeffs, F) {
  const n = P.deg(coeffs);
  if (n < 1) throw new Error('degree >= 1 required');
  const lines = [];
  let mults = 0, adds = 0, wid = 0;
  const disp = c => F.toDisplay(c);

  const powers = { 1: 'x' };
  const powDepth = { 1: 0 };
  const needPow = s => {
    if (powers[s]) return [powers[s], powDepth[s]];
    const [half, hd] = needPow(s / 2);
    const nm = `x${s}`;
    lines.push({ lhs: nm, rhs: `${half} * ${half}`, mul: true });
    mults++;
    powers[s] = nm; powDepth[s] = hd + 1;
    return [nm, hd + 1];
  };

  const addTerm = (base, c) => {
    if (F.isZero(c)) return base;
    adds++;
    const d = disp(c);
    return F.char !== 2 && d.startsWith('-')
      ? `${base} − ${d.slice(1)}` : `${base} + ${d}`;
  };

  // monic p, deg >= 1. returns [expr, depth]; expr is a sum (parenthesize at use).
  function goMonic(p) {
    const d = P.deg(p);
    if (d === 1) return [addTerm('x', p[0]), 0];
    if (d === 2) {
      const t = `w${wid++}`;
      lines.push({ lhs: t, rhs: `(${addTerm('x', p[1])}) * x`, mul: true });
      mults++;
      return [addTerm(t, p[0]), 1];
    }
    if (d === 3) {
      // (x + a)(x^2 + c) + (x + b):  a = p2, c = p1 − 1, b = p0 − a·c
      const a = p[2], c = F.sub(p[1], F.one), b = F.sub(p[0], F.mul(a, c));
      const [x2, x2d] = needPow(2);
      const t = `w${wid++}`;
      lines.push({ lhs: t, rhs: `(${addTerm('x', a)}) * (${addTerm(x2, c)})`, mul: true });
      mults++; adds++;
      return [`${t} + (${addTerm('x', b)})`, Math.max(1, x2d) + 1];
    }
    let s = 1; while (2 * s - 1 < d) s *= 2;      // minimal s with d <= 2s−1
    const Q = P.normalize(F, p.slice(s));          // monic, deg d−s <= s−1
    const Rt = P.normalize(F, p.slice(0, s));      // deg <= s−1
    const [px, pxd] = needPow(s);
    if (d === s) {                                 // high half is the bare power
      const low = goAny(Rt);
      if (!low) return [px, pxd];
      adds++;
      return [`${px} + (${low[0]})`, Math.max(pxd, low[1])];
    }
    const t = `w${wid++}`;
    if (d === 2 * s - 1) {
      // absorb: pivot is Q's monic top at row s−1
      const a = F.sub(P.coeff(F, Rt, s - 1), F.one);
      const R = P.normalize(F, Array.from({ length: s }, (_, i) =>
        F.sub(P.coeff(F, Rt, i), F.mul(a, P.coeff(F, Q, i)))));
      const [qe, qd] = goMonic(Q);
      const [re, rd] = goMonic(R);            // monic deg s−1 by construction
      adds++;
      lines.push({ lhs: t, rhs: `(${qe}) * (${addTerm(px, a)})`, mul: true });
      mults++;
      return [`${t} + (${re})`, Math.max(Math.max(qd, pxd) + 1, rd)];
    }
    // plain split: P = Q·x^s + Rt
    const [qe, qd] = goMonic(Q);
    lines.push({ lhs: t, rhs: `(${qe}) * ${px}`, mul: true });
    mults++;
    const low = goAny(Rt);
    if (!low) return [t, Math.max(qd, pxd) + 1];
    adds++;
    return [`${t} + (${low[0]})`, Math.max(Math.max(qd, pxd) + 1, low[1])];
  }

  // arbitrary p (possibly non-monic / zero)
  function goAny(p) {
    const d = P.deg(p);
    if (d < 0) return null;
    if (d === 0) return [disp(p[0]), 0];
    const top = p[d];
    if (F.isOne(top)) return goMonic(p);
    if (d === 1) {
      const t = `w${wid++}`;
      lines.push({ lhs: t, rhs: `${disp(top)} * x`, mul: true });
      mults++;
      return [addTerm(t, p[0]), 1];
    }
    // normalize: p = top · (p / top), monic recursion + one scalar multiplication
    const m = P.scale(F, F.inv(top), p);
    const [me, md] = goMonic(m);
    const t = `w${wid++}`;
    lines.push({ lhs: t, rhs: `${disp(top)} * (${me})`, mul: true });
    mults++;
    return [t, md + 1];
  }

  const root = P.isMonic(F, coeffs) ? goMonic(coeffs) : goAny(coeffs);
  lines.push({ lhs: 'P', rhs: root[0], mul: false });
  return {
    name: 'Rabin–Winograd', lines: layerLines(lines), mults, adds, height: root[1],
    preprocessing: 'rational', exact: true,
    note: '⌈n/2⌉ + O(log n) multiplications via balanced splits with one absorbed coefficient per product',
  };
}
