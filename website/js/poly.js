// Dense polynomial arithmetic over an abstract field F.
// A polynomial is a plain array of field elements, index = degree,
// ALWAYS normalized (no trailing zeros; the zero polynomial is []).
export function normalize(F, p) {
  let d = p.length - 1;
  while (d >= 0 && F.isZero(p[d])) d--;
  return p.slice(0, d + 1);
}
export const deg = p => p.length - 1;                     // deg 0-poly = -1
export const coeff = (F, p, i) => (i < p.length ? p[i] : F.zero);
export function add(F, a, b) {
  const n = Math.max(a.length, b.length), r = new Array(n);
  for (let i = 0; i < n; i++) r[i] = F.add(coeff(F, a, i), coeff(F, b, i));
  return normalize(F, r);
}
export function sub(F, a, b) {
  const n = Math.max(a.length, b.length), r = new Array(n);
  for (let i = 0; i < n; i++) r[i] = F.sub(coeff(F, a, i), coeff(F, b, i));
  return normalize(F, r);
}
export function scale(F, c, a) {
  if (F.isZero(c)) return [];
  return normalize(F, a.map(x => F.mul(c, x)));
}
export function mul(F, a, b) {
  if (!a.length || !b.length) return [];
  const r = new Array(a.length + b.length - 1).fill(F.zero);
  for (let i = 0; i < a.length; i++)
    for (let j = 0; j < b.length; j++)
      r[i + j] = F.add(r[i + j], F.mul(a[i], b[j]));
  return normalize(F, r);
}
export function divmod(F, a, b) {                          // a = q*b + r
  if (!b.length) throw new Error('division by zero polynomial');
  let r = a.slice(), q = [];
  const db = deg(b), lb = b[db];
  while (deg(r) >= db) {
    const dr = deg(r), c = F.div(r[dr], lb), sh = dr - db;
    q[sh] = c;
    for (let i = 0; i <= db; i++)
      r[sh + i] = F.sub(coeff(F, r, sh + i), F.mul(c, b[i]));
    r = normalize(F, r);
  }
  for (let i = 0; i < q.length; i++) if (q[i] === undefined) q[i] = F.zero;
  return [normalize(F, q), r];
}
export const C = (F, c) => (F.isZero(c) ? [] : [c]);       // constant poly
export const X = F => [F.zero, F.one];
export function xpow(F, n) {
  const r = new Array(n + 1).fill(F.zero); r[n] = F.one; return r;
}
export function evalAt(F, p, x) {
  let acc = F.zero;
  for (let i = p.length - 1; i >= 0; i--) acc = F.add(F.mul(acc, x), p[i]);
  return acc;
}
export const eqPoly = (F, a, b) =>
  a.length === b.length && a.every((c, i) => F.eq(c, b[i]));
export const isMonic = (F, p) => p.length > 0 && F.isOne(p[p.length - 1]);
