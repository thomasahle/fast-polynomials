// Knuth-Eve "adaptation of coefficients" (preconditioning) for polynomial
// evaluation over floating-point numbers.
//
// SCHEME IMPLEMENTED - Eve's method, a.k.a. the Knuth-Eve algorithm:
//   T. S. Motzkin, "Evaluation of polynomials and evaluation of rational
//     functions", Bull. Amer. Math. Soc. 61 (1955), 163 (introduced the idea
//     of adapting/preconditioning coefficients);
//   D. E. Knuth, "Evaluation of polynomials by computer", CACM 5 (1962);
//   J. Eve, "The evaluation of polynomials", Numer. Math. 6 (1964), 17-21;
//   presented as Theorem E in D. E. Knuth, TAOCP vol. 2, 3rd ed., section 4.6.4.
//
// Theorem E (Knuth): every real polynomial u of degree n >= 3 can be written
//     y = x + c,  w = y^2,  z = y + e  (n odd)  or  z = w + b*y + e  (n even),
//     u(x) = (...((z (w - s_1) + c_1)(w - s_2) + c_2)...)(w - s_K) + c_K,
//     K = ceil(n/2) - 1,
// with REAL parameters, and one may even take c_K = 0.  The proof: with
// p(y) = u(y - c), the parameters s_k exist iff the polynomial O formed from
// the odd-numbered coefficients of p has only real roots (then the s_k are its
// roots), and Eve's theorem says that O has only real roots as soon as at
// least n-1 roots of p have real part <= 0 (or all >= 0), i.e. for every
// c <= -max Re(root of u) and every c >= -min Re(root of u).  Knuth's own
// choice puts the extreme root pair a +- bi on the imaginary axis (c = -a),
// which makes w + b^2 a factor of p and therefore c_K = 0.
//
// Construction, as implemented:
//   1. Admissibility of a shift c is decided EXACTLY: p(y) = u(y - c) is
//      formed in rational arithmetic (BigInt; the coefficients and the printed
//      shift are exact rationals), and O is real-rooted iff a Sturm sequence
//      of its square-free part counts deg O distinct real roots on the whole
//      line (repeated roots are handled through gcd(O, O')).  No floating-point
//      root-finding can therefore produce a "false" parameterisation, and no
//      shift is ever rejected because a near-double root of O was missed.
//   2. Candidate shifts.  The roots of u (Aberth-Ehrlich iteration in doubles)
//      give Eve's sufficient shifts on both sides (c = -max Re, c = -min Re,
//      a lone real extreme root allowed to stay outside); Fujiwara's root
//      bound gives an unconditional fallback.  Eve's condition is only
//      sufficient, and the adapted constants grow like (|x| + 2|c|)^n, so on
//      each side the SMALLEST admissible |c| is located by bisection between
//      0 and Eve's shift (each probe is the exact test of step 1), and a few
//      shifts between that minimum and Eve's are tried as well.
//   3. The nodes s_k (roots of O) are isolated by Sturm bisection and refined
//      by exact bisection to 2^-62 relative width, then rounded to the printed
//      precision.  Because every sign evaluation is exact, clustered or nearly
//      double roots cost nothing in accuracy.
//   4. Peel: O(s) = 0 gives  p(y) = (y^2 - s) p1(y) + E(s)  with p1 of the
//      same form.  One multiplication per peel (w is precomputed) and two
//      additions.  The additive constants are the Newton-form (divided-
//      difference) values of E at the nodes s_k, computed in double-double
//      from the exact shifted coefficients.  The peel ORDER changes the
//      constants and the rounding error enormously, so it is searched: six
//      heuristic orders, then a swap-based local search with random restarts,
//      all scored by an exact double-precision model of the printed chain.
//   5. Base case after all K peels:  y + e  (n odd)  or  w + b*y + e (n even).
//   The shift, its nodes and its best order are chosen by the measured error
//   of the printed chain; a shift that Eve's condition endorses on the "other"
//   side of the root set needs no reflection of the polynomial - it is simply
//   a shift of the other sign (Theorem E with c of either sign).
//
// MULTIPLICATION COUNT (documented formula): for the monic input this module
// requires, exactly
//     floor(n/2) + 1  =  1 (w = y*y) + K = ceil(n/2) - 1 (peels)
//                        + [n even]  (b*y)
// multiplications (one fewer in the measure-zero case b = 0), and at most
// n + 1 additions (n when c_K = 0 - Knuth's exact shift - or when no shift is
// needed).  A non-monic input would need one final scaling multiply, giving
// the classical count floor(n/2) + 2 of Eve/Knuth.  Compare Belaga's lower
// bound of ceil(n/2) multiplications with any preprocessing.
//
// PREPROCESSING lives in R, not Q: the adapted constants come from numeric
// root-finding (they are algebraic numbers, generally irrational), so they are
// only available as floats - in contrast with schemes whose preprocessing
// stays exactly inside the rationals.  They are never complex: Theorem E
// guarantees a real parameterisation for every real polynomial, and step 1
// only ever accepts one.
//
// NUMERICAL LIMIT.  The chain evaluates p(y) = E(w) + y O(w) through the
// even/odd parts of the SHIFTED polynomial, and E(w) = (u(x) + u(-x - 2c))/2:
// its intermediate values are as large as |u(-x - 2c)|/2 even where u(x)
// itself is small, so the rounding error of the printed chain in binary64 is
// about 2^-53 |u(-x - 2c)|, i.e. it grows like (|x| + 2|c|)^n with the degree
// (the classical loss of significance of adapted chains).  The smallest
// admissible |c| minimises it; nothing else in the scheme can.  compileMotzkin
// therefore never rejects a polynomial for numerical reasons: it returns the
// most accurate chain it found and reports its error, and only throws when
// even that chain is wrong to more than 1e-3 (which does not happen for
// degrees <= 24 with coefficients of ordinary size).
//
// VERIFICATION: the emitted chain (the literal rhs strings, so the printed
// constants are what is checked) is re-parsed and evaluated at 69 sample
// points (a 0.1-grid on [-3,3] plus larger points) against direct Horner
// evaluation of the input. maxRelError is the maximum of
// |chain - horner| / max(|horner|, 1e-3 * sum_i |p_i| max(1,|x|)^i); the floor
// keeps points at or near a root of p (x = 0 for a polynomial without constant
// term, say) from dividing by (numerical) zero.  Constants are printed with 13
// significant digits, escalated to 17 when the verification demands it.

// ---------- complex arithmetic on {re, im} ----------

export const C = (re, im = 0) => ({ re, im });
export const cAdd = (a, b) => C(a.re + b.re, a.im + b.im);
export const cSub = (a, b) => C(a.re - b.re, a.im - b.im);
export const cMul = (a, b) => C(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re);
export const cNeg = a => C(-a.re, -a.im);
export const cAbs = a => Math.hypot(a.re, a.im);
export function cDiv(a, b) {
  const d = b.re * b.re + b.im * b.im;
  return C((a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d);
}
export const isZeroC = z => z.re === 0 && z.im === 0;

export function hornerComplex(p, z) {            // p: complex array, ascending
  let v = C(0);
  for (let i = p.length - 1; i >= 0; i--) v = cAdd(cMul(v, z), p[i]);
  return v;
}

function hornerReal(p, x) {
  let v = 0;
  for (let i = p.length - 1; i >= 0; i--) v = v * x + p[i];
  return v;
}

// ---------- exact rational arithmetic on BigInt ----------
// {n, d} with d > 0 and gcd(n, d) = 1.  Used for everything whose truth
// matters (admissibility of a shift, the real roots of O); floating point is
// only used to propose candidates and to print.

const babs = a => (a < 0n ? -a : a);
function bgcd(a, b) {
  a = babs(a); b = babs(b);
  while (b) { [a, b] = [b, a % b]; }
  return a;
}
export function rat(n, d = 1n) {
  if (d === 0n) throw new Error('division by zero');
  if (d < 0n) { n = -n; d = -d; }
  const g = bgcd(n, d);
  return g > 1n ? { n: n / g, d: d / g } : { n, d };
}
export const rAdd = (a, b) => rat(a.n * b.d + b.n * a.d, a.d * b.d);
export const rSub = (a, b) => rat(a.n * b.d - b.n * a.d, a.d * b.d);
export const rMul = (a, b) => rat(a.n * b.n, a.d * b.d);
export const rDiv = (a, b) => rat(a.n * b.d, a.d * b.n);
export const rNeg = a => ({ n: -a.n, d: a.d });
export const rSign = a => (a.n > 0n ? 1 : a.n < 0n ? -1 : 0);
export const rCmp = (a, b) => rSign(rSub(a, b));
export const R0 = rat(0n), R1 = rat(1n);

/** The exact rational value of a finite double. */
export function ratFromDouble(v) {
  if (!Number.isFinite(v)) throw new Error(`non-finite value ${v}`);
  if (v === 0) return R0;
  let e = 0;
  while (!Number.isInteger(v)) { v *= 2; e++; }
  return rat(BigInt(v), 1n << BigInt(e));
}

/** The exact rational value of a decimal literal such as "-1.25e-3". */
export function ratFromDecimal(s) {
  const m = /^\s*([+-]?)(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?\s*$/.exec(String(s));
  if (!m || (m[2] === '' && (m[3] ?? '') === '')) throw new Error(`bad decimal literal ${s}`);
  const ip = m[2] || '0', fp = m[3] || '', ex = Number(m[4] || 0);
  let num = BigInt(ip + fp), den = 10n ** BigInt(fp.length);
  if (ex > 0) num *= 10n ** BigInt(ex); else if (ex < 0) den *= 10n ** BigInt(-ex);
  return rat(m[1] === '-' ? -num : num, den);
}

const bitLen = x => (x === 0n ? 0 : babs(x).toString(2).length);

/** Nearest-ish double (64-bit truncated quotient, then rounded). */
export function ratToDouble(r) {
  if (r.n === 0n) return 0;
  const neg = r.n < 0n, n = babs(r.n), d = r.d;
  const sh = 64 - (bitLen(n) - bitLen(d));
  const q = sh >= 0 ? (n << BigInt(sh)) / d : n / (d << BigInt(-sh));
  const v = Number(q) * Math.pow(2, -sh);
  return neg ? -v : v;
}

/** Double-double [hi, lo] of a rational. */
export function ratToDD(r) {
  const hi = ratToDouble(r);
  const lo = ratToDouble(rSub(r, ratFromDouble(hi)));
  return [hi, lo];
}

// ---------- integer polynomials and Sturm sequences ----------
// Primitive integer polynomials (BigInt, ascending, content 1, no leading
// zeros); everything a Sturm sequence needs is exact and sign-safe.

function ipTrim(ip) {
  let d = ip.length - 1;
  while (d > 0 && ip[d] === 0n) d--;
  return ip.slice(0, d + 1);
}
function ipPrimitive(ip) {
  ip = ipTrim(ip);
  let g = 0n;
  for (const c of ip) g = bgcd(g, c);
  return g > 1n ? ip.map(c => c / g) : ip;
}
/** Clear denominators of a rational polynomial and remove the content. */
export function ipFromRat(p) {
  let l = 1n;
  for (const c of p) l = (l / bgcd(l, c.d)) * c.d;
  return ipPrimitive(p.map(c => c.n * (l / c.d)));
}
const ipIsZero = ip => ip.length === 1 && ip[0] === 0n;
const ipDeriv = ip => (ip.length === 1 ? [0n] : ip.slice(1).map((c, i) => c * BigInt(i + 1)));

/** sign of ip(a/b) for a rational a/b (b > 0): homogeneous Horner. */
function ipSignAt(ip, r) {
  const a = r.n, b = r.d;
  let v = 0n, bp = 1n;
  for (let i = ip.length - 1; i >= 0; i--) { v = v * a + ip[i] * bp; bp *= b; }
  return v > 0n ? 1 : v < 0n ? -1 : 0;
}
function ipSignAtInf(ip, dir) {
  const d = ip.length - 1, l = ip[d];
  const s = l > 0n ? 1 : l < 0n ? -1 : 0;
  return dir > 0 || d % 2 === 0 ? s : -s;
}

/** lc(b)^(delta+1) * (a mod b), delta = deg a - deg b >= 0 (signed pseudo-remainder). */
function ipPremSigned(a, b) {
  let r = ipTrim(a.slice());
  const db = b.length - 1, lb = b[db], delta = r.length - 1 - db;
  let k = 0;
  while (!ipIsZero(r) && r.length - 1 >= db) {
    const dr = r.length - 1, top = r[dr];
    const nr = new Array(dr).fill(0n);
    for (let i = 0; i < dr; i++) nr[i] = lb * r[i];
    for (let i = 0; i < db; i++) nr[dr - db + i] -= top * b[i];
    r = ipTrim(nr.length ? nr : [0n]);
    k++;
  }
  for (; k < delta + 1; k++) r = r.map(c => c * lb);
  return r;
}
/** Exact quotient a / b of integer polynomials (b divides a over Q). */
function ipDivExact(a, b) {
  const ra = a.map(c => rat(c)), rb = b.map(c => rat(c));
  const db = rb.length - 1, q = new Array(Math.max(0, ra.length - rb.length) + 1).fill(R0);
  const rem = ra.slice();
  for (let i = rem.length - 1; i >= db; i--) {
    const c = rDiv(rem[i], rb[db]);
    q[i - db] = c;
    for (let j = 0; j <= db; j++) rem[i - db + j] = rSub(rem[i - db + j], rMul(c, rb[j]));
  }
  return ipFromRat(q);
}
/** Sturm data of an integer polynomial by the subresultant PRS of (p, p'):
 *  seq[i] is a POSITIVE multiple of the i-th canonical Sturm term (so sign
 *  variations count distinct real roots), and its last term is gcd(p, p')
 *  up to a scalar (gdeg = its degree).  Subresultants grow linearly and
 *  need exact divisions only - no content gcds. */
function sturmData(ip) {
  const a0 = ipTrim(ip), a1 = ipTrim(ipDeriv(a0));
  const prs = [a0, a1], signs = [1, 1];
  let g = 1n, h = 1n;
  const sgn = x => (x < 0n ? -1 : 1);
  for (;;) {
    const a = prs[prs.length - 2], b = prs[prs.length - 1];
    if (ipIsZero(b)) { prs.pop(); signs.pop(); break; }
    if (b.length === 1) break;                     // nonzero constant: the sequence ends
    const delta = (a.length - 1) - (b.length - 1);
    let r = ipPremSigned(a, b);
    if (ipIsZero(r)) break;
    const denom = g * h ** BigInt(delta);
    r = r.map(c => c / denom);                     // exact (subresultant theory)
    const lb = b[b.length - 1];
    // r = sigma * (a mod b), sigma = lc(b)^(delta+1) / (g h^delta)
    const sigma = (delta % 2 === 0 ? sgn(lb) : 1) * sgn(g) * (delta % 2 === 1 ? sgn(h) : 1);
    prs.push(r);
    signs.push(-sigma * signs[signs.length - 2]);
    g = lb;
    h = delta === 0 ? h : delta === 1 ? g : (g ** BigInt(delta)) / (h ** BigInt(delta - 1));
  }
  const seq = prs.map((p, i) => (signs[i] < 0 ? p.map(c => -c) : p));
  return { seq, gdeg: prs[prs.length - 1].length - 1 };
}
function sturmVar(seq, r) {                  // r: rational or +-Infinity
  let v = 0, last = 0;
  for (const p of seq) {
    const s = r === Infinity ? ipSignAtInf(p, 1) : r === -Infinity ? ipSignAtInf(p, -1) : ipSignAt(p, r);
    if (s === 0) continue;
    if (last !== 0 && s !== last) v++;
    last = s;
  }
  return v;
}
/** Number of distinct real roots in (lo, hi]. */
const sturmCount = (seq, lo, hi) => sturmVar(seq, lo) - sturmVar(seq, hi);

/** Cauchy bound as an integer rational: every real root lies in (-B, B]. */
function ipRootBound(ip) {
  const d = ip.length - 1, l = babs(ip[d]);
  let m = 0n;
  for (let i = 0; i < d; i++) { const q = babs(ip[i]) / l + 1n; if (q > m) m = q; }
  return rat(m + 1n);
}

// Refine an isolating interval (lo, hi] of a square-free polynomial to
// relative width 2^-62 (or until an exact rational root is hit).
function refineRoot(ip, seq, lo, hi) {
  let slo = ipSignAt(ip, lo), shi = ipSignAt(ip, hi);
  if (shi === 0) return hi;
  const two = rat(2n);
  for (let it = 0; it < 2200; it++) {
    const width = rSub(hi, lo);
    // mag = max(|lo|, |hi|); stop when width <= 2^-62 mag (or width is absurdly small)
    const loBig = babs(lo.n) * hi.d >= babs(hi.n) * lo.d;
    const magN = loBig ? babs(lo.n) : babs(hi.n), magD = loBig ? lo.d : hi.d;
    if ((magN !== 0n && width.n * magD * (1n << 62n) <= magN * width.d) || width.n * (1n << 1100n) <= width.d) break;
    const mid = rDiv(rAdd(lo, hi), two);
    const sm = ipSignAt(ip, mid);
    if (sm === 0) return mid;
    if (slo !== 0 && shi !== 0) {
      if (sm === slo) { lo = mid; slo = sm; } else { hi = mid; shi = sm; }
    } else {
      // an end point is itself a root (of the polynomial, outside (lo, hi]):
      // fall back to Sturm counting, which is exact regardless
      if (sturmCount(seq, lo, mid) === 1) { hi = mid; shi = sm; } else { lo = mid; slo = sm; }
    }
  }
  return rDiv(rAdd(lo, hi), two);
}

/** All real roots of a square-free integer polynomial (given its Sturm
 *  sequence), ascending, as rationals accurate to 2^-62 relative - or null
 *  if it is not real-rooted. */
function realRootsSquareFree(ip, seq) {
  const d = ip.length - 1;
  if (d <= 0) return [];
  if (sturmCount(seq, -Infinity, Infinity) !== d) return null;
  const B = ipRootBound(ip);
  const stack = [[rNeg(B), B, d]], iso = [];
  const two = rat(2n);
  while (stack.length) {
    const [lo, hi, cnt] = stack.pop();
    if (cnt === 0) continue;
    if (cnt === 1) { iso.push([lo, hi]); continue; }
    const mid = rDiv(rAdd(lo, hi), two);
    const cl = sturmCount(seq, lo, mid);
    stack.push([lo, mid, cl], [mid, hi, cnt - cl]);
  }
  return iso.map(([lo, hi]) => refineRoot(ip, seq, lo, hi)).sort(rCmp);
}

/** All real roots of an integer polynomial WITH multiplicity (a root of
 *  multiplicity m appears m times), or null unless every root is real. */
export function realRootsExact(ip) {
  ip = ipTrim(ip);
  if (ip.length - 1 <= 0) return [];
  const { seq, gdeg } = sturmData(ip);
  if (gdeg === 0) return realRootsSquareFree(ip, seq);
  const g = ipPrimitive(seq[seq.length - 1]);      // gcd(p, p') = prod f_i^(i-1)
  const sf = ipDivExact(ip, g);                    // square-free part, p = sf * g
  const roots = realRootsExact(sf);
  if (!roots) return null;
  const rest = realRootsExact(g);
  return rest ? roots.concat(rest).sort(rCmp) : null;
}
/** Is every root of the integer polynomial real (multiplicities allowed)? */
export function isRealRooted(ip) {
  ip = ipTrim(ip);
  const d = ip.length - 1;
  if (d <= 0) return true;
  const { seq, gdeg } = sturmData(ip);
  return sturmCount(seq, -Infinity, Infinity) === d - gdeg;   // distinct roots = d - deg gcd(p, p')
}

// ---------- double-double helpers (preprocessing accuracy) ----------

const SPLIT = 134217729;                  // 2^27 + 1 (Dekker splitting)
function twoProd(a, b) {
  const p = a * b;
  const a1 = SPLIT * a, ah = a1 - (a1 - a), al = a - ah;
  const b1 = SPLIT * b, bh = b1 - (b1 - b), bl = b - bh;
  return [p, ((ah * bh - p) + ah * bl + al * bh) + al * bl];
}
function twoSum(a, b) {
  const s = a + b, bb = s - a;
  return [s, (a - (s - bb)) + (b - bb)];
}
function quick(s, e) { const h = s + e; return [h, e - (h - s)]; }
function ddAdd(a, b) { const [s, e] = twoSum(a[0], b[0]); return quick(s, e + a[1] + b[1]); }
function ddMulD(a, x) { const [p, e] = twoProd(a[0], x); return quick(p, e + a[1] * x); }
const ddNum = a => a[0] + a[1];

function ddHorner(pd, x) {                // dd-poly at double x -> dd
  let v = [0, 0];
  for (let i = pd.length - 1; i >= 0; i--) v = ddAdd(ddMulD(v, x), pd[i]);
  return v;
}

// ---------- root finder for the shift selection ----------

// Fujiwara's bound: every root z of p satisfies |z| <= 2 max_i |a_{n-i}/a_n|^{1/i}.
// (Cauchy's 1 + max|a_i/a_n| is useless for coefficient ranges like n!/k!.)
export function rootBound(pReal) {
  const d = pReal.length - 1;
  let R = 0;
  for (let i = 1; i <= d; i++) R = Math.max(R, Math.pow(Math.abs(pReal[d - i] / pReal[d]), 1 / i));
  return R > 0 ? 2 * R : 1;
}

export function rootBoundComplex(pc) {          // Fujiwara over complex coefficients
  const d = pc.length - 1;
  let R = 0;
  for (let i = 1; i <= d; i++) R = Math.max(R, Math.pow(cAbs(pc[d - i]) / cAbs(pc[d]), 1 / i));
  return R > 0 ? 2 * R : 1;
}

// Newton polish of a root of the complex polynomial pc (ascending); no real
// snap, so a root that is real up to rounding keeps its tiny imaginary part.
function polishRootC(pc, z0) {
  let z = z0;
  for (let it = 0; it < 30; it++) {
    let dv = C(0), v = C(0);
    for (let i = pc.length - 1; i >= 0; i--) { dv = cAdd(cMul(dv, z), v); v = cAdd(cMul(v, z), pc[i]); }
    if (isZeroC(dv)) break;
    let step = cDiv(v, dv);
    const sa = cAbs(step), cap = 0.25 * (1 + cAbs(z));
    if (!Number.isFinite(sa)) break;
    if (sa > cap) step = C(step.re * cap / sa, step.im * cap / sa);
    const nz = cSub(z, step);
    if (!Number.isFinite(nz.re) || !Number.isFinite(nz.im)) break;
    z = nz;
    if (sa <= 1e-16 * (1 + cAbs(z))) break;
  }
  return z;
}

// Newton polish of a complex root of the real polynomial p (ascending).
function polishComplexRoot(p, z0) {
  const z = polishRootC(p.map(v => C(v)), z0);
  // a root with a negligible imaginary part is a real root
  return Math.abs(z.im) <= 1e-12 * (1 + Math.abs(z.re)) ? C(z.re) : z;
}

// Aberth-Ehrlich simultaneous iteration on the monic complex polynomial bc
// (ascending, degree d >= 2, bc[0] != 0) from d points on the circle of
// radius r0 inside the root bound R.  Returns the unpolished roots.
function aberthRoots(bc, d, R, r0) {
  const z = [];
  for (let k = 0; k < d; k++) {
    const ang = (2 * Math.PI * k) / d + 0.4;       // offset avoids the axes
    z.push(C(r0 * Math.cos(ang), r0 * Math.sin(ang)));
  }
  let converged = false;
  for (let it = 0; it < 500 && !converged; it++) {
    let maxRel = 0;
    for (let k = 0; k < d; k++) {
      let dv = C(0), v = C(0);
      for (let i = d; i >= 0; i--) { dv = cAdd(cMul(dv, z[k]), v); v = cAdd(cMul(v, z[k]), bc[i]); }
      if (isZeroC(v)) continue;
      let w = isZeroC(dv) ? C(1e-8 * (1 + cAbs(z[k]))) : cDiv(v, dv);   // Newton step
      let sum = C(0);
      for (let j = 0; j < d; j++) {
        if (j === k) continue;
        const diff = cSub(z[k], z[j]);
        if (cAbs(diff) < 1e-300) continue;
        sum = cAdd(sum, cDiv(C(1), diff));
      }
      let step = cDiv(w, cSub(C(1), cMul(w, sum)));   // Aberth correction
      const sa = cAbs(step), cap = 0.5 * (1 + cAbs(z[k]));
      if (!Number.isFinite(sa)) {
        z[k] = C(R * Math.cos(2.4 * k + 0.1 * it), R * Math.sin(2.4 * k + 0.1 * it));
        maxRel = Infinity;
        continue;
      }
      if (sa > cap) step = C(step.re * cap / sa, step.im * cap / sa);
      z[k] = cSub(z[k], step);
      maxRel = Math.max(maxRel, cAbs(step) / (1 + cAbs(z[k])));
    }
    if (maxRel < 1e-15) converged = true;
  }
  return z;
}

// |bc(r)| <= 1e-8 sum |b_i| |r|^i for every root r, else null.
function checkedRoots(bc, d, roots) {
  for (const r of roots) {
    let scale = 0, rp = 1;
    const ar = cAbs(r);
    for (let i = 0; i <= d; i++) { scale += cAbs(bc[i]) * rp; rp *= ar; }
    if (!(cAbs(hornerComplex(bc, r)) <= 1e-8 * scale)) return null;
  }
  return roots;
}

// All roots of a real polynomial, or null when the iteration does not
// converge.  Aberth-Ehrlich simultaneous iteration (cubically convergent,
// robust to the wide coefficient ranges of Taylor polynomials) from points on
// a circle inside Fujiwara's bound, Newton polish, then a residual check
// |p(z)| <= 1e-8 sum |a_i| |z|^i on every root.  Exact roots at 0 (missing
// constant term) are split off first.
export function polyRoots(pReal) {
  let d = pReal.length - 1;
  if (d <= 0) return [];
  const a = pReal.map(c => c / pReal[d]);          // monic
  let zeros = 0;
  while (zeros < d && a[zeros] === 0) zeros++;
  const out = [];
  for (let i = 0; i < zeros; i++) out.push(C(0));
  const b = a.slice(zeros);                        // b[0] != 0
  d = b.length - 1;
  if (d === 0) return out;
  if (d === 1) return out.concat([C(-b[0])]);
  const R = rootBound(b);
  const bc = b.map(v => C(v));
  let r0 = Math.pow(Math.abs(b[0]), 1 / d);
  r0 = Math.min(Math.max(r0, 1e-3 * R), R);
  const z = aberthRoots(bc, d, R, r0);
  const roots = checkedRoots(bc, d, z.map(zk => polishComplexRoot(b, zk)));
  return roots && out.concat(roots);
}

// All roots of a polynomial with complex coefficients ({re, im} ascending),
// or null: the same Aberth iteration and residual check as polyRoots, but
// the roots are kept complex (no conjugate pairing, no real snap - a
// polynomial with complex coefficients has neither).
export function polyRootsComplex(pc) {
  let d = pc.length - 1;
  if (d <= 0) return [];
  const a = pc.map(c => cDiv(c, pc[d]));           // monic
  let zeros = 0;
  while (zeros < d && isZeroC(a[zeros])) zeros++;
  const out = [];
  for (let i = 0; i < zeros; i++) out.push(C(0));
  const b = a.slice(zeros);                        // b[0] != 0
  d = b.length - 1;
  if (d === 0) return out;
  if (d === 1) return out.concat([cNeg(b[0])]);
  const R = rootBoundComplex(b);
  let r0 = Math.pow(cAbs(b[0]), 1 / d);
  r0 = Math.min(Math.max(r0, 1e-3 * R), R);
  const z = aberthRoots(b, d, R, r0);
  const roots = checkedRoots(b, d, z.map(zk => polishRootC(b, zk)));
  return roots && out.concat(roots);
}

// ---------- constant formatting ----------

// The value rounded to `digits` significant digits, printed in its shortest
// round-trip form (so a short decimal such as a 7-digit shift prints as
// itself even at 17-digit precision; the printed literal parses back to
// exactly the quantized double).
export function fmt(v, digits) {
  if (Object.is(v, -0)) v = 0;
  return String(Number(v.toPrecision(digits)));
}

export function fmtC(z, digits) {                // complex literal (a+bi)
  if (z.im === 0) return fmt(z.re, digits);
  return `(${fmt(z.re, digits)}${z.im < 0 ? '-' : '+'}${fmt(Math.abs(z.im), digits)}i)`;
}

// expr + constant with the sign folded in; exact zeros are skipped
export function appendConst(expr, z, digits) {
  if (isZeroC(z)) return expr;
  if (z.im === 0) return `${expr}${z.re < 0 ? ' - ' : ' + '}${fmt(Math.abs(z.re), digits)}`;
  return `${expr} + ${fmtC(z, digits)}`;
}

// ---------- rhs mini-parser/evaluator over complex doubles ----------
// Grammar:  expr := term (('+'|'-') term)* ;  term := factor ('*' factor)* ;
//           factor := ['-'] (number['i'] | ident | '(' expr ')')

function evalRhs(src, env) {
  let i = 0;
  const ws = () => { while (i < src.length && src[i] === ' ') i++; };
  function expr() {
    let v = term();
    for (;;) {
      ws();
      const c = src[i];
      if (c === '+' || c === '-') { i++; const t = term(); v = c === '+' ? cAdd(v, t) : cSub(v, t); }
      else return v;
    }
  }
  function term() {
    let v = factor();
    for (;;) { ws(); if (src[i] === '*' || src[i] === '·') { i++; v = cMul(v, factor()); } else return v; }
  }
  function factor() {
    ws();
    let neg = false;
    if (src[i] === '-') { neg = true; i++; ws(); }
    let v;
    if (src[i] === '(') {
      i++; v = expr(); ws();
      if (src[i] !== ')') throw new Error(`bad rhs (missing ')'): ${src}`);
      i++;
    } else {
      const rest = src.slice(i);
      const num = /^\d+(?:\.\d+)?(?:[eE][+-]?\d+)?i?/.exec(rest);
      if (num) {
        i += num[0].length;
        v = num[0].endsWith('i') ? C(0, parseFloat(num[0].slice(0, -1))) : C(parseFloat(num[0]));
      } else {
        const id = /^[\p{L}_][\p{L}\p{M}\w]*/u.exec(rest);   // wires: x, y3, P, P̃ (combining tilde)
        if (!id || !(id[0] in env)) throw new Error(`bad rhs (unknown atom) in: ${src}`);
        i += id[0].length;
        v = env[id[0]];
      }
    }
    return neg ? cNeg(v) : v;
  }
  const v = expr();
  ws();
  if (i !== src.length) throw new Error(`bad rhs (trailing input): ${src}`);
  return v;
}

// ---------- verification against direct Horner ----------
// Relative error against Horner, with the reference floored at 1e-3 of the
// coefficient scale S(x) = sum_i |p_i| max(1,|x|)^i: passing at 1e-6 means an
// error below 1e-6 |p(x)| away from the roots of p and below 1e-9 S(x) near
// them.  S never vanishes (unlike sum_i |p_i| |x|^i, which is 0 at x = 0 for
// a polynomial without constant term, where the previous floor rejected every
// chain that merely rounded to 1e-12 there), and a floor is needed at all
// because an adapted chain, unlike Horner, does not compute p(x) = 0 exactly:
// its rounding error is set by the size of its constants, not by |p(x)|.

// A dense grid: an adapted chain's rounding error varies with x, and a
// coarse grid can miss a point near a root of p where the relative error
// is largest.
export const SAMPLE_XS = (() => {
  const xs = [];
  for (let i = -30; i <= 30; i++) xs.push(i / 10);
  xs.push(4, -4, 5, -5, 7, -7, 10, -10);
  return xs;
})();

export function relErrorAt(p, x, gotRe, gotIm) {
  const want = hornerReal(p, x);
  let scale = 0, xp = 1;
  const ax = Math.max(1, Math.abs(x));
  for (let i = 0; i < p.length; i++) { scale += Math.abs(p[i]) * xp; xp *= ax; }
  const denom = Math.max(Math.abs(want), 1e-3 * scale, 1e-300);
  const err = Math.hypot(gotRe - want, gotIm) / denom;
  return Number.isFinite(err) ? err : Infinity;
}

export function verifyLines(lines, p) {
  let maxRel = 0;
  for (const x of SAMPLE_XS) {
    const env = Object.create(null);
    env.x = C(x);
    for (const ln of lines) env[ln.lhs] = evalRhs(ln.rhs, env);
    const err = relErrorAt(p, x, env.P.re, env.P.im);
    if (err > maxRel) maxRel = err;
  }
  return maxRel;
}

// ---------- verification over C ----------
// The same check for a polynomial with complex coefficients ({re, im} or
// plain numbers, ascending): the real grid above plus points off the real
// axis (three circles, 16 directions each, and the unit-box corners), the
// reference computed by complex Horner and the error measured in |.| with the
// same floor 1e-3 S(z), S(z) = sum_i |p_i| max(1,|z|)^i.  A chain over C is
// a polynomial identity in z, so the real grid alone would pin it down, but
// its rounding error is largest where |z| is largest in every direction.
export const SAMPLE_ZS = (() => {
  const zs = SAMPLE_XS.map(x => C(x));
  for (const r of [0.5, 1.5, 3]) {
    for (let k = 0; k < 16; k++) {
      const ang = (2 * Math.PI * k) / 16 + Math.PI / 16;   // never on the axes
      zs.push(C(r * Math.cos(ang), r * Math.sin(ang)));
    }
  }
  zs.push(C(0, 1), C(0, -1), C(1, 1), C(-1, 1), C(1, -1), C(-1, -1), C(0, 5), C(0, -5));
  return zs;
})();

export const toComplex = v => (typeof v === 'object' && v !== null && 're' in v
  ? C(Number(v.re), Number(v.im ?? 0)) : C(Number(v)));

export function relErrorAtComplex(pc, z, got) {
  const want = hornerComplex(pc, z);
  let scale = 0, zp = 1;
  const az = Math.max(1, cAbs(z));
  for (let i = 0; i < pc.length; i++) { scale += cAbs(pc[i]) * zp; zp *= az; }
  const denom = Math.max(cAbs(want), 1e-3 * scale, 1e-300);
  const err = cAbs(cSub(got, want)) / denom;
  return Number.isFinite(err) ? err : Infinity;
}

export function verifyLinesComplex(lines, coeffs) {
  const pc = coeffs.map(toComplex);
  let maxRel = 0;
  for (const z of SAMPLE_ZS) {
    const env = Object.create(null);
    env.x = z;
    for (const ln of lines) env[ln.lhs] = evalRhs(ln.rhs, env);
    const err = relErrorAtComplex(pc, z, env.P);
    if (err > maxRel) maxRel = err;
  }
  return maxRel;
}

// ---------- peel orderings (they differ wildly in numerical quality) ----------

// Greedily pick the node minimizing the next divided-difference constant.
function greedyOrder(Edd, sArr, skipFirst) {
  let E = Edd.map(v => v.slice());
  const rem = sArr.slice(), out = [];
  let first = true;
  while (rem.length) {
    const vals = rem.map(s => Math.abs(ddNum(ddHorner(E, s))));
    let bi = 0;
    if (first && skipFirst && rem.length > 1) {
      bi = [...vals.keys()].sort((a, b) => vals[a] - vals[b])[1];
    } else {
      for (let i = 1; i < rem.length; i++) if (vals[i] < vals[bi]) bi = i;
    }
    first = false;
    const s = rem.splice(bi, 1)[0];
    out.push(s);
    const dE = E.length - 1, Eq = new Array(dE);
    Eq[dE - 1] = E[dE];
    for (let j = dE - 2; j >= 0; j--) Eq[j] = ddAdd(E[j + 1], ddMulD(Eq[j + 1], s));
    E = Eq;
  }
  return out;
}

// Leja-style: start nearest zero, then maximize distance products.
function lejaOrder(sArr) {
  const rem = sArr.slice(), out = [];
  let bi = 0;
  for (let i = 1; i < rem.length; i++) if (Math.abs(rem[i]) < Math.abs(rem[bi])) bi = i;
  out.push(rem.splice(bi, 1)[0]);
  while (rem.length) {
    let best = 0, bv = -Infinity;
    for (let i = 0; i < rem.length; i++) {
      let lp = 0;
      for (const o of out) lp += Math.log(Math.abs(rem[i] - o) + 1e-300);
      if (lp > bv) { bv = lp; best = i; }
    }
    out.push(rem.splice(best, 1)[0]);
  }
  return out;
}

function altOrder(sortedAsc) {            // large, small, large2, small2, ...
  const out = [];
  let lo = 0, hi = sortedAsc.length - 1, takeHi = true;
  while (lo <= hi) { out.push(takeHi ? sortedAsc[hi--] : sortedAsc[lo++]); takeHi = !takeHi; }
  return out;
}

// ---------- chain emission ----------
// y = x + c, w = y*y, base z, then the peels from the innermost node
// sArr[K-1] to the outermost sArr[0] (cs[k] is the constant added after the
// multiplication by w - sArr[k]).  All constants are real doubles; they are
// printed with `digits` significant digits and the printed strings are what
// the verification evaluates.

function emitChain(n, c, sArr, cs, eBase, bLead, digits) {
  const odd = n % 2 === 1;
  const lines = [];
  const depth = { x: 0 };
  let mults = 0, adds = 0;
  const push = (lhs, rhs, mul, deps) => {
    lines.push({ lhs, rhs, mul });
    depth[lhs] = Math.max(0, ...deps.map(dp => depth[dp])) + (mul ? 1 : 0);   // multiplicative depth: the shift y = x + c adds none
    if (mul) mults++;
  };
  let yName = 'x';
  if (c !== 0) {
    yName = 'y';
    push('y', appendConst('x', C(c), digits), false, ['x']);
    adds++;
  }
  push('w', `${yName} * ${yName}`, true, [yName]);
  let accExpr, accDeps;
  if (odd) {                                       // base: y + e
    accExpr = appendConst(yName, C(eBase), digits);
    if (accExpr !== yName) adds++;
    accDeps = [yName];
  } else if (bLead !== 0) {                        // base: w + b*y + e
    push('z', `${fmt(bLead, digits)} * ${yName}`, true, [yName]);
    accExpr = appendConst('w + z', C(eBase), digits);
    adds += accExpr === 'w + z' ? 1 : 2;
    accDeps = ['w', 'z'];
  } else {
    accExpr = appendConst('w', C(eBase), digits);
    if (accExpr !== 'w') adds++;
    accDeps = ['w'];
  }
  const K = sArr.length;
  for (let k = K - 1; k >= 0; k--) {               // innermost peel first
    const factor = appendConst('w', C(-sArr[k]), digits);
    if (factor !== 'w') adds++;
    const accAtom = /^[A-Za-z_]\w*$/.test(accExpr) ? accExpr : `(${accExpr})`;
    const rhs = `${accAtom} * (${factor})`;
    const withC = appendConst(rhs, C(cs[k]), digits);
    if (withC !== rhs) adds++;
    const lhs = k === 0 ? 'P' : `t${K - 1 - k}`;
    push(lhs, withC, true, [...accDeps, 'w']);
    accExpr = lhs;
    accDeps = [lhs];
  }
  return { lines, mults, adds, height: depth.P };
}

// ---------- adapted constants and their numeric model ----------
// The peel constants c_k are the Newton-form values of the even part E at the
// nodes s_k (synthetic division in double-double), quantized to the printed
// precision so that the model below and the printed chain agree bit for bit.
// A constant below the printing resolution (relative to the coefficient size
// of the shifted polynomial) is an exact 0 of the scheme, e.g. c_K = 0 for
// Knuth's shift, and is dropped so the addition is saved.
function chainConstants(qdd, sArr, digits) {
  const n = qdd.length - 1;
  const E = [], O = [];
  for (let j = 0; j <= n; j++) (j % 2 ? O : E).push(qdd[j]);
  let qSum = 0;
  for (const c of qdd) qSum += Math.abs(ddNum(c));
  const tiny = Math.pow(10, -digits) * qSum;
  const quant = v => { const r = parseFloat(fmt(ddNum(v), digits)); return Math.abs(r) <= tiny ? 0 : r; };
  let Ec = E.map(v => v.slice());
  const cs = [];
  for (const s of sArr) {
    const dE = Ec.length - 1, Eq = new Array(dE);
    Eq[dE - 1] = Ec[dE];
    for (let j = dE - 2; j >= 0; j--) Eq[j] = ddAdd(Ec[j + 1], ddMulD(Eq[j + 1], s));
    cs.push(quant(ddAdd(Ec[0], ddMulD(Eq[0], s))));
    Ec = Eq;
  }
  return { cs, eBase: quant(Ec[0]), bLead: n % 2 === 0 ? quant(O[O.length - 1]) : 0 };
}

// Evaluate the chain in doubles with exactly the operations, in the same
// order, that the printed rhs strings perform (see emitChain), so the search
// below optimizes the error of the chain that will actually be emitted.
function evalChainModel(n, c, sArr, k, x) {
  const odd = n % 2 === 1;
  const y = x + c;
  const w = y * y;
  let acc;
  if (odd) acc = y + k.eBase;
  else if (k.bLead !== 0) acc = (w + k.bLead * y) + k.eBase;
  else acc = w + k.eBase;
  for (let i = sArr.length - 1; i >= 0; i--) acc = acc * (w - sArr[i]) + k.cs[i];
  return acc;
}

function modelError(p, n, c, sArr, k) {
  let maxRel = 0;
  for (const x of SAMPLE_XS) {
    const err = relErrorAt(p, x, evalChainModel(n, c, sArr, k, x), 0);
    if (err > maxRel) maxRel = err;
    if (maxRel === Infinity) break;
  }
  return maxRel;
}

// ---------- peel-order search ----------
// The K peels can be taken in any order; the divided-difference constants
// and hence the rounding error depend on it enormously.  Starting from the
// heuristic orders, a first-improvement local search over pairwise swaps
// (with a few random restarts) minimizes the model error directly.
function searchOrder(p, n, c, qdd, sArr, digits, budget) {
  const Edd = qdd.filter((_, j) => j % 2 === 0);
  const asc = sArr.slice().sort((a, b) => a - b);
  const cache = new Map();
  let evals = 0;
  const cost = ord => {
    const key = ord.join(',');
    let v = cache.get(key);
    if (v === undefined) {
      evals++;
      v = modelError(p, n, c, ord, chainConstants(qdd, ord, digits));
      cache.set(key, v);
    }
    return v;
  };
  let seed = 0x9e3779b9 ^ (n * 7919);
  const rnd = () => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed / 4294967296; };
  const shuffled = () => {
    const o = sArr.slice();
    for (let i = o.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [o[i], o[j]] = [o[j], o[i]]; }
    return o;
  };
  const starts = [
    greedyOrder(Edd, sArr, false), greedyOrder(Edd, sArr, true),
    asc.slice().reverse(), asc, lejaOrder(sArr), altOrder(asc),
  ];
  let best = null, bestErr = Infinity;
  const localSearch = ord0 => {
    let ord = ord0.slice(), cur = cost(ord);
    let improved = true;
    while (improved && evals < budget) {
      improved = false;
      for (let i = 0; i < ord.length && !improved; i++) {
        for (let j = i + 1; j < ord.length; j++) {
          const t = ord.slice();
          [t[i], t[j]] = [t[j], t[i]];
          const cst = cost(t);
          if (cst < cur) { ord = t; cur = cst; improved = true; break; }
          if (evals >= budget) break;
        }
      }
    }
    if (cur < bestErr) { bestErr = cur; best = ord; }
    return cur;
  };
  for (const st of starts) { localSearch(st); if (bestErr < 1e-10) return { ord: best, err: bestErr }; }
  // random restarts (bounded by count, not only by evaluations: for small K
  // every order is soon cached and costs nothing)
  for (let t = 0; t < 40 && evals < budget && bestErr >= 1e-10; t++) localSearch(shuffled());
  return { ord: best, err: bestErr };
}

// ---------- shifts: exact admissibility and the search for small ones ----------

// The exact odd part O of p(y) = u(y - c) as a primitive integer polynomial,
// with the exact shifted coefficients available on demand; null if O is
// degenerate (Theorem E needs deg O = K, i.e. u_{n-1} - n c != 0 for even n).
// Pure integer arithmetic: u = U/D (U integer coefficients), c = Cn/Cd, and
// P(Y) = D Cd^n u(Y/Cd) has integer coefficients U_i Cd^(n-i); the shift
// P(Y - Cn) is an integer Ruffini-Horner pass, and the coefficient of y^j in
// u(y - c) is its j-th coefficient times Cd^j / (D Cd^n), so O is the odd
// part of it up to a positive scalar.
function shiftedParts(uInt, D, cR) {
  const n = uInt.length - 1, K = Math.ceil(n / 2) - 1;
  const Cd = cR.d, T = -cR.n;
  const V = new Array(n + 1);
  let pw = 1n;
  for (let i = n; i >= 0; i--) { V[i] = uInt[i] * pw; pw *= Cd; }
  for (let i = 0; i < n; i++) for (let j = n - 1; j >= i; j--) V[j] += V[j + 1] * T;
  const O = [];
  let cp = Cd;
  for (let j = 1; j <= n; j += 2) { O.push(V[j] * cp); cp *= Cd * Cd; }
  if (O.length !== K + 1 || O[K] === 0n) return null;
  const q = () => {
    const den = D * Cd ** BigInt(n);
    return V.map((v, j) => rat(v * Cd ** BigInt(j), den));
  };
  return { q, O: ipTrim(O) };
}

// Candidate shifts on each side of the root set, ordered so that the
// smallest admissible |c| is tried first.  Every returned c is admissible
// (exactly verified); `knuth` marks Eve's own shift (c_K = 0 when the
// extreme roots are a complex pair).
function admissibleShifts(p, uInt, D) {
  const parts = c => shiftedParts(uInt, D, ratFromDecimal(fmt(c, 13)));
  const admissible = c => { const sp = parts(c); return !!sp && isRealRooted(sp.O); };
  const round = (c, digits) => parseFloat(fmt(c, digits));
  const roots = polyRoots(p);
  const RB = rootBound(p);
  // Eve's shifts: [side, c].  side +1: c <= -max Re (roots go left);
  // side -1: c >= -min Re (roots go right).  A lone real extreme root may
  // stay outside (Eve needs only n-1 roots).
  const eve = [];
  if (roots) {
    const isReal = z => z.im === 0;
    for (const side of [1, -1]) {
      const rs = roots.map(r => C(side * r.re, r.im))
        .sort((a, b) => (b.re - a.re) || (Math.abs(a.im) - Math.abs(b.im)));
      const r0 = rs[0], r1 = rs[1];
      let exact;
      if (!isReal(r0)) exact = r0.re;
      else if (r1 && !isReal(r1)) exact = r1.re;
      else if (r1) exact = 0.5 * (r0.re + r1.re);
      else exact = r0.re;
      eve.push([side, -side * exact]);
      if (isReal(r0)) eve.push([side, -side * r0.re]);
    }
  }
  const out = [];
  const seen = new Set();
  const add = (c, tag) => { const key = String(c); if (!seen.has(key)) { seen.add(key); out.push({ c, tag }); } };
  if (admissible(0)) { add(0, 'none'); return out; }
  for (const side of [1, -1]) {
    // a safe (admissible) shift on this side: Eve's, pushed outward if the
    // computed roots were not accurate enough, the root bound as last resort
    const proposals = eve.filter(([s]) => s === side).map(([, c]) => c).sort((a, b) => Math.abs(a) - Math.abs(b));
    let cSafe = null, tagSafe = 'eve';
    for (const c0 of proposals) {
      let c = round(c0, 13);
      for (let t = 0; t < 8 && cSafe === null; t++) {
        if (admissible(c)) cSafe = c;
        else { c = round(-side * (Math.abs(c) * 1.05 + 0.02 * RB), 13); tagSafe = 'margin'; }
      }
      if (cSafe !== null) break;
    }
    if (cSafe === null) {
      const c = round(-side * RB, 13);
      if (admissible(c)) { cSafe = c; tagSafe = 'bound'; }
      else continue;
    }
    // the smallest admissible |c| on this side, by bisection from 0
    let cIn = 0, cOut = cSafe;
    for (let it = 0; it < 16; it++) {
      const mid = round(0.5 * (cIn + cOut), 7);
      if (mid === cIn || mid === cOut) break;
      if (admissible(mid)) cOut = mid; else cIn = mid;
    }
    add(cOut, cOut === cSafe ? tagSafe : 'min');
    for (const f of [0.15, 0.4]) {
      const c = round(cOut + f * (cSafe - cOut), 7);
      if (c !== cOut && c !== cSafe && admissible(c)) add(c, 'between');
    }
    add(cSafe, tagSafe);
  }
  return out.sort((a, b) => Math.abs(a.c) - Math.abs(b.c));
}

// ---------- main entry point ----------

const SCREEN_BUDGET = 1200;               // model evaluations per candidate shift
const REFINE_BUDGET = 4000;               // ... for the best candidates
const REFINE_TOP = 3;

/**
 * Eve's explicit real decomposition data for an odd polynomial, exposed for
 * Pan's real scheme (9).  The input may be non-monic: normalization does not
 * change the admissible shift or the roots of the odd part.  Every returned
 * candidate has been certified real-rooted by the exact Sturm test above;
 * `nodes` are all roots (with multiplicity) of that odd part.
 */
export function eveOddDecompositionCandidates(coeffs) {
  if (!Array.isArray(coeffs) || coeffs.length < 4)
    throw new Error('need a degree >= 3 polynomial');
  const raw = coeffs.map(Number);
  if (!raw.every(Number.isFinite)) throw new Error('coefficients must be finite numbers');
  const n = raw.length - 1, lc = raw[n];
  if (n % 2 === 0) throw new Error('odd degree required');
  if (lc === 0) throw new Error('leading coefficient must be nonzero');
  const p = raw.map(v => v / lc);
  const uRat = p.map(ratFromDouble);
  let D = 1n;
  for (const r of uRat) D = (D / bgcd(D, r.d)) * r.d;
  const uInt = uRat.map(r => r.n * (D / r.d));
  const out = [];
  for (const cand of admissibleShifts(p, uInt, D)) {
    const sp = shiftedParts(uInt, D, ratFromDecimal(fmt(cand.c, 13)));
    if (!sp) continue;
    const roots = realRootsExact(sp.O);
    if (!roots) continue;
    const nodes = roots.map(r => ratToDouble(r));
    if (nodes.every(Number.isFinite)) out.push({ shift: cand.c, nodes, tag: cand.tag });
  }
  return out;
}

// Knuth--Eve's decomposition starts at degree 3.  These are its elementary
// base cases, exposed through the same compiler entry point so the comparison
// row is useful for every polynomial degree (including constants).
export function compileKnuthEve(coeffs) {
  if (!Array.isArray(coeffs) || coeffs.length === 0)
    throw new Error('need a nonempty coefficient array');
  const p = coeffs.map(Number), n = p.length - 1;
  if (!p.every(Number.isFinite))
    throw new Error('coefficients must be finite numbers');
  if (n >= 3) return compileMotzkin(p);
  if (n > 0 && p[n] !== 1)
    throw new Error('input must be monic (coeffs[n] === 1)');

  let lines, mults = 0, adds = 0;
  if (n === 0) {
    lines = [{ lhs: 'P', rhs: String(p[0]), mul: false }];
  } else if (n === 1) {
    const rhs = appendConst('x', C(p[0]), 17);
    adds = rhs === 'x' ? 0 : 1;
    lines = [{ lhs: 'P', rhs, mul: false }];
  } else {
    const right = appendConst('x', C(p[1]), 17);
    lines = [
      { lhs: 'q2', rhs: `x * (${right})`, mul: true },
      { lhs: 'P', rhs: appendConst('q2', C(p[0]), 17), mul: false },
    ];
    mults = 1;
    adds = (right === 'x' ? 0 : 1) + (lines[1].rhs === 'q2' ? 0 : 1);
  }
  const err = verifyLines(lines, p);
  return {
    name: 'Knuth-Eve base case', lines, mults, adds, height: mults,
    preprocessing: 'real', preprocessingLabel: 'elementary real preprocessing',
    exact: false, maxRelError: err,
    note: `elementary degree-${n} base case of the Knuth–Eve real construction`,
  };
}

export function compileMotzkin(coeffs) {
  if (!Array.isArray(coeffs) || coeffs.length < 4)
    throw new Error('need a degree >= 3 polynomial');
  const p = coeffs.map(Number);
  if (!p.every(Number.isFinite))
    throw new Error('coefficients must be finite numbers');
  const n = p.length - 1;
  if (p[n] !== 1)
    throw new Error('input must be monic (coeffs[n] === 1)');
  const K = Math.ceil(n / 2) - 1;
  const uRat = p.map(ratFromDouble);                 // u = U / D exactly
  let D = 1n;
  for (const r of uRat) D = (D / bgcd(D, r.d)) * r.d;
  const uInt = uRat.map(r => r.n * (D / r.d));

  // Every candidate shift is admissible (exact test); for each one the exact
  // real roots of the odd part are the nodes, and a peel order is searched.
  const cands = admissibleShifts(p, uInt, D);
  const prepared = [];
  for (const cand of cands) {
    const sp = shiftedParts(uInt, D, ratFromDecimal(fmt(cand.c, 13)));
    if (!sp) continue;
    const nodes = realRootsExact(sp.O);
    if (!nodes || nodes.length !== K) continue;      // cannot happen for an admissible shift
    const qdd = sp.q().map(ratToDD);
    const s17 = nodes.map(r => parseFloat(fmt(ratToDouble(r), 17)));
    if (!s17.every(Number.isFinite)) continue;
    const r = searchOrder(p, n, cand.c, qdd, s17, 17, SCREEN_BUDGET);
    prepared.push({ err: r.err, ord: r.ord, qdd, c: cand.c, tag: cand.tag });
    if (r.err < 1e-10) break;
  }
  if (!prepared.length) {
    throw new Error('no admissible shift found (the polynomial has no real ' +
      'parameterisation of the required form: degenerate odd part for every shift)');
  }
  prepared.sort((a, b) => a.err - b.err);
  let best = prepared[0];
  if (best.err >= 1e-10) {
    for (const cand of prepared.slice(0, REFINE_TOP)) {
      const s17 = cand.ord;
      const r = searchOrder(p, n, cand.c, cand.qdd, s17, 17, REFINE_BUDGET);
      if (r.err < best.err) best = { ...cand, err: r.err, ord: r.ord };
    }
  }

  // Emit with 13 printed digits when that is accurate enough, else 17; the
  // printed strings are what is verified.
  let chosen = null;
  for (const digits of [13, 17]) {
    const sArr = best.ord.map(v => parseFloat(fmt(v, digits)));
    const k = chainConstants(best.qdd, sArr, digits);
    const chain = emitChain(n, best.c, sArr, k.cs, k.eBase, k.bLead, digits);
    const err = verifyLines(chain.lines, p);
    if (!chosen || err < chosen.err) chosen = { err, chain };
    if (err <= 1e-9) break;
  }
  if (!(chosen.err <= 1e-3)) {
    throw new Error('the adapted constants exceed double precision at this degree - ' +
      `max relative error ${chosen.err.toExponential(3)} over ${prepared.length} admissible shifts and ` +
      'their peel orders (the real parameterisation exists by Knuth\'s Theorem E and was found, but ' +
      'its constants are too large for the chain to be evaluated accurately in binary64: the ' +
      'rounding error of an adapted chain grows like (|x| + 2|c|)^n with the degree)');
  }

  const note = 'coefficient adaptation (Motzkin 1955 / Eve 1964; Knuth TAOCP 4.6.4, ' +
    `Thm E): after the shift y = x${best.c < 0 ? ' - ' : ' + '}${fmt(Math.abs(best.c), 6)} ` +
    '(the smallest shift whose odd part is real-rooted, decided exactly by Sturm sequences) ' +
    'the constants are the real roots of the odd part and its divided differences - ' +
    'algebraic numbers found numerically, so they live in R rather than Q and the chain is ' +
    'only correct up to floating-point error';
  return {
    name: 'Motzkin-Eve adaptation',
    lines: chosen.chain.lines,
    mults: chosen.chain.mults,
    adds: chosen.chain.adds,
    height: chosen.chain.height,
    preprocessing: 'real',
    exact: false,
    note,
    maxRelError: chosen.err,
    shift: best.c,
  };
}
