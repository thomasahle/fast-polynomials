// Characteristic-2 lane: fixed circuits with complete, exactly-invertible
// decoders at the odd degrees n = 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25 — all
// using floor(n/2)+1 multiplications (n=7 and n=17 need finite fields, the
// rest are polynomial decoders valid over every field of characteristic two).
// Ported from the paper repo's Python reference decoders and search tools:
//   n=3:  char2/worked_examples.py (_eval_n3); unit-pivot (identity coordinates)
//   n=5:  square-first search over the legal-gate grammar (all 128 circuits
//         with both key-free slots on the seed y=x*x; the fewest-XOR winner is
//         the universal head y, z=(y+a0)(x+y+a1), t=(x+a2)(z+a3) of the
//         certified n=15/19/21 family); unit-pivot, valid over EVERY
//         characteristic-2 field
//   n=7:  the complete GF(2) (7,4) solution set (tools/char2_complete_sets.c,
//         14,336 circuits) contains NO circuit with a unit Jacobian, so no
//         polynomial (everywhere-defined) decoder exists in this gate grammar;
//         the circuit below has the explicit two-square-root decoder (rows
//         x^5 and x^3 are Frobenius pivots) — perfect fields only, i.e. every
//         finite GF(2^k)
//   n=9:  char2/worked_examples.py (_eval_n9); unit-pivot in linear
//         coordinates (greedy_unitriangular of tools/char2_rebuild19.py),
//         valid over EVERY characteristic-2 field
//   n=11: char2/worked_examples.py's _eval_n11 has a singular Jacobian (no
//         polynomial decoder exists for it), so this is a fresh circuit: the
//         universal head y, z, t plus three gates, found by a GF(2)-bijectivity +
//         unit-Jacobian sweep over all 6-gate extensions of that head (131,072
//         bijective, 65,536 unit-Jacobian) and certified by the exact symbolic
//         unit-pivot decoder — fewest XORs (17) among the certified circuits;
//         valid over EVERY characteristic-2 field
//   n=13: char2/decode_n13.py (closed-form back-substitution, unit pivots)
//   n=15/19/21: char2/verify_n{15,19,21}_unitriangular_symbolic.py
//               (square-first unitriangular family; generic baseline decoder;
//                valid over EVERY field of characteristic two)
//   n=17: char2/decode_n17_uniform.py (2 square pivots + 1 fourth-power pivot;
//         perfect fields — every finite GF(2^k) qualifies)
//   n=23: char2/verify_n23_unitriangular_symbolic.py (core-B square-first family:
//         the ten-gate prefix of (25,13) with a two-gate exit; transcribed via
//         tools/char2_rebuild19.py C23). KEYS_FROM_Q[23] is that certificate's
//         polynomial key-coordinate inverse (its rho/aa/bb/cc helpers; a19 =
//         q14 + [x^8] P(a | a19 = 0), exactly as the certificate defines it) with
//         the certificate's terminal four-row block (its q18, q19) rewritten as
//         unit pivots, Q19 = q18 and Q18 = q19 + (q0 + q8 + 1) q18, so that the
//         generic baseline decoder applies; every field of characteristic two
//   n=25: char2/verify_n25_unitriangular_symbolic.py (circuit transcribed via
//         tools/char2_frontier27.py C25). Its 24-step certificate is a chain of
//         elementary substitutions a_j := q_i + tail_i whose fully expanded
//         inverse is far too large to transcribe (13,417 monomials in a22 alone),
//         so the chain is replayed numerically (chainRun): with the four "late"
//         keys a14, a16, a18, a20 fixed by their 1–4-term closed forms, every
//         tail is affine in the still-undecoded keys with slopes 1, q0+q6 or
//         q0+q6+1 (spec.chain), and the constant parts are read off the circuit.
//         Unit pivots only — every field of characteristic two
import * as P from './poly.js';
import { decodeN13 } from './n13decode.js';

// ---------- circuit specs ----------
// gate: { w: wireName, l: {t: [taps], k: keyIndex|null}, r: {...} }
// out:  { t: [taps], k: keyIndex }
// family: 'unitriangular' — unit-pivot decoder (KEYS_FROM_Q coordinates), every char-2 field
//         'closed-form'   — hand-transpiled back-substitution (n=13), every char-2 field
//         'frobenius'     — unit pivots plus 2^t-th-root rows (rootDepths), finite fields GF(2^k)
//         'pivot-loop'    — n=17's hand-written Frobenius decoder, finite fields GF(2^k)
const g = (w, lt, lk, rt, rk) => ({ w, l: { t: lt, k: lk }, r: { t: rt, k: rk } });

const COMMON6 = [
  g('y', ['x'], null, ['x'], null),
  g('z', ['y'], 0, ['x', 'y'], 1),
  g('t', ['x'], 2, ['z'], 3),
  g('u', ['y', 't'], 4, ['z', 't'], 5),
  g('v', ['x', 'z'], 6, ['z'], 7),
  g('w', ['x', 'y', 'z'], 8, ['y', 'v'], 9),
];
// the ten-gate prefix shared by the certified (23,12) and (25,13) circuits
const COREB = [
  g('y', ['x'], null, ['x'], null),
  g('z', ['y'], 0, ['x', 'y'], 1),
  g('t', ['x'], 2, ['z'], 3),
  g('u', ['y', 'z', 't'], 4, ['z', 't'], 5),
  g('v', ['x'], 6, ['y', 'z'], 7),
  g('w', ['x', 'y', 'z'], 8, ['y', 'v'], 9),
  g('s', ['z'], 10, ['v'], 11),
  g('r', ['x', 't'], 12, ['u'], 13),
  g('g', ['z', 't'], 14, ['x', 'u'], 15),
  g('l', ['x'], 16, ['z', 'v'], 17),
];
const ONE = () => 1n;

export const CIRCUITS = {
  3: {
    n: 3, keys: 3, family: 'unitriangular',
    gates: [
      g('y', ['x'], null, ['x'], null),
      g('z', ['x'], 0, ['x', 'y'], 1),
    ],
    out: { t: ['z'], k: 2 },
  },
  5: {
    n: 5, keys: 5, family: 'unitriangular',
    gates: [...COMMON6.slice(0, 3)],
    out: { t: ['t'], k: 4 },
  },
  7: {
    n: 7, keys: 7, family: 'frobenius',
    gates: [
      g('y', ['x'], null, ['x'], 0),
      g('z', ['x'], 1, ['y'], 2),
      g('t', ['z'], null, ['z'], 3),
      g('u', ['x'], 4, ['y', 't'], 5),
    ],
    out: { t: ['u'], k: 6 },
    rootDepths: [0, 1, 0, 1, 0, 0, 0],          // rows x^6 .. x^0
  },
  9: {
    n: 9, keys: 9, family: 'unitriangular',
    gates: [
      g('y', ['x'], null, ['x'], 0),
      g('z', ['x'], null, ['y'], 1),
      g('t', ['y', 'z'], 2, ['z'], 3),
      g('u', ['x', 'z'], 4, ['t'], 5),
      g('v', ['y'], 6, ['z'], 7),
    ],
    out: { t: ['u', 'v'], k: 8 },
  },
  11: {
    n: 11, keys: 11, family: 'unitriangular',
    gates: [...COMMON6.slice(0, 3),
      g('u', ['x'], 4, ['y'], 5),
      g('v', ['z', 'u'], 6, ['y', 'z', 'u'], 7),
      g('w', ['u'], 8, ['t', 'v'], 9),
    ],
    out: { t: ['z', 'w'], k: 10 },
  },
  13: {
    n: 13, keys: 13, family: 'closed-form',
    gates: [
      g('y', ['x'], null, ['x'], null),
      g('z', ['x', 'y'], 12, ['y'], 11),
      g('w', ['y', 'z'], 10, ['z'], 9),
      g('v', ['y', 'z'], 8, ['w'], 7),
      g('u', ['z', 'v'], 6, ['x'], 5),
      g('t', ['x', 'y'], 4, ['x'], 3),
      g('s', ['w', 't'], 2, ['y'], 1),
    ],
    out: { t: ['v', 'u', 's'], k: 0 },
  },
  15: {
    n: 15, keys: 15, family: 'unitriangular',
    gates: [...COMMON6,
      g('s', ['z'], 10, ['v'], 11),
      g('r', ['t'], 12, ['u'], 13),
    ],
    out: { t: ['w', 's', 'r'], k: 14 },
  },
  17: {
    n: 17, keys: 17, family: 'pivot-loop',
    gates: [
      g('y', ['x'], null, ['x'], 0),
      g('z', ['x'], 1, ['x', 'y'], 2),
      g('t', ['y'], 3, ['x', 'y'], 4),
      g('u', ['y', 'z'], 5, ['z', 't'], 6),
      g('v', ['x', 'z'], 7, ['x', 'z', 't', 'u'], 8),
      g('h', ['y'], 9, ['x'], null),
      g('j', ['y'], 10, ['x'], 11),
      g('l', ['t'], 12, ['h'], 13),
      g('w', ['x', 'u'], 14, ['u', 'v'], 15),
    ],
    out: { t: ['j', 'l', 'w'], k: 16 },
  },
  19: {
    n: 19, keys: 19, family: 'unitriangular',
    gates: [...COMMON6,
      g('s', ['x'], 10, ['y'], 11),
      g('r', ['x'], 12, ['y'], 13),
      g('q', ['v'], 14, ['t', 'v', 's'], 15),
      g('l', ['s'], 16, ['u', 'w', 'q'], 17),
    ],
    out: { t: ['r', 'l'], k: 18 },
  },
  21: {
    n: 21, keys: 21, family: 'unitriangular',
    gates: [...COMMON6,
      g('s', ['x'], 10, ['y'], 11),
      g('r', ['x'], 12, ['y'], 13),
      g('q', ['v'], 14, ['t', 'v', 's'], 15),
      g('l', ['s'], 16, ['u', 'w', 'q'], 17),
      g('m', ['t', 's'], 18, ['z', 'u', 'w', 'q'], 19),
    ],
    out: { t: ['m', 'z', 'r', 'l'], k: 20 },
  },
  23: {
    n: 23, keys: 23, family: 'unitriangular',
    gates: [...COREB,
      g('m', ['x', 'y', 'z'], 18, ['x', 'y', 'z', 'w', 's', 'g', 'l'], 19),
      g('n', ['z'], 20, ['u', 'm'], 21),
    ],
    out: { t: ['y', 'v', 'w', 's', 'r', 'g', 'n'], k: 22 },
  },
  25: {
    n: 25, keys: 25, family: 'unitriangular',
    gates: [...COREB,
      g('h', ['y', 'z', 't'], 18, ['x', 'y', 'z', 'u', 'v', 'w', 'r'], 19),
      g('j', ['x', 'y', 't'], 20, ['l'], 21),
      g('n', ['x', 't', 'u', 's', 'r', 'g', 'l', 'h', 'j'], 22, ['t'], 23),
    ],
    out: { t: ['y', 'z', 'u', 'l', 'n'], k: 24 },
    // The 24-step certificate (verify_n25_*.py pivot_order + a24), replayed by
    // chainRun: pivots[i] is the key that enters row x^(24-i) with unit slope;
    // late: the keys whose tails are not affine in the others, with their closed
    // forms in the q's; steps[i]: dep = the tail involves late keys (its constant
    // part is then read off the circuit), slopes = the tail's coefficients of the
    // still-undecoded non-late keys. Steps not listed have an empty tail.
    chain: {
      pivots: [2, 0, 1, 3, 4, 12, 6, 5, 23, 7, 9, 13, 8, 17, 10, 11, 15, 19, 21, 22, 18, 16, 14, 20, 24],
      late: {
        14: Q => Q[22], 16: Q => Q[21], 20: Q => Q[23],
        18: (Q, F) => Q[20] ^ F.mul(Q[0] ^ Q[6] ^ 1n, Q[21]),
      },
      steps: {
        1: { slopes: { 1: ONE } },
        4: { dep: true, slopes: { 5: ONE, 12: ONE, 23: ONE } },
        5: { slopes: { 23: ONE } },
        9: { dep: true, slopes: { 8: ONE, 13: ONE } },
        10: { dep: true, slopes: { 13: Q => Q[0] ^ Q[6] } },
        11: { dep: true }, 12: { dep: true }, 13: { dep: true },
        14: { dep: true, slopes: { 15: ONE, 19: ONE, 21: ONE } },
        15: { dep: true, slopes: { 15: Q => Q[0] ^ Q[6] ^ 1n, 19: Q => Q[0] ^ Q[6] ^ 1n,
                                  21: Q => Q[0] ^ Q[6] } },
        16: { dep: true, slopes: { 19: ONE, 21: ONE } },
        17: { dep: true, slopes: { 21: ONE } },
        18: { dep: true }, 19: { dep: true },
      },
    },
  },
};

// ---------- generic evaluator ----------
function factorPoly(F, wires, keys, f) {
  let p = [];
  for (const tap of f.t) p = P.add(F, p, wires[tap]);
  if (f.k !== null) p = P.add(F, p, P.C(F, keys[f.k]));
  return p;
}
export function evalCircuit(spec, keys, F) {
  const wires = { x: P.X(F) };
  for (const gate of spec.gates)
    wires[gate.w] = P.mul(F, factorPoly(F, wires, keys, gate.l),
                             factorPoly(F, wires, keys, gate.r));
  return { coeffs: factorPoly(F, wires, keys, spec.out), wires };
}
/** Coefficient of x^r of the circuit output; every wire is truncated to degree
 *  <= r on the way (the x^r coefficient of a product only needs the factors'
 *  coefficients up to x^r), so low rows cost a fraction of a full evaluation. */
export function circuitCoeff(spec, keys, F, r) {
  const mulT = (a, b) => {
    if (!a.length || !b.length) return [];
    const out = new Array(Math.min(a.length + b.length - 1, r + 1)).fill(F.zero);
    for (let i = 0; i < a.length && i <= r; i++)
      for (let j = 0; j < b.length && i + j <= r; j++)
        out[i + j] = F.add(out[i + j], F.mul(a[i], b[j]));
    return P.normalize(F, out);
  };
  const wires = { x: r >= 1 ? P.X(F) : [] };
  for (const gate of spec.gates)
    wires[gate.w] = mulT(factorPoly(F, wires, keys, gate.l), factorPoly(F, wires, keys, gate.r));
  return P.coeff(F, factorPoly(F, wires, keys, spec.out), r);
}

// ---------- stats ----------
export function circuitStats(spec) {
  const depth = { x: 0 };
  let xors = 0;
  for (const gate of spec.gates) {
    let dmax = 0;
    for (const f of [gate.l, gate.r]) {
      xors += f.t.length - 1 + (f.k !== null ? 1 : 0);
      for (const tap of f.t) dmax = Math.max(dmax, depth[tap]);
    }
    depth[gate.w] = dmax + 1;
  }
  xors += spec.out.t.length - 1 + (spec.out.k !== null ? 1 : 0);
  let height = 0;
  for (const tap of spec.out.t) height = Math.max(height, depth[tap]);
  return { mults: spec.gates.length, adds: xors, height };
}

// ---------- pivot coordinate changes (a = A(q)) ----------
// Row n-1-i of P(A(q)) reads q_i^(2^d_i) + K_i(q_0..q_{i-1}) with d_i = rootDepths[i]
// (0 = unit pivot). Every entry is a polynomial over GF(2) in the q's, so with all
// d_i = 0 the decoder is defined over every field of characteristic two.
const KEYS_FROM_Q = {
  3: (Q, F) => [Q[0], Q[1], Q[2]],
  5: (Q, F) => [Q[1] ^ Q[2], Q[2], Q[0], Q[3], Q[4]],
  7: (Q, F) => [
    Q[1] ^ Q[4], Q[4], Q[3] ^ F.mul(Q[1], Q[4]) ^ F.mul(Q[4], Q[4]),
    Q[2], Q[0], Q[5], Q[6],
  ],
  9: (Q, F) => [
    Q[0], Q[1], Q[2] ^ Q[3], Q[3] ^ Q[4], Q[4], Q[5] ^ Q[7], Q[7], Q[6], Q[8],
  ],
  // pivots (row, key): (10,4) (9,5) (8,8) (7,6) (6,2) (5,7) (4,3) (3,9) (2,1) (1,0) (0,10)
  11: (Q, F) => {
    const M = (a, b) => F.mul(a, b);
    const [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10] = Q;
    const q0_2 = M(q0, q0), q3_2 = M(q3, q3), q8_2 = M(q8, q8), q8_3 = M(q8_2, q8),
      q8_4 = M(q8_3, q8), q8_5 = M(q8_4, q8), q8_6 = M(q8_5, q8), q9_2 = M(q9, q9),
      q9_3 = M(q9_2, q9), q9_4 = M(q9_3, q9);
    return [
      q9,                                                                       // a0
      q8 ^ q9,                                                                  // a1
      q4 ^ q8 ^ q9,                                                             // a2
      q6 ^ M(q1, q9) ^ M(q3, q9) ^ q9_2 ^ M(q1, q8_2) ^ M(q8_2, q9),             // a3
      q0,                                                                       // a4
      q1,                                                                       // a5
      q3 ^ q4 ^ q5 ^ q9 ^ M(q0, q9) ^ M(q3, q8) ^ M(q8, q9) ^ q8_2 ^ M(q0, q8_2) ^ q8_3, // a6
      q5 ^ M(q0, q9) ^ M(q3, q8) ^ M(q8, q9) ^ M(q0, q8_2) ^ q8_3,               // a7
      q2,                                                                       // a8
      q7 ^ M(q5, q9) ^ M(q6, q8) ^ M(q6, q9) ^ M(M(q0, q1), q9) ^ M(M(q0, q3), q9) ^  // a9
        M(M(q0, q4), q9) ^ M(q0, q9_2) ^ M(M(q1, q4), q9) ^ M(M(q1, q8), q9) ^ M(q1, q9_2) ^
        M(M(q3, q4), q8) ^ M(M(q3, q4), q9) ^ M(q3_2, q8) ^ M(M(q4, q8), q9) ^ M(q4, q9_2) ^
        M(q5, q8_2) ^ M(q8, q9_2) ^ M(q8_2, q9) ^ q9_3 ^ M(M(q0, q1), q8_2) ^
        M(M(q0, q3), q8_2) ^ M(M(q0, q4), q8_2) ^ M(q0_2, q9_2) ^ M(M(q1, q4), q8_2) ^
        M(M(q1, q8_2), q9) ^ M(q1, q8_3) ^ M(q3_2, q8_2) ^ M(M(q4, q8_2), q9) ^ M(q4, q8_3) ^
        q9_4 ^ M(q0, q8_4) ^ q8_5 ^ M(q0_2, q8_4) ^ q8_6,
      q10,                                                                      // a10
    ];
  },
  15: (Q, F) => [
    Q[2], Q[1] ^ Q[2], Q[0], Q[3], Q[4] ^ Q[5] ^ Q[7], Q[5],
    Q[8] ^ Q[11], Q[11], Q[6] ^ Q[12] ^ Q[13], Q[13],
    Q[12] ^ Q[13], Q[10] ^ Q[13], Q[7], Q[9], Q[14],
  ],
  19: (Q, F) => [
    Q[5], Q[4] ^ Q[5], Q[3], Q[8], Q[12] ^ Q[14], Q[14],
    Q[9], Q[6] ^ Q[8] ^ Q[9], Q[13], Q[11] ^ Q[12] ^ Q[14],
    Q[0], Q[1], Q[16], Q[17], Q[10] ^ Q[12],
    Q[7] ^ Q[10] ^ Q[12] ^ Q[13] ^ F.mul(Q[8], Q[8]) ^ Q[8],
    Q[2], Q[15], Q[18],
  ],
  21: (Q, F) => [
    Q[2], Q[1] ^ Q[2], Q[0], Q[3], Q[12] ^ Q[14], Q[14],
    Q[9], Q[6] ^ Q[8] ^ Q[3] ^ Q[9], Q[13], Q[11] ^ Q[12] ^ Q[14],
    Q[5], Q[8], Q[18], Q[19], Q[10] ^ Q[12],
    Q[7] ^ Q[8] ^ F.mul(Q[8], Q[8]) ^ F.mul(Q[0], Q[8]) ^ F.mul(Q[5], Q[8])
      ^ Q[10] ^ Q[12] ^ Q[13] ^ F.mul(Q[3], Q[3]) ^ Q[3],
    Q[4] ^ Q[16], Q[17], Q[16], Q[15], Q[20],
  ],
  // verify_n23_unitriangular_symbolic.py's inverse, in that script's letters;
  // its block coordinates q18, q19 are Q19 and Q18 + (Q0 + Q8 + 1) Q19 here.
  23: (Q, F) => {
    const m = (a, b) => F.mul(a, b), sq = a => F.mul(a, a);
    const q18 = Q[19], q19 = Q[18] ^ m(Q[0] ^ Q[8] ^ 1n, Q[19]);
    const w = m(Q[7], Q[16]) ^ sq(Q[16]) ^ Q[20];
    const rho = m(Q[0] ^ Q[8], w) ^ m(Q[7], Q[16]) ^ sq(Q[16]);
    const cc = Q[0] ^ Q[3] ^ Q[5] ^ Q[6] ^ Q[8] ^ Q[9] ^ Q[11] ^ 1n;
    const aa = cc ^ sq(Q[7]), bb = m(Q[7], cc) ^ 1n;
    const a = new Array(23).fill(0n);
    a[0] = Q[2]; a[1] = Q[1] ^ Q[2]; a[2] = Q[0]; a[3] = Q[3] ^ Q[5] ^ Q[6];
    a[4] = Q[4] ^ Q[5] ^ Q[6] ^ Q[7]; a[5] = Q[16]; a[6] = Q[8]; a[7] = Q[11] ^ w;
    a[12] = Q[15] ^ Q[16]; a[13] = Q[17] ^ q18; a[14] = Q[7] ^ Q[16]; a[15] = Q[20];
    a[16] = q18; a[17] = Q[21]; a[18] = Q[5]; a[20] = Q[6]; a[21] = q19; a[22] = Q[22];
    a[11] = Q[13] ^ sq(sq(Q[16])) ^ m(aa, sq(Q[16])) ^ m(bb, Q[16]) ^ sq(Q[20])
      ^ m(cc, Q[20]) ^ q18 ^ Q[21];
    a[10] = Q[12] ^ rho ^ Q[16] ^ a[11] ^ a[12];
    a[9] = Q[10] ^ rho ^ a[11] ^ Q[20] ^ q18;
    a[8] = Q[9] ^ sq(Q[16]) ^ m(Q[7], Q[16]) ^ a[10] ^ Q[20] ^ q18;
    // a19 occurs in row x^8 with unit slope and in no other key formula:
    // a19 = q14 + [x^8] P(a | a19 = 0)  (row x^8 then reads exactly q14)
    a[19] = Q[14] ^ circuitCoeff(CIRCUITS[23], a, F, 8);
    return a;
  },
  // the chain replay (a polynomial map, evaluated rather than written out)
  25: (Q, F) => chainRun(CIRCUITS[25], F, null, Q),
};
/** The key coordinates a = A(q) of a unit-pivot degree (tests and tooling). */
export const keysFromQ = (n, Q, F) => KEYS_FROM_Q[n](Q, F);

// ---------- decoders ----------
// c = [c0 .. c_{n-1}] of a MONIC degree-n polynomial (top coefficient dropped).
// Top-down pivot loop: with q_i.. = 0 the base circuit reproduces K_i, so the
// residual of row n-1-i is q_i (unit pivot) or q_i^(2^d) (Frobenius pivot, taken
// back by the unique 2^d-th root of the finite field).
function decodeUnitriangular(n, c, F) {
  const spec = CIRCUITS[n], A = KEYS_FROM_Q[n], depths = spec.rootDepths;
  const Q = new Array(n).fill(0n);
  for (let i = 0; i < n; i++) {
    const r = c[n - 1 - i] ^ circuitCoeff(spec, A(Q, F), F, n - 1 - i);
    Q[i] = depths && depths[i] ? F.rootPow2(r, depths[i]) : r;
  }
  return A(Q, F);
}

// n = 17: ported from decode_n17_uniform.py
function aff(F, ...polys) { return polys.reduce((a, b) => P.add(F, a, b), []); }
const withK = (F, p, k) => P.add(F, p, P.C(F, k));

function unequalDegreeOffsets(F, lower, higher, qHigher, qLower, degLower, degHigher) {
  const baseline = P.mul(F, lower, higher);
  const a = qHigher ^ P.coeff(F, baseline, degHigher);
  const withA = P.add(F, baseline, P.scale(F, a, higher));
  const b = qLower ^ P.coeff(F, withA, degLower);
  return [a, b];
}

function keysFromNormalized17(zc, F) {
  const [q1, q2, ss, rr, q0, ee, q14, q6, q5, q15, q8, q9, q12, q13, q10, q11, q16] = zc;
  const q3 = ss ^ q0;
  const q4 = ee ^ F.sq(q5) ^ q5;
  const q7 = rr ^ q5;
  const x = P.X(F);
  const a = new Array(17).fill(0n);
  a[0] = q0;
  const y = P.mul(F, x, withK(F, x, a[0]));
  [a[1], a[2]] = unequalDegreeOffsets(F, x, aff(F, x, y), q1, q2, 1, 2);
  const zw = P.mul(F, withK(F, x, a[1]), withK(F, aff(F, x, y), a[2]));
  const sigma = q3 ^ F.sq(q0) ^ q0;
  a[3] = q4 ^ F.mul(q0, sigma);
  a[4] = sigma ^ a[3];
  const t = P.mul(F, withK(F, y, a[3]), withK(F, aff(F, x, y), a[4]));
  [a[5], a[6]] = unequalDegreeOffsets(F, aff(F, y, zw), aff(F, zw, t), q5, q6, 3, 4);
  const u = P.mul(F, withK(F, aff(F, y, zw), a[5]), withK(F, aff(F, zw, t), a[6]));
  [a[7], a[8]] = unequalDegreeOffsets(F, aff(F, x, zw), aff(F, x, zw, t, u), q7, q8, 3, 7);
  const v = P.mul(F, withK(F, aff(F, x, zw), a[7]), withK(F, aff(F, x, zw, t, u), a[8]));
  a[9] = q9;
  const h = P.mul(F, withK(F, y, a[9]), x);
  [a[11], a[10]] = unequalDegreeOffsets(F, x, y, q10, q11, 1, 2);
  [a[13], a[12]] = unequalDegreeOffsets(F, h, t, q12, q13, 3, 4);
  [a[14], a[15]] = unequalDegreeOffsets(F, aff(F, x, u), aff(F, u, v), q14, q15, 7, 10);
  a[16] = q16;
  return a;
}

function decodeN17(c, F) {
  const degrees = [16, 15, 13, 14, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0];
  const rootDepths = [0, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0];
  const normalized = new Array(17).fill(0n);
  for (let i = 0; i < 17; i++) {
    const keys = keysFromNormalized17(normalized, F);
    const base = evalCircuit(CIRCUITS[17], keys, F).coeffs;
    const residual = c[degrees[i]] ^ P.coeff(F, base, degrees[i]);
    normalized[i] = F.rootPow2(residual, rootDepths[i]);
  }
  return keysFromNormalized17(normalized, F);
}

// ---------- chained unit pivots (n = 25) ----------
// The certificate is a chain of elementary substitutions: at row n-1-i the key
// pivots[i] enters with unit slope, a_j = q_i + tail_i, and tail_i involves only
// keys pivoted later. With the late keys fixed the tail is affine in the still-
// undecoded keys, so the chain is replayed as an exact elimination: each decoded
// key is kept as an affine form alpha + sum_k beta_k b_k in the undecoded non-late
// keys; the constant part is the row at the current alphas minus K_i (the same row
// at the prefix point A(q_0..q_{i-1}, 0, ..)), the slopes come from spec.chain, and
// b_j is substituted into the earlier forms. A late pivot fixes its key from the
// closed form and re-eliminates the earlier keys at the new late values. Every
// quantity is a polynomial in the q's, so this decoder is defined over every
// field of characteristic two. With c given it decodes (q_i = c_{n-1-i} - K_i);
// with Q given it evaluates the coordinate change A(Q).
function chainRun(spec, F, c, Qgiven = null) {
  const n = spec.n, { pivots, late, steps } = spec.chain;
  const Q = new Array(n).fill(0n), base = new Array(n).fill(0n);
  let lateVals = [];                                      // [key, value] pairs
  const fresh = () => {
    const alpha = new Array(n).fill(0n);
    for (const [j, v] of lateVals) alpha[j] = v;
    return { alpha, beta: new Map() };
  };
  const step = (E, i, zero) => {                          // eliminate key pivots[i] from row n-1-i
    const j = pivots[i], st = steps[i] || {}, { alpha, beta } = E;
    if (st.dep) {
      if (zero === undefined) zero = circuitCoeff(spec, alpha, F, n - 1 - i);
      alpha[j] = Q[i] ^ zero ^ base[i];
    } else alpha[j] = Q[i];
    const bj = new Map();
    for (const k in st.slopes || {}) bj.set(Number(k), st.slopes[k](Q, F));
    for (const [jj, bb] of beta) {                        // substitute b_j into the earlier forms
      if (!bb.has(j)) continue;
      const cf = bb.get(j); bb.delete(j);
      alpha[jj] ^= F.mul(cf, alpha[j]);
      for (const [k, s] of bj) bb.set(k, (bb.get(k) ?? 0n) ^ F.mul(cf, s));
    }
    beta.set(j, bj);
  };
  let E = fresh();
  for (let i = 0; i < n; i++) {
    const j = pivots[i], row = n - 1 - i;
    base[i] = circuitCoeff(spec, E.alpha, F, row);        // K_i(q_0..q_{i-1})
    Q[i] = Qgiven ? Qgiven[i] : c[row] ^ base[i];
    if (late[j]) {                                        // late pivot: fix it, redo the earlier keys
      const Qp = Q.map((v, t) => (t <= i ? v : 0n));
      lateVals = Object.entries(late).map(([k, f]) => [Number(k), f(Qp, F)]);
      E = fresh();
      for (let t = 0; t < i; t++) if (!late[pivots[t]]) step(E, t);
    } else step(E, i, base[i]);
  }
  return E.alpha;
}

/** Decode monic degree-n coefficients c0..c_{n-1} to the circuit keys. */
export function decodeChar2(n, c, F) {
  if (!(n in CIRCUITS)) throw new Error(`no char-2 decoder for degree ${n}`);
  if (n === 13) return decodeN13(c, F);
  if (n === 17) return decodeN17(c, F);
  if (CIRCUITS[n].chain) return chainRun(CIRCUITS[n], F, c);
  return decodeUnitriangular(n, c, F);
}
/** The odd degrees that carry a fixed circuit above (3, 5, ..., 25). */
export const CIRCUIT_DEGREES = Object.keys(CIRCUITS).map(Number);
/** Largest degree the lane compiles; 27 is the paper's open frontier. */
export const MAX_DEGREE = 26;
/** Every degree the lane compiles, 1..26: the odd degrees 3..25 by their
 *  circuits, 1 and 2 directly (P = x + a0, P = x (x + a1) + a0), and every
 *  even degree 4..26 by lifting the circuit of degree n-1 with one extra
 *  multiplication, P = x · P_{n-1} + c0 (js/compile2.js). */
export const SUPPORTED_DEGREES = Array.from({ length: MAX_DEGREE }, (_, i) => i + 1);
/** The circuit degree behind degree n: n itself when odd (and for the one-gate
 *  degree-2 chain), n-1 (then lifted by x) for even n >= 4. */
export const baseDegree = n => (n % 2 || n <= 2 ? n : n - 1);
/** True when the degree's decoder is a polynomial map (no root extraction),
 *  i.e. defined over every field of characteristic two (the even lift and the
 *  degree-1/2 identities are polynomial, so they inherit the base circuit's class). */
export const isEverywhereDefined = n =>
  n <= 2 || ['unitriangular', 'closed-form'].includes(CIRCUITS[baseDegree(n)]?.family);
