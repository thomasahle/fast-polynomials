// polyparse.test.js — the user-input grammar: every spelling a person is
// likely to type for the same polynomial reads to the same coefficients, and
// the rejections name the actual problem.
import { parsePoly, polyToString } from '../js/polyparse.js';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };
const eq = (a, b, msg) => check(JSON.stringify(a) === JSON.stringify(b), `${msg}: ${JSON.stringify(a)} != ${JSON.stringify(b)}`);
const str = (src, o) => polyToString(parsePoly(src, o).coeffs, o);
const rejects = (src, re, o) => {
  try { parsePoly(src, o); check(false, `${JSON.stringify(src)} should be rejected`); }
  catch (e) { check(re.test(e.message), `${JSON.stringify(src)} rejected with a clear message: ${e.message}`); }
};

// ---- characteristic 0: equivalent spellings --------------------------------
const taylor = 'x^4 + 1/6·x^3 + 1/2·x^2 + x + 1';
for (const src of [
  'x^4 + x^3/6 + x^2/2 + x + 1',        // a term divided by an integer
  'x^4 + 1/6x^3 + 1/2x^2 + x + 1',      // fraction coefficient
  'x^4 + (1/6)x^3 + (1/2)*x^2 + x + 1', // parenthesized coefficient, explicit *
  'x⁴ + x³/6 + x²/2 + x + 1',           // Unicode superscripts
  'x**4 + x**3/6 + x**2/2 + x + 1',     // Python-style powers
  'x^4 + x^3·(1/6) + x^2 × 0.5 + x + 1', // trailing coefficient, · and × products
  '1 + x + x^2/2 + x^3/6 + x^4',        // ascending order
  '  x^4+x^3/6+x^2/2+x+1  ',            // whitespace-free
]) eq(str(src), taylor, `reads ${JSON.stringify(src)}`);
eq(str('x^5 − 1/4x^4 + 1/3x^3'), 'x^5 − 1/4·x^4 + 1/3·x^3', 'Unicode minus');
eq(str('3x^2/2 - x/2'), '3/2·x^2 − 1/2·x', 'coefficient and divisor combine');
eq(str('2*x + x*2 + x·3 + 4×x'), '11·x', 'like terms add');
eq(str('(−1/2)x + (-3)'), '-1/2·x − 3', 'negative parenthesized coefficients');
eq(str('-x + 1'), '-x + 1', 'a coefficient of −1 prints as a bare minus');
eq(str('0.5x^3 - 1.5e-2x + 2e1 + .25x^2'), '1/2·x^3 + 1/4·x^2 − 3/200·x + 20', 'decimals and exponents stay exact');
eq(str('2e-3x^2 + 1e+2'), '1/500·x^2 + 100', 'signed exponents are not term breaks');
eq(parsePoly('x^3 - x^3 + x').degree, 1, 'cancelled leading terms are trimmed');
eq(str('X^2 + X'), 'x^2 + x', 'upper-case variable');

// ---- characteristic 2 ------------------------------------------------------
eq(str('x^3 + 0x1f x + 1', { char2: true }), 'x^3 + 0x1f·x + 1', 'hex coefficients');

eq(str('0x1f*x^2 + x·0x3', { char2: true }), '0x1f·x^2 + 0x3·x', 'hex and trailing coefficients over GF(2^k)');
eq(str('x² + x + 1', { char2: true }), 'x^2 + x + 1', 'superscripts over GF(2^k)');

// ---- rejections name the problem -------------------------------------------
rejects('x^2/0', /division by zero/);
rejects('(x+1)^2', /parentheses may only wrap a coefficient/);
rejects('3y + 1', /variable must be x.*"y"/);
rejects('x^2 +', /ends with a sign/);
rejects('(x^2', /unbalanced parentheses/);
rejects('', /empty input/);
rejects('x^3/6', /no division by 6/, { char2: true });
rejects('x^2 - 1', /no negatives/, { char2: true });
rejects('1/2x + 1', /is a fraction/, { char2: true });
rejects('0.5x', /is a decimal/, { char2: true });

if (fails) { console.log(`POLYPARSE FAILED (${fails}/${checks})`); process.exit(1); }
console.log(`POLYPARSE PASSES (${checks} checks)`);
