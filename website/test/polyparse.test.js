// polyparse.test.js — the user-input grammar: every spelling a person is
// likely to type for the same polynomial reads to the same coefficients, and
// the rejections name the actual problem.
import { parsePoly, polyToString } from '../js/polyparse.js';
import { GaussRat } from '../js/gauss.js';
import { Rat } from '../js/rat.js';

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

// ---- ℂ: Gaussian-rational coefficients -------------------------------------
{
  const C = { complex: true };
  const every = src => parsePoly(src, C).coeffs.every(c => c instanceof GaussRat);
  const cx = (src, want, msg) => { eq(str(src, C), want, msg); check(every(src), `${msg}: every coefficient is a GaussRat`); };
  cx('i', '(0+1i)', 'a bare i');
  cx('2i', '(0+2i)', '2i');
  cx('2.5i', '(0+5/2i)', 'a decimal imaginary part stays exact');
  cx('1/2i', '(0+1/2i)', '1/2i is (1/2)i');
  cx('(1/2)i', '(0+1/2i)', 'a parenthesized real part before i');
  cx('(-1/2)*i x^2', '(0-1/2i)·x^2', 'parenthesized real, explicit product with i, on a power');
  cx('x*(0.5)i - (2e-3)i', '(0+1/2i)·x + (0-1/500i)', 'parenthesized decimal / exponent parts before i');
  cx('(1+2i)', '(1+2i)', 'parenthesized complex constant');
  cx('(1/2-3/4i)', '(1/2-3/4i)', 'fractional parts');
  cx('(1+2i)x^2', '(1+2i)·x^2', 'complex coefficient on a power');
  cx('x + i', 'x + (0+1i)', 'i as a term');
  cx('2i*x', '(0+2i)·x', 'explicit product');
  cx('i x^3', '(0+1i)·x^3', 'i before a power');
  cx('(2-i)', '(2-1i)', 'a bare i in the imaginary part');
  cx('-i', '(0-1i)', 'negated i');
  cx('(-i)x + (-1-2i)', '(0-1i)·x + (-1-2i)', 'negative parenthesized complex coefficients');
  cx('x·(1+i) + x^2/2', '1/2·x^2 + (1+1i)·x', 'trailing complex coefficient, real fraction');
  cx('x^3 - 2i x + 3', 'x^3 + (0-2i)·x + 3', 'a minus before an imaginary term');
  cx('2e-3i x + 1e+2', '(0+1/500i)·x + 100', 'exponent forms in the imaginary part');
  cx('i x + i x - 2i x', '0', 'like imaginary terms cancel');
  cx('x^4 + 1/6·x^3 + 1/2·x^2 + x + 1', taylor, 'a real polynomial reads over ℂ exactly as over ℚ');
  eq(parsePoly('i x^3 - i x^3 + x', C).degree, 1, 'cancelled complex leading terms are trimmed');
  // every coefficient is a GaussRat, real ones included
  check(parsePoly('x^2 + 3', C).coeffs.every(c => c instanceof GaussRat), 'real input over ℂ still yields GaussRat coefficients');
  check(parsePoly('x^2 + 3', C).coeffs[0].eq(new GaussRat(new Rat(3n))), 'real coefficient value over ℂ');
  eq(parsePoly('(1/2-3/4i)x', C).coeffs[1].toString(), '(1/2-3/4i)', 'exact Rat parts');
  // round trips: polyToString output re-parses to the same coefficients
  for (const src of ['(1+2i)x^2 - 1/2i x + (3-4i)', 'x^5 + i', '(-1/3+2/7i)x^3 + 2i', 'i x^3 + x^2 - i']) {
    const a = parsePoly(src, C).coeffs, b = parsePoly(polyToString(a, C), C).coeffs;
    check(a.length === b.length && a.every((c, k) => c.eq(b[k])), `round trip through polyToString: ${src}`);
  }
  check(!/\+ -/.test(str('x^2 + (-1+2i)x - 3', C)) && str('x^2 + (-1+2i)x - 3', C) === 'x^2 + (-1+2i)·x − 3',
        'the "+ -" → "−" rewrite leaves a parenthesized complex coefficient alone');
  // rejections
  rejects('3y + 1', /variable must be x.*"y"/, C);
  rejects('3y + i', /variable must be x.*"y"/, C);
  rejects('xi', /imaginary unit/, C);
  rejects('Xi', /imaginary unit/, C);                                // X is the variable, not a stray letter
  rejects('2I', /imaginary unit/, C);                                // an upper-case unit gets the hint
  rejects('i^2', /imaginary unit/, C);
  rejects('(x+i)', /parentheses may only wrap a coefficient/, C);
  rejects('((1/2)i)', /parentheses may only wrap a coefficient/, C);
  rejects('i*(1/2)', /parentheses may only wrap a coefficient/, C);
  rejects('x^2/0', /division by zero/, C);
  rejects('x + i', /complex number.*choose ℂ/);                     // ℚ / ℝ
  rejects('(1+2i)x', /"1\+2i" is a complex number.*choose ℂ/);
  rejects('(1/2)i', /"1\/2i" is a complex number.*choose ℂ/);
  rejects('x + 2i', /is a complex number.*choose ℂ/, { char2: true });
  rejects('1/2i x', /is a complex number.*choose ℂ/, { char2: true });
  rejects('i', /is a complex number.*choose ℂ/, { char2: true });
}

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
