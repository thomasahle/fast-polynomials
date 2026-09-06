// gauss.test.js — the Gaussian rationals (js/gauss.js GaussRat), the ℂ field
// object Cx (re-exported by js/field.js) and gaussCoreField(), the duck-typed
// field the exact core accepts: arithmetic identities (inverse via the
// conjugate), coercions, predicates, the exact toString form and the canonical
// complex-double toDisplay token, and a core round trip over ℚ(i): decode →
// compile_paper_params_chain → validate → eval at points with Im ≠ 0 equals
// Horner, for n = 3..16 with Gaussian, real and fractional coefficients.
// Plain node, exit 1 on failure.
import { GaussRat, Cx as CxDirect, gaussCoreField } from '../js/gauss.js';
import { Cx, R } from '../js/field.js';
import { Rat } from '../js/rat.js';
import { COMPLEX_TOKEN, REAL_TOKEN, parseComplexToken } from '../js/tokens.js';
import * as core from '../js/char0/core.js';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };
const throws = f => { try { f(); return false; } catch (e) { return true; } };
const G = (re, im = 0n, rd = 1n, id = 1n) => new GaussRat(new Rat(BigInt(re), rd), new Rat(BigInt(im), id));
const r = (n, d = 1n) => new Rat(BigInt(n), d);

// ---------- construction / coercion ----------
check(Cx === CxDirect, 'field.js re-exports the Cx of gauss.js');
check(GaussRat.of(3) instanceof GaussRat && GaussRat.of(3).eq(G(3)) && GaussRat.of(3).isReal(), 'of(integer Number)');
check(GaussRat.of(-7n).eq(G(-7)) && GaussRat.of(r(2, 3n)).re.eq(r(2, 3n)) && GaussRat.of(r(2, 3n)).im.isZero(), 'of(bigint), of(Rat)');
{ const z = G(1, 2); check(GaussRat.of(z) === z, 'of(GaussRat) is identity'); }
check(throws(() => GaussRat.of(1.5)) && throws(() => GaussRat.of('1')) && throws(() => GaussRat.of(null)), 'of rejects non-integers, strings, null');
check(Object.isFrozen(G(1, 1)) && G(1, 1).re instanceof Rat && G(1, 1).im instanceof Rat, 'immutable, Rat parts');
check(!(G(1, 1) instanceof Rat), 'not a Rat subclass');
check(GaussRat.I.eq(G(0, 1)) && GaussRat.ZERO.isZero() && GaussRat.ONE.isOne(), 'constants I, ZERO, ONE');

// ---------- arithmetic identities ----------
const samples = [G(0), G(1), G(-1), G(0, 1), G(0, -1), G(3, 4), G(-2, 5), G(1, -1, 2n, 3n), G(-5, 7, 3n, 4n), G(7, 0, 2n), G(0, 3, 1n, 8n)];
check(GaussRat.I.mul(GaussRat.I).eq(G(-1)), 'i² = −1');
check(G(3, 4).mul(G(3, -4)).eq(G(25)) && G(3, 4).norm().eq(r(25)) && G(3, 4).conj().eq(G(3, -4)), 'z · conj(z) = |z|²');
check(G(3, 4).inv().eq(new GaussRat(r(3, 25n), r(-4, 25n))), 'inv(3+4i) = (3−4i)/25');
check(G(1, 2).add(G(3, -5)).eq(G(4, -3)) && G(1, 2).sub(G(3, -5)).eq(G(-2, 7)) && G(1, 2).mul(G(3, -5)).eq(G(13, 1)), 'add/sub/mul');
check(G(1, 2).div(G(3, -5)).mul(G(3, -5)).eq(G(1, 2)), '(a/b)·b = a');
check(G(2, 3).add(5).eq(G(7, 3)) && G(2, 3).mul(r(1, 2n)).eq(G(1, 3, 1n, 2n)) && G(2, 3).sub(2n).eq(G(0, 3)), 'mixed operands coerce (Number, Rat, bigint)');
for (const a of samples) {
  check(a.add(a.neg()).isZero() && a.sub(a).isZero() && a.mul(GaussRat.ONE).eq(a) && a.add(GaussRat.ZERO).eq(a), `${a}: additive identities`);
  if (!a.isZero()) {
    check(a.mul(a.inv()).isOne() && a.div(a).isOne() && a.inv().inv().eq(a), `${a}: multiplicative inverse via conjugate`);
    check(a.inv().eq(a.conj().mul(GaussRat.of(a.norm().inv()))), `${a}: inv = conj / norm`);
  } else {
    check(throws(() => a.inv()) && throws(() => G(1).div(a)), 'inv / div by zero throw');
  }
  for (const b of samples) {
    check(a.mul(b).eq(b.mul(a)) && a.add(b).eq(b.add(a)), `${a},${b}: commutative`);
    for (const c of samples.slice(0, 5)) {
      check(a.mul(b.add(c)).eq(a.mul(b).add(a.mul(c))), `${a},${b},${c}: distributive`);
      check(a.mul(b).mul(c).eq(a.mul(b.mul(c))), `${a},${b},${c}: associative`);
    }
  }
}

// ---------- predicates ----------
check(G(3, 0, 2n).isReal() && !G(3, 1, 2n).isReal() && G(-4).isInt() && !G(1, 0, 2n).isInt() && !G(2, 1).isInt(), 'isReal / isInt');
check(G(-3, 0).isNeg() && !G(3, 0).isNeg() && !G(0).isNeg() && G(-1, 0, 2n).isNeg(), 'isNeg (real part sign)');
check(G(1).isOne() && !G(1, 1).isOne() && !G(2).isOne() && G(0).isZero() && !G(0, 1).isZero(), 'isOne / isZero');
check(G(1, 2).eq(G(1, 2)) && !G(1, 2).eq(G(1, -2)) && G(3).eq(3) && G(3).eq(r(3)) && G(1, 0, 2n).eq(r(1, 2n)), 'eq (incl. coerced operands)');

// ---------- toString: exact input form ----------
check(G(3, 0, 2n).toString() === '3/2' && G(-4).toString() === '-4' && G(0).toString() === '0', 'toString real → plain Rat form');
check(G(1, 3, 2n, 4n).toString() === '(1/2+3/4i)' && G(1, -3, 2n, 4n).toString() === '(1/2-3/4i)' && G(0, 1).toString() === '(0+1i)' &&
      G(-2, 1).toString() === '(-2+1i)' && G(0, -1).toString() === '(0-1i)', `toString complex: ${G(1, 3, 2n, 4n)} ${G(0, -1)}`);
check(`${G(5, 0, 3n)}` === '5/3', 'template literal uses toString');

// ---------- toDisplay: the canonical complex-double token ----------
const tok = [[G(0, 2), '(0+2i)'], [G(-2, 1), '(-2+1i)'], [G(3, -1, 2n, 4n), '(1.5-0.25i)'], [G(0, 1), '(0+1i)'], [G(0, -1), '(0-1i)'],
             [new GaussRat(r(1, 10n ** 7n), r(32, 1n).mul(r(10 ** 4))), '(1e-7+320000i)'],
             [new GaussRat(r(1, 3n), r(-1, 3n)), '(0.3333333333333333-0.3333333333333333i)'],
             [new GaussRat(r(1, 10n ** 7n), r(15n * 10n ** 21n)), '(1e-7+1.5e+22i)']];
for (const [z, want] of tok) {
  const got = z.toDisplay();
  check(got === want, `toDisplay ${z} → ${got}, want ${want}`);
  check(COMPLEX_TOKEN.test(got), `${got} matches COMPLEX_TOKEN`);
  const p = parseComplexToken(got);
  check(p && p.re === Number(z.re.n) / Number(z.re.d) && p.im === Number(z.im.n) / Number(z.im.d), `${got} parses back to the same doubles`);
}
// real values print exactly as ℝ prints — never in the (re±imi) form
for (const q of [r(3, 2n), r(-4), r(0), r(1, 3n), r(1, 10n ** 7n), r(15n * 10n ** 21n), r(-25, 10000n)]) {
  const got = new GaussRat(q).toDisplay();
  check(got === R.toDisplay(q) && REAL_TOKEN.test(got) && !COMPLEX_TOKEN.test(got), `real toDisplay ${q} → ${got} == ℝ's ${R.toDisplay(q)}`);
}
check(Cx.toDisplay(G(3, -1, 2n, 4n)) === '(1.5-0.25i)' && Cx.toDisplay(r(1, 2n)) === '0.5' && Cx.toDisplay(2) === '2', 'Cx.toDisplay coerces');

// ---------- Cx: the field object (mirrors R) ----------
check(Cx.name === 'ℂ' && Cx.char === 0 && Cx.real === false && Cx.complex === true, 'Cx tags');
check(Cx.zero.isZero() && Cx.one.isOne() && Cx.isZero(Cx.zero) && Cx.isOne(Cx.one), 'Cx zero/one');
check(Cx.fromInt(-3).eq(G(-3)) && Cx.fromRat(r(1, 2n)).eq(G(1, 0, 2n)) && Cx.fromRat(G(1, 2)).eq(G(1, 2)), 'Cx.fromInt / fromRat (Rat or GaussRat)');
{
  const three = Cx.fromInt(3), five = Cx.fromInt(5), z = G(1, 2);
  check(Cx.eq(Cx.div(Cx.mul(three, five), five), three) && Cx.isZero(Cx.sub(three, three)) && Cx.eq(Cx.neg(Cx.neg(five)), five), 'Cx (3*5)/5 == 3 (the registry sanity check)');
  check(Cx.eq(Cx.mul(z, Cx.inv(z)), Cx.one) && Cx.eq(Cx.add(z, Cx.neg(z)), Cx.zero) && Cx.eq(Cx.div(z, z), Cx.one), 'Cx inverse identities');
  check(Cx.eq(Cx.mul(GaussRat.I, GaussRat.I), Cx.fromInt(-1)), 'Cx: i² = −1');
  // ℂ is exact: 1/10 + 2/10 = 3/10, i/3 · 3 = i
  check(Cx.eq(Cx.add(Cx.fromRat(r(1, 10n)), Cx.fromRat(r(2, 10n))), Cx.fromRat(r(3, 10n))) && Cx.eq(Cx.mul(Cx.div(GaussRat.I, three), three), GaussRat.I), 'Cx arithmetic is exact');
  check(throws(() => Cx.inv(Cx.zero)) && throws(() => Cx.div(three, Cx.zero)), 'Cx inv/div by zero throw');
}
for (const k of ['zero', 'one', 'add', 'sub', 'mul', 'div', 'neg', 'inv', 'eq', 'isZero', 'isOne', 'fromInt', 'fromRat', 'toDisplay', 'name', 'char'])
  check(k in Cx && k in R, `Cx and R both expose ${k}`);

// ---------- gaussCoreField(): the core's duck-typed field ----------
const F = gaussCoreField();
const Fq = core.rationals();
for (const k of ['modulus', 'use_fractions', 'coerce', 'from_int', 'zero', 'one', 'add', 'sub', 'neg', 'mul', 'inv', 'div', 'is_zero', 'eq'])
  check(k in F && typeof F[k] === typeof Fq[k], `gaussCoreField exposes ${k} like core.rationals() (${typeof F[k]} vs ${typeof Fq[k]})`);
check(F.modulus === null && F.use_fractions === true, 'modulus null, use_fractions');
check(F.zero().isZero() && F.one().isOne() && F.from_int(4).eq(G(4)) && F.coerce(0).isZero() && F.coerce(r(1, 2n)).eq(G(1, 0, 2n)), 'zero()/one()/from_int/coerce');
check(F.add(0, G(1, 2)).eq(G(1, 2)) && F.sub(3, 1n).eq(G(2)) && F.mul(2, GaussRat.I).eq(G(0, 2)) && F.neg(1).eq(G(-1)), 'core ops coerce integer literals');
check(F.eq(F.div(G(1, 2), G(3, -5)), G(1, 2).div(G(3, -5))) && F.eq(F.inv(G(3, 4)), G(3, 4).inv()) && F.is_zero(F.sub(G(1, 1), G(1, 1))) && !F.is_zero(GaussRat.I), 'div/inv/is_zero/eq');
check(throws(() => F.inv(0)) && throws(() => F.div(1, F.zero())), 'core inv/div by zero throw');
check(F.eq(F.add(F.one(), F.one()), 2) && !F.is_zero(F.add(F.one(), F.one())), 'characteristic 0 (2 ≠ 0)');

// ---------- core round trip over ℚ(i) ----------
const horner = (cs, x) => { let acc = GaussRat.ZERO; for (let i = cs.length - 1; i >= 0; i--) acc = acc.mul(x).add(cs[i]); return acc; };
const points = [G(1, 1), G(-3, 2, 7n, 1n), G(5, -1, 2n, 3n), G(0, 1), G(2)];
const cases = {
  gaussian: (n, i) => G((i * 7 + 3) % 11 - 5, (i * 5 + 1) % 9 - 4),
  real: (n, i) => new GaussRat(new Rat(BigInt((i * 7 + 3) % 11 - 5), BigInt(1 + (i % 3)))),
  fractions: (n, i) => new GaussRat(new Rat(BigInt((i * 7 + 3) % 11 - 5), BigInt(1 + (i % 3))), new Rat(BigInt((i * 5 + 1) % 9 - 4), BigInt(2 + (i % 2)))),
};
let evals = 0;
for (const [name, coef] of Object.entries(cases)) {
  for (let n = 3; n <= 16; n++) {
    const cs = [...Array.from({ length: n }, (_, i) => coef(n, i)), GaussRat.ONE];
    let chain;
    try {
      const params = core.decode(n, cs, gaussCoreField());
      check(params.length === n && params.every(p => p instanceof GaussRat), `${name} n=${n}: ${n} GaussRat parameters`);
      chain = core.compile_paper_params_chain(params, gaussCoreField());
      chain.validate?.();
    } catch (e) { check(false, `${name} n=${n}: ${e.message}`); continue; }
    if (name !== 'real') check(cs.some(c => !c.isReal()), `${name} n=${n}: coefficients not all real`);
    for (const x of points) {
      const got = chain.eval(x), want = horner(cs, x); evals++;
      check(got instanceof GaussRat && got.eq(want), `${name} n=${n} x=${x}: chain.eval ${got} != Horner ${want}`);
    }
    console.log(`${name} n=${n}: ${chain.gates.length} gates OK`);
  }
}
// a real-coefficient chain over ℚ(i) evaluates to the same values as the ℚ chain
{
  const n = 9, csq = [...Array.from({ length: n }, (_, i) => cases.real(n, i).re), Rat.ONE];
  const chainQ = core.compile_paper_params_chain(core.decode(n, csq, core.rationals()), null);
  const chainC = core.compile_paper_params_chain(core.decode(n, csq.map(c => new GaussRat(c)), gaussCoreField()), gaussCoreField());
  for (const x of [r(2), r(-3, 7n)]) check(chainC.eval(new GaussRat(x)).eq(new GaussRat(chainQ.eval(x))), `ℚ vs ℚ(i) chain agree at ${x}`);
  check(chainC.gates.length === chainQ.gates.length, 'same gate count over ℚ and ℚ(i)');
}

console.log(`${checks} checks, ${evals} chain evaluations, ${fails} failures`);
if (fails) process.exit(1);
console.log('GAUSS PASSES');
