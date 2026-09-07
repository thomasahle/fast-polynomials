// methodlist.test.js — js/methodlist.js is the dependency-free list of method
// names and degree caps the page thread reads before any worker replies; the
// compilers' tables (compare.js) and the char-2 lane (char2.js) must agree with it.
import { CLASSICAL_METHODS, NUMERIC_METHODS, NUMERIC_METHODS_C, numericMethodsFor, needsNumericWorker,
         pendingNumericRows, methodNamesFor, MAX_DEGREE } from '../js/methodlist.js';
import * as compare from '../js/compare.js';
import * as char2 from '../js/char2.js';
import { FIELDS, FIELD_IDS } from '../js/field.js';
import { Rat } from '../js/rat.js';
import { GaussRat } from '../js/gauss.js';
import { readFileSync } from 'node:fs';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };
const eq = (a, b, msg) => check(JSON.stringify(a) === JSON.stringify(b), `${msg}: got ${JSON.stringify(a)}, want ${JSON.stringify(b)}`);

// the module loads nothing else (the page thread must not pull the compilers)
const srcText = readFileSync(new URL('../js/methodlist.js', import.meta.url), 'utf8');
check(!/^\s*import\b/m.test(srcText), 'methodlist.js has no imports');

eq(CLASSICAL_METHODS, ['Horner', 'Estrin', 'Rabin–Winograd'], 'classical rows');
eq(NUMERIC_METHODS, ['Knuth–Eve', 'Pan'], 'numeric rows over ℚ / ℝ');
eq(NUMERIC_METHODS_C, ['Knuth–Eve', 'Pan', 'Belaga'], 'ℂ adds Belaga');
eq(numericMethodsFor('C'), NUMERIC_METHODS_C, 'numericMethodsFor(C)');
for (const m of FIELD_IDS.filter(id => id !== 'C')) eq(numericMethodsFor(m), NUMERIC_METHODS, `numericMethodsFor(${m})`);
eq(FIELD_IDS.filter(needsNumericWorker), ['Q', 'R', 'C'], 'the numeric worker runs over the exact fields');
eq(FIELD_IDS.filter(needsNumericWorker), FIELDS.filter(f => f.char === 0).map(f => f.id), '… which are the registry\'s characteristic-0 fields');
eq(pendingNumericRows('C').map(r => [r.name, r.ok, r.pending]), [['Knuth–Eve', false, true], ['Pan', false, true], ['Belaga', false, true]], 'pending placeholders');
eq(pendingNumericRows().map(r => r.name), NUMERIC_METHODS, 'pendingNumericRows defaults to ℚ');
eq(methodNamesFor('Q'), ['ours', ...CLASSICAL_METHODS, ...NUMERIC_METHODS], 'every method over ℚ, ours first');
eq(methodNamesFor('C'), ['ours', ...CLASSICAL_METHODS, ...NUMERIC_METHODS_C], 'every method over ℂ');
eq(methodNamesFor('gf64'), ['ours', ...CLASSICAL_METHODS], 'hashing fields: no numeric rows');
eq(MAX_DEGREE, 26, 'the char-2 cap');

// the re-exports are the same values
for (const k of ['CLASSICAL_METHODS', 'NUMERIC_METHODS', 'NUMERIC_METHODS_C', 'numericMethodsFor', 'needsNumericWorker', 'pendingNumericRows'])
  check(compare[k] === (await import('../js/methodlist.js'))[k], `compare.js re-exports ${k}`);
check(char2.MAX_DEGREE === MAX_DEGREE && char2.SUPPORTED_DEGREES.length === MAX_DEGREE, 'char2.js re-exports MAX_DEGREE and sizes SUPPORTED_DEGREES by it');

// the implementation tables in compare.js cover exactly the listed names (item 73: no second hand-synced list)
const F = FIELDS.find(f => f.id === 'Q').make(), FC = FIELDS.find(f => f.id === 'C').make();
const coeffs = [1n, 2n, 3n, 1n].map(n => new Rat(n));
eq(compare.buildClassical(coeffs, F, 'Q').map(r => r.name), CLASSICAL_METHODS, 'buildClassical rows = CLASSICAL_METHODS');
eq(compare.buildNumeric(coeffs, F, 'Q').map(r => r.name), numericMethodsFor('Q'), 'buildNumeric rows over ℚ = numericMethodsFor(Q)');
eq(compare.buildNumeric(coeffs.map(c => new GaussRat(c, Rat.ZERO)), FC, 'C').map(r => r.name), numericMethodsFor('C'), 'buildNumeric rows over ℂ = numericMethodsFor(C)');
eq(compare.buildNumeric(coeffs, FIELDS.find(f => f.id === 'p89').make(), 'p89').map(r => [r.name, r.ok]), NUMERIC_METHODS.map(n => [n, false]), 'over GF(p) the numeric rows are listed and rejected');
eq(compare.buildComparisons(coeffs, F, 'Q').map(r => r.name), methodNamesFor('Q').slice(1), 'buildComparisons = the table order');

console.log(fails ? `METHODLIST FAILED (${fails}/${checks})` : `METHODLIST PASSES (${checks} checks)`);
process.exit(fails ? 1 : 0);
