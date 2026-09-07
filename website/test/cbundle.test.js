// cbundle.test.js — archive contents and the executable benchmark handoff.
import { mkdtempSync, mkdirSync, writeFileSync, chmodSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { spawnSync } from 'node:child_process';
import { buildCBundle, cBundleArchive, hasCBundle, tarBytes } from '../js/cbundle.js';
import { C_PROVENANCE, hasCProvenance } from '../js/cgen.js';
import { paneContent, reduce, initialState, staleRow } from '../js/uistate.js';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; console.log(`FAIL: ${msg}`); } };
const C = `${C_PROVENANCE}\n#include <math.h>\ndouble eval_P(double x) { return x*x + 1.0; }\n`;
const state = { mode: 'Q', method: 'ours', view: 'c', cstyle: 'fraction', src: 'x^2 + 1', result: {
  fieldName: 'ℚ', cText: C, cTextFraction: C.replace('1.0', '(double)1/1'),
  comparisons: [
    { name: 'Horner', ok: true, cText: C, cTextFraction: null },
    { name: 'Unavailable', ok: false, cText: null },
  ],
} };

const b = buildCBundle(state), names = b.files.map(f => f.name);
check(hasCBundle(state) && !hasCBundle({ result: { oursFailed: true, comparisons: [] } }),
      'bundle availability follows successful C rows');
check(b.baseName === 'fast-polynomials-Q-degree-2', 'stable archive name');
for (const n of ['README.md', 'selected.c', 'benchmark.c', 'benchmark.sh', 'inspect.sh', 'methods/this-paper.c',
                 'methods/this-paper-fractions.c', 'methods/horner.c'])
  check(names.includes(n), `bundle contains ${n}`);
check(b.files.find(f => f.name === 'selected.c').text === paneContent(state).code,
      'selected.c is byte-for-byte the C source shown in the pane');
const hornerState = { ...state, method: 'Horner' };
check(buildCBundle(hornerState).files.find(f => f.name === 'selected.c').text === paneContent(hornerState).code,
      'selected.c follows the selected method and its effective constant style');
check(!names.some(n => n.includes('unavailable')), 'failed methods omitted');
check(b.files.find(f => f.name === 'benchmark.sh').mode === 0o755, 'benchmark script executable mode');
check(b.files.find(f => f.name === 'inspect.sh').mode === 0o755, 'inspection script executable mode');
check(b.files.filter(f => f.name.endsWith('.c')).every(f => hasCProvenance(f.text)),
      'every generated C file carries the stable site provenance');
// the doc block of every generated C file (the harness cites the paper) stays within
// 88 columns: long lines wrap with a continuation indent (a lone URL may exceed it)
check(b.files.filter(f => f.name.endsWith('.c')).every(f => f.text.slice(0, f.text.indexOf('*/')).split('\n')
        .every(l => l.length <= 88 || !l.replace(/^ \* +/, '').includes(' '))) &&
      / \* Reference: T\. D\. Ahle/.test(b.files.find(f => f.name === 'benchmark.c').text),
      'header lines within 88 columns, the harness Reference line wrapped');

const tar = tarBytes(b);
check(tar.length % 512 === 0 && tar.slice(-1024).every(x => x === 0), 'ustar padding and end blocks');
check(new TextDecoder().decode(tar.slice(257, 263)) === 'ustar\0', 'ustar magic');

const archive = await cBundleArchive(state);
const archiveBytes = new Uint8Array(await archive.blob.arrayBuffer());
check(archive.name.endsWith(typeof CompressionStream === 'function' ? '.tar.gz' : '.tar'),
      'browser archive extension matches its encoding');
if (archive.name.endsWith('.gz')) {
  check(archiveBytes[0] === 0x1f && archiveBytes[1] === 0x8b, 'gzip archive magic');
  const unpacked = new Uint8Array(await new Response(
    archive.blob.stream().pipeThrough(new DecompressionStream('gzip')),
  ).arrayBuffer());
  check(unpacked.length === tar.length && unpacked.every((x, i) => x === tar[i]),
        'gzip archive expands to the tested ustar payload');
}

// Materialize the plain file list and prove the shipped command builds and runs.
const dir = mkdtempSync(join(tmpdir(), 'fastpoly-bundle-'));
for (const f of b.files) {
  const path = join(dir, f.name);
  mkdirSync(dirname(path), { recursive: true });
  writeFileSync(path, f.text);
  chmodSync(path, f.mode);
}
const run = spawnSync('sh', ['benchmark.sh', '100'], { cwd: dir, encoding: 'utf8' });
check(run.status === 0, `benchmark.sh exits successfully: ${run.stderr}`);
check(/this-paper.*ns\/eval/.test(run.stdout) && /horner.*ns\/eval/.test(run.stdout),
      `benchmark reports every method: ${run.stdout}`);

const inspect = spawnSync('sh', ['inspect.sh'], { cwd: dir, encoding: 'utf8' });
check(inspect.status === 0, `inspect.sh exits successfully: ${inspect.stderr}`);
check(/method\s+FMA\s+SIMD-FP\s+CLMUL/.test(inspect.stdout) &&
      /this-paper\s+\d+\s+\d+\s+\d+/.test(inspect.stdout),
      `inspection reports compiler instruction families: ${inspect.stdout}`);

// ---- a state over ℂ: C99 double complex sources, the complex harness (creal/cimag, |checksum|), -lm ----
{
  const CC = `${C_PROVENANCE}\n#include <complex.h>\ndouble complex eval_P(double complex x) { return x * x + (0.0 + 1.0*I); }\n`;
  const stateC = { mode: 'C', method: 'ours', view: 'c', cstyle: 'float', src: 'x^2 + i', result: {
    fieldName: 'ℂ', cText: CC, cTextFraction: null,
    comparisons: [{ name: 'Horner', ok: true, cText: CC, cTextFraction: null }, { name: 'Pan', ok: false, cText: null }],
  } };
  const bc = buildCBundle(stateC), namesC = bc.files.map(f => f.name);
  check(hasCBundle(stateC) && bc.baseName === 'fast-polynomials-C-degree-2', 'ℂ bundle available, stable name');
  for (const n of ['README.md', 'selected.c', 'benchmark.c', 'benchmark.sh', 'inspect.sh', 'methods/this-paper.c', 'methods/horner.c'])
    check(namesC.includes(n), `ℂ bundle contains ${n}`);
  check(!namesC.some(n => n.includes('fractions')), 'ℂ bundle: no fraction variants');
  const harness = bc.files.find(f => f.name === 'benchmark.c').text;
  check(harness.includes('#include <complex.h>') && /typedef double complex bench_input_t;/.test(harness) && /creal\(checksum\), cimag\(checksum\), cabs\(checksum\)/.test(harness) && /\* I;/.test(harness),
        'ℂ harness: complex inputs, creal/cimag/cabs checksum');
  const script = bc.files.find(f => f.name === 'benchmark.sh').text;
  check(/-fcx-limited-range/.test(script) && /-lm/.test(script) && /-fcx-limited-range/.test(bc.files.find(f => f.name === 'inspect.sh').text), 'ℂ scripts: -lm, -fcx-limited-range where accepted');
  check(/<complex.h>/.test(bc.files.find(f => f.name === 'README.md').text), 'ℂ README explains the complex sources');
  const dirC = mkdtempSync(join(tmpdir(), 'fastpoly-bundle-C-'));
  for (const f of bc.files) {
    const path = join(dirC, f.name);
    mkdirSync(dirname(path), { recursive: true });
    writeFileSync(path, f.text);
    chmodSync(path, f.mode);
  }
  const runC = spawnSync('sh', ['benchmark.sh', '100'], { cwd: dirC, encoding: 'utf8' });
  check(runC.status === 0, `ℂ benchmark.sh exits successfully: ${runC.stderr}`);
  check(/this-paper.*ns\/eval.*\*I\s+\|checksum\| \d/.test(runC.stdout) && /horner.*ns\/eval/.test(runC.stdout), `ℂ benchmark reports complex checksums: ${runC.stdout}`);
  const inspectC = spawnSync('sh', ['inspect.sh'], { cwd: dirC, encoding: 'utf8' });
  check(inspectC.status === 0 && /this-paper\s+\d+\s+\d+\s+\d+/.test(inspectC.stdout), `ℂ inspect.sh runs: ${inspectC.stderr}`);
}

// ---- a selected numeric method still computing, its previous chain shown (uistate.staleRow): selected.c is withheld ----
{
  const rowC = (name, tag) => ({ name, ok: true, mults: 1, adds: 1, height: 1, exact: false, mathText: `${tag} math`,
    cText: `${C_PROVENANCE}\n/* ${tag} */\ndouble eval_P(double x) { return x; }\n`, cTextFraction: null });
  const full = { fieldId: 'Q', fieldName: 'ℚ', cText: C, cTextFraction: null, mults: 1, adds: 1, height: 1,
    comparisons: [rowC('Horner', 'horner OLD'), rowC('Knuth–Eve', 'KE OLD')] };
  let s = reduce({ ...initialState, mode: 'Q', src: 'x^7 - 1', exKey: null, view: 'c' }, { type: 'compile' });
  s = reduce(s, { type: 'reply', id: s.jobId, part: 'main', ok: true, result: full });
  s = reduce(s, { type: 'setMethod', method: 'Knuth–Eve' });
  s = reduce(reduce(s, { type: 'setSrc', src: 'x^9 - 2' }), { type: 'compile' });
  const pendingKE = { ...full, comparisons: [rowC('Horner', 'horner NEW'), { name: 'Knuth–Eve', ok: false, pending: true, note: 'computing…' }] };
  s = reduce(s, { type: 'reply', id: s.jobId, part: 'main', ok: true, result: pendingKE });
  check(staleRow(s)?.name === 'Knuth–Eve' && paneContent(s).kind === 'c' && paneContent(s).code.includes('KE OLD'),
        'fixture: the pane shows the previous Knuth–Eve source while the new one computes');
  const bp = buildCBundle(s), namesP = bp.files.map(f => f.name);
  check(!namesP.includes('selected.c') && !/byte-for-byte/.test(bp.files.find(f => f.name === 'README.md').text) &&
        namesP.includes('methods/horner.c') && !namesP.some(n => /knuth/.test(n)) &&
        bp.files.find(f => f.name === 'methods/horner.c').text.includes('horner NEW') && bp.baseName === 'fast-polynomials-Q-degree-9',
        'while the selected numeric method shows its previous chain the archive omits selected.c (methods/ is the new polynomial\'s)');
  const s2 = reduce(s, { type: 'reply', id: s.jobId, part: 'numeric', ok: true, result: { comparisons: [rowC('Knuth–Eve', 'KE NEW')] } });
  check(staleRow(s2) === null && buildCBundle(s2).files.find(f => f.name === 'selected.c')?.text.includes('KE NEW') &&
        /byte-for-byte the Knuth–Eve source/.test(buildCBundle(s2).files.find(f => f.name === 'README.md').text),
        'once the numeric reply lands selected.c is the new Knuth–Eve source and the README says so');
}

console.log(fails ? `C BUNDLE FAILED (${fails}/${checks})` : `C BUNDLE PASSES (${checks} checks)`);
process.exit(fails ? 1 : 0);
