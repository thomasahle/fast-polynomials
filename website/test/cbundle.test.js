// cbundle.test.js — archive contents and the executable benchmark handoff.
import { mkdtempSync, mkdirSync, writeFileSync, chmodSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';
import { spawnSync } from 'node:child_process';
import { buildCBundle, cBundleArchive, hasCBundle, tarBytes } from '../js/cbundle.js';
import { C_PROVENANCE } from '../js/cgen.js';
import { paneContent } from '../js/uistate.js';

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
check(b.baseName === 'fast-polyhash-Q-degree-2', 'stable archive name');
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
check(b.files.filter(f => f.name.endsWith('.c')).every(f => f.text.startsWith(C_PROVENANCE)),
      'every generated C file carries the stable site provenance');

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

console.log(fails ? `C BUNDLE FAILED (${fails}/${checks})` : `C BUNDLE PASSES (${checks} checks)`);
process.exit(fails ? 1 : 0);
