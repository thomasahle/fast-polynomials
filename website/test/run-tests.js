import { spawnSync } from 'node:child_process';

// A group is a list of test files; an entry may be [file, env] to run the file
// with extra environment (FAST_POLY_PART splits the long files across CI jobs so
// every job stays under a minute).  `npm test` runs every group.
const groups = {
  core: [
    'chain.test.js',
    'constructions.test.js',
    'factor.test.js',
    'gauss.test.js',
    'graph.test.js',
    'mathview.test.js',
    'methodlist.test.js',
    'polyparse.test.js',
    'rat.test.js',
  ],
  ui: ['ui-smoke.test.js', 'uistate.test.js'],
  fields: ['fields.test.js'],
  'char0-core': [['char0.test.js', { FAST_POLY_PART: 'core' }]],
  'char0-pipeline': [['char0.test.js', { FAST_POLY_PART: 'pipeline' }]],
  'char2-decode': [['char2.test.js', { FAST_POLY_PART: 'decode' }]],
  'char2-pipeline': [['char2.test.js', { FAST_POLY_PART: 'pipeline' }]],
  cgen: ['cgen.test.js', 'cbundle.test.js'],
  belaga: ['belaga.test.js'],
  motzkin: ['motzkin.test.js'],
  'knutheve-complex': ['knutheve-complex.test.js'],
  methods: ['methods.test.js'],
  'pan-complex': ['pan1978.test.js'],
  'pan-real': ['pan1978real.test.js'],
};

const requested = process.argv.slice(2);
const selected = requested.length ? requested : Object.keys(groups);
const unknown = selected.filter(name => !(name in groups));
if (unknown.length) {
  console.error(`Unknown test group: ${unknown.join(', ')}. Choose from ${Object.keys(groups).join(', ')}.`);
  process.exit(2);
}

const entries = selected.flatMap(name => groups[name]).map(e => (Array.isArray(e) ? e : [e, {}]));
const files = [...new Map(entries.map(e => [JSON.stringify(e), e])).values()];
const suiteStart = Date.now();
for (const [file, env] of files) {
  const start = Date.now();
  const tag = Object.keys(env).length ? ` (${Object.entries(env).map(([k, v]) => `${k}=${v}`).join(' ')})` : '';
  console.log(`\n==> ${file}${tag}`);
  const result = spawnSync(process.execPath, [new URL(file, import.meta.url).pathname], {
    stdio: 'inherit',
    env: { ...process.env, ...env },
  });
  if (result.error) throw result.error;
  if (result.status !== 0) process.exit(result.status ?? 1);
  console.log(`<== ${file} (${((Date.now() - start) / 1000).toFixed(1)}s)`);
}
console.log(`\n${files.length} test files passed in ${((Date.now() - suiteStart) / 1000).toFixed(1)}s`);
