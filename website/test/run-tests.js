import { spawnSync } from 'node:child_process';

const groups = {
  core: [
    'chain.test.js',
    'constructions.test.js',
    'factor.test.js',
    'gauss.test.js',
    'graph.test.js',
    'mathview.test.js',
    'polyparse.test.js',
    'ui-smoke.test.js',
    'uistate.test.js',
  ],
  fields: ['fields.test.js'],
  char0: ['char0.test.js'],
  char2: ['char2.test.js'],
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

const files = [...new Set(selected.flatMap(name => groups[name]))];
const suiteStart = Date.now();
for (const file of files) {
  const start = Date.now();
  console.log(`\n==> ${file}`);
  const result = spawnSync(process.execPath, [new URL(file, import.meta.url).pathname], {
    stdio: 'inherit',
    env: process.env,
  });
  if (result.error) throw result.error;
  if (result.status !== 0) process.exit(result.status ?? 1);
  console.log(`<== ${file} (${((Date.now() - start) / 1000).toFixed(1)}s)`);
}
console.log(`\n${files.length} test files passed in ${((Date.now() - suiteStart) / 1000).toFixed(1)}s`);
