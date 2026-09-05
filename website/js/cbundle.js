// Downloadable C benchmark bundles. The site has no build step or archive
// dependency, so we write POSIX ustar directly and use the browser's native
// gzip stream when available.

import { C_PROVENANCE, C_LICENSE, cFileHeader, hasCProvenance } from './cgen.js';
import { selectedCSource } from './uistate.js';

const UTF8 = new TextEncoder();

const slug = (name, fallback) => {
  const s = String(name ?? '').normalize('NFKD').replace(/[\u0300-\u036f]/g, '')
    .toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
  return s || fallback;
};

const fieldStem = mode => String(mode || 'field').replace(/[^A-Za-z0-9_-]+/g, '-');

function cRows(state) {
  const r = state?.result;
  if (!r) return [];
  const rows = [];
  if (!r.oursFailed && r.cText) rows.push({ name: 'This paper', row: r });
  for (const c of r.comparisons ?? []) if (c.ok && c.cText) rows.push({ name: c.name, row: c });
  return rows;
}

export const hasCBundle = state => cRows(state).length > 0;
const withCProvenance = text => (hasCProvenance(text) ? text : `${C_PROVENANCE}\n${text}`);

function uniqueStem(wanted, used) {
  let out = wanted, i = 2;
  while (used.has(out)) out = `${wanted}-${i++}`;
  used.add(out);
  return out;
}

function benchTypes(mode) {
  switch (mode) {
    case 'Q': case 'R': return { input: 'double', output: 'double', floating: true };
    case 'gf32': return { input: 'uint32_t', output: 'uint32_t', bits: 32 };
    case 'gf64': case 'p61': return { input: 'uint64_t', output: 'uint64_t', bits: 64 };
    case 'gf128': case 'p127': return { input: '__uint128_t', output: '__uint128_t', bits: 128 };
    case 'p': case 'p89': return { input: 'uint64_t', output: '__uint128_t', bits: 128 };
    default: throw new Error(`no benchmark harness type for ${mode}`);
  }
}

/** One timing harness, compiled once per METHOD_FILE by benchmark.sh. */
export function benchmarkHarness(mode) {
  const t = benchTypes(mode);
  const init = t.floating
    ? '        inputs[i] = ((double)(next64() & 0xffffu) / 32768.0) - 1.0;'
    : t.input === '__uint128_t'
      ? '        inputs[i] = ((__uint128_t)next64() << 64) | next64();'
      : `        inputs[i] = (${t.input})next64();`;
  // Integer XOR accumulators would cancel identically after every even number
  // of rounds, giving an optimizer an avoidable shortcut.  Unsigned addition
  // is only a checksum here (not a field operation), and cannot self-cancel.
  const zero = t.floating ? '0.0' : '0', assign = '+=', op = '+';
  const print = t.floating
    ? '    printf("%.3f ns/eval  checksum %.17g\\n", ns_per_eval, (double)checksum);'
    : t.bits === 128
      ? '    printf("%.3f ns/eval  checksum %016llx:%016llx\\n", ns_per_eval,\n' +
        '           (unsigned long long)(checksum >> 64), (unsigned long long)checksum);'
      : t.bits === 64
        ? '    printf("%.3f ns/eval  checksum %016llx\\n", ns_per_eval, (unsigned long long)checksum);'
        : '    printf("%.3f ns/eval  checksum %08x\\n", ns_per_eval, (unsigned)checksum);';
  return `${cFileHeader(['Shared timing harness: compile with -DMETHOD_FILE="methods/<name>.c" (benchmark.sh does).'])}
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#ifndef METHOD_FILE
#error "compile with -DMETHOD_FILE=\\\"methods/name.c\\\""
#endif
#include METHOD_FILE

typedef ${t.input} bench_input_t;
typedef ${t.output} bench_output_t;
static volatile bench_input_t inputs[8];
static volatile bench_output_t sink;
static uint64_t rng_state = 0x243f6a8885a308d3ULL;

static uint64_t next64(void) {
    rng_state ^= rng_state << 7;
    rng_state ^= rng_state >> 9;
    return rng_state;
}

static uint64_t now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000ULL + (uint64_t)t.tv_nsec;
}

int main(int argc, char **argv) {
    long rounds = argc > 1 ? strtol(argv[1], NULL, 10) : 200000;
    if (rounds < 1) rounds = 1;
    for (unsigned i = 0; i < 8; ++i) {
${init}
    }
    bench_output_t a0=${zero}, a1=${zero}, a2=${zero}, a3=${zero};
    bench_output_t a4=${zero}, a5=${zero}, a6=${zero}, a7=${zero};
    /* Volatile inputs prevent loop hoisting; eight accumulators expose throughput. */
    uint64_t start = now_ns();
    for (long r = 0; r < rounds; ++r) {
        a0 ${assign} eval_P(inputs[0]); a1 ${assign} eval_P(inputs[1]);
        a2 ${assign} eval_P(inputs[2]); a3 ${assign} eval_P(inputs[3]);
        a4 ${assign} eval_P(inputs[4]); a5 ${assign} eval_P(inputs[5]);
        a6 ${assign} eval_P(inputs[6]); a7 ${assign} eval_P(inputs[7]);
    }
    uint64_t elapsed = now_ns() - start;
    bench_output_t checksum = a0 ${op} a1 ${op} a2 ${op} a3 ${op} a4 ${op} a5 ${op} a6 ${op} a7;
    sink = checksum;
    double ns_per_eval = (double)elapsed / (8.0 * (double)rounds);
${print}
    return 0;
}
`;
}

function archSetup(mode) {
  const binary = /^gf(?:32|64|128)$/.test(mode);
  return `ARCH=\$(uname -m)
ARCH_FLAGS="-march=native"
${binary ? `case "$ARCH" in
  x86_64|amd64) ARCH_FLAGS="-march=native -mpclmul -mssse3" ;;
  arm64|aarch64) ARCH_FLAGS="-march=armv8-a+crypto" ;;
  *) echo "binary-field kernels require x86 CLMUL or ARM PMULL (got $ARCH)" >&2; exit 1 ;;
esac` : ''}
`;
}

function benchmarkScript(mode, sources) {
  return `#!/bin/sh
set -eu

CC=\${CC:-cc}
CFLAGS=\${CFLAGS:--O3}
ROUNDS=\${1:-\${ROUNDS:-200000}}
mkdir -p build

${archSetup(mode)}

printf '%-28s %s\\n' method result
printf '%-28s %s\\n' ---------------------------- ------------------------------
${sources.map(src => {
    const base = src.replace(/^methods\//, '').replace(/\.c$/, '');
    return `"$CC" $CFLAGS $ARCH_FLAGS -std=c11 -DMETHOD_FILE='"${src}"' benchmark.c -lm -o "build/${base}"
printf '%-28s ' '${base}'
"build/${base}" "$ROUNDS"`;
  }).join('\n')}
`;
}

/** Compile each evaluator to assembly and count the instruction families that
 * matter to the advertised kernels.  This is intentionally an inspection aid,
 * not a brittle pass/fail test: exact mnemonics and optimization choices vary
 * by compiler and CPU. */
function inspectionScript(mode, sources) {
  return `#!/bin/sh
set -eu

CC=\${CC:-cc}
CFLAGS=\${CFLAGS:--O3}
mkdir -p build/assembly

${archSetup(mode)}

printf '%-28s %8s %8s %8s\n' method FMA SIMD-FP CLMUL
printf '%-28s %8s %8s %8s\n' ---------------------------- -------- -------- --------
${sources.map(src => {
    const base = src.replace(/^methods\//, '').replace(/\.c$/, '');
    return `ASM="build/assembly/${base}.s"
"$CC" $CFLAGS $ARCH_FLAGS -std=c11 -S "${src}" -o "$ASM"
FMA=\$(awk 'BEGIN{n=0} /v?fm(add|sub)|fmla|fmls/{n++} END{print n}' "$ASM")
SIMD=\$(awk 'BEGIN{n=0} /f(mul|add|sub|mla|mls)\\.[248][sd]|v(fmadd|fmsub|fnmadd|mul|add|sub)[^[:space:]]*p[sd]/{n++} END{print n}' "$ASM")
CLMUL=\$(awk 'BEGIN{n=0} /pclmul|pmull/{n++} END{print n}' "$ASM")
printf '%-28s %8s %8s %8s\n' '${base}' "$FMA" "$SIMD" "$CLMUL"`;
  }).join('\n')}

printf '\nAssembly files are in build/assembly/. Counts are descriptive, not a correctness test.\n'
`;
}

function readme(state, entries, selected) {
  const field = state.result?.fieldName ?? state.mode;
  return `# Generated polynomial-evaluation benchmark

Code generated from https://thomasahle.com/fast-polynomials/ — for details, see
"Fast Evaluation of Polynomials with Rational Preprocessing" by Thomas Ahle and
Jakob Knudsen.  ${C_LICENSE}

Field: ${field}

${selected ? `\`selected.c\` is byte-for-byte the ${selected.label} source selected by the
web page${selected.style === 'fraction' ? ' with fraction literals' : ''}.  The files in
\`methods/\` are the complete benchmark set.

` : ''}Each file in \`methods/\` is a self-contained C implementation of the same
polynomial, with its key/preprocessed constants baked in. Successful methods
available in the web comparison are included; over Q, distinct decimal and
fraction-literal renderings are both preserved.

Run the throughput benchmark with:

    ./benchmark.sh

Inspect whether this compiler actually emitted FMA, packed floating-point SIMD,
or carry-less multiply instructions with:

    ./inspect.sh

Pass a repetition count as the first argument, or override the compiler flags:

    CC=clang CFLAGS="-O3" ./benchmark.sh 1000000

For floating-point code, also try \`CFLAGS="-O3 -ffp-contract=fast"\`.  It can
enable more aggressive FMA/SLP packing, but whether that is faster is
microarchitecture- and degree-dependent; compare both and use \`inspect.sh\`.

The harness evaluates eight independent inputs per loop. It is a convenient
comparison, not a substitute for benchmarking in the calling application:
latency-heavy dependency chains and batched throughput can favor different
field kernels.

Polynomial supplied to the compiler:

    ${String(state.src ?? '').replace(/\n/g, '\n    ')}

Included sources:

${entries.map(e => `- \`${e.file}\`: ${e.label}`).join('\n')}
`;
}

/** Plain files constituting the download. */
export function buildCBundle(state) {
  const rows = cRows(state);
  if (!rows.length) throw new Error('no generated C implementations are available');
  const selected = selectedCSource(state);
  const used = new Set(), entries = [], files = [];
  for (let i = 0; i < rows.length; ++i) {
    const { name, row } = rows[i];
    const stem = uniqueStem(slug(name, `method-${i + 1}`), used);
    const file = `methods/${stem}.c`;
    files.push({ name: file, text: withCProvenance(row.cText), mode: 0o644 });
    entries.push({ file, label: name });
    if (row.cTextFraction && row.cTextFraction !== row.cText) {
      const frac = `methods/${stem}-fractions.c`;
      files.push({ name: frac, text: withCProvenance(row.cTextFraction), mode: 0o644 });
      entries.push({ file: frac, label: `${name} (fraction literals)` });
    }
  }
  const sources = entries.map(e => e.file);
  files.unshift(
    { name: 'README.md', text: readme(state, entries, selected), mode: 0o644 },
    ...(selected ? [{ name: 'selected.c', text: selected.code, mode: 0o644 }] : []),
    { name: 'benchmark.c', text: benchmarkHarness(state.mode), mode: 0o644 },
    { name: 'benchmark.sh', text: benchmarkScript(state.mode, sources), mode: 0o755 },
    { name: 'inspect.sh', text: inspectionScript(state.mode, sources), mode: 0o755 },
  );
  const degree = /x\^(\d+)/i.exec(state.src ?? '')?.[1] ?? 'poly';
  return { baseName: `fast-polyhash-${fieldStem(state.mode)}-degree-${degree}`, files };
}

function ascii(dst, off, len, value) {
  const b = UTF8.encode(String(value));
  if (b.length > len) throw new Error(`tar field is too long: ${value}`);
  dst.set(b, off);
}
function octal(dst, off, len, value) {
  ascii(dst, off, len, Math.trunc(value).toString(8).padStart(len - 1, '0') + '\0');
}

/** POSIX ustar bytes. Paths are deliberately short enough for its name field. */
export function tarBytes(bundle) {
  const chunks = [];
  for (const f of bundle.files) {
    const data = UTF8.encode(f.text.endsWith('\n') ? f.text : f.text + '\n');
    const h = new Uint8Array(512);
    ascii(h, 0, 100, `${bundle.baseName}/${f.name}`);
    octal(h, 100, 8, f.mode ?? 0o644); octal(h, 108, 8, 0); octal(h, 116, 8, 0);
    octal(h, 124, 12, data.length); octal(h, 136, 12, 0);
    h.fill(0x20, 148, 156); h[156] = 0x30;
    ascii(h, 257, 6, 'ustar\0'); ascii(h, 263, 2, '00');
    ascii(h, 265, 32, 'fast-polyhash'); ascii(h, 297, 32, 'fast-polyhash');
    let sum = 0; for (const x of h) sum += x;
    ascii(h, 148, 8, sum.toString(8).padStart(6, '0') + '\0 ');
    chunks.push(h, data, new Uint8Array((512 - data.length % 512) % 512));
  }
  chunks.push(new Uint8Array(1024));
  const size = chunks.reduce((n, c) => n + c.length, 0), out = new Uint8Array(size);
  let at = 0; for (const c of chunks) { out.set(c, at); at += c.length; }
  return out;
}

/** Browser-ready archive; gzip when the native streaming codec is available. */
export async function cBundleArchive(state) {
  const bundle = buildCBundle(state), tar = tarBytes(bundle);
  if (typeof CompressionStream === 'function') {
    const stream = new Blob([tar]).stream().pipeThrough(new CompressionStream('gzip'));
    return { name: `${bundle.baseName}.tar.gz`, blob: await new Response(stream).blob(), bundle };
  }
  return { name: `${bundle.baseName}.tar`, blob: new Blob([tar], { type: 'application/x-tar' }), bundle };
}
