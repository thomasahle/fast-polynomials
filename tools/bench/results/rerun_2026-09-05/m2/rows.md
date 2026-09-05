# Lane C, M2 Pro re-measurements: old -> new per cell, paste-ready rows, recomputed ratios

Machine: Apple M2 Pro, macOS 26.6.2, Apple clang 17.0.0 (clang-1700.6.4.2), 2026-09-05 20:23-21:16 CEST, other agents' jobs running
(1-min load recorded before/after every run; the driver waited for load < 3 with a 20-min cap before each group: reached 2.94
(apps), 2.54 (harness), timed out at 3.54 (prime-field rows), 2.83 (SMHasher3 mersenne), see `driver.log`).  Raw logs:
`S/m2/*.txt` = `tools/bench/results/rerun_2026-09-05/m2/*.txt` (README there).  Selection rule: three repetitions per binary,
the reported one has the median Horner value (apps) or the median mean Horner ns over the table's configurations (prime-field
rows); all three are listed in the harvest section below.  x86 cells are NOT touched here (Xeon lane).  Line numbers (l.NNN) are those of `sections/experiments.tex` /
`sections/injective.tex` as of 2026-09-05 21:45 (experiments.tex has shifted by +9 lines since the plan of 19:50, and is
modified in the working tree by another lane); apply the cells by exact old-string match, never by line number.

## A. Application benchmarks (sections/experiments.tex l.255-306), ARM cells

| cell (line) | old | new | run |
|---|---|---|---|
| CountSketch ns/update Horner / R-W / Ours (l.255) | 5.49 / 4.96 / **4.33** | 5.31 / 4.84 / **4.16** | countsketch_arm.2 (20:23:52, load 2.95) |
| ARM sketch speedup Ours vs Horner (l.258) | 1.27x | 1.28x (5.31/4.16 = 1.276; R-W 1.10x) | |
| Linear probing ns/insert (l.278) | 32.5 / 28.5 / **28.5** | 26.5 / 23.9 / **23.4** | linearprobe_arm.3 (20:23:58, load 3.59) |
| Linear probing ns/query (l.279) | 42.7 / 41.9 / **38.6** | 36.3 / 35.4 / **33.6** | same |
| ARM insert / lookup speedups (l.282) | 1.14x / 1.11x | 1.13x / 1.08x (26.5/23.4 = 1.132; 36.3/33.6 = 1.080) | |
| XOR filter ns/key build (l.302) | 96.1 / **82.4** / 92.0 | 80.7 / 84.2 / **75.6** | xorfilter_arm.3 (20:23:59, load 3.59) |
| XOR filter ns/query (l.303) | 5.56 / 5.53 / **5.04** | 5.55 / 5.44 / **5.21** | same |
| ARM query speedup (l.306) | 1.10x, "R--W is faster at build time" | query 1.07x (5.55/5.21 = 1.065); build: Ours 1.07x over Horner (80.7/75.6), R-W 0.96x | |

Paste-ready (x86 cells left as in the file; replace them from the Xeon lane):
```
ns/update & 5.31 & 4.84 & \textbf{4.16} & 38.3 & 24.9 & \textbf{23.7}
```
```
On ARM, our method achieves $1.28\times$ speedup over Horner.
```
```
ns/insert & 26.5 & 23.9 & \textbf{23.4} & 37.4 & 29.9 & \textbf{24.5} \\
ns/query  & 36.3 & 35.4 & \textbf{33.6} & 46.3 & 35.4 & \textbf{31.4}
```
```
On ARM, our method achieves $1.13\times$ speedup for inserts and $1.08\times$ for lookups.
```
```
ns/key (build) & 80.7 & 84.2 & \textbf{75.6} & 142.0 & 110.3 & \textbf{97.1} \\
ns/query       & 5.55 & 5.44 & \textbf{5.21} & 19.6 & 15.6 & \textbf{11.1}
```
```
On ARM, our method improves query throughput by $1.07\times$ over Horner and is also fastest at build time
($1.07\times$), although the single timed builds of the three methods are within run-to-run noise.
```
Caveats.  The sketch numbers are stable across the three repetitions (Horner 5.11-5.33, Ours 4.09-4.16; Ours fastest in all).
The hash-table insert and the XOR-filter build are *single* timed constructions and scatter by 25 %: Horner insert 32.4 / 24.5 /
26.5, XOR build Horner 85.9 / 76.2 / 80.7, and the build ordering flips between repetitions (rep 2: R-W 75.0 fastest; reps 1 and 3:
Ours fastest).  Ours is fastest for lookups and queries in all three repetitions.  The old ARM XOR-filter build row
(96.1 / 82.4 / 92.0) is therefore not contradicted by a stable measurement; the wording above states that.

## B. Mersenne 2^89-1 rows (experiments.tex l.354-355, prose l.340-343), ARM

Reported repetition: shamir_sharegen_mersenne.1 (20:56:18, load 3.54 -- the 20-min load wait timed out; the three repetitions at
loads 3.5-8.4 agree to +-0.03, this kernel is load-insensitive).

| row | old | new |
|---|---|---|
| ARM: Sharegen (x_i = i) | 2.02 / 2.37 / 2.47 / 2.49 / 2.44 | 2.05 / 2.35 / 2.51 / 2.47 / 2.45 |
| ARM: Random point | 2.01 / 2.34 / 2.48 / 2.48 / 2.48 | 2.06 / 2.38 / 2.51 / 2.47 / 2.44 |
| prose "consistent 2.0x-2.5x speedups" (l.340) | 2.0x-2.5x | unchanged (min 2.05x, max 2.51x) |
| store variant (l.343 "essentially the same speedups") | -- | store 2.07 / 2.38 / 2.50 / 2.49 / 2.47 (shamir_sharegen_mersenne_store.1): unchanged wording |

```
ARM: Sharegen ($x_i=i$) & 2.05$\times$ & 2.35$\times$ & 2.51$\times$ & 2.47$\times$ & 2.45$\times$ \\
ARM: Random point ($x_i \sim \F_p$) & 2.06$\times$ & 2.38$\times$ & 2.51$\times$ & 2.47$\times$ & 2.44$\times$ \\
```

## C. Goldilocks rows (experiments.tex l.372-373, l.380), ARM

Reported repetition: goldilocks_stark_eval.3 (20:59:09, load 6.23) and goldilocks_sharegen_store.3 (20:59:19, load 5.73); the
three repetitions agree to +-0.02 except one 2.23 at degree 21 (rep 1 rand) and 2.25 (rep 2 seq).

| row | old | new |
|---|---|---|
| ARM: Sharegen (x_i = i) | 1.98 / 2.23 / 2.39 / 2.33 / 2.32 | 2.00 / 2.25 / 2.37 / 2.35 / 2.33 |
| ARM: Random point | 1.96 / 2.29 / 2.35 / 2.34 / 2.34 | 2.00 / 2.26 / 2.36 / 2.34 / 2.33 |
| ARM store range (l.380) | 2.19x-2.36x | 1.98x-2.34x (store 1.98 / 2.25 / 2.31 / 2.34 / 2.29) |

```
ARM: Sharegen ($x_i=i$) & 2.00$\times$ & 2.25$\times$ & 2.37$\times$ & 2.35$\times$ & 2.33$\times$ \\
ARM: Random point ($x_i \sim \F_p$) & 2.00$\times$ & 2.26$\times$ & 2.36$\times$ & 2.34$\times$ & 2.33$\times$ \\
```
```
On ARM, including memory stores gives $1.98\times$--$2.34\times$ speedup;
```

## D. XXH3-128 cell of tab:injective:adversarial (sections/injective.tex l.334)

Binary `tools/bench/adversarial/speed` as found (mtime 2026-09-05 19:53, md5 ed67bef9efb99360ab8ebc31272ff624, from
speed.cpp/speed_hashes.h of 2026-09-04 20:27; not rebuilt by this lane).  Three runs:

| run | XXH3-128 16 KB / 512 B (median; min-max) | XXH3-64 control (table 38.2 / 27.2) |
|---|---|---|
| `./speed 9 0.5 run XXH3` (20:35:43, load 4.32 -> 3.96) | **33.81** (31.6-38.2) / **24.73** (21.4-25.1) | 38.21 (30.8-38.9) / 27.64 (25.3-28.0) |
| `./speed 5 0.5 run XXH3-128` (20:36:11, load 3.96 -> 4.21) | 34.25 (33.6-37.8) / 24.88 (23.4-25.1) | -- |
| `./speed 9 0.15 run` full table, run 1 (20:34:00, load 2.54 -> 4.32) | 34.19 (34.0-38.1) / 15.64 (11.1-17.8; disturbed, see below) | 38.64 / 23.44 (15.8-27.8; disturbed) |
| `./speed 9 0.15 run` full table, run 2 (21:08:43, load 2.06 -> 3.17, clean) | 39.02 (38.6-39.5) / 25.17 (24.9-25.2) | 39.51 (39.0-39.7) / 28.56 (28.2-28.7) |

| cell | old | new (recommended) | alternative |
|---|---|---|---|
| XXH3-128 GB/s 16 KB / 512 B | 33.8 / 24.0 | 33.8 / 24.7 (`./speed 9 0.5 run XXH3`, control matches the table) | 39.0 / 25.2 (full-table run 2, where every row is 3-6 % above the table) |

```
\texttt{XXH3-128} (128-bit output)          & 1 & 28.5$^*$ & 33.8 & 24.7 \\
```
The XXH3-64 control of the recommended run (38.21 / 27.64) is within 0.1 / 0.4 GB/s of the table row (38.2 / 27.2), inside its
run-to-run spread, so the XXH3 row stays as traced, and the old XXH3-128 cell 33.8 / 24.0 is reproduced to 0 % / 3 %.  Caveat: the
16 KB XXH3-128 value is bimodal across the four runs -- medians 33.8 / 34.3 / 34.2 (maxima 38.1-38.2) and 39.0 in the clean run 2
(all nine timings 38.6-39.5); if the coordinator prefers the cleanest run, use the alternative `39.0 & 25.2`, but then the
neighbouring rows measured on 2026-09-02 are 3-6 % below what the same binary gives today (see run 2 below).

Comparability rows from the two full-table runs (`speed_full_runs9_t0.15.txt`, `speed_full_runs9_t0.15.run2.txt`; one binary,
RUNS=9, TARGET=0.15 s = the parameters of `speed_rerun.txt`).  In run 1 the load rose from 2.54 to 4.32 and the 512-byte half
(second half of the run) shows 2x min-max spreads for several rows (Polymur 5.6-15.4, komihash 8.5-24.3, XXH3-128 11.1-17.8):
its 512 B column is disturbed (*); run 2 is clean throughout.

| table row | table | run 1: 16 KB / 512 B | run 2: 16 KB / 512 B |
|---|---|---|---|
| This paper, one chain / 8 lanes / F_2^89-1 | 4.1 / 10.1; 23.8 / 17.9; 4.4 / 3.9 | 4.14 / 10.18; 23.38 / 18.06; 4.34 / 4.73 | 4.26 / 10.48; 24.50 / 18.17; 4.46 / 4.89 |
| Horner; unrolled; BRW; CLNH; mult-shift | 1.3 / 2.3; 5.1 / 7.4; 6.0 / 5.3; 27.3 / 26.3; -- / 16.5 | 1.28 / 2.30; 5.04 / 8.13; 6.03 / 5.94; 27.50 / 27.71; -- / 17.12 | 1.31 / 2.37; 5.29 / 8.36; 6.13 / 6.01; 28.32 / 28.04; -- / 17.26 |
| Polymur | 19.7 / 16.2 | 19.75 / 9.86* | 20.25 / 16.73 |
| wyhash; rapidhash | 26.5 / 34.8; 27.1 / 32.1 | 27.22 / 32.99; 27.17 / 34.12 | 28.20 / 36.00; 28.25 / 34.98 |
| XXH3; XXH3-128 | 38.2 / 27.2; 33.8 / 24.0 | 38.64 / 23.44*; 34.19 / 15.64* | 39.51 / 28.56; 39.02 / 25.17 |
| MUM v3; komihash | 33.0 / 26.8; 24.8 / 24.3 | 33.57 / 25.35; 25.24 / 15.71* | 34.22 / 27.97; 26.02 / 25.27 |
| UMASH-64; UMASH-128 | 40.7 / 32.9; 23.9 / 19.7 | 36.09 (29.4-38.2) / 33.26; 23.50 / 18.11 | 42.64 / 34.34; 24.68 / 20.06 |
| ChainHash 1 KB; 256 B; 64 B | 61.7 / 40.5; 57.7 / 36.8; 26.6 / 27.4 | 70.43 / 44.43; 67.78 / 40.61; 27.09 / 30.05 | 71.39 / 44.84; 69.03 / 40.93; 27.89 / 30.70 (see note) |
| caption "2.2 GB/s" (univ_injective_64 single key, 16 KB) | 2.2 | 2.47 | 2.54 |

Note on ChainHash: `tools/bench/chainhash/chainhash.h` has mtime 2026-09-05 19:45 and the `speed` binary 19:53 (not this lane), so
the ChainHash rows above are a newer chainhash.h than the `hrepo_v8` code of `batch4.out` behind the table's rows (61.7 / 57.7 /
26.6) and the "62 GB/s" prose (injective.tex:403-410, appendix_chainhash.tex:812-814); +14-17 % at 16 KB for the 1 KB and 256 B
configurations.  Not proposed as cell changes here -- whoever owns the chainhash.h change should re-time it under the manifest's
batch4 protocol (`./speed 5 0.5 run ChainHash`).

## E. SMHasher3 port of the plain recurrence (sections/injective.tex l.188-192), M2 Pro

Fork `~/repos/smhasher3`, `build-chainhash/SMHasher3` (Release, `-Xclang -target-feature -Xclang +aes -O3 -march=native`; binary
rebuilt 2026-09-05 19:55 by another lane, `hashes/injective_hash.cpp` md5 854b88d8415674c56bf6adf249485bfd, 9 lanes).  The M2 has no
user-mode cycle counter: SMHasher3 derives "cycles" from wall time at an assumed 3.5 GHz, so these numbers follow the P-core clock
and the load.  `--test=Speed` only (Small key speed test [1,31]-byte keys, Bulk speed test 262144-byte keys).

| run | small keys, cycles/hash | bulk 262144 B, bytes/cycle | load |
|---|---|---|---|
| `injective-hash.mersenne` run 1 (21:01:40) -- reported | **141.59** | **1.49** (all 8 alignments 1.49) | 2.83 -> 2.41 |
| `injective-hash.mersenne` run 2 (21:10:55) | 145.82 | 1.45 | 2.60 -> 3.20 (1-min load peaked at 5.2 mid-run) |
| `injective-hash.mersenne` noon reproduction (manifest, old binary of 00:19, load 6.7) | 138.79 | 1.57 | 6.7 |
| `injective-hash.mum` (21:07:02) | 64.92 | 14.08 (second bulk test 13.47) | 2.41 -> 2.51 |

| cell | old | new |
|---|---|---|
| bulk throughput, Mersenne port (l.188) | `$1.59$~bytes/cycle` | `$1.49$~bytes/cycle` |
| short keys (l.189) | `$133$~cycles per hash` | `$142$~cycles per hash` |
| MUM fold (l.192) | `$9\times$ higher ($14.4$~bytes/cycle)` | `$9\times$ higher ($14.1$~bytes/cycle)` (14.08 / 1.49 = 9.45x) |

```
and two rounds of shift-and-add reduction) it reaches $1.49$~bytes/cycle of
bulk throughput on a 256\,KiB message and $142$~cycles per hash on short
```
```
the bulk throughput $9\times$ higher ($14.1$~bytes/cycle), but that variant is
```
The old 133 / 1.59 are 6 % better than today's cleanest run; the three 2026-09-05 runs span 138.8-145.8 cycles and 1.45-1.57
bytes/cycle with no correlation to the recorded load (the noon run at load 6.7 was the fastest), i.e. the spread is the clock,
not the code.  The MUM/Mersenne ratio (9.45x) still rounds to the "$9\times$" of the text.

## F. Items not changed by this lane

* x86 cells of every table (Xeon lane).  * The ChainHash rows and the "62 GB/s" prose (see the note in D).
* The XXH3 (64-bit) row: control reproduced.  * The Mersenne prose "2.0x-2.5x" and "essentially the same speedups" (B).

## G. Raw data (harvest.py output, all repetitions)

## 1. Application benchmarks, ARM (Apple M2 Pro), 3 repetitions each; reported rep = median Horner value

Old cells: countsketch 5.49/4.96/4.33; linearprobe insert 32.5/28.5/28.5, query 42.7/41.9/38.6; xorfilter build 96.1/82.4/92.0, query 5.56/5.53/5.04 (Horner/R-W/Ours).

| binary | rep | Horner | R-W | Ours | header |
|---|---|---|---|---|---|
| countsketch ns/update | 1 | 5.33 | 4.68 | 4.12 | 2026-09-05 20:23:47 CEST, load 2.94 -> 2.95 |
| countsketch ns/update | 2 | 5.31 | 4.84 | 4.16 | 2026-09-05 20:23:52 CEST, load 2.95 -> 2.95 |
| countsketch ns/update | 3 | 5.11 | 4.64 | 4.09 | 2026-09-05 20:23:56 CEST, load 3.59 -> 3.59 |
| linearprobe ns/insert | 1 | 32.4 | 26.7 | 23.4 | 2026-09-05 20:23:50 CEST, load 2.95 -> 2.95 |
| linearprobe ns/query | 1 | 41.6 | 36.9 | 34.4 | |
| linearprobe ns/insert | 2 | 24.5 | 24.7 | 23.6 | 2026-09-05 20:23:54 CEST, load 2.95 -> 3.59 |
| linearprobe ns/query | 2 | 43.7 | 35.0 | 32.4 | |
| linearprobe ns/insert | 3 | 26.5 | 23.9 | 23.4 | 2026-09-05 20:23:58 CEST, load 3.59 -> 3.59 |
| linearprobe ns/query | 3 | 36.3 | 35.4 | 33.6 | |
| xorfilter ns/key (build) | 1 | 85.9 | 83.0 | 79.1 | 2026-09-05 20:23:51 CEST, load 2.95 -> 2.95 |
| xorfilter ns/query | 1 | 5.48 | 5.43 | 5.06 | |
| xorfilter ns/key (build) | 2 | 76.2 | 75.0 | 80.0 | 2026-09-05 20:23:55 CEST, load 3.59 -> 3.59 |
| xorfilter ns/query | 2 | 5.45 | 5.45 | 4.96 | |
| xorfilter ns/key (build) | 3 | 80.7 | 84.2 | 75.6 | 2026-09-05 20:23:59 CEST, load 3.59 -> 3.59 |
| xorfilter ns/query | 3 | 5.55 | 5.44 | 5.21 | |

**CountSketch** (rep 2): old `5.49 & 4.96 & \textbf{4.33}` -> new `5.31 & 4.84 & \textbf{4.16}`; ARM speedup Ours/Horner old 1.27x -> new 1.28x (R-W 1.10x).
LaTeX ARM part: `ns/update & 5.31 & 4.84 & \textbf{4.16} & <x86 cells>`

**Linear probing** (rep 3): insert old `32.5 & 28.5 & \textbf{28.5}` -> new `26.5 & 23.9 & \textbf{23.4}`; query old `42.7 & 41.9 & \textbf{38.6}` -> new `36.3 & 35.4 & \textbf{33.6}`.
ARM speedups Ours/Horner: inserts old 1.14x -> new 1.13x; lookups old 1.11x -> new 1.08x (R-W: 1.11x / 1.03x).
LaTeX ARM parts: `ns/insert & 26.5 & 23.9 & \textbf{23.4} & <x86>` / `ns/query  & 36.3 & 35.4 & \textbf{33.6} & <x86>`

**XOR filter** (rep 3): build old `96.1 & \textbf{82.4} & 92.0` -> new `80.7 & 84.2 & \textbf{75.6}`; query old `5.56 & 5.53 & \textbf{5.04}` -> new `5.55 & 5.44 & \textbf{5.21}`.
ARM ratios Horner/Ours: query old 1.10x -> new 1.07x; build (old: 'R-W is faster at build time') -> new Ours 1.07x, R-W 0.96x over Horner.
LaTeX ARM parts: `ns/key (build) & 80.7 & 84.2 & \textbf{75.6} & <x86>` / `ns/query       & 5.55 & 5.44 & \textbf{5.21} & <x86>`

## 2. Mersenne 2^89-1 rows (ARM), 3 repetitions; reported rep = median of mean Horner ns/eval over the table's 10 configs

Old: ARM Sharegen 2.02/2.37/2.47/2.49/2.44; ARM Random point 2.01/2.34/2.48/2.48/2.48; prose '2.0x-2.5x'; store 'essentially the same speedups'.

| rep | section | deg13 | deg15 | deg17 | deg19 | deg21 | Horner ns/eval (13..21) | Chain ns/eval (13..21) | header |
|---|---|---|---|---|---|---|---|---|---|
| 1 | x2s/u64-x | 0.51 | 0.61 | 0.62 | 0.63 | 0.63 | 31.2/37.9/41.6/47.4/53.6 | 60.7/61.7/66.8/75.4/85.7 | 2026-09-05 20:56:18 CEST, load 3.54 -> 3.70 |
| 1 | x2s/sharegen-seq | 2.05 | 2.35 | 2.51 | 2.47 | 2.45 | 137.0/158.8/182.9/204.0/225.9 | 66.9/67.6/72.9/82.7/92.3 |  |
| 1 | x2s/prf-rand | 2.06 | 2.38 | 2.51 | 2.47 | 2.44 | 137.8/159.1/181.6/203.5/226.2 | 66.9/67.0/72.2/82.3/92.7 |  |
| 2 | x2s/u64-x | 0.52 | 0.62 | 0.62 | 0.62 | 0.64 | 31.1/37.8/41.3/46.9/54.1 | 60.1/60.9/66.5/75.4/84.9 | 2026-09-05 20:57:26 CEST, load 4.04 -> 3.95 |
| 2 | x2s/sharegen-seq | 2.05 | 2.37 | 2.46 | 2.49 | 2.47 | 137.8/159.0/179.8/204.2/225.2 | 67.3/67.0/73.1/82.1/91.3 |  |
| 2 | x2s/prf-rand | 2.04 | 2.22 | 2.48 | 2.48 | 2.48 | 136.9/158.7/181.2/203.0/225.8 | 66.9/71.4/73.0/81.7/91.2 |  |
| 3 | x2s/u64-x | 0.51 | 0.62 | 0.62 | 0.63 | 0.62 | 30.9/37.8/41.0/47.2/53.2 | 60.3/61.3/66.4/74.5/85.2 | 2026-09-05 20:58:33 CEST, load 8.43 -> 7.52 |
| 3 | x2s/sharegen-seq | 2.06 | 2.35 | 2.51 | 2.48 | 2.45 | 137.3/159.0/184.3/204.1/224.8 | 66.7/67.7/73.4/82.3/91.8 |  |
| 3 | x2s/prf-rand | 2.05 | 2.36 | 2.47 | 2.47 | 2.45 | 137.2/159.1/181.5/206.9/225.0 | 67.0/67.5/73.4/83.8/91.8 |  |

**Mersenne (rep 1)**: Sharegen old 2.02/2.37/2.47/2.49/2.44 -> new 2.05/2.35/2.51/2.47/2.45; Random point old 2.01/2.34/2.48/2.48/2.48 -> new 2.06/2.38/2.51/2.47/2.44.
Range over both regimes: 2.05x-2.51x (prose old '2.0x-2.5x').
LaTeX: `ARM: Sharegen ($x_i=i$) & 2.05$\times$ & 2.35$\times$ & 2.51$\times$ & 2.47$\times$ & 2.45$\times$ \\`
LaTeX: `ARM: Random point ($x_i \sim \F_p$) & 2.06$\times$ & 2.38$\times$ & 2.51$\times$ & 2.47$\times$ & 2.44$\times$ \\`

**Mersenne store variant** (65536 points x 256 iters):

| rep | deg13 | deg15 | deg17 | deg19 | deg21 | header |
|---|---|---|---|---|---|---|
| 1 | 2.07 | 2.38 | 2.50 | 2.49 | 2.47 | 2026-09-05 20:56:32 CEST, load 3.70 -> 3.97 |
| 2 | 2.06 | 2.35 | 2.49 | 2.50 | 2.49 | 2026-09-05 20:57:40 CEST, load 3.95 -> 5.10 |
| 3 | 2.05 | 2.37 | 2.51 | 2.49 | 2.47 | 2026-09-05 20:58:47 CEST, load 7.52 -> 6.23 |

store (rep 1): 2.07/2.38/2.50/2.49/2.47, range 2.07x-2.50x (prose: 'essentially the same speedups').

## 3. Goldilocks rows (ARM), 3 repetitions; same selection rule

Old: ARM Sharegen 1.98/2.23/2.39/2.33/2.32; ARM Random point 1.96/2.29/2.35/2.34/2.34; ARM store range 2.19x-2.36x.

| rep | section | deg13 | deg15 | deg17 | deg19 | deg21 | Horner ns/eval | Chain ns/eval | header |
|---|---|---|---|---|---|---|---|---|---|
| 1 | x2s/seq | 1.98 | 2.26 | 2.36 | 2.35 | 2.36 | 127.4/148.6/169.8/189.7/213.9 | 64.2/65.6/71.9/80.8/90.6 | 2026-09-05 20:56:54 CEST, load 3.97 -> 4.04 |
| 1 | x2s/rand | 1.99 | 2.26 | 2.34 | 2.35 | 2.23 | 127.1/148.7/168.7/189.7/210.9 | 63.9/65.7/72.1/80.6/94.4 |  |
| 2 | x2s/seq | 1.99 | 2.26 | 2.37 | 2.36 | 2.25 | 126.5/147.3/169.2/191.0/210.7 | 63.5/65.2/71.5/80.9/93.7 | 2026-09-05 20:58:02 CEST, load 5.10 -> 6.58 |
| 2 | x2s/rand | 1.98 | 2.26 | 2.36 | 2.34 | 2.33 | 125.9/147.5/169.5/189.2/210.2 | 63.6/65.4/72.0/80.8/90.1 |  |
| 3 | x2s/seq | 2.00 | 2.25 | 2.37 | 2.35 | 2.33 | 127.2/147.2/169.0/191.3/211.8 | 63.6/65.3/71.5/81.6/90.7 | 2026-09-05 20:59:09 CEST, load 6.23 -> 5.73 |
| 3 | x2s/rand | 2.00 | 2.26 | 2.36 | 2.34 | 2.33 | 126.9/147.5/169.5/190.5/211.7 | 63.4/65.3/71.8/81.4/91.0 |  |

**Goldilocks (rep 3)**: Sharegen old 1.98/2.23/2.39/2.33/2.32 -> new 2.00/2.25/2.37/2.35/2.33; Random point old 1.96/2.29/2.35/2.34/2.34 -> new 2.00/2.26/2.36/2.34/2.33.
LaTeX: `ARM: Sharegen ($x_i=i$) & 2.00$\times$ & 2.25$\times$ & 2.37$\times$ & 2.35$\times$ & 2.33$\times$ \\`
LaTeX: `ARM: Random point ($x_i \sim \F_p$) & 2.00$\times$ & 2.26$\times$ & 2.36$\times$ & 2.34$\times$ & 2.33$\times$ \\`

**Goldilocks store variant**:

| rep | deg13 | deg15 | deg17 | deg19 | deg21 | header |
|---|---|---|---|---|---|---|
| 1 | 1.99 | 2.24 | 2.37 | 2.35 | 2.30 | 2026-09-05 20:57:05 CEST, load 4.04 -> 4.04 |
| 2 | 1.98 | 2.26 | 2.35 | 2.32 | 2.31 | 2026-09-05 20:58:12 CEST, load 6.58 -> 8.43 |
| 3 | 1.98 | 2.25 | 2.31 | 2.34 | 2.29 | 2026-09-05 20:59:19 CEST, load 5.73 -> 5.01 |

store (rep 3): 1.98/2.25/2.31/2.34/2.29; ARM store range old 2.19x-2.36x -> new 1.98x-2.34x.
LaTeX: `On ARM, including memory stores gives $1.98\times$--$2.34\times$ speedup;`

## 4. tab:injective:adversarial harness (tools/bench/adversarial/speed), M2 Pro

**speed_full_runs9_t0.15.txt** -- full table, `./speed 9 0.15 run` (RUNS/TARGET of speed_rerun.txt); 2026-09-05 20:34:00 CEST, load 2.54 -> 4.32

| table row | harness name | old 16 KB / 512 B | new 16 KB / 512 B (median; min-max) | ratio new/old |
|---|---|---|---|---|
| This paper, one chain, F_2^64 | Paper GF(2^64) injective, sequential | 4.1 / 10.1 | 4.14 (4.11-4.16) / 10.18 (9.91-10.27) | 1.01 / 1.01 |
| This paper, 8 lanes, F_2^64 | Paper GF(2^64) injective, 8 lanes | 23.8 / 17.9 | 23.38 (23.23-23.66) / 18.06 (17.63-18.11) | 0.98 / 1.01 |
| This paper, F_2^89-1 | Paper injective over F_{2^89-1} (smart reduction, 15 B/step) | 4.4 / 3.9 | 4.34 (4.32-4.40) / 4.73 (4.71-4.80) | 0.99 / 1.21 |
| Horner, F_2^64 | univ_horner_64 | 1.3 / 2.3 | 1.28 (1.01-1.29) / 2.30 (2.27-2.33) | 0.98 / 1.00 |
| Horner, unrolled | horner_unrolled_64 | 5.1 / 7.4 | 5.04 (1.96-5.10) / 8.13 (8.05-8.17) | 0.99 / 1.10 |
| BRW | univ_brw_64 | 6.0 / 5.3 | 6.03 (6.00-6.12) / 5.94 (5.79-5.97) | 1.01 / 1.12 |
| Polymur | Polymur (random k, s) | 19.7 / 16.2 | 19.75 (19.55-19.96) / 9.86 (5.63-15.42) | 1.00 / 0.61 |
| wyhash v4.3 | wyhash 4.3 (random secret) | 26.5 / 34.8 | 27.22 (27.06-27.40) / 32.99 (29.89-34.41) | 1.03 / 0.95 |
| rapidhash v1 | rapidhash v1 (random secret) | 27.1 / 32.1 | 27.17 (27.05-27.35) / 34.12 (33.93-34.27) | 1.00 / 1.06 |
| XXH3 | XXH3-64 withSeed (random seed) | 38.2 / 27.2 | 38.64 (38.39-39.03) / 23.44 (15.75-27.79) | 1.01 / 0.86 |
| XXH3-128 | XXH3-128 withSeed (random seed) | 33.8 / 24.0 | 34.19 (33.95-38.11) / 15.64 (11.13-17.79) | 1.01 / 0.65 |
| MUM v3 | MUM v3 (unroll 16) | 33.0 / 26.8 | 33.57 (32.91-33.74) / 25.35 (21.51-26.51) | 1.02 / 0.95 |
| komihash v5.34 | komihash 5.34 (random seed) | 24.8 / 24.3 | 25.24 (24.70-25.47) / 15.71 (8.51-24.25) | 1.02 / 0.65 |
| ChainHash, 1 KB | ChainHash, 1 KB blocks, K=5+twist, S=2 | 61.7 / 40.5 | 70.43 (68.27-70.89) / 44.43 (43.82-44.93) | 1.14 / 1.10 |
| ChainHash, 256 B | ChainHash, 256 B blocks, K=5+twist | 57.7 / 36.8 | 67.78 (65.32-68.92) / 40.61 (39.77-40.82) | 1.17 / 1.10 |
| ChainHash, 64 B | ChainHash, 64 B blocks, K=5+twist | 26.6 / 27.4 | 27.09 (26.59-27.20) / 30.05 (25.12-30.36) | 1.02 / 1.10 |
| UMASH-64 | UMASH 64 (umash_full) | 40.7 / 32.9 | 36.09 (29.35-38.22) / 33.26 (32.47-33.40) | 0.89 / 1.01 |
| UMASH-128 | UMASH 128 (umash_fprint) | 23.9 / 19.7 | 23.50 (17.27-23.60) / 18.11 (14.03-19.37) | 0.98 / 0.92 |
| CLNH | clnh_64 | 27.3 / 26.3 | 27.50 (26.54-27.99) / 27.71 (27.34-27.85) | 1.01 / 1.05 |
| Multiply-shift | Vector multiply-shift (Dietzfelbinger) | --- / 16.5 | --- / 17.12 (16.85-17.22) | --- / 1.04 |
| caption one-chain framework | univ_injective_64 (single key) | 2.2 / --- | 2.47 (2.46-2.48) / 4.74 (4.71-4.77) | 1.12 / --- |

**speed_full_runs9_t0.15.run2.txt** -- full table, second run, `./speed 9 0.15 run`; 2026-09-05 21:08:43 CEST, load 2.06 -> 3.17

| table row | harness name | old 16 KB / 512 B | new 16 KB / 512 B (median; min-max) | ratio new/old |
|---|---|---|---|---|
| This paper, one chain, F_2^64 | Paper GF(2^64) injective, sequential | 4.1 / 10.1 | 4.26 (4.13-4.31) / 10.48 (10.14-10.53) | 1.04 / 1.04 |
| This paper, 8 lanes, F_2^64 | Paper GF(2^64) injective, 8 lanes | 23.8 / 17.9 | 24.50 (21.34-24.57) / 18.17 (16.06-18.40) | 1.03 / 1.02 |
| This paper, F_2^89-1 | Paper injective over F_{2^89-1} (smart reduction, 15 B/step) | 4.4 / 3.9 | 4.46 (4.19-4.53) / 4.89 (4.81-4.93) | 1.01 / 1.25 |
| Horner, F_2^64 | univ_horner_64 | 1.3 / 2.3 | 1.31 (1.29-1.33) / 2.37 (2.33-2.40) | 1.01 / 1.03 |
| Horner, unrolled | horner_unrolled_64 | 5.1 / 7.4 | 5.29 (5.20-5.32) / 8.36 (7.52-8.40) | 1.04 / 1.13 |
| BRW | univ_brw_64 | 6.0 / 5.3 | 6.13 (5.43-6.20) / 6.01 (5.97-6.03) | 1.02 / 1.13 |
| Polymur | Polymur (random k, s) | 19.7 / 16.2 | 20.25 (17.05-20.47) / 16.73 (14.39-16.92) | 1.03 / 1.03 |
| wyhash v4.3 | wyhash 4.3 (random secret) | 26.5 / 34.8 | 28.20 (27.61-28.56) / 36.00 (35.29-36.34) | 1.06 / 1.03 |
| rapidhash v1 | rapidhash v1 (random secret) | 27.1 / 32.1 | 28.25 (25.25-28.38) / 34.98 (31.41-35.42) | 1.04 / 1.09 |
| XXH3 | XXH3-64 withSeed (random seed) | 38.2 / 27.2 | 39.51 (38.95-39.69) / 28.56 (28.23-28.68) | 1.03 / 1.05 |
| XXH3-128 | XXH3-128 withSeed (random seed) | 33.8 / 24.0 | 39.02 (38.62-39.48) / 25.17 (24.85-25.21) | 1.15 / 1.05 |
| MUM v3 | MUM v3 (unroll 16) | 33.0 / 26.8 | 34.22 (33.63-34.53) / 27.97 (27.47-28.19) | 1.04 / 1.04 |
| komihash v5.34 | komihash 5.34 (random seed) | 24.8 / 24.3 | 26.02 (25.55-26.15) / 25.27 (25.13-25.59) | 1.05 / 1.04 |
| ChainHash, 1 KB | ChainHash, 1 KB blocks, K=5+twist, S=2 | 61.7 / 40.5 | 71.39 (70.51-71.82) / 44.84 (44.32-45.41) | 1.16 / 1.11 |
| ChainHash, 256 B | ChainHash, 256 B blocks, K=5+twist | 57.7 / 36.8 | 69.03 (68.23-69.53) / 40.93 (40.81-41.35) | 1.20 / 1.11 |
| ChainHash, 64 B | ChainHash, 64 B blocks, K=5+twist | 26.6 / 27.4 | 27.89 (27.22-27.99) / 30.70 (30.14-30.88) | 1.05 / 1.12 |
| UMASH-64 | UMASH 64 (umash_full) | 40.7 / 32.9 | 42.64 (41.65-42.72) / 34.34 (33.72-34.58) | 1.05 / 1.04 |
| UMASH-128 | UMASH 128 (umash_fprint) | 23.9 / 19.7 | 24.68 (24.33-24.76) / 20.06 (19.74-20.18) | 1.03 / 1.02 |
| CLNH | clnh_64 | 27.3 / 26.3 | 28.32 (28.01-28.40) / 28.04 (27.67-28.25) | 1.04 / 1.07 |
| Multiply-shift | Vector multiply-shift (Dietzfelbinger) | --- / 16.5 | --- / 17.26 (16.88-17.36) | --- / 1.05 |
| caption one-chain framework | univ_injective_64 (single key) | 2.2 / --- | 2.54 (2.49-2.55) / 4.90 (4.74-4.94) | 1.15 / --- |

**speed_xxh3_runs9_t0.5.txt** -- `./speed 9 0.5 run XXH3`; 2026-09-05 20:35:43 CEST, load 4.32 -> 3.96

| table row | harness name | old 16 KB / 512 B | new 16 KB / 512 B (median; min-max) | ratio new/old |
|---|---|---|---|---|
| XXH3 | XXH3-64 withSeed (random seed) | 38.2 / 27.2 | 38.21 (30.83-38.94) / 27.64 (25.28-28.00) | 1.00 / 1.02 |
| XXH3-128 | XXH3-128 withSeed (random seed) | 33.8 / 24.0 | 33.81 (31.61-38.19) / 24.73 (21.36-25.11) | 1.00 / 1.03 |

**speed_xxh3_128_runs5_t0.5.txt** -- `./speed 5 0.5 run XXH3-128`; 2026-09-05 20:36:11 CEST, load 3.96 -> 4.21

| table row | harness name | old 16 KB / 512 B | new 16 KB / 512 B (median; min-max) | ratio new/old |
|---|---|---|---|---|
| XXH3-128 | XXH3-128 withSeed (random seed) | 33.8 / 24.0 | 34.25 (33.61-37.78) / 24.88 (23.42-25.11) | 1.01 / 1.04 |

## 5. SMHasher3 injective-hash speed (M2 Pro)

Old (injective.tex:188-192): 1.59 bytes/cycle bulk, 133 cycles/hash small keys (mersenne); MUM fold 14.4 bytes/cycle, '9x higher'.

- `injective-hash.mersenne` second run: small keys 145.82 cycles/hash; bulk 1.45 bytes/cycle (2026-09-05 21:10:55 CEST, load 2.60 -> 3.20)
- `injective-hash.mersenne`: small keys 141.59 cycles/hash; bulk 1.49 bytes/cycle (2026-09-05 21:01:40 CEST, load 2.83 -> 2.41)
- `injective-hash.mum`: small keys 64.92 cycles/hash; bulk 14.08 bytes/cycle (2026-09-05 21:07:02 CEST, load 2.41 -> 2.51)
- ratio mum/mersenne bulk: 9.45x (old 9x = 14.4/1.59 = 9.06)
- cells: `$1.59$~bytes/cycle` -> `$1.49$~bytes/cycle`; `$133$~cycles per hash` -> `$142$~cycles per hash`; `$9\times$ higher ($14.4$~bytes/cycle)` -> `$9\times$ higher ($14.1$~bytes/cycle)`
