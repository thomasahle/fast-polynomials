# Xeon 8375C re-run of every x86 application / prime-field cell (lane C, 2026-09-05)

Machine: Intel Xeon Platinum 8375C @ 2.90 GHz (Ice Lake, 2 sockets, 96 logical CPUs,
`hardware.normalcomputing.net`, shared host), Linux, clang 21.1.8 (Red Hat), flags
`-O3 -std=c++17 -march=native`.  Sources: `tools/bench/*.cpp` + `tools/bench/framework/*.h`
rsync'ed from this repository the same day (md5 list in `sources.md5`; the source md5 of each
binary is also in the header of every log).  Driver: `run_laneC.sh` (in this directory).

Every binary is single-threaded, was run with its default arguments (= the protocol stated in
`sections/experiments.tex`) and pinned with `taskset -c 80-95` (16 logical CPUs on NUMA node 1,
distinct physical cores; siblings are CPUs 32-47).  Three repetitions per binary, interleaved
(rep 1 of all seven binaries, then rep 2, then rep 3).  Each log starts with `#` header lines
(date, host, `uptime` before, exact command, compiler, source md5) and ends with the exit code,
wall time in ms and `uptime` after; everything between is the binary's verbatim stdout.

Files (`<binary>.<rep>.txt`):

| binary | paper cells | protocol (defaults) |
|---|---|---|
| `app_countsketch_x86` | CountSketch x86 ns/update (experiments.tex:255) | 2^16 table, 2^20 updates, mean of fastest 50 of 100 reps |
| `app_linearprobe_x86` | linear probing x86 ns/insert, ns/query (278-279) | 2^20 table, load 70 %, one timed build after 2^12 warm-up, lookups = total over 5 passes |
| `app_xorfilter_x86` | XOR filter x86 ns/key (build), ns/query (302-303) | 2^20 table, load 75 %, one timed build, queries = total over 5 passes |
| `shamir_sharegen_mersenne` | Mersenne 2^89-1 x86 rows (357-358): `x2s/sharegen-seq`, `x2s/prf-rand` Speedup lines | 4096 points x 1024 iterations |
| `shamir_sharegen_mersenne_store` | (no x86 cell; store-to-memory control) | 65536 points x 256 iterations |
| `app_goldilocks_stark_eval` | Goldilocks x86 rows (375-376): `x2s/seq`, `x2s/rand` Speedup lines | 4096 x 1024 |
| `app_goldilocks_sharegen_store` | Goldilocks x86 store range (381) | 65536 x 256 |

Selection rule for the quoted cell: the repetition with the median Horner value (median
degree-13 Horner time for the prime-field kernels); all three repetitions are kept here.
`rows.md` lists old cell -> new cell, the LaTeX rows and the recomputed ratios.

## Two sets

* `setA_contaminated/` (18:04-18:09 UTC): the first three repetitions.  While they ran, another
  lane's `adversarial` harness (`laneC/adv`, `laneC/adv16` on the Xeon) executed 12-16 threads
  pinned to the same CPUs 80-95 (`run_length.sh 12 31` 18:04:38-18:06:12, `scan 12 29`,
  `random 12 30`, a 16-thread `length` replicate).  Repetition 3 is visibly disturbed (Mersenne
  degree-19 Horner 265.9 ns instead of 212.7 ns; Goldilocks store degree 19/21 Horner 280/331 ns
  instead of 166/184).  Kept as evidence, not quoted.
* this directory (set B, 18:13-18:17 UTC, driver `run_laneC_setB.sh`, same binaries): started
  after that job reported `ALL_DONE`; `top_procs.<rep>.txt` lists every process above 20 % CPU
  at the start of each repetition (one unrelated single-threaded python job with affinity 0-95, and
  during rep 2 a `lean` process at 38 %).  1-min load 4.4-9.9 on 96 CPUs.  **Quoted set.**
  The three repetitions agree to within ~1 % on every cell.

## Quoted cells (set B, median-Horner repetition)

| paper cell | value | repetition |
|---|---|---|
| CountSketch x86 ns/update (Horner / R--W / Ours) | 16.2 / 9.64 / 7.35 (ours 2.20x over Horner) | `app_countsketch_x86.2.txt` |
| Linear probing x86 ns/insert | 40.7 / 28.0 / 24.2 (1.68x) | `app_linearprobe_x86.3.txt` |
| Linear probing x86 ns/query | 58.2 / 39.5 / 34.9 (1.67x) | `app_linearprobe_x86.3.txt` |
| XOR filter x86 ns/key (build) | 136.6 / 101.2 / 96.1 (1.42x) | `app_xorfilter_x86.3.txt` |
| XOR filter x86 ns/query | 20.9 / 13.4 / 10.5 (1.99x) | `app_xorfilter_x86.3.txt` |
| Mersenne 2^89-1 x86 Sharegen (x_i=i), degrees 13-21 | 1.77x / 2.00x / 2.00x / 2.02x / 2.03x | `shamir_sharegen_mersenne.1.txt` (`x2s/sharegen-seq`) |
| Mersenne 2^89-1 x86 Random point | 1.77x / 2.00x / 2.00x / 2.02x / 2.03x | `shamir_sharegen_mersenne.3.txt` (`x2s/prf-rand`) |
| Mersenne x86 store-to-memory (no paper cell) | 1.80x / 2.02x / 2.02x / 2.03x / 2.05x | `shamir_sharegen_mersenne_store.1.txt` |
| Goldilocks x86 Sharegen (x_i=i) | 1.69x / 1.84x / 1.86x / 1.89x / 1.89x | `app_goldilocks_stark_eval.3.txt` (`x2s/seq`) |
| Goldilocks x86 Random point | 1.69x / 1.85x / 1.86x / 1.89x / 1.90x | `app_goldilocks_stark_eval.2.txt` (`x2s/rand`) |
| Goldilocks x86 store range | 1.68x-1.89x | `app_goldilocks_sharegen_store.2.txt` |

These replace the AMD EPYC 9R14 rows of `tools/bench/x86_output.txt`
(= `results/application_benchmarks/x86_output_amd_epyc_9r14.txt`, kept as history) and the
untraceable x86 application cells; see `rows.md` for old -> new per cell, LaTeX rows and the
prose/abstract consequences (the abstract's "up to 4.6x" was the EPYC degree-19 Mersenne cell).
