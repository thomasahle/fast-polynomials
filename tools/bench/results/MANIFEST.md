# Raw benchmark logs behind the paper's number tables

Compiled 2026-09-05.  Every file under `tools/bench/results/` is a verbatim copy
(`cp -p`, original mtimes kept) of a raw run log; nothing here was edited.  Paths
are relative to the repository root; `sections/` line numbers refer to the sources
as of 2026-09-05.  Files whose origin is marked *scratchpad* or *task output*
existed only in an ephemeral working directory before this copy.  No copied file
exceeds 1.6 MB, so no log was truncated.

`.git/info/exclude` lists `/tools/`, so these files (and `tools/bench/x86_output.txt`
etc.) must be added with `git add -f`.

Machines: **M2 Pro** = Apple M2 Pro, macOS, Apple clang 17.0.0 (`-O3 -std=c++17
-march=armv8-a+crypto`).  **Xeon** = Intel Xeon Platinum 8375C
(hardware.normalcomputing.net), clang 21.1.8 (`-O3 -std=c++17 -march=native`).
**EPYC** = AMD EPYC 9R14 (the January 2026 x86 run; compiler not recorded in the log).

Directory overview (details per table below):

| directory | contents |
|---|---|
| `kwise_injective_universal/` | the four `carryless_arm.cpp` / `carryless.cpp` harness runs of 2026-09-02 behind `tab:kwise_both`, `tab:injective`, `tab:injective:universal`, plus `mktable.py` |
| `figure_bench_all/` | data behind `figures/bench_all.pdf` (created by the figure-provenance pass, commit `cbb33c7`) |
| `tabulation_table/` | the EPYC run behind the x86 column of the Section 5.7 table, and the 2026-09-05 `bench_tabrows` re-runs on M2 Pro and Xeon |
| `application_benchmarks/` | the EPYC run behind the x86 prime-field rows; 2026-09-05 reproduction runs of the ARM application kernels |
| `adversarial_table/` | `tools/bench/adversarial/speed` harness outputs behind `tab:injective:adversarial` (heuristic hashes, framework rows, three-key rows, ChainHash rows) |
| `smhasher3_chainhash/` | full SMHasher3 suites (M2 Pro, Xeon) and speed-only runs of the shipped ChainHash; build/verify logs |
| `twist_experiment/` | the six SMHasher3 runs of the finalizer-degree / twist experiment |
| `seeded_differential/` | default-tier SeedDifferential sweep (308 hashes), extended-tier (2^30) runs, XXH3 differential counts |
| `numstab/` | JSON/log outputs of `tools/numstab.mjs` that `tools/numstab_table.py` renders into `sections/numstab_table.tex` |
| `appendix_char2_timings/` | nanosecond timings quoted in `appendix_polynomials.tex` |

---

## 1. `tab:kwise_both` (sections/experiments.tex:176-188)

* **Script**: `tools/bench/carryless_arm.cpp` (ARM) / `tools/bench/carryless.cpp` (x86),
  function `test_speed_function64`: `nr_trials` random 64-bit inputs, `2*nr_times`
  timed repetitions (fresh `init()` each), sorted, fastest `nr_times` kept, mean and
  population std of those, in microseconds per `nr_trials` hashes.  Both runs used
  `nr_trials = 100000, nr_times = 100` (the ARM log prints "Trials per test: 100000 /
  Repetitions: 100"; the x86 harness does not print its arguments, the scale is
  inferred from the identical magnitudes).  The table is in microseconds per 10^6
  hashes, i.e. **the log values times 10, rounded**.
* **Logs**: `kwise_injective_universal/arm_rerun.txt` (M2 Pro, 2026-09-02 19:05,
  scratchpad) and `kwise_injective_universal/x86_rerun.txt` (Xeon, 2026-09-02 19:17,
  scratchpad).
* **Extraction**: in each `Degree k` block take the lines `Carryless` (Horner),
  `Lemire`, `Estrin`, `Rabin Winograd`, `Smart CL` (Ours); multiply the mean by 10.

| k | ARM log means (x10 = table) | x86 log means (x10 = table) |
|---|---|---|
| 3 | 82.52/88.16/113.66/89.96/87.05 -> 825/882/1137/900/870 | 193/164.87/219/192.95/175 -> 1930/1649/2190/1930/1750 |
| 5 | 189.46/214.86/232.63/220.37/143.39 -> 1895/2149/2326/2204/1434 | 481.61/422.27/462.14/450.39/309 -> 4816/4223/4621/4504/3090 |
| 7 | 322.46/411.54/312.64/223.47/224.08 -> 3225/4115/3126/2235/2241 | 853.54/774.87/621.72/507.36/488.01 -> 8535/7749/6217/5074/4880 |
| 9 | 486.89/669.41/491/399.56/264.14 -> 4869/6694/4910/3996/2641 | 1281.65/1203.13/870.87/824.98/595.16 -> 12817/12031/8709/8250/5952 |

All 40 cells reproduce exactly.

## 2. `tab:injective` (sections/experiments.tex:456-470)

* **Script/protocol**: same two runs as Section 1 (the `Universal Hash Comparison`
  section that `carryless_arm.cpp`/`carryless.cpp` print after the k-wise blocks),
  lines `Horner (2N-1 mults)` and `Injective (N mults)` for N = 4, 8, 16, 32.
  Table = log mean and std times 10, rounded to the nearest 10.
* **Logs**: `kwise_injective_universal/arm_rerun.txt`, `kwise_injective_universal/x86_rerun.txt`.

| 2N | ARM Horner / Injective (log) | x86 Horner / Injective (log) |
|---|---|---|
| 8 | 538.04+/-6.9 / 383.17+/-4.6 -> 5380+/-70 / 3830+/-50 | 1338.67+/-2.0 / 1194.37+/-1.1 -> 13390+/-20 / 11940+/-10 |
| 16 | 2032.02+/-37.2 / 960.28+/-11.5 -> 20320+/-370 / 9600+/-110 | 4560.85+/-3.3 / 2427.2+/-3.1 -> 45610+/-30 / 24270+/-30 |
| 32 | 7201.26+/-98.0 / 3978.46+/-50.1 -> 72010+/-980 / 39780+/-500 | 14064.7+/-3.1 / 6009.94+/-2.1 -> 140650+/-30 / 60100+/-20 |
| 64 | 21809.7+/-154.3 / 11125.6+/-97.6 -> 218100+/-1540 / 111260+/-980 | 36286.7+/-4.5 / 17583.6+/-4.5 -> 362870+/-50 / 175840+/-50 |

All cells reproduce.

## 3. `figures/bench_all.pdf` and the k=9 sentence (sections/experiments.tex:423-439)

Recorded from the figure-provenance pass (commit `cbb33c7`, 2026-09-05 12:05, "Figure:
regenerate bench_all.pdf from the run behind the k-wise table"); its files are in
`figure_bench_all/`:

* `figure_bench_all/arm_rerun_x10.txt`: `arm_rerun.txt` of Section 1 with the means
  scaled to 10^6 hashes; this is what `tools/plot_bench_paper.py` (reads the harness
  output on stdin, `plot_all_algorithms`, plots the per-degree `Mean` with the std as
  error bar) was fed to produce the **current** `figures/bench_all.pdf`.  The figure
  is M2 Pro only (Mersenne panel and carryless panel from the same run).
* `figure_bench_all/data_fig_20260902_1321.txt`: the harness output behind the
  **previous** figure (M2 Pro, "Trials per test: 1000000, Repetitions: 100", 109 lines,
  no universal section).  It is the source of the text's k=9 numbers: `Degree 9 /
  Smart CL: 2833.07 +/- 13.77` and `Mersenne, smart: 11863.6 +/- 42.12` ("2833 us",
  "11864 us", ratio 4.19).  In the run now plotted (`arm_rerun_x10.txt`) the same
  cells are 2641 and 11361 (ratio 4.30); the sentence at experiments.tex:437-439 still
  quotes the old run.

## 4. Tabulation comparison, Section 5.7 (sections/experiments.tex:363-411)

Current table (MurmurHash3 593/1042, xxHash64 1174/1862, Tabulation 1660/6952,
Dietzfelbinger 1569/3498, 3205/8219, 4993/13633, This Paper 914/2285, 1036/3930,
1521/4214, 2346/6074):

* **x86 column** = `tabulation_table/x86_output_amd_epyc_9r14.txt` (copy of
  `tools/bench/x86_output.txt`, 2026-01-04, header "x86 (AMD EPYC 9R14)", i.e. *not*
  the Xeon): `Tabulation 8x2^8: 6952.14 +/- 4.55`, `Degree 3 Smart CL 2285 +/- 2.55`,
  `Degree 4 Smart CL 3929.74 +/- 4.66` (the x86 `smartcl_64<4>` is the
  three-multiplication lift, see `tab:families`), `Degree 5 Smart CL 4213.69 +/- 3.21`.
  `Degree 7 Smart CL` is `6076.65 +/- 4.18` in the log while the paper prints
  `6074 +/- 4`: nearest surviving log, not an exact match.  The file has **no**
  MurmurHash3, xxHash64 or Dietzfelbinger lines: x86 1042, 1862, 3498, 8219, 13633 are
  untraceable.
* **ARM column**: `Tabulation 1660 +/- 12` and `This Paper (k=7) 2346 +/- 9` are the
  lines `Tabulation 8x2^8: 1660.02 +/- 11.61` and `Degree 7 Smart CL: 2346.1 +/- 8.53`
  of `figure_bench_all/data_fig_20260902_1321.txt` (M2 Pro, 10^6 trials).  The other
  ARM cells (593, 1174, 1569, 3205, 4993, 914, 1036, 1521) match no surviving log
  (that run has Degree 3 = 902.7, Degree 5 = 1493.2; `arm_rerun*.txt` have
  Tabulation 1620/1656 and Dietz-192 1481/1513): untraceable.
  `tools/bench/bench_nonpoly_arm.cpp` (Murmur/xxHash/tabulation loop) has no
  surviving output at all.
* **New runs (2026-09-05)**, not yet in the paper: `tabulation_table/tabrows_2026-09-05/`.
  Driver `tools/bench/bench_tabrows.cpp` (all rows, one wrapper, `1e6` inputs,
  fastest 100 of 200 repetitions).  `m2/tabrows_run{1,2,3}.txt` (M2 Pro, Apple clang,
  1-min load 5.15-4.73 recorded in `*.load`), `xeon/tabrows_run{1,2,3}.txt` (Xeon,
  clang 21.1.8, `taskset -c 80-87`, load 8.26-8.85 on 96 CPUs).  `table.md` gives the
  per-row three-run ranges, the quoted cell (run with the median mean) and the proposed
  LaTeX rows; `result.md` documents the added `quartic2_64`/`quartic3_64`/`motzkin_61`
  classes and their selftests.  Quoted cells: M2 Pro 589/1160/1668/1563/3085/4893/886/
  992/1428/2008/1470/2299; Xeon 854/1888/2244/2280/4986/7905/1779/1903/2909/3199/3141/4968.

## 5. Application benchmarks (sections/experiments.tex:222-361)

### Sketch (236-244), hash table (257-265), membership filter (279-287)

No surviving log on either platform for any of the 30 cells (ARM 5.49/4.96/4.33;
32.5/28.5/28.5, 42.7/41.9/38.6; 96.1/82.4/92.0, 5.56/5.53/5.04; x86 38.3/24.9/23.7;
37.4/29.9/24.5, 46.3/35.4/31.4; 142.0/110.3/97.1, 19.6/15.6/11.1).  Sources and the
January 2026 ARM binaries are in `tools/bench/` (`app_countsketch_{arm,x86}.cpp`,
`app_linearprobe_*.cpp`, `app_xorfilter_*.cpp`; binaries `countsketch_arm`,
`linearprobe_arm`, `xorfilter_arm`, all 2026-01-04).  **Untraceable.**

`application_benchmarks/rerun_2026-09-05_m2pro/` holds a **reproduction run**
(2026-09-05 12:11, M2 Pro, 1-min load 8.9 before / 6.7 after, other jobs running, the
January binaries with default arguments = the paper's parameters).  It is *not* the
paper's run and does not reproduce it: CountSketch 5.28/4.78/4.23 ns/update
(Horner/RW/Ours); linear probing insert 29.6/24.8/26.5, query 38.3/36.8/34.3;
XOR filter build 112.9/135.5/130.4 ns/key (the paper has Horner 96.1 slowest of the
three; here it is fastest), query 6.19/6.10/5.75.  `*.time` = wall time, `load_*.txt`
= `uptime` before/after.

### Mersenne 2^89-1 share generation / random-point rows (328-337)

* **x86 rows** (1.66/4.50/4.57/4.63/4.60 twice): `application_benchmarks/
  x86_output_amd_epyc_9r14.txt`, section `--- Mersenne Shamir Benchmark ---`
  (`points=4096 iters=1024`), `Speedup:` lines of `x2s/sharegen-seq` =
  1.6627/4.50338/4.56429/4.629/4.60091 and `x2s/prf-rand` =
  1.66263/4.49914/4.56599/4.62889/4.60286.  The degree-17 sharegen cell rounds to
  4.56 in the log (the paper prints 4.57 in both rows).  Machine is the EPYC, whereas
  the "Platform scope" paragraph names the Xeon for x86.
* **ARM rows** (2.02/2.37/2.47/2.49/2.44 and 2.01/2.34/2.48/2.48/2.48) and the
  store-variant sentence: **untraceable** (no log; binaries `shamir_sharegen_mersenne`,
  `shamir_sharegen_mersenne_store`).  Reproduction 2026-09-05 (same directory):
  `shamir_sharegen_mersenne.txt` sharegen-seq 2.89/2.46/2.48/2.54/2.47, prf-rand
  2.06/2.37/2.33/2.31/2.44 (the `u64-x` rows are a different, small-x regime not in
  the paper); `shamir_sharegen_mersenne_store.txt` 2.05/2.34/2.74/2.55/2.41.

### Goldilocks rows (346-359)

* **x86 rows**: same EPYC file, `--- Goldilocks STARK Eval ---`: seq
  1.27199/1.38258/1.41527/1.42784/1.37008 -> 1.27/1.38/1.42/1.43/1.37; rand
  1.27246/1.38329/1.41598/1.42859/1.36813 -> same.  "on x86, the range is 1.31x-1.90x"
  (store) = `--- Goldilocks Sharegen Store ---` 1.30835 ... 1.90423.  All match.
* **ARM rows** (1.98/2.23/2.39/2.33/2.32; 1.96/2.29/2.35/2.34/2.34; store 2.19-2.36):
  **untraceable**.  Reproduction 2026-09-05: `goldilocks_eval.txt` seq
  1.88/3.01/2.12/2.17/1.89, rand 2.05/2.31/2.35/2.36/2.32; `goldilocks_sharegen_store.txt`
  2.04/2.14/2.23/2.33/3.02.

## 6. `tab:injective:universal` (sections/injective.tex:222-255)

* **Script**: `carryless_arm.cpp` / `carryless.cpp` universal section (framework
  classes in `tools/bench/framework/injective_hashing.h`), 100000 inputs, fastest 100
  of 200 repetitions, microseconds per 10^5 hashes (used as printed, no scaling).
  Table body generated by `kwise_injective_universal/mktable.py` (scratchpad script):
  `python3 mktable.py arm_rerun2.txt "Apple M2 Pro (ARM, PMULL)"` and
  `python3 mktable.py x86_rerun2.txt "Intel Xeon Platinum 8375C (x86, PCLMULQDQ)"`;
  it rounds means, bolds the best O(1)-key column, marks std > 5% with a dagger.
* **Logs**: `kwise_injective_universal/arm_rerun2.txt` (M2 Pro, 2026-09-02 20:42,
  scratchpad), `kwise_injective_universal/x86_rerun2.txt` (Xeon, 2026-09-02 20:44,
  scratchpad).
* **Check**: `mktable_output_arm_rerun2.tex` and `mktable_output_x86_rerun2.tex`
  (regenerated 2026-09-05) are byte-identical to the table rows in
  `sections/injective.tex` (all 96 cells).

## 7. `tab:injective:adversarial` (sections/injective.tex:299-341)

* **Harness**: `tools/bench/adversarial/speed.cpp` + `speed_hashes.h` (+ vendored
  hashes in `tools/bench/adversarial/vendor/`), built by `tools/bench/adversarial/
  Makefile`.  `./speed <RUNS> <TARGET_SECONDS> run [name-filter]`: for each row, a
  calibrated number of calls on one L1-resident random buffer of 16384 or 512 bytes is
  timed RUNS times; the JSON line reports the **median** GB/s (`gbps`), min and max,
  reps and runs.  All rows M2 Pro, single thread.
* **Row -> log** (GB/s at 16 KB / 512 B):

| table row | value | log file (row name; median at 16384 / 512) |
|---|---|---|
| Horner, F_2^64 | 1.3 / 2.3 | `adversarial_table/speed_rerun.txt` (`univ_horner_64`; 1.26 / 2.26) |
| Horner, unrolled | 5.1 / 7.4 | same (`horner_unrolled_64`; 5.09 / 7.38) |
| BRW | 6.0 / 5.3 | same (`univ_brw_64`; 5.98 / 5.33) |
| CLNH (fixed length) | 27.3 / 26.3 | same (`clnh_64`; 27.29 / 26.25) |
| Multiply-shift (fixed length) | -- / 16.5 | same (`Vector multiply-shift (Dietzfelbinger)`; 16.48 at 512) |
| This paper, F_2^89-1 (89-bit output) | 4.4 / 3.9 | same (`Paper injective over F_{2^89-1} (smart reduction, 15 B/step)`; 4.40 / 3.88) |
| wyhash v4.3 | 26.5 / 34.8 | same (`wyhash 4.3 (random secret)`; 26.51 / 34.80) |
| rapidhash v1 | 27.1 / 32.1 | same (`rapidhash v1 (random secret)`; 27.11 / 32.12) |
| XXH3 | 38.2 / 27.2 | same (`XXH3-64 withSeed (random seed)`; 38.15 / 27.24) |
| MUM v3 | 33.0 / 26.8 | same (`MUM v3 (unroll 16)`; 32.95 / 26.79) |
| komihash v5.34 | 24.8 / 24.3 | same (`komihash 5.34 (random seed)`; 24.78 / 24.29) |
| UMASH-64 | 40.7 / 32.9 | same (`UMASH 64 (umash_full)`; 40.65 / 32.90) |
| UMASH-128 | 23.9 / 19.7 | same (`UMASH 128 (umash_fprint)`; 23.87 / 19.74) |
| caption: framework one-chain "2.2 GB/s" | 2.2 | same (`univ_injective_64 (single key)`; 2.24 at 16384) |
| Polymur | 19.7 / 16.2 | `adversarial_table/speed_new.txt` (`Polymur (random k, s)`; 19.66 / 16.19) |
| This paper, one chain, F_2^64 (3 keys) | 4.1 / 10.1 | `adversarial_table/threekey_runs/bv8gjh5w3.output` (`sequential`; 4.0575 / 10.0983) |
| This paper, 8 lanes, F_2^64 | 23.8 / 17.9 | same (`8 lanes`; 23.8056 / 17.9325) |
| ChainHash, 1 KB blocks | 61.7 / 40.5 | `adversarial_table/chainhash_perf_batches/batch4.out`, section `### harness v8` (61.67 / 40.46) |
| ChainHash, 256 B blocks | 57.7 / 36.8 | same (57.65 / 36.80) |
| ChainHash, 64 B blocks | 26.6 / 27.4 | same (26.60 / 27.42) |
| XXH3-128 (128-bit output) | 33.8 / 24.0 | **untraceable** (see below) |

  - `speed_rerun.txt`: M2 Pro, 2026-09-02 19:11, RUNS=9, scratchpad; the earlier
    3-pass run that is already in the public tree (`tools/bench/adversarial/
    speed_pass{1,2,3}_arm.jsonl`, assembled by `speed_assemble.py` into
    `speed_results.json`, meta "Apple M2 Pro, Apple clang 17.0.0, 3 passes x 15 runs")
    gives the same rows within noise but is *not* the run the table quotes.
  - `speed_new.txt`: M2 Pro, 2026-09-02 19:12 (Polymur and the superseded PaperHash rows).
  - `threekey_runs/bv8gjh5w3.output` (task output, 2026-09-03 02:18): the three-key
    (`u,y,z`) vector-resident implementation of `speed_hashes.h`; the file is the
    driving task's compact extract `name",size,gbps,min,max` of the harness JSON (the
    JSON itself did not survive).  Earlier runs of the same code under load:
    `bm0nbkunl.output` (02:00), `b65sfbyv4.output` (02:05), `final_speed_pg.txt`
    (01:25, 2.26/4.46/8.85/16.76), `final_speed_pg2.txt` (02:13, 4.32/8.27/15.91/17.73).
  - `chainhash_perf_batches/batch4.out`: M2 Pro, 2026-09-04 23:20, load 3.23 at the
    harness section, produced by `batch4.sh` (`./speed 5 0.5 run ChainHash` inside
    `hrepo_v8/adversarial`, i.e. RUNS=5).  `hrepo_v8/chainhash/chainhash.h` differs
    from the shipped `tools/bench/chainhash/chainhash.h` only in comment text
    (25 diff lines, five comment hunks); `speed.cpp`/`speed_hashes.h` are identical.
    `batch1.out` (v0/v3/v4), `batch2_loaded.out` (v4/v5/v6, load ~6), `batch3.out`
    (v5/v7) are the earlier optimisation steps; the `### bench vN` sections are the
    cycle-level microbenchmark `bench.cpp` (`build_bench.sh`), summarised by `parse.py`.
    `harness_m2_k5.jsonl` (+`.stderr`) is the pre-optimisation harness run of the same
    degree-5+twist hash (2026-09-04 20:39: 57.28/50.96/14.12 at 16 KB, 28.49/31.06/21.33
    at 512 B).  `k7_era/` are the degree-7-finalizer rows of 2026-09-03 (superseded).
  - `harness_competitors.txt` (2026-09-03 09:43): Polymur/komihash/ChainHash(K=7) re-timed
    under load 25-28 (not used).
  - **XXH3-128 row**: the harness has the row `XXH3-128 withSeed (random seed)`
    (`speed.cpp:159`) but no surviving output contains it; the only record is an agent
    report stating "33.8 GB/s".  `adversarial_table/reproduction_2026-09-05/
    speed_xxh3_128_rerun.txt` is a 2026-09-05 reproduction on the loaded M2 Pro
    (load 5.8): 22.70 / 20.86 GB/s, i.e. it does **not** reproduce the table.
* The *bits* column: proven bounds from the text; measured entries from the
  differential experiments of `tools/bench/adversarial/results_*.md` (public) and
  `seeded_differential/` (Section 10).

## 8. SMHasher3 results quoted for ChainHash

Paper claims and their logs (all SMHasher3 = the paper's fork with the
`SeedDifferential` test; hash registered as `chainhash-256` / `chainhash-1k` in the
fork's `hashes/chainhash.cpp`, which is not part of this repository):

* "both variants pass all 200 tests ... on an Apple M2 Pro and on an Intel Xeon 8375C"
  (injective.tex:399-402): `smhasher3_chainhash/final4_degree5_twist_optimised/
  final4_{m2,x86}_{256,1k}.txt`, each `Overall result: pass (200 / 200 passed)`.
  **Verification codes**: `chainhash-256` LE `0xAA4E2A3B`, `chainhash-1k` LE
  `0x7A1ED2E0` (M2 Pro `[hwpmull]`, Xeon `[hwclmul]`).  Runs 2026-09-05 00:29-00:39
  (M2), 00:36 (Xeon); the copies carry the handoff timestamp 10:56.
* `final3_degree5_twist_pre_optimisation/` (2026-09-04 20:46-20:53): the same
  function before the (A7) implementation optimisation, also 200/200 on both machines
  with the same verification codes -- the log evidence for "computes the same function
  bit for bit" (appendix_chainhash.tex:811).
* "66 cycles per small key (72 for the 1 KB configuration) and 20.7 (17.5) bytes/cycle
  in bulk" (appendix_chainhash.tex:812-814): `speed_optimised/sanity_speed_m2_256.txt`
  (`Average - 65.95 cycles/hash`, bulk 262144-byte keys `20.68 bytes/cycle`) and
  `speed_optimised/sanity_speed_m2_1k.txt` (`71.90 cycles/hash`, `17.50 bytes/cycle`);
  M2 Pro, 2026-09-05 00:21 (`--test=Speed` only; `build_m2.log` is the fork build).
  Xeon counterparts `sanity_speed_x86_*.txt` (112.02 / 111.18 cycles; 15.35 / 12.58 b/c).
  `speed_pre_optimisation/` (2026-09-04 20:32-20:51): 83.97 / 97.77 cycles, 17.38 /
  17.62 b/c on M2 Pro.
* "62 GB/s ... with 1 KB blocks", "26.6 against 23.8 GB/s at 16 KB"
  (injective.tex:403-410): harness rows of Section 7 (`batch4.out` v8: 61.67, 26.60;
  `bv8gjh5w3.output`: 23.8056).
* "worst bias ... 195.9x ... 16-bit window of the Permutation keyset"
  (appendix_chainhash.tex:786): `twist_experiment/k5.txt` line 964.
* `build_and_verify/`: `build_sh_m2.log` (`tools/bench/chainhash/build.sh`: reference
  vs optimised equality tests), `verify5.out` (`verify5.py`, degree-5 finalizer
  decoder identities), `exh5.out` (`exh5.c`, exhaustive small-field check).
* **Untraceable**: the SMHasher3 port of the plain recurrence in injective.tex:182-197
  ("1.59 bytes/cycle ... 133 cycles per hash ... 14.4 bytes/cycle" for
  `injective-hash.mersenne` / `injective-hash.mum`): no speed log of those registrations
  survives (they appear only in the seeded-differential sweep, Section 10).

## 9. Twist experiment table (sections/appendix_chainhash.tex:791-805)

* **Setup**: SMHasher3 full suite, 256-byte configuration, M2 Pro, 2026-09-03
  (`tools/bench/chainhash/twist_results.md`); the six variants are the registrations of
  `twist_experiment/chainhash_exp.cpp` (copied from the fork's `hashes/`).
* **Logs**: pass counts from the full-suite logs, cycle counts from the separate
  `--test=Speed` runs (`*_speed.txt`, "Average" over 1-31-byte keys):

| row | tests | log | cycles | log |
|---|---|---|---|---|
| degree 7, none | 200/200 | `k7.txt` (LE 0xCB0491AF) | 95.7 | `k7_speed.txt` 95.69 |
| degree 5, none | 178/200 | `k5.txt` (0xA6F72889) | 82.0 | `k5_speed.txt` 81.98 |
| degree 5, input twist | 200/200 | `k5_tin.txt` (0xAA4E2A3B = shipped) | 81.8 | `k5_tin_speed.txt` 81.80 |
| degree 5, in+out | 200/200 | `k5_tin_tout.txt` (0xB48D2403) | 83.2 | `k5_tin_tout_speed.txt` 83.19 |
| degree 3, input | 183/200 | `k3_tin.txt` (0x996A2EAD) | 66.5 | `k3_tin_speed.txt` 66.54 |
| degree 3, in+out | 183/200 | `k3_tin_tout.txt` (0x0A7FFA9A) | 67.4 | `k3_tin_tout_speed.txt` 67.40 |

  The bulk range "16.0-19.0 bytes/cycle" is the spread of the `Alignment 0` /
  `Average` bulk lines across these twelve files (16.36-19.00).  The full-suite logs
  also give the per-keyset failure lists quoted in the text (k5: 22 failures in Zeroes,
  Sparse, Permutation, TwoBytes, Bitflip; k3_tin: 17 in Zeroes, Permutation, SeedZeroes).

## 10. Seeded-differential test (sections/appendix_adversarial.tex:165-180; injective.tex:401-408)

* `seeded_differential/seeddiff_sweep_default_tier.log` (1.5 MB, handoff copy dated
  2026-09-04 19:56; M2 Pro; `SMHasher3 <hash> --test=SeedDifferential`, default tier
  2^24 seeds per pair, 308 hashes): 258 PASS, 48 FAIL (every `mum1/2/3.*` variant,
  `mir.exact/inexact`, and the deliberately weak `donothing*`, `aesrng*`, `sum8/32hash`,
  `fibonacci*`, `o1hash`, `khash*`, `FNV-YoshimitsuTRIAD`, `CrapWow`); `wyhash`,
  `rapidhash`, `XXH3` pass this tier.  The `chainhash-256`/`chainhash-1k` entries in
  this sweep are the **degree-7** build of 2026-09-04.
* `seeded_differential/extended_tier_2026-09-03/` (`run_one.sh`: `./SMHasher3 <hash>
  --test=SeedDifferential --extra` in the fork's `build-advtest`, M2 Pro, 2026-09-03
  00:38-01:09; `driver_verdicts_b14pf90dv.output` lists the verdicts and wall times):
  extended tier = 2^30 seeds on the first-fold pairs at 32/64/128/240 B and the adjacent
  pairs at 32 B.  Worst rows: `wyhash` 14/2^30 (2^-26.2), `wyhash.strict` 16, `rapidhash`
  13 (2^-26.3), `rapidhash.protected` 15, `XXH3-64` 17 (2^-25.9), `XXH3-128` 17,
  `injective-hash.mum` 15 (2^-26.1); every `mum*` 2^30/2^30 (rate 1) on the adjacent
  pairs; 0/2^30 for `komihash`, `polymurhash(-tweakseed)`, `SipHash-1-3/2-4`, `t1ha2-64/128`,
  `FarmHash-64.NA`, `CityHash-64`, `a5hash`, `gxhash-64`, `rust-ahash`, `MurmurHash3-128`,
  `poly-mersenne.deg{1,2,4}`, `chainhash-256` (degree-7 build, and `-k7-s1`).  These runs
  used SMHasher3's in-tree `wyhash v4.2` registration (the table's throughput row is the
  harness port of v4.3).
* `seeded_differential/xxh3_differential/results_compact.txt` (2026-09-02 21:46,
  `assemble.sh`/`compact.py`): collision counts in 2^30 trials per XXH3 build
  (v0.8.3, dev, homebrew) x variant x length for the three differentials A/B/C
  (e.g. `XXH3_64bits_withSeed`, 32 B, A: 10/2^30 = 2^-26.7; `XXH3_128bits_withSeed` A:
  5-12/2^30, B and C: 0).  The appendix's "2^31 trials ... 20-35 observed collisions"
  runs are **not** among the surviving logs; the public record of the differential
  search is `tools/bench/adversarial/results_{scan,fold,length,determ,random}.md`
  (2026-09-02, M2 Pro, threads=12, generated by `adversarial.cpp`, `fold_search.cpp`,
  `run_length.sh`), which report 2^24-2^30 trials per cell.  The truncated-Mersenne
  counts ("4 collisions in 2^26 random keys", "1 in 2^30") were not found in any
  surviving log.

## 11. `tab:numstab` (sections/numstab_table.tex, input at numerical_stability.tex:332)

* **Scripts**: `tools/numstab.mjs` (`node tools/numstab.mjs 7,15,31[,63] 12 coeffs|keys
  [fma]`; 12 random monic polynomials x 3 points = 36 samples per cell; writes
  `notes/numstab_<regime>[_fma].json` and prints the `.log` lines) and
  `tools/numstab_table.py`, which renders `notes/numstab_{coeffs,keys}.json` into
  `sections/numstab_table.tex`.  Pure JavaScript/rational arithmetic (website
  `char0` compiler), so machine-independent.
* **Data** (copies of the `notes/` files, which are git-excluded): `numstab/
  numstab_coeffs.json` + `.log` (2026-08-30 09:26, n = 7, 15, 31), `numstab_keys.json`
  (re-saved 2026-09-02 09:39) + `numstab_keys.log` (2026-08-30 09:26, n = 7, 15, 31,
  63); `*_fma.*` (2026-08-30 09:47, FMA variant, not tabulated); `numstab_sweep.log`
  (`tools/numstab_sweep.mjs`, 2026-08-29, per-degree amplification sweep used in the
  prose only).
* **Check**: `numstab_table_regenerated_2026-09-05.tex` (running `numstab_table.py` on
  these JSON files) differs from `sections/numstab_table.tex` in exactly two cells
  (`diff_paper_vs_regenerated.txt`): prescribed-coefficients Rabin-Winograd n=7 has
  rho = 12 in the paper but 11 in the JSON/log, and Horner n=31 has rho = 61 in the
  paper but 59 in the JSON/log.  The paper's values equal the prescribed-keys rho of
  the same schedules (rho does not depend on the regime), so the two cells were
  evidently harmonised by hand after generation; the raw coefficient-regime log records
  11 and 59.  Every other cell of the table matches the regenerated output.

## 12. Nanosecond timings in `sections/appendix_polynomials.tex` (lines 36, 52, 147, 166)

* "2.3 ns" (degree 7), "3.1 ns" (9), "4.4 ns" (11), "5.5 ns" (13): `appendix_char2_timings/
  appendix_char2_bench.txt` (M2 Pro PMULL, 10^6 random inputs, median of 41 repetitions;
  2026-09-03 09:36, scratchpad), second of the two runs in the file: 2.35 / 3.13 / 4.49 /
  5.54 ns (first run: 3.54 / 3.31 / 4.47 / 5.52).  Source
  `tools/bench/appendix_char2_circuits_arm.cpp` (2026-09-02).  Degrees 15-21 have no
  timing in the appendix.

## 13. Older files in `tools/bench/` (not the source of any current table)

`arm_output.txt`, `arm_output_fixed.txt`, `arm_output_fixed2.txt`, `arm_output_full.txt`,
`bench_fresh.txt`, `bench_fresh2.txt` (M2 Pro, 2026-01-04, earlier code generations) and
`sample_output.txt` (round-valued format example, not a measurement) match none of the
cells above and were left where they are.

---

## Untraceable numbers (no surviving raw log)

1. Section 5.7 table, ARM column: MurmurHash3 593+/-8, xxHash64 1174+/-5, Dietzfelbinger
   1569+/-36 / 3205+/-39 / 4993+/-58, This Paper k=3 914+/-4, Motzkin quartic 1036+/-13,
   k=5 1521+/-8 (only Tabulation 1660 and k=7 2346 are traced).
2. Section 5.7 table, x86 column: MurmurHash3 1042+/-2, xxHash64 1862+/-4, Dietzfelbinger
   3498+/-2 / 8219+/-4 / 13633+/-9; and k=7 6074+/-4 is off by 3 from the only
   candidate log (6076.65).
3. All 30 cells of the sketch, hash-table and membership-filter tables (both platforms).
4. ARM rows of the Mersenne share-generation table (10 cells) and of the Goldilocks
   table (10 cells), and the ARM store-variant range 2.19-2.36x.
5. `tab:injective:adversarial`: XXH3-128 33.8 / 24.0 GB/s.
6. injective.tex:182-197: 1.59 bytes/cycle, 133 cycles/hash, 14.4 bytes/cycle for the
   SMHasher3 ports `injective-hash.mersenne` / `injective-hash.mum`.
7. appendix_adversarial.tex: the 2^31-trial collision counts ("20-35 observed
   collisions in 2^31") and the truncated-Mersenne counts (4 in 2^26, 1 in 2^30); the
   in-tree `results_*.md` cover the same attacks at 2^24-2^30 trials.
8. `tab:numstab`: the two rho cells 12 (RW, n=7) and 61 (Horner, n=31) of the
   prescribed-coefficients block are not what the generator produces from the data (11, 59).

Also note (traceable but inconsistent): the k=9 sentence "2833 us ... 11864 us" comes
from the previous figure's run while the regenerated figure uses the k-wise-table run
(2641 / 11361); the x86 prime-field rows and the x86 tabulation column are AMD EPYC 9R14
runs although the platform paragraph names the Xeon 8375C.

## Directory listing (bytes, mtime, path)

```
    36711  2026-09-04 23:02  adversarial_table/chainhash_perf_batches/batch1.out
      337  2026-09-04 22:56  adversarial_table/chainhash_perf_batches/batch1.sh
    48340  2026-09-04 23:10  adversarial_table/chainhash_perf_batches/batch2_loaded.out
      437  2026-09-04 23:01  adversarial_table/chainhash_perf_batches/batch2.sh
    30424  2026-09-04 23:13  adversarial_table/chainhash_perf_batches/batch3.out
      406  2026-09-04 23:12  adversarial_table/chainhash_perf_batches/batch3.sh
    24486  2026-09-04 23:20  adversarial_table/chainhash_perf_batches/batch4.out
      331  2026-09-04 23:15  adversarial_table/chainhash_perf_batches/batch4.sh
     3537  2026-09-04 21:02  adversarial_table/chainhash_perf_batches/bench.cpp
      278  2026-09-04 21:03  adversarial_table/chainhash_perf_batches/build_bench.sh
     3296  2026-09-04 23:03  adversarial_table/chainhash_perf_batches/parse.py
     4019  2026-09-03 09:43  adversarial_table/harness_competitors.txt
     1309  2026-09-04 20:54  adversarial_table/harness_m2_k5.jsonl
      118  2026-09-04 20:54  adversarial_table/harness_m2_k5.stderr
     1198  2026-09-03 01:25  adversarial_table/k7_era/final_speed_ch.txt
     1226  2026-09-03 00:47  adversarial_table/k7_era/speed_chainhash.jsonl
     1226  2026-09-03 00:48  adversarial_table/k7_era/speed_chainhash2.jsonl
      771  2026-09-05 12:14  adversarial_table/reproduction_2026-09-05/speed_xxh3_128_rerun.txt
     2289  2026-09-02 19:12  adversarial_table/speed_new.txt
    15013  2026-09-02 19:11  adversarial_table/speed_rerun.txt
     1479  2026-09-03 02:05  adversarial_table/threekey_runs/b65sfbyv4.output
     3641  2026-09-03 02:00  adversarial_table/threekey_runs/bm0nbkunl.output
      685  2026-09-03 02:18  adversarial_table/threekey_runs/bv8gjh5w3.output
     2280  2026-09-03 01:25  adversarial_table/threekey_runs/final_speed_pg.txt
      909  2026-09-03 02:13  adversarial_table/threekey_runs/final_speed_pg2.txt
      425  2026-09-03 09:36  appendix_char2_timings/appendix_char2_bench.txt
       42  2026-09-05 12:11  application_benchmarks/rerun_2026-09-05_m2pro/countsketch_arm.time
      444  2026-09-05 12:11  application_benchmarks/rerun_2026-09-05_m2pro/countsketch_arm.txt
       44  2026-09-05 12:12  application_benchmarks/rerun_2026-09-05_m2pro/goldilocks_eval.time
     1074  2026-09-05 12:12  application_benchmarks/rerun_2026-09-05_m2pro/goldilocks_eval.txt
       44  2026-09-05 12:12  application_benchmarks/rerun_2026-09-05_m2pro/goldilocks_sharegen_store.time
      697  2026-09-05 12:12  application_benchmarks/rerun_2026-09-05_m2pro/goldilocks_sharegen_store.txt
       42  2026-09-05 12:11  application_benchmarks/rerun_2026-09-05_m2pro/linearprobe_arm.time
      495  2026-09-05 12:11  application_benchmarks/rerun_2026-09-05_m2pro/linearprobe_arm.txt
       31  2026-09-05 12:13  application_benchmarks/rerun_2026-09-05_m2pro/load_after.txt
       31  2026-09-05 12:10  application_benchmarks/rerun_2026-09-05_m2pro/load_before.txt
       44  2026-09-05 12:13  application_benchmarks/rerun_2026-09-05_m2pro/shamir_sharegen_mersenne_store.time
      686  2026-09-05 12:13  application_benchmarks/rerun_2026-09-05_m2pro/shamir_sharegen_mersenne_store.txt
       44  2026-09-05 12:12  application_benchmarks/rerun_2026-09-05_m2pro/shamir_sharegen_mersenne.time
     1718  2026-09-05 12:12  application_benchmarks/rerun_2026-09-05_m2pro/shamir_sharegen_mersenne.txt
       42  2026-09-05 12:11  application_benchmarks/rerun_2026-09-05_m2pro/xorfilter_arm.time
      550  2026-09-05 12:11  application_benchmarks/rerun_2026-09-05_m2pro/xorfilter_arm.txt
     7941  2026-01-04 23:05  application_benchmarks/x86_output_amd_epyc_9r14.txt
     9054  2026-09-05 12:05  figure_bench_all/arm_rerun_x10.txt
     4517  2026-09-05 12:05  figure_bench_all/data_fig_20260902_1321.txt
     8983  2026-09-02 19:05  kwise_injective_universal/arm_rerun.txt
     9375  2026-09-02 20:42  kwise_injective_universal/arm_rerun2.txt
      497  2026-09-05 12:06  kwise_injective_universal/mktable_output_arm_rerun2.tex
      526  2026-09-05 12:06  kwise_injective_universal/mktable_output_x86_rerun2.tex
     1502  2026-09-02 20:44  kwise_injective_universal/mktable.py
     8961  2026-09-02 19:17  kwise_injective_universal/x86_rerun.txt
     9183  2026-09-02 20:44  kwise_injective_universal/x86_rerun2.txt
      252  2026-09-05 12:14  numstab/diff_paper_vs_regenerated.txt
     2925  2026-08-30 09:47  numstab/numstab_coeffs_fma.json
     1531  2026-08-30 09:47  numstab/numstab_coeffs_fma.log
     2925  2026-08-30 09:26  numstab/numstab_coeffs.json
     1531  2026-08-30 09:26  numstab/numstab_coeffs.log
     3883  2026-08-30 09:47  numstab/numstab_keys_fma.json
     1969  2026-08-30 09:47  numstab/numstab_keys_fma.log
     3883  2026-09-02 09:39  numstab/numstab_keys.json
     1964  2026-08-30 09:26  numstab/numstab_keys.log
      743  2026-08-29 20:23  numstab/numstab_sweep.log
     3093  2026-09-05 12:06  numstab/numstab_table_regenerated_2026-09-05.tex
     2544  2026-09-03 01:08  seeded_differential/extended_tier_2026-09-03/driver_verdicts_b14pf90dv.output
      603  2026-09-03 00:38  seeded_differential/extended_tier_2026-09-03/hashlist.txt
     2520  2026-09-03 00:39  seeded_differential/extended_tier_2026-09-03/parse.py
      419  2026-09-03 00:38  seeded_differential/extended_tier_2026-09-03/run_one.sh
  ~5-6 KB  2026-09-03 00:38-01:09  seeded_differential/extended_tier_2026-09-03/sd_<hash>.txt  (39 files: a5hash, chainhash-256, chainhash-256-k7-s1, CityHash-64, FarmHash-64.NA, gxhash-64, injective-hash.mum, komihash, mum1/2/3.*.unroll*, MurmurHash3-128, poly-mersenne.deg1/2/4, polymurhash(-tweakseed), rapidhash(-micro,-nano,.protected), rust-ahash, SipHash-1-3/2-4, t1ha2-64/128, wyhash(-32,.strict), XXH3-64/128(.regen))
  1566018  2026-09-04 19:56  seeded_differential/seeddiff_sweep_default_tier.log
      562  2026-09-02 21:23  seeded_differential/xxh3_differential/assemble.sh
     2468  2026-09-02 21:46  seeded_differential/xxh3_differential/compact.py
     6570  2026-09-02 21:46  seeded_differential/xxh3_differential/results_compact.txt
     7601  2026-09-04 20:54  smhasher3_chainhash/build_and_verify/build_sh_m2.log
      498  2026-09-04 20:55  smhasher3_chainhash/build_and_verify/exh5.out
     1563  2026-09-04 20:55  smhasher3_chainhash/build_and_verify/verify5.out
   205290  2026-09-04 20:54  smhasher3_chainhash/final3_degree5_twist_pre_optimisation/final3_m2_1k.txt
   205269  2026-09-04 20:54  smhasher3_chainhash/final3_degree5_twist_pre_optimisation/final3_m2_256.txt
   205290  2026-09-04 20:54  smhasher3_chainhash/final3_degree5_twist_pre_optimisation/final3_x86_1k.txt
   205266  2026-09-04 20:54  smhasher3_chainhash/final3_degree5_twist_pre_optimisation/final3_x86_256.txt
   205299  2026-09-05 10:56  smhasher3_chainhash/final4_degree5_twist_optimised/final4_m2_1k.txt
   205265  2026-09-05 10:56  smhasher3_chainhash/final4_degree5_twist_optimised/final4_m2_256.txt
   205288  2026-09-05 10:56  smhasher3_chainhash/final4_degree5_twist_optimised/final4_x86_1k.txt
   205267  2026-09-05 10:56  smhasher3_chainhash/final4_degree5_twist_optimised/final4_x86_256.txt
     6629  2026-09-05 00:19  smhasher3_chainhash/speed_optimised/build_m2.log
     3193  2026-09-05 00:21  smhasher3_chainhash/speed_optimised/sanity_speed_m2_1k.txt
     3169  2026-09-05 00:21  smhasher3_chainhash/speed_optimised/sanity_speed_m2_256.txt
     3193  2026-09-05 00:26  smhasher3_chainhash/speed_optimised/sanity_speed_x86_1k.txt
     3169  2026-09-05 00:25  smhasher3_chainhash/speed_optimised/sanity_speed_x86_256.txt
     3193  2026-09-04 20:54  smhasher3_chainhash/speed_pre_optimisation/sanity_speed_m2_1k.txt
     3169  2026-09-04 20:54  smhasher3_chainhash/speed_pre_optimisation/sanity_speed_m2_256.txt
     3193  2026-09-04 20:54  smhasher3_chainhash/speed_pre_optimisation/sanity_speed_x86_1k.txt
     3169  2026-09-04 20:54  smhasher3_chainhash/speed_pre_optimisation/sanity_speed_x86_256.txt
   ~1 KB   2026-09-05 11:17  tabulation_table/tabrows_2026-09-05/{m2,xeon}/tabrows_run{1,2,3}.txt (+ .load files)
    10127  2026-09-05 11:17  tabulation_table/tabrows_2026-09-05/result.md
    15975  2026-09-05 11:17  tabulation_table/tabrows_2026-09-05/table.md
     7941  2026-01-04 23:05  tabulation_table/x86_output_amd_epyc_9r14.txt
    31996  2026-09-04 19:56  twist_experiment/chainhash_exp.cpp
     3096  2026-09-04 19:56  twist_experiment/k3_tin_speed.txt
     3111  2026-09-04 19:56  twist_experiment/k3_tin_tout_speed.txt
   206296  2026-09-04 19:56  twist_experiment/k3_tin_tout.txt
   206380  2026-09-04 19:56  twist_experiment/k3_tin.txt
     3077  2026-09-04 19:56  twist_experiment/k5_speed.txt
     3096  2026-09-04 19:56  twist_experiment/k5_tin_speed.txt
     3111  2026-09-04 19:56  twist_experiment/k5_tin_tout_speed.txt
   205558  2026-09-04 19:56  twist_experiment/k5_tin_tout.txt
   205539  2026-09-04 19:56  twist_experiment/k5_tin.txt
   206468  2026-09-04 19:56  twist_experiment/k5.txt
   205541  2026-09-04 19:56  twist_experiment/k7.txt
     3103  2026-09-04 19:56  twist_experiment/k7_speed.txt
```

Totals: 159 files, 5.2 MB (`du -sk`: seeded_differential 1.9 MB, smhasher3_chainhash
1.7 MB, twist_experiment 1.3 MB, adversarial_table 236 KB, the rest under 100 KB each).
