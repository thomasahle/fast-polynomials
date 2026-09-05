# Lane C: x86 cells re-measured on the Intel Xeon Platinum 8375C (2026-09-05)

Purpose: replace every x86 number that came from the January-2026 AMD EPYC 9R14 run
(`tools/bench/x86_output.txt`) or from no surviving log at all, so that the paper has a single x86
host (the Xeon 8375C named in `sections/experiments.tex:27` and `:84`).  No `.tex` file was edited in
this step; the replacement rows below are ready to paste.

Machine and protocol: Xeon 8375C @ 2.90 GHz, 96 logical CPUs, shared host (`uptime` recorded in
every log: 1-min load 4-10 at the start of each timed run of the quoted set, 15-min load 8-13 --
the load is other users' jobs on other cores), clang 21.1.8, `-O3 -std=c++17 -march=native`,
`taskset -c 80-95`, default arguments = the protocol printed in the paper, three repetitions each.
Raw logs: `tools/bench/results/rerun_2026-09-05/xeon/` (README there; scratch copy in
`final/C/xeon/`).  Quoted cell = repetition with the median Horner value (median degree-13 Horner
time for the prime-field kernels).

Two complete three-repetition sets were run:

* **set A** (18:04-18:09 UTC, `setA_contaminated/`): during it another lane's `adversarial`
  harness ran 12-16 threads pinned to the *same* CPUs 80-95 (its `run_length.sh 12 31` from
  18:04:38, `scan 12 29`, `random 12 30`, a 16-thread replicate); rep 3 shows the interference
  clearly (e.g. Mersenne degree-19 Horner 265.9 ns instead of 212.7).  Kept as evidence only.
* **set B** (from 18:13 UTC, after that job reported `ALL_DONE`; no other process pinned to
  80-95, see `top_procs.<rep>.txt`): **the quoted set**.  All cells below are from set B.

## A. Application kernels (experiments.tex lines 255, 278-279, 302-303; x86 columns only)

Old x86 cells: no log survives (MANIFEST section 5, "untraceable"; the platform paragraph names the Xeon, the numbers were most likely the January EPYC run).
New: Xeon 8375C, `taskset -c 80-95`, default arguments (= paper protocol), three repetitions; the quoted repetition is the one with the median Horner value (all three logs kept).

| cell (Horner / R--W / Ours) | old x86 (paper) | rep1 | rep2 | rep3 | quoted rep | new x86 (Xeon) |
|---|---|---|---|---|---|---|
| CountSketch ns/update | 38.3/24.9/23.7 | 16.2/9.64/7.35 | 16.2/9.64/7.35 | 16.2/9.64/7.35 | rep2 (load 6.10/6.01) | 16.2/9.64/7.35 |
| Linear probing ns/insert | 37.4/29.9/24.5 | 40.8/28.0/24.2 | 40.5/28.0/24.2 | 40.7/28.0/24.2 | rep3 (load 4.85/4.78) | 40.7/28.0/24.2 |
| Linear probing ns/query | 46.3/35.4/31.4 | 58.2/39.6/34.9 | 58.2/39.6/35.0 | 58.2/39.5/34.9 | rep3 (load 4.85/4.78) | 58.2/39.5/34.9 |
| XOR filter ns/key (build) | 142.0/110.3/97.1 | 136.0/100.4/94.9 | 137.7/101.2/97.4 | 136.6/101.2/96.1 | rep3 (load 4.78/4.78) | 136.6/101.2/96.1 |
| XOR filter ns/query | 19.6/15.6/11.1 | 21.0/13.3/10.4 | 21.0/13.4/10.5 | 20.9/13.4/10.5 | rep3 (load 4.78/4.78) | 20.9/13.4/10.5 |

Speedups over Horner (ours; R--W in parentheses), recomputed from the quoted repetition:

* CountSketch: old $1.62\times$ (line 259) -> **2.20x** (R--W 1.68x)
* Linear probing: old $1.53\times$ inserts / $1.47\times$ lookups (line 282) -> **1.68x inserts / 1.67x lookups** (R--W 1.45x / 1.47x)
* XOR filter: old $1.46\times$ build / $1.76\times$ queries (line 306) -> **1.42x build / 1.99x queries** (R--W 1.35x / 1.57x)

LaTeX (x86 half of each row; the ARM half belongs to the M2 Pro re-measurement of another lane and is left as printed here):

```latex
ns/update & 5.49 & 4.96 & \textbf{4.33} & 16.2 & 9.64 & \textbf{7.35}
ns/insert & 32.5 & 28.5 & \textbf{28.5} & 40.7 & 28.0 & \textbf{24.2} \\
ns/query  & 42.7 & 41.9 & \textbf{38.6} & 58.2 & 39.5 & \textbf{34.9}
ns/key (build) & 96.1 & \textbf{82.4} & 92.0 & 136.6 & 101.2 & \textbf{96.1} \\
ns/query       & 5.56 & 5.53 & \textbf{5.04} & 20.9 & 13.4 & \textbf{10.5}
```
Prose: line 259 `On x86, the speedup is $1.62\times$, reflecting ...` -> `$2.20\times$`; line 282 `$1.53\times$ for inserts and $1.47\times$ for lookups` -> `$1.68\times$ for inserts and $1.67\times$ for lookups`; line 306 `$1.46\times$ speedup for build and $1.76\times$ for queries` -> `$1.42\times$ speedup for build and $1.99\times$ for queries`.

## B. Mersenne 2^89-1 rows (experiments.tex lines 357-358) and Goldilocks rows (375-376), x86 store ranges

Old: AMD EPYC 9R14, `tools/bench/x86_output.txt` (Jan 2026, compiler unknown).  New: Xeon 8375C, three repetitions, quoted repetition = median degree-13 Horner time; Speedup = Horner ns / chain ns as printed by the binary, rounded to two decimals as in the paper.

| row | old EPYC log values | old paper cells | rep1 | rep2 | rep3 | quoted rep (load before/after) | **new Xeon cells** |
|---|---|---|---|---|---|---|---|
| Mersenne sharegen (x_i=i) | 1.6627/4.50338/4.56429/4.629/4.60091 | 1.66/4.50/4.57/4.63/4.60 | 1.77/2.00/2.00/2.02/2.03 | 1.77/2.00/2.00/2.01/2.03 | 1.77/2.00/2.00/2.01/2.03 | rep1 (9.43/8.22) | **1.77/2.00/2.00/2.02/2.03** (range 1.77-2.03) |
| Mersenne random point | 1.66263/4.49914/4.56599/4.62889/4.60286 | 1.66/4.50/4.57/4.63/4.60 | 1.78/2.00/2.00/2.01/2.03 | 1.77/2.00/2.00/2.02/2.03 | 1.77/2.00/2.00/2.02/2.03 | rep3 (4.78/4.82) | **1.77/2.00/2.00/2.02/2.03** (range 1.77-2.03) |
| Goldilocks sharegen (x_i=i) | 1.27199/1.38258/1.41527/1.42784/1.37008 | 1.27/1.38/1.42/1.43/1.37 | 1.69/1.85/1.86/1.89/1.90 | 1.69/1.85/1.85/1.89/1.89 | 1.69/1.84/1.86/1.89/1.89 | rep3 (4.54/4.45) | **1.69/1.84/1.86/1.89/1.89** (range 1.69-1.89) |
| Goldilocks random point | 1.27246/1.38329/1.41598/1.42859/1.36813 | 1.27/1.38/1.42/1.43/1.37 | 1.69/1.84/1.86/1.89/1.89 | 1.69/1.85/1.86/1.89/1.90 | 1.69/1.85/1.85/1.89/1.89 | rep2 (5.31/5.18) | **1.69/1.85/1.86/1.89/1.90** (range 1.69-1.90) |
| Goldilocks store-to-memory (range only) | 1.50544/1.30835/1.31205/1.35776/1.90423 | (range 1.31-1.90) | 1.68/1.84/1.87/1.89/1.89 | 1.68/1.84/1.87/1.89/1.89 | 1.68/1.84/1.87/1.89/1.89 | rep2 (5.18/4.85) | **1.68/1.84/1.87/1.89/1.89** (range 1.68-1.89) |
| Mersenne store-to-memory (not in the paper for x86) | -- | -- | 1.80/2.02/2.02/2.03/2.05 | 1.79/2.02/2.02/2.03/2.05 | 1.80/2.02/2.02/2.03/2.05 | rep1 (8.22/7.02) | **1.80/2.02/2.02/2.03/2.05** (range 1.80-2.05) |

Absolute times of the quoted repetitions (ns per evaluation, Horner -> chain), for the prose:

* Mersenne sharegen: d13 145.5->82.0, d15 168.1->84.1, d17 190.5->95.3, d19 212.8->105.6, d21 235.3->115.7
* Mersenne random: d13 145.5->82.1, d15 168.1->84.0, d17 190.4->95.1, d19 212.7->105.5, d21 235.1->115.6
* Mersenne store: d13 146.9->81.8, d15 169.6->83.8, d17 191.8->94.9, d19 214.6->105.6, d21 237.3->116.0
* Goldilocks sharegen: d13 112.6->66.7, d15 130.6->70.8, d17 148.4->80.0, d19 166.2->87.8, d21 184.2->97.2
* Goldilocks random: d13 112.4->66.7, d15 130.4->70.6, d17 148.3->79.9, d19 166.2->87.8, d21 185.0->97.2
* Goldilocks store: d13 112.3->66.8, d15 130.4->70.8, d17 148.4->79.3, d19 166.3->88.2, d21 183.6->97.3

LaTeX rows (replace lines 357-358 and 375-376; row labels `x86 (EPYC 9R14)` -> `x86 (Xeon 8375C)`):

```latex
x86 (Xeon 8375C): Sharegen ($x_i=i$) & 1.77$\times$ & 2.00$\times$ & 2.00$\times$ & 2.02$\times$ & 2.03$\times$ \\
x86 (Xeon 8375C): Random point ($x_i \sim \F_p$) & 1.77$\times$ & 2.00$\times$ & 2.00$\times$ & 2.02$\times$ & 2.03$\times$
...
x86 (Xeon 8375C): Sharegen ($x_i=i$) & 1.69$\times$ & 1.84$\times$ & 1.86$\times$ & 1.89$\times$ & 1.89$\times$ \\
x86 (Xeon 8375C): Random point ($x_i \sim \F_p$) & 1.69$\times$ & 1.85$\times$ & 1.86$\times$ & 1.89$\times$ & 1.90$\times$
```

Note: the `x2s/u64-x` blocks of `shamir_sharegen_mersenne` (evaluation points that are small 64-bit integers, so Horner multiplies a full-width key by a small x) are not in the paper; on the Xeon the chain is slower there (0.55x-0.63x), as on the M2 Pro (0.52x-0.63x in the 2026-09-05 reproduction).

Recomputed ranges: Mersenne x86 both regimes 1.77x-2.03x (degrees 15-21: 2.00x-2.03x); Mersenne x86 store 1.80x-2.05x; Goldilocks x86 eval 1.69x-1.90x; Goldilocks x86 store 1.68x-1.89x (old EPYC 1.31x-1.90x, line 381).

## C. Prose that quotes these cells, and the abstract

* main.tex:45-47 (abstract) `up to $4.6\times$ speedups for the prime-field evaluation kernel of Shamir secret sharing`: **derives from these rows** -- it is the EPYC degree-19 Mersenne cell (4.629x, paper 4.63x, rounded down to 4.6).  With the Xeon replacing the EPYC the largest Mersenne cell on x86 is 2.03x and the largest over both platforms is the ARM 2.49x (paper ARM row; the ARM re-measurement lane may change it), so the abstract should read `up to $2.5\times$` -- to be recomputed as the maximum over both Mersenne tables (ARM and x86) once the ARM rows are final, rounded to one decimal.
* experiments.tex:361-362 `On the EPYC, the speedups for degrees $15$--$21$ reach $4.5\times$--$4.6\times$, significantly exceeding the ARM results.` -> e.g. `On the Xeon the speedups are $1.77\times$ at degree $13$ and $2.00\times$--$2.03\times$ for degrees $15$--$21$, below the ARM results.` (Xeon d13 1.77x; Horner 146->235 ns, chain 82->116 ns over degrees 13->21).
* experiments.tex:343-344 (`Including the cost of writing shares to memory gives essentially the same speedups`): holds on the Xeon too (store 1.80x-2.05x vs eval 1.77x-2.03x); no x86 cell, nothing to change.
* experiments.tex:345-348 (`The x86 rows of the two tables below, and the x86 store-to-memory range for Goldilocks, are the run on an AMD EPYC 9R14 recorded in tools/bench/x86_output.txt, not the Xeon 8375C of the other x86 tables; the ARM rows are the Apple M2 Pro.`): delete, or replace by `The x86 rows of the two tables below are the Xeon 8375C (logs in tools/bench/results/rerun_2026-09-05/xeon/); the ARM rows are the Apple M2 Pro.`
* experiments.tex:27-31 (`One x86 result is from a different host: the prime-field kernels ... AMD EPYC 9R14 (Zen~4, Linux) recorded in tools/bench/x86_output.txt.`) and :84 (`8375C; AMD EPYC 9R14 for the prime-field kernels, as noted above`): delete the EPYC clauses (all x86 numbers are now the Xeon).
* experiments.tex:381-383 `on the EPYC, the range is $1.31\times$--$1.90\times$. The smaller x86 gains reflect that Goldilocks multiplication (64-bit) is relatively cheaper, reducing the benefit of fewer multiplications.` -> `on the Xeon, the range is $1.68\times$--$1.89\times$.`  The explanation sentence no longer matches the data on the Xeon: Goldilocks (1.69x-1.90x) is only slightly below Mersenne (1.77x-2.03x) there, and the gap is not the EPYC's 1.3x-vs-4.6x; suggested replacement: `The x86 gains are slightly smaller than for the Mersenne field, reflecting that Goldilocks multiplication (64-bit) is relatively cheaper.` or drop the sentence.
* experiments.tex:259, 282, 306 speedup sentences: see section A.  Line 259 `reflecting the larger benefit from reducing multiplications` still fits (x86 speedups exceed ARM).  Line 306 `On x86, our method is fastest for both` still holds (build: ours < R--W < Horner on the Xeon).
* Not derived from these rows (unchanged): introduction.tex:87 `$2.15\times$ on x86 (Intel Xeon) at $k=9$` (tab:kwise_both, Xeon run of 2026-09-02); injective.tex x86 numbers (Xeon runs of 2026-09-02).
* main.tex:45 `up to $2\times$ speedups for $k$-wise independent hashing`: not from these rows (tab:kwise_both).

## D. Files

* `/Users/ahle/repos/fast-polynomials/tools/bench/results/rerun_2026-09-05/xeon/`: set B logs `<binary>.<rep>.txt`, `top_procs.<rep>.txt`, `build.log`, `sources.md5`, `run_laneC.sh`, `run_laneC_setB.sh`, `README.md`; `setA_contaminated/` with the first set.
* scratch: `/private/tmp/claude-501/-Users-ahle-repos-notes-fast-polyhash/671fdc97-fe99-4719-bea0-4eedf88d5744/scratchpad/final/C/xeon/` (same files, `rows.md`, plus `parse_xeon.py`, `make_rows.py` which generated sections A-C of this file).
