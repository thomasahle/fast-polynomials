# Section 5.7 tabulation-comparison table: consistent circuits, one machine per column

Date: 2026-09-05.  Repo: /Users/ahle/repos/fast-polynomials (nothing under sections/ touched; no git
operations).  Driver: `tools/bench/bench_tabrows.cpp` (all rows, one wrapper, one protocol per column).

## 1. Protocol

Same wrapper as `carryless.cpp` / `carryless_arm.cpp` (`test_speed_function64`): 10^6 64-bit inputs from
`poly_64<2>`, 2 x 100 repetitions each with a fresh `init()`, fastest 100 kept, mean +/- std of those 100,
in microseconds per 10^6 hashes.  Sink: `volatile uint64_t` (ARM) / `volatile __uint128_t` (x86), as in
the two harnesses.  Three complete runs per machine; the quoted cell is the run with the median mean for
that row (its mean +/- its within-run std, the paper's format); the run-to-run range of the three means is
given next to it.

Implementations (the ones the original harnesses used, found by grepping the bench sources):
- MurmurHash3, xxHash64: `murmur3_64` (64-bit finalizer) and `xxhash64` (8-byte input path) copied
  verbatim from `tools/bench/bench_nonpoly_arm.cpp` (the file has its own `main`, so it cannot be included).
- Tabulation: `tabulation_64` (8 x 2^8, `getRandomUInt64()` tables) from the framework headers, the class
  the k-wise harnesses time (the paper's ARM 1660 came from that loop; `bench_nonpoly_arm.cpp`'s
  `Tabulation_64` is the same computation with `rand()` tables).
- Dietzfelbinger k=3/5/7: `dietz_192<k>` (`framework/dietzfelbinger_hash.h`, W=192 as the paper's text
  states; `carryless_arm.cpp` times `dietz_192<n>`).  NB: the old x86 cells 3498/8219/13633 have no
  recorded provenance in the repo or on the Xeon (`x86_output.txt` has no Dietz/Murmur/xxHash lines at
  all; `carryless.cpp` only times `dietz_128_opt`/`dietz_256`), so they cannot be attributed to a W.
- This Paper k=3/5/7: `smartcl_64<3/5/7>` (2 / 3 / 4 carryless multiplications on ARM).
- Quartics: `quartic2_64` (Motzkin, 2 carryless mults, 3-wise over F_{2^64}), `quartic3_64`
  (x Q_3(x)+c_0, 3 carryless mults, 4-wise), `motzkin_61` (Motzkin over 2^61-1, 2 integer 64x64->128
  products + folds, 4-wise on [p]).  The platform's own `smartcl_64<4>` is timed as a cross-check row
  (it equals `quartic2_64` on ARM and `quartic3_64` on x86; the cross-check agrees on both machines).

Machines / compilers:
- ARM: Apple M2 Pro, Apple clang, `-O3 -std=c++17 -march=armv8-a+crypto`, `./bench_tabrows 1e6 100`.
  1-min load during the runs: 5.15 -> 4.73 (it never fell below 3; minimum seen during the 5-minute wait
  was 4.73, lean/browser from other work).
- x86: Intel Xeon Platinum 8375C (hardware.normalcomputing.net, `~/fastpoly-bench/bench/`), clang 21.1.8,
  `-O3 -std=c++17 -march=native`, `taskset -c 80-87 ./bench_tabrows_clang 1e6 100`.  1-min load
  8.26 -> 8.85 on 96 CPUs (other users' jobs; the pinned cores were otherwise idle).  g++ 11.5 also builds
  and passes the selftest (not used for the numbers).

## 2. Measurements

### ARM, Apple M2 Pro (three runs, us per 1e6 hashes)

| row | run 1 | run 2 | run 3 | quoted | range | paper (ARM) |
|---|---|---|---|---|---|---|
| MurmurHash3 | 589+/-13 | 601+/-15 | 583+/-14 | **589+/-13** | 583-601 | 593+/-8 |
| xxHash64 | 1124+/-5 | 1181+/-14 | 1160+/-14 | **1160+/-14** | 1124-1181 | 1174+/-5 |
| Tabulation 8x2^8 | 1623+/-21 | 1668+/-11 | 1686+/-33 | **1668+/-11** | 1623-1686 | 1660+/-12 |
| Dietzfelbinger k=3 (dietz_192) | 1534+/-20 | 1568+/-24 | 1563+/-29 | **1563+/-29** | 1534-1568 | 1569+/-36 |
| Dietzfelbinger k=5 | 3117+/-29 | 3085+/-24 | 3069+/-21 | **3085+/-24** | 3069-3117 | 3205+/-39 |
| Dietzfelbinger k=7 | 4893+/-44 | 4836+/-38 | 4893+/-69 | **4893+/-44** | 4836-4893 | 4993+/-58 |
| This Paper k=3 (smartcl_64<3>) | 886+/-13 | 911+/-18 | 880+/-7 | **886+/-13** | 880-911 | 914+/-4 |
| quartic2_64 (Motzkin, F_{2^64}, 2 mults, 3-wise) | 990+/-11 | 1030+/-15 | 992+/-10 | **992+/-10** | 990-1030 | 1036+/-13 (= ARM smartcl_64<4>) |
| quartic3_64 (x Q3(x)+c0, F_{2^64}, 3 mults, 4-wise) | 1434+/-13 | 1428+/-17 | 1426+/-13 | **1428+/-17** | 1426-1434 | new |
| motzkin_61 (Motzkin, F_{2^61-1}, 2 mults, 4-wise) | 2013+/-24 | 2008+/-22 | 1978+/-21 | **2008+/-22** | 1978-2013 | new |
| This Paper k=5 | 1482+/-19 | 1460+/-15 | 1470+/-17 | **1470+/-17** | 1460-1482 | 1521+/-8 |
| This Paper k=7 | 2332+/-28 | 2289+/-22 | 2299+/-20 | **2299+/-20** | 2289-2332 | 2346+/-9 |
| cross-check smartcl_64<4> (= quartic2_64) | 1012+/-14 | 994+/-12 | 1002+/-11 | 1002+/-11 | 994-1012 | 1036+/-13 |

Reproduction of the paper's ARM column: MurmurHash3, xxHash64, Tabulation, Dietzfelbinger k=3, k=3 and
the F_{2^64} Motzkin quartic reproduce within the run-to-run range (the paper's k=3 914 and quartic 1036
sit at the top of today's ranges 880-911 / 990-1030).  Four rows came out 2-4 % faster than the paper in
all three of today's runs, i.e. just outside today's tight range: Dietzfelbinger k=5 (3069-3117 vs 3205),
Dietzfelbinger k=7 (4836-4893 vs 4993), This Paper k=5 (1460-1482 vs 1521) and k=7 (2289-2332 vs 2346).
The previous agent's four runs of the same binary spanned 1468-1539 (k=5) and 2331-2630 (k=7), so the
paper's values are inside the day-to-day spread on this loaded machine; the differences are load/thermal
noise, not implementation changes (the classes are untouched).

### x86, Intel Xeon Platinum 8375C, clang 21.1.8 (three runs, us per 1e6 hashes)

| row | run 1 | run 2 | run 3 | quoted | range | paper (x86 = AMD EPYC 9R14!) |
|---|---|---|---|---|---|---|
| MurmurHash3 | 854+/-6 | 854+/-5 | 857+/-5 | **854+/-5** | 854-857 | 1042+/-2 |
| xxHash64 | 1888+/-8 | 1888+/-9 | 1920+/-19 | **1888+/-8** | 1888-1920 | 1862+/-4 |
| Tabulation 8x2^8 | 2243+/-3 | 2244+/-4 | 2255+/-8 | **2244+/-4** | 2243-2255 | 6952+/-5 |
| Dietzfelbinger k=3 (dietz_192) | 2276+/-3 | 2280+/-5 | 2283+/-5 | **2280+/-5** | 2276-2283 | 3498+/-2 (W unknown) |
| Dietzfelbinger k=5 | 4977+/-17 | 4994+/-13 | 4986+/-19 | **4986+/-19** | 4977-4994 | 8219+/-4 |
| Dietzfelbinger k=7 | 7901+/-5 | 7905+/-5 | 7916+/-5 | **7905+/-5** | 7901-7916 | 13633+/-9 |
| This Paper k=3 (smartcl_64<3>) | 1779+/-5 | 1780+/-5 | 1779+/-5 | **1779+/-5** | 1779-1780 | 2285+/-3 |
| quartic2_64 (Motzkin, F_{2^64}, 2 mults, 3-wise) | 1903+/-5 | 1905+/-5 | 1900+/-4 | **1903+/-5** | 1900-1905 | new on x86 |
| quartic3_64 (x Q3(x)+c0, F_{2^64}, 3 mults, 4-wise) | 2909+/-4 | 2911+/-5 | 2908+/-5 | **2909+/-4** | 2908-2911 | 3930+/-4 (= x86 smartcl_64<4>, mislabelled 3-wise) |
| motzkin_61 (Motzkin, F_{2^61-1}, 2 mults, 4-wise) | 3199+/-8 | 3198+/-7 | 3207+/-7 | **3199+/-8** | 3198-3207 | new |
| This Paper k=5 | 3146+/-11 | 3138+/-5 | 3141+/-6 | **3141+/-6** | 3138-3146 | 4214+/-3 |
| This Paper k=7 | 4955+/-4 | 4968+/-6 | 4971+/-9 | **4968+/-6** | 4955-4971 | 6074+/-4 |
| cross-check smartcl_64<4> (= quartic3_64) | 2910+/-4 | 2915+/-6 | 2903+/-4 | 2910+/-4 | 2903-2915 | 3930+/-4 |

Run-to-run range on the Xeon is <= 0.5 % for every row except xxHash64 (1.7 %) and Tabulation (0.5 %).
The previous agent's Xeon numbers (k=3 1779, smartcl_64<4> 2910, k=5 3140, k=7 4957-4970, tabulation
2238, motzkin_61 3224-3230) are reproduced; motzkin_61 is ~1 % faster today (3199).

## 3. Proposed LaTeX rows (complete table body)

```latex
\begin{center}
\begin{tabular}{l|rr|rr}
    & \multicolumn{2}{c|}{ARM (Apple M2 Pro)} & \multicolumn{2}{c}{x86 (Intel Xeon 8375C)} \\
    Method & Time (\textmu s) & Indep. & Time (\textmu s) & Indep. \\
    \hline
    MurmurHash3 & 589$\pm$13 & none & 854$\pm$5 & none \\
    xxHash64 & 1160$\pm$14 & none & 1888$\pm$8 & none \\
    Tabulation & 1668$\pm$11 & 3-wise & 2244$\pm$4 & 3-wise \\
    Dietzfelbinger ($k=3$) & 1563$\pm$29 & 3-wise & 2280$\pm$5 & 3-wise \\
    Dietzfelbinger ($k=5$) & 3085$\pm$24 & 5-wise & 4986$\pm$19 & 5-wise \\
    Dietzfelbinger ($k=7$) & 4893$\pm$44 & 7-wise & 7905$\pm$5 & 7-wise \\
    This Paper ($k=3$) & 886$\pm$13 & 3-wise & 1779$\pm$5 & 3-wise \\
    This Paper (Motzkin quartic, $\F_{2^{64}}$) & 992$\pm$10 & 3-wise & 1903$\pm$5 & 3-wise \\
    This Paper (quartic $x\,Q_3(x)+c_0$, $\F_{2^{64}}$) & 1428$\pm$17 & 4-wise & 2909$\pm$4 & 4-wise \\
    This Paper (Motzkin quartic, $\F_{2^{61}-1}$) & 2008$\pm$22 & 4-wise & 3199$\pm$8 & 4-wise \\
    This Paper ($k=5$) & 1470$\pm$17 & 5-wise & 3141$\pm$6 & 5-wise \\
    This Paper ($k=7$) & 2299$\pm$20 & 7-wise & 4968$\pm$6 & 7-wise \\
\end{tabular}
\end{center}
```

Independence labels: `quartic2_64` 3-wise, `quartic3_64` 4-wise, `motzkin_61` 4-wise (on the 61-bit
universe [p]; 64-bit inputs are folded mod p, so x and x+p collide).  Multiplication counts for the prose:
Motzkin quartic over F_{2^64}: 2 carryless; x Q_3(x)+c_0: 3 carryless; Motzkin over F_{2^61-1}: 2 integer
64x64->128 products (each followed by a fold); for reference k=3: 2 carryless, k=5: 3, k=7: 4 (ARM
`smartcl_64` code).

## 4. Proposed replacement for the Section 5.7 sentences (machine + quartic rows)

Replace the paragraph from "On ARM, simple tabulation ..." through "... should not be compared with each
other." and the "Notably, ..." paragraph (sections/experiments.tex lines 369-386) by:

```latex
On ARM, simple tabulation (8 tables of 256 entries) achieves
1668$\pm$11\,\textmu s per $10^6$ hashes; on x86, it achieves 2244$\pm$4\,\textmu s.
Every row of the table below is timed by one driver,
\texttt{tools/bench/bench\_tabrows.cpp}, under the wrapper and batching of the
$k$-wise comparison ($10^6$ inputs, fastest $100$ of $200$ repetitions with
fresh keys, mean $\pm$ standard deviation in \textmu s per $10^6$ hashes), on the
same two machines as the other tables: the Apple M2 Pro (Apple clang~17,
\texttt{-O3 -march=armv8-a+crypto}) and the Intel Xeon Platinum 8375C
(clang~21.1.8, \texttt{-O3 -march=native}, pinned to eight cores).
MurmurHash3 and xxHash64 are the single-word variants (the 64-bit finalizer and
the 8-byte xxHash64 path), Dietzfelbinger is the $W=192$ Horner evaluation
described below, and the polynomial rows are the implementations of
Table~\ref{tab:kwise_both}; because the wrapper differs, they remain separate
runs from that table (x86, $k=3$: $1750$ there against $1779$\,\textmu s here).

Notably, our 3-wise independent hash function runs in 886$\pm$13\,\textmu s on
ARM---nearly $2\times$ faster than tabulation with the same independence
guarantee; on x86 (1779\,\textmu s) it is $1.26\times$ faster than tabulation.
The table lists three quartics.  Motzkin's two-multiplication quartic
$y = x(x+a)$, $P=(y+b)(y+x+c)+d$ over $\F_{2^{64}}$ is only $3$-wise (see the
footnote above) and costs 992 / 1903\,\textmu s, still below tabulation on both
platforms.  A $4$-wise quartic over $\F_{2^{64}}$ needs a third multiplication:
the lift $x\,Q_3(x)+c_0$ (\Cref{tab:families}) uses three carryless
multiplications and runs in 1428 / 2909\,\textmu s, between our $k=3$ and $k=5$
rows on both platforms.  Alternatively, the same two-multiplication Motzkin
circuit can be evaluated over the Mersenne prime $p=2^{61}-1$, where the odd
characteristic makes the key map a bijection onto the monic quartics
($b_0=(a_3-1)/2$, then $b_1,b_2,b_3$ by back-substitution), so with uniform keys
the hash is exactly $4$-wise independent on the $61$-bit universe ($64$-bit
inputs are folded modulo $p$).  Its cost, 2008 / 3199\,\textmu s, exceeds even
our $5$-wise carryless quintic ($1470$ / $3141$\,\textmu s): each of its two
multiplications is a $64\times 64\to 128$-bit integer product followed by a
fold rather than a single carryless multiply, so in the presence of
\texttt{PMULL}/\texttt{PCLMULQDQ} the third carryless multiplication is cheaper
than the odd characteristic.
```

Also replace the sentence in the Reproducibility paragraph (line 84-87 region) only if desired: it
already names clang 21.1.8 / Apple clang 17 and the Xeon, so it stays; the sentence about
`x86_output.txt` / AMD EPYC in Section 5.7 is deleted by the replacement above.  The Table~tab:kwise_both
caption note "ARM: mult4 Motzkin; x86: mult4 is the three-multiplication lift" (line 127) stays true:
`smartcl_64<4>` was not changed; only the new named classes exist on both platforms.

Consistency checks against the new numbers, for the surrounding text: k=3 vs tabulation ARM 1668/886 =
1.88x ("nearly 2x" ok); x86 2244/1779 = 1.26x (the old "3x faster than tabulation" was an EPYC artefact and
must go); Dietzfelbinger vs ours k=3: 1563/886 = 1.8x, 2280/1779 = 1.3x; k=5: 3085/1470 = 2.1x,
4986/3141 = 1.6x; k=7: 4893/2299 = 2.1x, 7905/4968 = 1.6x.

## 5. Ports and selftests

- x86 `tools/bench/framework/fast_hashing.h` (CRLF preserved, +69 lines, pure addition):
  `quartic2_64` lines 1123-1141 (Motzkin, `lemul` = PCLMULQDQ + Lemire reduction, same multiply as
  `smartcl_64`), `quartic3_64` lines 1143-1163 (byte-identical arithmetic to `smartcl_64<4>::mult4`).
  Header comment at 1096-1121.  `motzkin_61` (previous agent) at 295-327.
- ARM `tools/bench/framework/fast_hashing_arm.h` (+62 lines, pure addition):
  `quartic2_64` lines 629-644 (identical to `smartcl_64<4>::mult4`), `quartic3_64` lines 646-662
  (`slemul` = PMULL + 3-PMULL reduction, the multiply `smartcl_64` uses).  Comment at 602-627.
  `motzkin_61` at 202-234.
- Both classes expose `set_keys(a0,a1,a2,a3)` for the selftest; `init()` draws keys with
  `getRandomUInt64()` like `smartcl_64`.
- `./bench_tabrows selftest` (identical output on M2 Pro/clang, Xeon/clang 21.1.8, Xeon/g++ 11.5):
  ```
  quartic2_64 / quartic3_64 selftest: 15408640 evaluations checked against Horner over GF(2^64),
    64 random + 1296 extreme key sets each, 64 quartic3_64 decoder round-trips
    (a0 = c3, a1 = c2, a2 = c1 + c3 c2, a3 = c0): PASS
  motzkin_61 selftest: 14755200 evaluations checked against Horner, 64 random + 1296 extreme key sets,
    64 decoder round-trips (b0 = (a3-1)/2, ...): PASS
  ```
  What is checked: a shift-and-add reference multiply in GF(2)[x]/(x^64+x^4+x^3+x+1) (the field of both
  `lemul` and `slemul`; sanity x * x^63 = 27) drives Horner on the expanded polynomials
  quartic2: x^4 + 1*x^3 + (a0^2+a0+a2) x^2 + (a0 a2 + a1) x + (a1^2 + a1 a2 + a3)  (x^3 coefficient 1
  for every key -> 3-wise), quartic3: x^4 + a0 x^3 + a1 x^2 + (a0 a1 + a2) x + a3.  Each circuit is
  compared with Horner for 64 random key sets x (12 extreme + 10^5 random inputs) and all 6^4 extreme key
  combinations x (12 + 500 inputs).  Bijectivity of quartic3's coefficient map: 64 random monic quartics
  c are decoded to keys (a0=c3, a1=c2, a2=c1+c3 c2, a3=c0), re-encoded (must equal c, and a0 = c3 shows
  the x^3 coefficient ranges over all of F_{2^64}) and the circuit with those keys is compared with Horner
  on c at 20000 points.  motzkin_61: unchanged from the previous report.

## 6. Files changed under tools/bench/ (all need `git add -f`; `/tools/` is in .git/info/exclude)

- `tools/bench/framework/fast_hashing.h`      (+69 lines: quartic2_64/quartic3_64 at 1096-1163; plus the
                                                previous +58 for motzkin_61 at 271-328)
- `tools/bench/framework/fast_hashing_arm.h`  (+62 lines: quartic2_64/quartic3_64 at 602-662; plus the
                                                previous +58 for motzkin_61 at 178-235)
- `tools/bench/bench_tabrows.cpp`             (rewritten: all 12 table rows + cross-check row, GF(2^64)
                                                and 2^61-1 selftests, Murmur/xxHash copied from
                                                bench_nonpoly_arm.cpp, includes dietzfelbinger_hash.h)
- `tools/bench/bench_tabrows`                 (rebuilt ARM binary; binaries are excluded like the others)
- Xeon: `~/fastpoly-bench/bench/{bench_tabrows.cpp, bench_tabrows (g++), bench_tabrows_clang,
  framework/{fast_hashing.h, fast_hashing_arm.h, dietzfelbinger_hash.h, multiplication.h, randomgen.h},
  staging/, tabrows_run{1,2,3}.{txt,load}, tabrows_done}`
- Raw outputs and aggregator in this scratchpad: `xeon/tabrows_run{1,2,3}.{txt,load}`,
  `m2/tabrows_run{1,2,3}.{txt,load}`, `aggregate.py`; header backups `*.bak`.
