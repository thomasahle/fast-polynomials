# Motzkin quartic over F_{2^61-1}: a 4-wise hash with two multiplications

Date: 2026-09-05.  Repo: /Users/ahle/repos/fast-polynomials (nothing under sections/ touched, no git operations).

## 1. Where the Section 5.7 numbers come from

- Table rows "This Paper (k=3 / Motzkin quartic / k=5 / k=7)" are the `Smart CL` lines of the
  k-wise harness `tools/bench/carryless_arm.cpp` (ARM) / `tools/bench/carryless.cpp` (x86), i.e.
  `smartcl_64<3>`, `smartcl_64<4>`, `smartcl_64<5>`, `smartcl_64<7>` from
  `framework/fast_hashing_arm.h` / `framework/fast_hashing.h`, timed with `test_speed_function64`:
  10^6 64-bit inputs from `poly_64<2>` (`rng(i)`), 2*100 repetitions each with a fresh `init()`,
  the fastest 100 kept, mean +/- std of those 100, in microseconds per 10^6 hashes.
  Tabulation is `tabulation_64` (8 x 256) in the same loop; `bench_nonpoly_arm.cpp` has an identical
  loop (`benchmark<T>`) for MurmurHash3/xxHash64/tabulation.
- The x86 column of that table matches `tools/bench/x86_output.txt` exactly (Smart CL degree 3 =
  2285 +/- 2.5, degree 4 = 3929.74, degree 5 = 4213.69, tabulation 6952) and the header of that
  file says `x86 (AMD EPYC 9R14)`, not the Xeon.  The ARM column (914/1036/1521/2346, tabulation
  1660) is reproduced by the runs below.
- The framework had no Mersenne-61 primitive (only 2^89-1 in `multiplication*.h`, and an ad-hoc
  `mers_mul` in `tools/bench/adversarial/hashes.h`), so `motzkin_61` carries its own
  one-product + fold multiplication.
- Discrepancy found: on x86, `smartcl_64<4>::mult4` (`fast_hashing.h` line 976) is NOT Motzkin's
  circuit.  It is `y=x*x; z=(x+a0)(y+a1); t=(z+a2)*x; P=t+a3` -- three carryless multiplications
  whose coefficient map (a0, a1, a0*a1+a2, a3) is a bijection, i.e. a 4-wise quartic.  Only the ARM
  `smartcl_64<4>` (`fast_hashing_arm.h` line 557) is the 2-multiplication Motzkin circuit (3-wise
  over F_{2^64}).  So the existing "This Paper (Motzkin quartic)" x86 cell (3930) is a
  3-multiplication 4-wise hash, mislabelled "3-wise"/"Motzkin".

## 2. Implementation

- `tools/bench/framework/fast_hashing_arm.h` lines 178-235 (class `motzkin_61` at 202-234).
- `tools/bench/framework/fast_hashing.h` lines 271-328 (class `motzkin_61` at 295-327; the file's
  CRLF line endings preserved -- git diff is +58 lines in each header, nothing else changed).
- Identical code in both headers (portable: `__uint128_t` product, no intrinsics):

```
x = fold(x);                                 // 64-bit input folded mod p:  x < 2^61 + 8
y = fold(mul(x, x + b0) + b1);               // y = x(x+b0)+b1            y < 2^61 + 4
t = y + x + b2;                              //                           t < 3*2^61 + 12
P = mul(y, t) + b3;                          // P = y(y+x+b2)+b3          P < 5*2^61 + 32
P = fold(P);  return P - (P61 & (0 - (P >= P61)));   // canonical value in [0, p), branch-free
```
  with `fold(v) = (v & p) + (v >> 61)` and `mul(a,b) = ((uint64)z & p) + (uint64)(z >> 61)`,
  `z = (uint128)a*b` (valid while a*b < 7*2^122; the bounds above are all well inside).  Keys
  b0..b3 uniform in [0, p) (rejection sampling from `getRandomUInt64() >> 3`).  Exactly two
  64x64->128 products per hash.  4-wise independence is on the universe [p] (61-bit; x and x+p
  collide), the output is in [0, p).
- Explicit decoder (documented in the class comment, checked by the selftest):
  a3 = 2b0+1, a2 = b0^2+b0+2b1+b2, a1 = b1(2b0+1)+b0 b2, a0 = b1^2+b1 b2+b3;
  b0 = (a3-1)/2, c = a2-b0^2-b0, b1 = a1-b0 c, b2 = c-2b1, b3 = a0-b1^2-b1 b2.
- Driver + selftest: `tools/bench/bench_tabrows.cpp` (new; selftest at lines 86-207, the table
  rows in `main` at 209-245).  Same `test_speed_function64` loop as the harnesses (sink is
  `volatile uint64_t` on ARM, `volatile __uint128_t` on x86, as in carryless_arm.cpp/carryless.cpp).
  Compile: ARM `clang++ -O3 -std=c++17 -march=armv8-a+crypto bench_tabrows.cpp -o bench_tabrows`;
  x86 `clang++ -O3 -std=c++17 -march=native bench_tabrows.cpp -o bench_tabrows`.
  Note: `.git/info/exclude` excludes `/tools/` in this checkout, so the new .cpp does not show in
  `git status` (needs `git add -f` if it is to be tracked).
- Schedule choice (scratchpad `variants.cpp`, cross-checked on 8x10^6 inputs): the naive
  "3-part fold + second fold after each product" version cost 2662 us ARM / 4439 us x86; the lazy
  2-fold schedule above costs 1911-1950 us ARM / 3236 us x86; fully cmov-reduced intermediates
  were slowest (2833 / 5071).  Dropping the final canonical reduction would give 1918 / 2997 but
  the output would then not be a function of the field element, so it is kept.

## 3. Selftest output (identical on M2 Pro/clang and Xeon/clang 21.1.8 and g++ 11.5)

```
$ ./bench_tabrows selftest
Reading random bytes from seed
motzkin_61 selftest: 14755200 evaluations checked against Horner, 64 random + 1296 extreme key sets,
64 decoder round-trips (b0 = (a3-1)/2, ...): PASS
```
Checks: (1) 64 random key sets x (20 extreme inputs incl. 0, p-1, p, p+1, 2^64-1, 2^64-1-p, 7p+6 ...
+ 2x10^5 random 64-bit inputs) against Horner evaluation of the expanded quartic in exact mod-p
arithmetic, also asserting output < p; (2) all 6^4 = 1296 combinations of extreme keys
{0, 1, p-1, p-2, 2^60, 2^60-1} x (extremes + 500 random inputs); (3) 64 random monic quartics
decoded with the closed form, re-encoded (must round-trip) and the circuit with the decoded keys
compared with Horner on the target quartic at 20000 random points; (4) 1000 `init()` calls give
keys in [0, p).

## 4. Timings (paper protocol: 1e6 inputs, best 100 of 200 reps, us per 1e6 hashes, mean +/- std)

### ARM, Apple M2 Pro, Apple clang, `-O3 -march=armv8-a+crypto`, `./bench_tabrows 1e6 100`
1-min load at run time: 8.7 / 8.6 / 8.6 / 9.9 (lean + browser from other work; it never fell below
5.4 during the ~10 min I polled, so the "< 2.5" condition could not be met within the 5-minute
budget).  Four runs:

| row | run 1 | run 2 | run 3 | run 4 | paper |
|---|---|---|---|---|---|
| Tabulation 8x2^8 | 1675+/-14 | 1665+/-22 | 1646+/-26 | 1609+/-13 | 1660+/-12 |
| This Paper (k=3) smartcl_64<3> | 929+/-14 | 908+/-6 | 905+/-8 | 884+/-9 | 914+/-4 |
| Motzkin quartic F_{2^64} smartcl_64<4> | 1028+/-8 | 1048+/-24 | 1027+/-9 | 987+/-9 | 1036+/-13 |
| **Motzkin quartic F_{2^61-1} motzkin_61** | **2042+/-26** | 2049+/-28 | 2041+/-21 | 1984+/-18 | new |
| This Paper (k=5) | 1522+/-27 | 1500+/-20 | 1539+/-37 | 1468+/-17 | 1521+/-8 |
| This Paper (k=7) | 2347+/-12 | 2335+/-23 | 2630+/-203 | 2331+/-36 | 2346+/-9 |

Quoted: motzkin_61 2042 +/- 26 us (spread 1984-2049 over the four runs); k=3 905 +/- 8 (884-929);
F_{2^64} quartic 1027 +/- 9 (987-1048).  The existing ARM column reproduces within this spread.

### x86, Intel Xeon Platinum 8375C (hardware.normalcomputing.net, ~/fastpoly-bench/bench),
clang 21.1.8, `-O3 -march=native`, `taskset -c 80-87 ./bench_tabrows_clang 1e6 100`, load ~8.5 on 96 CPUs.
(clang is what the Sep-2 `x86_rerun2.txt` used: its Smart CL degree-3 = 175 us per 1e5 matches
the clang build, not g++.)  Three runs:

| row | run 1 | run 2 | run 3 | g++ 11.5 | paper (EPYC 9R14!) |
|---|---|---|---|---|---|
| Tabulation 8x2^8 | 2240+/-4 | 2233+/-3 | 2238+/-2 | 2230+/-33 | 6952+/-5 |
| This Paper (k=3) | 1782+/-5 | 1779+/-5 | 1779+/-5 | 2170+/-5 | 2285+/-3 |
| "Motzkin quartic" F_{2^64} smartcl_64<4> (3 mults on x86, 4-wise) | 2913+/-5 | 2904+/-6 | 2910+/-5 | 3670+/-7 | 3930+/-4 |
| **Motzkin quartic F_{2^61-1} motzkin_61** | 3230+/-6 | 3224+/-4 | **3227+/-4** | 3725+/-5 | new |
| This Paper (k=5) | 3144+/-7 | 3131+/-3 | 3140+/-4 | 3920+/-4 | 4214+/-3 |
| This Paper (k=7) | 4957+/-4 | 4955+/-4 | 4970+/-6 | 5914+/-5 | 6074+/-4 |

Quoted: motzkin_61 3227 +/- 4 us; k=3 1779 +/- 5; F_{2^64} quartic 2910 +/- 5 (same run).
Caveat: the table's x86 column is from the AMD EPYC (x86_output.txt); on the Xeon the polynomial
rows are ~20-25% faster and tabulation is 3x faster, so a Xeon number cannot be dropped into the
EPYC column as-is.  Either re-time the whole x86 column on the Xeon (this run already gives the
tabulation and the four polynomial rows; Murmur/xxHash/Dietzfelbinger need bench_nonpoly and
carryless.cpp runs there), or use the same-run ratio: motzkin_61 / k=3 = 3227/1779 = 1.81x, i.e.
about 4140 us on the EPYC scale (estimate, not a measurement).

## 5. Proposed table row and prose (Section 5.7)

Row (ARM = M2 Pro measurement; x86 = Xeon measurement, see caveat above):

```
This Paper (Motzkin quartic, $\F_{2^{61}-1}$) & 2042$\pm$26 & 4-wise & 3227$\pm$4 & 4-wise \\
```

Prose, to follow the sentence "Our Motzkin-quartic hash ($3$-wise over $\F_{2^{64}}$, see the
footnote above) is still faster than 3-wise tabulation on both platforms." (existing footnote kept):

The row over $\F_{2^{61}-1}$ evaluates the same two-multiplication Motzkin circuit
$y = x(x+b_0)+b_1$, $P = y(y+x+b_2)+b_3$ in the Mersenne prime field, where the characteristic is
odd and the key map is a bijection onto the monic quartics ($b_0 = (a_3-1)/2$, then $b_1, b_2, b_3$
by back-substitution), so with uniform keys the hash is exactly $4$-wise independent on the 61-bit
universe (64-bit inputs are folded modulo $p$).
Over $\F_{2^{64}}$ the identical circuit is only $3$-wise (footnote above); the price of the odd
characteristic is that each multiplication is a $64\times64\to128$-bit integer product followed by
a fold rather than a single carryless multiply, which is why the $4$-wise Mersenne row is slower
than the $3$-wise carryless quartic on both platforms while still using only two multiplications.

## 6. Files changed under tools/bench/

- `tools/bench/framework/fast_hashing_arm.h`  (+58 lines, class `motzkin_61`, lines 178-235)
- `tools/bench/framework/fast_hashing.h`      (+58 lines, class `motzkin_61`, lines 271-328, CRLF kept)
- `tools/bench/bench_tabrows.cpp`             (new: table-row driver + `selftest`)
- `tools/bench/bench_tabrows`                 (built ARM binary; excluded from git like the other binaries)
- Xeon copy: `~/fastpoly-bench/bench/{bench_tabrows.cpp, bench_tabrows, bench_tabrows_clang,
  framework/fast_hashing.h, framework/fast_hashing_arm.h}`.
