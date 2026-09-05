# ChainHash with the strided word pairing -- lane E step 2 (2026-09-05, measurement run "final5")

Definition under test: `tools/bench/chainhash/chainhash.h` as shipped by lane E step 1 (PH level pairs the
words of every 32-byte group first-with-third and second-with-fourth, last block at 32-byte group
granularity, pair count 2*ceil(r/32); recurrence, twist, degree-5 finalizer, key W+9 words unchanged),
SMHasher3 port `~/repos/smhasher3/hashes/chainhash.cpp` (verification codes chainhash-256 LE 0xBFC38A57 /
BE 0xC84FA5C3, chainhash-1k LE 0x710CF02B / BE 0x1AB98587, identical on hwpmull / hwclmul / portable).

## RESULT: chainhash-256 FAILS one SMHasher3 test (199/200) on both machines; chainhash-1k passes 200/200

`m2/final5_m2_256.txt`, `xeon/final5_x86_256.txt`: Keyset 'Zeroes', "Analyzing differential distribution",
`Testing distribution (any 8..15 bits) - Worst bias is 8 bits at bit 20: 2.199x (^51) !!!!!` -- identical on
the M2 Pro (hwpmull) and the Xeon (hwclmul); the suite is deterministic (seed 0).  Every other test passes.
`m2/final5_m2_1k.txt`, `xeon/final5_x86_1k.txt`: 200/200 (Zeroes differential bias 0.63x / 0.67x).
The previous (adjacent-pairing) design had 0.53x here (`../../smhasher3_chainhash/final4_*`).

### Diagnosis (`zeroes_diagnosis/`)
The Zeroes test hashes the all-zero messages of length 0..204799 and tests the XOR of consecutive hashes
h(l) ^ h(l+1).  For zero data the PH sum of the last block depends only on the group count G = ceil(r/32),
so the level-2 value is V(l) = l XOR C(n, G): within a run of 32 consecutive lengths V differs only in its
low five bits, the twist's carry chain then acts almost affinely, and the degree-5 finalizer (GF(2)-quadratic)
has affine discrete derivatives, so the deltas of a run cluster on few values per 8-bit window.  The adjacent
pairing had the same structure with runs of 16 (pair count ceil(r/16)); halving the number of runs while
doubling their length multiplies the excess same-bin pair count by about 2.5, which is what pushes the
statistic over the threshold.  `zeroes5.cpp` (uses `chainhash_ref.h`, O(1) per zero message through
prefix tables, checked against the bit-serial reference on 20 lengths) reproduces SMHasher3's statistic
exactly (seed 0: 2.20x at width 8, bit 20) and evaluates design variants over 32 seeds
(`zeroes5_32seeds_xeon.out`; SMHasher3 uses seed 0; ">1.5x" = would fail):

| variant (both configurations) | 256 B, S=1: max / mean / seeds >1.5x | 1 KB, S=2: max / mean / seeds >1.5x |
|---|---|---|
| strided 32 B, length XORed into a (shipped by step 1) | 2.67x / 1.26x / 9 of 32 | 9.38x / 1.49x / 11 of 32 |
| adjacent 16 B, length into a (previous design, 200/200 at seed 0) | 1.76x / 0.86x / 2 of 32 | 7.62x / 1.12x / 4 of 32 |
| strided 32 B, length XORed into a AND b of the last pair | 0.82x / 0.62x / 0 | 0.78x / 0.60x / 0 |
| strided 32 B, length encoded as len*0x9E3779B97F4A7C15 mod 2^64 into a | 0.88x / 0.65x / 0 | 0.92x / 0.65x / 0 |
| adjacent 16 B, length into a and b | 0.81x / 0.61x / 0 | 0.90x / 0.64x / 0 |

So the weakness is in the design family (the length enters the recurrence value linearly and only in its
low bits); the strided pairing amplified it from "passes at seed 0" to "fails at seed 0".  Both candidate
fixes are provable at zero cost to the proof: with the length also XORed into b_p the stream lemma's
constant becomes C = (l + l')(1 + X^64), still nonzero for l != l'; with an injective encoding e(l) it becomes
e(l) + e(l').  Cost: "into a and b" is free in the multi-block loop and in the S=1 small path (one extra
length-times-key product at entry, off the data path), but the fused S=2 small path needs two
length-times-key products; "len * odd constant" is one scalar multiply.
`chainhash_lenexp.cpp` is the SMHasher3 port with the second variant (names chainhash-256-lenexp /
chainhash-1k-lenexp, LE codes 0x32A28E9F / 0x2827EEDB, hwclmul; BE codes not computed); its full-suite runs
`xeon/lenexp_x86_256.txt` and `xeon/lenexp_x86_1k.txt` (Xeon, taskset 80-87 / 88-95, `--ncpu=8`, load ~6) both pass
**200/200**, Zeroes differential bias 0.768x (^2) and 0.636x (^0), as the simulator predicted for seed 0 (0.77x / 0.66x);
no other test changed.  The "length into a and b" variant was only simulated, not run in SMHasher3.

## Timing (this definition)

M2 Pro harness (`tools/bench/adversarial`, `./speed 5 0.5 run ChainHash`, 1-min load 2.99 at start,
`m2/harness_speed_5_0.5_ChainHash.run1.txt`; median of 5, GB/s):

| row | 16 KB | 512 B | table (adjacent) |
|---|---|---|---|
| ChainHash, 1 KB blocks | 70.42 (69.99-70.99) | 44.17 (43.80-44.28) | 61.7 / 40.5 |
| ChainHash, 256 B blocks | 67.05 (66.79-67.27) | 38.84 (22.34-39.95) | 57.7 / 36.8 |
| ChainHash, 64 B blocks | 25.78 (25.12-27.08) | 29.57 (24.60-29.69) | 26.6 / 27.4 |

Run 2 (`m2/harness_speed_5_0.5_ChainHash.run2.txt`, load 2.80 at start, 22:39): 1 KB 71.33 / 43.22; 256 B 67.49 / 39.82;
64 B 26.95 / 29.70 GB/s.  Suggested table values (mean of the two runs): 70.9 / 43.7, 67.3 / 39.3, 26.4 / 29.6.

SMHasher3 Sanity+Speed:
* Xeon 8375C (`xeon/final5_x86_speed_*.txt`, taskset 80-95, clang 21.1.8, load 2.22 / 3.21 at start):
  chainhash-256 107.14 cycles/hash (1-31 B), 15.35 bytes/cycle bulk; chainhash-1k 107.69 cycles, 12.10 bytes/cycle
  (previous design: 112.02 / 15.35 and 111.18 / 12.58: neutral on x86, as expected).
* M2 Pro, Speed section of the full-suite logs: chainhash-256 71.53 cycles, 22.53 bytes/cycle (load 2.99 at start);
  chainhash-1k 53.99 cycles, 25.16 bytes/cycle -- taken at 1-min load 11.7 (unrelated jobs; the driver's 20-minute
  load gate timed out), indicative only (previous design, quiet machine: 65.95 / 20.68 and 71.90 / 17.50).

## Files
* `m2/`: full suite logs (`final5_m2_256.txt` FAIL 199/200, `final5_m2_1k.txt`), harness output, driver script and load log.
* `xeon/`: full suite logs (`final5_x86_256.txt` FAIL 199/200, `final5_x86_1k.txt` 200/200), Sanity+Speed logs, driver, load log, build log;
  `lenexp_x86_*.txt`: the length-encoding experiment.
* `step1_logs/`: lane E step 1 build/test logs (`build_sh.log`: ALL TESTS PASSED x3, 318,970 checks; SMHasher3 Sanity+Speed
  under load 2.5-7; portable-backend Sanity; the vcode recomputation).
* `zeroes_diagnosis/`: simulator, its outputs, the experimental port.

Not done because of the failure: paper edits (sections/injective.tex, appendix_chainhash.tex; plan in
`paper_edit_plan.md` here), SMHasher3 MR commit/push, MR draft update.
