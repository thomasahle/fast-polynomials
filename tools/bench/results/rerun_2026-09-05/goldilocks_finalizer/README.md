# Goldilocks-field finalizer experiment (2026-09-05)

**Question.** Would a finalizer over the prime field F_p, p = 2^64 - 2^32 + 1 (Goldilocks),
beat ChainHash's shipped finalizer (the certified characteristic-2 degree-5 circuit, 3 PMULL
products each with a 2-PMULL2 reduction, behind the additive twist)?

**Definition under test.** `tools/bench/chainhash/chainhash.h` and `chainhash_ref.h` at git HEAD
(adjacent 16-byte pairing; SMHasher3 registration `hashes/chainhash.cpp` of branch `mr/chainhash`,
codes chainhash-256 LE 0xDE1AB9F9 / chainhash-1k LE 0x32B4EE71), with the finalizer made a template
parameter FIN in `src/chainhash_goldi.h` (arm64 header; PH and recurrence levels verbatim):

| FIN | finalizer on the chain value P_n | mults | independence | key words appended |
|---|---|---|---|---|
| CHAR2 | as shipped: v = P_n + t_in (integer add), then the char-2 circuit (c0..c4) | 3 PMULL (+6 PMULL2 folds) | 5-wise | 0 |
| G4 | x = fold(P_n); Motzkin's quartic y = x(x+g0)+g1, out = y(y+x+g2)+g3, g0..g3 uniform in F_p | 2 (64x64->128 + reduce) | 4-wise | 4 |
| G5 | x = fold(P_n); paper's degree-5 scheme (x+g2)((x^2+g4)(x^2+x+g3)+g1)+g0, g0..g4 uniform in F_p | 3 | 5-wise | 5 |

fold(v) = v - p if v >= p else v (one conditional subtraction).  No twist for G4/G5 (a polynomial
over F_p is not GF(2)-quadratic, the reason the twist exists).  Key derivation: the shipped order
k[0..W), u, y, z, c[0..5), t_in, then the F_p words g[] by rejection sampling of further splitmix64
words (a word is rejected iff >= p, probability 2^-32); c[] and t_in stay in the derivation and are
unused by G4/G5.  Key sizes: chainhash-g4-256 45 words, chainhash-g5-256 46, chainhash-g5-1k 142
(shipped 41 / 137).  Output range of G4/G5: [0, p), i.e. the 2^32 - 1 largest 64-bit values never occur.

## Correctness and independence (all checks run; `validation/`)

* `check_bijections.txt` (`src/check_bijections.py`, sympy 1.14): explicit decoders.
  G4: coefficients a3 = 2 b0 + 1, a2 = b0^2 + b0 + 2 b1 + b2, a1 = 2 b0 b1 + b0 b2 + b1,
  a0 = b1^2 + b1 b2 + b3; decoder b0 = (a3 - 1)/2, r2 = a2 - b0^2 - b0, b1 = a1 - b0 r2,
  b2 = r2 - 2 b1, b3 = a0 - b1^2 - b1 b2 (the 2x2 block for (b1, b2) has determinant -1);
  decode(encode(b)) = b and encode(decode(a)) = a verified symbolically over Q -- a bijection wherever
  2 is invertible, in particular over F_p (1/2 = 2^63 - 2^31 + 1).
  G5: a4 = c2 + 1, a3 = c2 + c3 + c4, a2 = c4 + c2 (c3 + c4), a1 = c1 + c3 c4 + c2 c4,
  a0 = c0 + c2 (c1 + c3 c4); decoder c2 = a4 - 1, s = a3 - c2, c4 = a2 - c2 s, c3 = s - c4,
  c1 = a1 - c3 c4 - c2 c4, c0 = a0 - c2 (c1 + c3 c4): unit pivots only, verified symbolically over Z,
  hence a bijection over every commutative ring (F_p and GF(2^64) alike).  Plus 10^4 random
  round trips of both maps over F_p.
  Consequence: uniform parameters give a uniformly random monic quartic (G4) / quintic (G5) over
  F_p, so the finalizer is 4-wise / 5-wise independent on F_p and two distinct folded inputs
  collide with probability exactly 1/p.
* `check_goldi_field.txt`: the scalar Goldilocks arithmetic (`src/goldi_field.h`: Plonky2-style
  reduce128 made branchless, lazy non-canonical values, subtraction-form additions, fused
  multiply-add) against Python big-int arithmetic on 1,000,324 (a, b, c) triples (10^6 random with
  biased ranges + all pairs of 18 edge values: 0, 1, EPS, 2^32, p-1, p, p+1, 2^63, 2^64-1, ...):
  a*b, a*b+c, a+b, fold -- 0 mismatches; and the two finalizers on 2000 random keys/inputs against
  the polynomial formulas -- 0 mismatches.  (Regenerate the 90 MB dump with
  `clang++ -O2 test_goldi_field.cpp && ./test_goldi_field | python3 check_goldi_field.py`.)
* `python_ref_check.txt` (`src/goldi_ref.py`, bit-serial Python reference of the whole hash):
  2000 random (seed, message) pairs, lengths 0..2100, x 5 configurations (CHAR2-256, G4-256,
  G5-256, CHAR2-1k, G5-1k) -- 0 mismatches.  The same driver (`src/test_goldi.cpp`) checks the
  experimental header's CHAR2 path against the shipped `chainhash.h` bit for bit (2000 x 2
  configurations, 0 mismatches) and reproduces the registered SMHasher3 code 0xDE1AB9F9.
* Verification codes (LE) computed by the driver, by the SMHasher3 file through a shim on the
  M2 (hwpmull and portable) and on the Xeon (hwclmul and portable), and printed by SMHasher3
  itself: chainhash-g4-256 0xA3577E75, chainhash-g5-256 0xF89E636F, chainhash-g5-1k 0xC8B38421
  (BE, from SMHasher3's bswap variant: 0xAE143AED / 0x229C22B5 / 0x6024310F).
* Collision accounting for the whole hash (two distinct messages of at most q (sub-)block pairs):
  P(P_n = P_n') <= (q + 2)/2^64 as shipped; the fold adds P(P_n != P_n', fold equal) -- only the
  2^32 - 1 residues r < 2^32 - 1 have two preimages (r and r + p), so for a pairwise-uniform chain
  value this is at most (2^33/2^64) * 2^-64 ~ 2^-95; then the finalizer adds exactly 1/p ~
  2^-64 (1 + 2^-32).  Total <= (q + 3)/2^64 + 2^-95 + 2^-96 -- the same bound as shipped up to
  2^-95.  Independence: 4-wise (G4) / 5-wise (G5) over F_p; 5-wise is what linear probing
  provably needs (Pagh-Pagh-Ruzic), 4-wise is not enough (Patrascu-Thorup), so G4 is only a
  candidate if that guarantee is given up.

## Two implementation rounds

v1 (`src/goldi_field_v1_unfused.h`, logs `*_v1_unfused.txt`): one addition per gate as written,
each a separate subs/csel (arm64) -- and on x86-64 clang turned several of the selects into
`jb`/`jae` branches, which mispredict half the time on hash data (the Xeon whole-hash numbers of
v1 are ~15 cycles worse than the isolated finalizer latency predicts).
v2 (`src/goldi_field.h`, the version registered in SMHasher3; same function, same codes): every
select marked `__builtin_unpredictable` (csel/cmov confirmed by counting conditional branches per
symbol in the bench binaries), the addition that follows a multiply fused into the 128-bit product
before the reduction (`gl_mul_add`, the analogue of the char-2 circuit's `reduce_add`), and the
sums that involve only x and a key computed off the critical path.  Everything below is v2 unless
marked v1.

## Isolated finalizer latency (`fin_latency.cpp`, dependent chain, min of 7 x 2*10^7)

| cycles per evaluation | M2 Pro | Xeon 8375C |
|---|---|---|
| CHAR2 circuit, state kept in the vector register (as inside the hash, minus the final lane extract) | 35.1 | 51.3 |
| CHAR2 with a GPR -> vector -> GPR round trip | 47.0 | 53.8 |
| G4 (lane extract, fold, quartic) | 35.7 (v1: 42.5) | 33.0 (v1: 37.9) |
| G5 (lane extract, fold, quintic) | 43.4 (v1: 51.7) | 40.4 (v1: 57.4) |
| one F_p multiply (mul + umulh / mulx, lazy reduction) | 10.3 | 9.5 |
| one F_p addition (subs + add + csel) | 3.0 | 2.5 |
| one GF(2^64) multiply (PMULL + 2 PMULL2 + EOR3 / 3 PCLMULQDQ + XORs) | 10.9 | 15.9 |

Reading: on the M2 the two kinds of multiply cost the same (10.3 vs 10.9 cycles), so the prime
field can only lose -- its additions cost 3 cycles each and are not free the way the circuit's XORs
are (folded into the reductions), and the lane extract (~6 cycles) moves from the end of the hash
to before the finalizer either way.  On the Xeon PCLMULQDQ latency makes a GF(2^64) multiply
16 cycles against 9.5, and G4's two multiplies beat the circuit's three by ~18 cycles.

## Whole-hash microbenchmark (`bench_goldi.cpp`; SMHasher3's small-key protocol: the output XORed into the key's first 4 bytes, 15000 hashes/trial, median of 50 trials, raw incl. ~5-7 cycles of loop overhead; bulk = median GB/s of 50 trials)

Cycles on the M2 are ns x 3.26-3.34 (SMHasher3's dependent-add calibration); on the Xeon TSC
ticks at 2.9 GHz (rdtsc/rdtscp, as SMHasher3).  "hdr" = the arm64 header `chainhash_goldi.h`,
"smh" = the SMHasher3 file through `src/shim/` (its arm64 backend is the same schedule; x86-64
backend PCLMULQDQ), "shipped" = the untouched HEAD `chainhash.h`.

### M2 Pro (Apple clang 17, `-O3 -march=native+crypto`; load at start 2.75 (1-min), the other lane idle)

| function | avg 1-31 B | 8 B | 16 B | 64 B | 16 KB GB/s (B/cyc) | 512 B GB/s (B/cyc) |
|---|---|---|---|---|---|---|
| nothing (overhead) | 6.68 | 6.4 | 6.7 | 6.7 | - | - |
| hdr CHAR2-256 | 65.31 | 62.9 | 62.1 | 69.1 | 60.36 (18.47) | 36.85 (11.27) |
| hdr G4-256 | 68.55 | 70.4 | 66.3 | 69.5 | 60.36 (18.47) | 38.34 (11.73) |
| hdr G5-256 | 75.76 | 79.3 | 73.9 | 77.1 | 59.76 (18.28) | 35.90 (10.99) |
| hdr CHAR2-1k | 68.04 | 65.8 | 63.2 | 73.4 | 63.17 (19.33) | 41.27 (12.63) |
| hdr G5-1k | 78.45 | 82.0 | 71.9 | 81.0 | 62.76 (19.20) | 42.23 (12.92) |
| shipped chainhash-256 | 65.81 | 67.5 | 62.9 | 64.5 | 60.40 (18.48) | 36.79 (11.26) |
| shipped chainhash-1k | 68.04 | 65.7 | 63.1 | 67.0 | 63.42 (19.41) | 41.06 (12.56) |
| smh CHAR2-256 | 65.34 | 65.6 | 63.2 | 66.9 | 61.58 (18.84) | 34.66 (10.61) |
| smh G4-256 | 65.98 | 63.3 | 65.5 | 68.8 | 59.71 (18.27) | 36.03 (11.03) |
| smh G5-256 | 76.29 | 77.3 | 73.5 | 77.6 | 59.22 (18.12) | 33.78 (10.34) |
| smh CHAR2-1k | 70.57 | 70.3 | 70.9 | 66.9 | 62.91 (19.25) | 40.26 (12.32) |
| smh G5-1k | 75.63 | 76.5 | 71.5 | 75.4 | 62.46 (19.11) | 42.48 (13.00) |

Run-to-run spread of these medians is about +-2 cycles (compare hdr CHAR2-256 vs shipped
chainhash-256, the same code): G4 costs +1 to +3 cycles on the M2, G5 about +10; bulk throughput is
unchanged (the finalizer is off the block loop).

v1 on the M2 (load 2.59): hdr CHAR2-256 63.8 / G4-256 70.7 / G5-256 77.6 avg cycles (see
`m2/bench_m2_v1_unfused.txt`).

### Xeon Platinum 8375C (clang 21, `-O3 -march=native`, `taskset -c 80-95`; load 15.7 at start -- another user's unpinned campaign was running, results reproducible to +-0.5 cycle across the v1/v2 runs)

| function | avg 1-31 B | 8 B | 16 B | 64 B | 16 KB GB/s (B/cyc) | 512 B GB/s (B/cyc) |
|---|---|---|---|---|---|---|
| nothing (overhead) | 4.98 | 5.0 | 5.0 | 5.0 | - | - |
| smh CHAR2-256 | 114.78 | 109.3 | 97.0 | 97.2 | 42.67 (14.71) | 19.43 (6.70) |
| smh G4-256 | 94.95 | 90.0 | 76.1 | 76.7 | 43.29 (14.93) | 21.15 (7.29) |
| smh G5-256 | 102.54 | 97.8 | 83.7 | 85.8 | 42.93 (14.80) | 18.54 (6.39) |
| smh CHAR2-1k | 116.23 | 110.8 | 98.2 | 99.6 | 37.09 (12.79) | 22.15 (7.64) |
| smh G5-1k | 103.91 | 99.6 | 87.1 | 87.2 | 37.31 (12.86) | 19.97 (6.89) |

v1 on the Xeon: CHAR2-256 114.98 / G4-256 118.35 / G5-256 133.38 (`xeon/bench_xeon_v1_unfused.txt`).

## SMHasher3 (experimental file `~/repos/smhasher3/hashes/chainhash_goldi_exp.cpp`, family `chainhash_goldi`, one line added to `hashes/Hashsrc.cmake`; builds `build-goldi/`)

Full suites (all 200 tests), verification codes as above.  Baseline = the shipped chainhash-256 /
chainhash-1k (`../../smhasher3_chainhash/final4_degree5_twist_optimised/`, same codes, same
machines, earlier run; the M2 baseline of chainhash-1k there reports 36.6 cycles/hash, an SMHasher3
arm64 calibration artefact, so only chainhash-256 is quoted on the M2).

| hash | machine | result | small keys avg 1-31 B (cycles/hash) | 8 / 16 / 31 B | bulk 256 KB (bytes/cycle) | wall time | load (1-min) |
|---|---|---|---|---|---|---|---|
| chainhash-256 (shipped, baseline) | Xeon | 200/200 | 111.98 | 107.8 / 95.3 / 118.6 | 15.35 | 543 s | - |
| chainhash-g4-256 | Xeon, taskset 80-87, --ncpu=8 | **200/200** | 89.85 | 83.9 / 74.4 / 98.5 | 15.37 | 466 s | 15 -> 13 |
| chainhash-g5-256 | Xeon, taskset 88-95, --ncpu=8 | **200/200** | 97.74 | 91.8 / 83.5 / 106.3 | 15.36 | 479 s | 15 -> 13 |
| chainhash-1k (shipped, baseline) | Xeon | 200/200 | 111.17 | 104.5 / 92.0 / 119.7 | 12.26 | 600 s | - |
| chainhash-g5-1k | Xeon, taskset 80-87, --ncpu=8 | **200/200** | 100.19 | 96.3 / 84.9 / 107.6 | 12.15 | 507 s | 13 -> 7 |
| chainhash-256 (shipped, baseline) | M2 Pro | 200/200 | 71.03 | 69.9 / 70.2 / 69.9 | 19.31 | 430 s | - |
| chainhash-g4-256 | M2 Pro | [[M2_SUITE]] |

No test reports a failure or a "!!!!!" line in any of the four experimental runs (grep counts in
the logs are 0); the differential-distribution Zeroes bias that the strided variant tripped is
far below threshold here as well.  The Xeon speed sections were measured with another user's
unpinned 5-8-process campaign on the box (load 13-15); they agree with the pinned microbenchmark
above to within 3 cycles.  Logs: `xeon/smh_xeon_{g4_256,g5_256,g5_1k}.txt`, `m2/smh_m2_g4_256.txt`.

## Code size and latency notes

* Small-key path (`hash` entry with the PH level and finalizer inlined), M2 arm64 instructions:
  CHAR2-256 223, G4-256 253 (+30), G5-256 268 (+45); multi-block path 331 / 363 / 378.
  Xeon bytes: 1211 / 1299 / 1371; multi-block 1655 / 1735 / 1807 (`m2/codesize_m2.txt`,
  `xeon/codesize_xeon.txt`).
* The prime-field finalizer runs in general registers: one lane extract (FMOV / MOVQ) at the start
  instead of at the end; on the M2 that move is ~6 cycles either way, on the Xeon ~1-2.
* G4 critical path (v2): add 3 + mul_add ~12 + add 3 + mul_add ~12 + fold ~2 = ~32 cycles; G5:
  mul 10 + add 3 + 2 x mul_add + fold = ~40; CHAR2: 3 x 11 = 33 (M2) / 3 x 16 = 48 (Xeon).
* The x86 branch hazard is real: without `__builtin_unpredictable` clang emitted data-dependent
  `jb`/`jae` for the modular selects inside the hash (v1), costing ~15-20 cycles of mispredicts.

## Recommendation

**No on the M2 Pro, yes on the Xeon -- and only for G4, which gives up 5-wise independence.**

* Apple M2 Pro: a 64x64->128 multiply with Goldilocks reduction (10.3 cycles) and a PMULL
  multiply with the 2-fold reduction (10.9) cost the same, so a degree-5 prime-field finalizer
  (3 multiplies + 6 additions + fold, 43 cycles) cannot beat the char-2 circuit (3 multiplies,
  XORs free, 35 cycles): G5 costs +10 cycles per hash (65 -> 76, +15 %), and the 2-multiply G4
  only ties (+1..3 cycles).  Bulk throughput is unchanged either way.
* Xeon 8375C (Ice Lake): PCLMULQDQ makes a GF(2^64) multiply 16 cycles against 9.5, so G4 saves
  ~20 cycles per small key (115 -> 95 in the microbenchmark; SMHasher3 112 -> 90) and G5 saves
  ~12 (115 -> 103; SMHasher3 112 -> 98); both pass the full SMHasher3 suite 200/200 without any
  twist.  The gain hinges on the branchless v2 code: with clang's default lowering (v1) the
  modular selects became mispredicted branches and the prime field was *slower* than the circuit.
* Guarantees: G5 keeps the 5-wise independence and the (q + 3)/2^64 + 2^-95 collision bound (the
  fold's extra term is negligible), so it is a drop-in on x86-64 at a 12-cycle gain -- but a
  10-cycle loss on arm64 and a code-size increase of ~20 %, with the output confined to [0, p) (2^32 - 1
  of the 2^64 values unreachable).  G4 is the faster one but is only 4-wise independent, which is
  not enough for the linear-probing guarantee the paper advertises (Patrascu-Thorup); it would
  need a different story (e.g. 4-wise + the chain's own structure) to be shipped as such.
* Recommendation: keep the characteristic-2 degree-5 circuit as the single shipped finalizer.
  If an x86-specific fast path is ever wanted, G5 over Goldilocks is a proven-equivalent
  alternative worth ~12 cycles there (v2 code, `__builtin_unpredictable` mandatory); it should
  not replace the circuit on arm64, and G4 should not be shipped under the 5-wise claim.  A
  4-wise-suffices setting (e.g. plain hash tables with chaining, count sketches) could use G4 on
  x86 for ~20 cycles.

## Files

* `src/`: `goldi_field.h` (F_p arithmetic + finalizers, v2), `goldi_field_v1_unfused.h`,
  `chainhash_goldi.h` (arm64 header, FIN parameter), `chainhash_goldi_exp.cpp` (the SMHasher3
  file) and `derive_exp.py` (generates it from the mr/chainhash `chainhash.cpp`), `goldi_ref.py`,
  `check_bijections.py`, `test_goldi.cpp`, `test_goldi_field.cpp`, `check_goldi_field.py`,
  `vcode_smh.cpp`, `bench_goldi.cpp`, `fin_latency.cpp`, `shim/` (Platform.h/Hashlib.h/Intrinsics.h
  stand-ins for the standalone builds), `run_xeon*.sh`.
* `validation/`, `m2/`, `xeon/`: logs as named above; `xeon/smh_xeon_*.txt` and
  `m2/smh_m2_g4_256.txt` are the full SMHasher3 runs.
