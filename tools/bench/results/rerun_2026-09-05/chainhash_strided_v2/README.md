# ChainHash, strided pairing with the length XORed into BOTH halves of the last pair -- lane E step 3 (measurement run "final6", 2026-09-05/06)

Definition under test: `tools/bench/chainhash/chainhash.h` after the Zeroes fix (strided 32-byte-group word
pairing from step 1, and the byte length now XORed into both words a AND b of the last pair in every
path; recurrence, twist, degree-5 finalizer, key W+9 words unchanged), reference `chainhash_ref.h`,
SMHasher3 port `~/repos/smhasher3/hashes/chainhash.cpp` (same definition in the x86 `hwclmul`, ARM
`hwpmull` and portable backends).  Step-2 diagnosis of the failure this fixes: `../chainhash_strided/`.

**Verification codes** (identical on hwpmull M2 Pro, hwclmul Xeon and the portable backend, see
`step3_logs/smh_portable.log` -- there the port still carried the step-1 codes, so the check prints
"FAIL! (Expected 0xbfc38a57)" while computing 0xAA4E2A3B / 0x7A1ED2E0, i.e. the same values as the
hardware backends):

| hash | LE | BE | step 1 (strided, len into a) | shipped adjacent pairing |
|---|---|---|---|---|
| chainhash-256 | `0xAA4E2A3B` | `0x11037F6F` | 0xBFC38A57 / 0xC84FA5C3 | 0xDE1AB9F9 / 0xCA97ABE0 |
| chainhash-1k  | `0x7A1ED2E0` | `0x85B2F299` | 0x710CF02B / 0x1AB98587 | 0x32B4EE71 / 0xAE91BF9E |

## RESULT: 200/200 on both machines for both configurations

| suite log | machine / backend | result | Keyset 'Zeroes' differential distribution, worst bias |
|---|---|---|---|
| `m2/final6_m2_256.txt`   | M2 Pro, hwpmull | `Overall result: pass ( 200 / 200 passed)` | 0.773x (^4) (12 bits at bit 5) |
| `m2/final6_m2_1k.txt`    | M2 Pro, hwpmull | 200 / 200 | 0.520x (^0) (13 bits at bit 23) |
| `xeon/final6_x86_256.txt`| Xeon 8375C, hwclmul | 200 / 200 | 0.773x (^4) |
| `xeon/final6_x86_1k.txt` | Xeon 8375C, hwclmul | 200 / 200 | 0.520x (^0) |

Step 1 (length into a only) had 2.199x (^51) here for chainhash-256 (FAIL, 199/200) and 0.63x / 0.67x for
chainhash-1k; the step-2 simulator `../chainhash_strided/zeroes_diagnosis/zeroes5.cpp` predicted 0.62x / 0.60x
mean over 32 seeds for this variant.  The suite is deterministic (seed 0): the M2 and Xeon logs agree on every
statistic; only the Speed section differs.  No other test changed.

## Timing

### M2 Pro harness (`tools/bench/adversarial`, `./speed 5 0.5 run ChainHash`, median of 5 x 0.5 s, GB/s)

`speed` rebuilt against the new header (`c++ -O3 -std=c++17 -mcpu=native`, Apple clang 17.0.0,
`make speed`; `./speed 1 0.1 selftest`: "selftests passed").  Run 1 `m2/harness_speed_5_0.5_ChainHash.run1.txt`
(2026-09-05 23:47:35, 1-min load 1.83 at start, 2.27 at end); run 2 `m2/harness_speed_5_0.5_ChainHash.run2.txt`
(2026-09-06 00:11:44, load 2.80 at start, 3.49 at end; `m2/m2_harness2_load.log`).

| row | run 1: 16 KB / 512 B | run 2: 16 KB / 512 B | mean | step 1 (strided, len in a; 2 runs) | shipped adjacent (paper table) |
|---|---|---|---|---|---|
| ChainHash, 1 KB blocks (S=2) | 68.73 / 39.87 | 69.92 / 38.48 | **69.3 / 39.2** | 70.9 / 43.7 | 61.7 / 40.5 |
| ChainHash, 256 B blocks      | 68.76 / 38.09 | 66.58 / 37.03 | **67.7 / 37.6** | 67.3 / 39.3 | 57.7 / 36.8 |
| ChainHash, 64 B blocks       | 27.89 / 29.56 | 27.17 / 29.33 | **27.5 / 29.4** | 26.4 / 29.6 | 26.6 / 27.4 |

(run 1 min-max: 1 KB 66.9-71.4 / 39.8-40.1; 256 B 65.7-69.6 / 37.6-38.6; 64 B 27.6-28.1 / 28.6-30.3.)
The 512-byte rows of the 1 KB and 256 B configurations carry the cost of the extra length-times-key
products (two in the fused S=2 path, one in the S=1 leaf path); the 16 KB rows are unchanged within noise.

### SMHasher3 Sanity+Speed

* Xeon 8375C (`xeon/final6_x86_speed_{256,1k}.txt`, `taskset -c 80-95 ./SMHasher3 --test=Sanity,Speed`,
  clang 21.1.8, `-O3 -march=native`; 1-min load 9.9 / 9.8 at start -- other users' jobs, on other cores):
  chainhash-256 **107.77 cycles/hash** (1-31 B), **15.35 bytes/cycle** bulk (262144 B, 50.04 GiB/s), 15.30 on
  [262017,262144]; chainhash-1k **108.57 cycles/hash**, **12.25 bytes/cycle** (39.94 GiB/s), 12.15 on the
  odd-size range.  Earlier run of the same code at load 3.1-3.4 (`step3_logs/xeon_smh_sanity_speed.log`):
  108.17 / 15.35 and 108.56 / 12.20.
* M2 Pro, Speed section of the full-suite logs (`m2/final6_m2_{256,1k}.txt`; load 2.27 / 2.90 at start,
  rising to 5-7 during the runs because of unrelated jobs, `m2/m2_load.log`): chainhash-256 **72.44 cycles/hash**,
  **22.20 bytes/cycle** (72.4 GiB/s; 20.90 on the odd-size range); chainhash-1k **76.51 cycles/hash**,
  **17.28 bytes/cycle** (56.3 GiB/s; 17.02 odd-size).  Earlier Sanity+Speed runs of the same code under
  load 3-6 (`step3_logs/m2_smh_sanity_speed.log`, `m2_speed_run2.log`): 71.37 / 72.50 cycles and 22.88 / 22.45
  bytes/cycle (256), 73.91 / 71.23 cycles and 17.93 / 18.57 bytes/cycle (1k).

| | M2 Pro bulk B/cycle (256 / 1k) | M2 Pro small keys cycles (256 / 1k) | Xeon bulk B/cycle | Xeon small keys cycles |
|---|---|---|---|---|
| shipped adjacent pairing (`../smhasher3_chainhash/`) | 20.7 / 17.5 | 66 / 72 | 15.4 / 12.3 | 112 / 111 |
| step 1: strided, length into a (`../chainhash_strided/`) | 22.5-22.7 / 17.4-17.9 | 70.5-71.5 / 73.6-74.8 | 15.35 / 12.10 | 107.1 / 107.7 |
| **this run: strided, length into a and b** | **22.2 (22.5-22.9) / 17.3 (17.9-18.6)** | **72.4 (71.4-72.5) / 76.5 (71.2-73.9)** | **15.35 / 12.25** | **107.8 / 108.6** |

Xeon: bulk unchanged, small keys +0.6 / +0.9 cycles vs step 1 (the extra length-times-key product), still
4.2 / 2.6 cycles below the shipped adjacent design.  M2: within run-to-run noise of step 1 (bulk +1.5 / -0.2
bytes/cycle vs the shipped design; small keys about +6 / +4 cycles vs the shipped design's quiet-machine
figures, of which +4.5 / +2 already came with step 1 and the rest is noise at load 3-7 -- the 76.51 1k figure
was taken while the machine's 1-min load rose from 2.9 to 6.8).

## Commands and environment

* M2 Pro (Apple M2 Pro, macOS Darwin 25.6.0, Apple clang 17.0.0 (clang-1700.6.4.2)); SMHasher3 fork build
  `~/repos/smhasher3/build-chainhash` (`/usr/bin/c++ -O3 -march=native -Xclang -target-feature -Xclang +aes`,
  `step3_logs/smh_build.log`).  Driver `m2/m2_driver.sh`: 1-min-load < 3 gate (polled every 30 s, 20 min max)
  before the harness and before each suite, `./speed 5 0.5 run ChainHash`, then `./SMHasher3 chainhash-256`
  and `./SMHasher3 chainhash-1k` sequentially (372 s and 423 s); `m2/m2_harness2.sh`: second harness pass.
  Load log `m2/m2_load.log`: the gate opened at 1.83 (harness), 2.27 (256 suite) and 2.90 (1k suite, after
  waiting 8 min); an unrelated agent's benchmark/build jobs and the usual background processes kept the
  1-min load at 5-8 between and during the suites.
* Xeon Platinum 8375C @ 2.90 GHz (`hardware.normalcomputing.net`, clang 21.1.8, `-O3 -march=native`, build
  dir `~/smhasher3/build-chainhash`, `cmake --build . -j16`: `xeon/build.log`).  `xeon/xeon_driver.sh`:
  `taskset -c 80-95 ./SMHasher3 --test=Sanity,Speed` for both hashes (54 s, 64 s), then the two full suites in
  parallel, `taskset -c 80-87 ./SMHasher3 --ncpu=8 chainhash-256` and `taskset -c 88-95 ... chainhash-1k`
  (8 min / 9 min).  `xeon/xeon_load.log`: 1-min load 9.9 at start, 13-18 during the suites (other users).
* Xeon harness: `tools/bench/chainhash` and `tools/bench/adversarial` were rsynced to
  `~/fastpoly-bench/bench/`, but the harness does not build on x86 (`xeon/harness_build.log`:
  `../framework/multiplication_arm.h:9:10: fatal error: arm_neon.h`; `chainhash.h` and `speed_hashes.h` are
  NEON-only -- the x86 ChainHash implementation exists only in the SMHasher3 port).  No Xeon harness rows.
* Tests of the header (`step3_logs/build_sh.log`, `tools/bench/chainhash/build.sh`): -O3, ASAN (Homebrew LLVM)
  and Guard Malloc runs each "ALL TESTS PASSED", 490,022 checks (T1-T9, T9 = stream-recurrence equivalence and
  the len-in-a-only / b-only / previous-pair negative checks); re-run at -O3 against the final header text
  before this measurement (490,022 checks, 0 failed).  `step3_logs/smh_sanity_local.log`: M2 Sanity incl.
  `--endian=nonnative` (BE codes).

## Files
* `m2/`: full suites (`final6_m2_256.txt`, `final6_m2_1k.txt`), harness runs 1-2, drivers, load logs.
* `xeon/`: full suites (`final6_x86_256.txt`, `final6_x86_1k.txt`), Sanity+Speed (`final6_x86_speed_*.txt`),
  driver, load log, SMHasher3 build log, harness build failure log.
* `step3_logs/`: header test log, SMHasher3 fork build log, portable-backend code check, local Sanity (LE+BE),
  earlier Sanity+Speed runs of this code on both machines.
