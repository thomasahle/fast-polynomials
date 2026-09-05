# Lane C re-measurement, Apple M2 Pro, 2026-09-05

Raw logs of the M2 Pro re-runs of the "untraceable" ARM numbers (MANIFEST.md
items 3-6): application benchmarks (sketch / linear probing / XOR filter),
Mersenne 2^89-1 share generation and Goldilocks rows, the
`tab:injective:adversarial` speed harness (full table in one run, plus the two
XXH3 filtered runs), and the SMHasher3 `--test=Speed` runs of
`injective-hash.mersenne` / `injective-hash.mum`.

* Machine: Apple M2 Pro (12 cores, 8P+4E), macOS (see the `# machine:` header
  line of each log), single-threaded benchmarks; other agents' jobs were running
  on the laptop, so each log records the 1-min load average before and after
  (`# uptime before:` / `# uptime after:`).  Timing protocol: before each group
  the driver polled `uptime` until the 1-min load was < 3 (cap 20 min; the
  `WAIT` lines of `driver.log` record the load reached and the wait time).
* Compiler: Apple clang 17.0.0 (clang-1700.6.4.2); application and prime-field
  binaries built 2026-09-05 20:04 with `clang++ -O3 -std=c++17
  -march=armv8-a+crypto <src>.cpp` (`compile.log` has the source md5s).
  The speed harness binary `tools/bench/adversarial/speed` was NOT rebuilt
  (binary of 2026-09-05 19:53 from `speed.cpp`/`speed_hashes.h` of 2026-09-04
  20:27; md5s in the log headers).  SMHasher3: fork `~/repos/smhasher3`,
  `build-chainhash/SMHasher3` (binary of 2026-09-05 19:55),
  `hashes/injective_hash.cpp` md5 854b88d8415674c56bf6adf249485bfd,
  `INJECTIVE_HASH_LANES` = 9.
* Driver: `driver.sh` (sequential; `driver.log` = timeline).  Harvest:
  `harvest.py <dir>` produces `rows.md`.
* Selection rule for the paper cells: three repetitions per binary; the
  reported repetition is the one with the median Horner value (application
  benchmarks) or the median mean Horner ns/eval over the table's configurations
  (prime-field rows); all three logs are kept.  Harness rows: median of RUNS
  timings, as printed by the harness (`gbps`).

## Files

| file | date | command | load before -> after |
|---|---|---|---|
| `countsketch_arm.1.txt` | 2026-09-05 20:23:47 CEST | `cd $RUN_M2 && ./countsketch_arm   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_countsketch_arm.cpp)` | 2.94 -> 2.95 |
| `countsketch_arm.2.txt` | 2026-09-05 20:23:52 CEST | `cd $RUN_M2 && ./countsketch_arm   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_countsketch_arm.cpp)` | 2.95 -> 2.95 |
| `countsketch_arm.3.txt` | 2026-09-05 20:23:56 CEST | `cd $RUN_M2 && ./countsketch_arm   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_countsketch_arm.cpp)` | 3.59 -> 3.59 |
| `goldilocks_sharegen_store.1.txt` | 2026-09-05 20:57:05 CEST | `cd $RUN_M2 && ./goldilocks_sharegen_store   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_goldilocks_sharegen_store.cpp)` | 4.04 -> 4.04 |
| `goldilocks_sharegen_store.2.txt` | 2026-09-05 20:58:12 CEST | `cd $RUN_M2 && ./goldilocks_sharegen_store   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_goldilocks_sharegen_store.cpp)` | 6.58 -> 8.43 |
| `goldilocks_sharegen_store.3.txt` | 2026-09-05 20:59:19 CEST | `cd $RUN_M2 && ./goldilocks_sharegen_store   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_goldilocks_sharegen_store.cpp)` | 5.73 -> 5.01 |
| `goldilocks_stark_eval.1.txt` | 2026-09-05 20:56:54 CEST | `cd $RUN_M2 && ./goldilocks_stark_eval   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_goldilocks_stark_eval.cpp)` | 3.97 -> 4.04 |
| `goldilocks_stark_eval.2.txt` | 2026-09-05 20:58:02 CEST | `cd $RUN_M2 && ./goldilocks_stark_eval   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_goldilocks_stark_eval.cpp)` | 5.10 -> 6.58 |
| `goldilocks_stark_eval.3.txt` | 2026-09-05 20:59:09 CEST | `cd $RUN_M2 && ./goldilocks_stark_eval   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_goldilocks_stark_eval.cpp)` | 6.23 -> 5.73 |
| `linearprobe_arm.1.txt` | 2026-09-05 20:23:50 CEST | `cd $RUN_M2 && ./linearprobe_arm   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_linearprobe_arm.cpp)` | 2.95 -> 2.95 |
| `linearprobe_arm.2.txt` | 2026-09-05 20:23:54 CEST | `cd $RUN_M2 && ./linearprobe_arm   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_linearprobe_arm.cpp)` | 2.95 -> 3.59 |
| `linearprobe_arm.3.txt` | 2026-09-05 20:23:58 CEST | `cd $RUN_M2 && ./linearprobe_arm   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_linearprobe_arm.cpp)` | 3.59 -> 3.59 |
| `shamir_sharegen_mersenne_store.1.txt` | 2026-09-05 20:56:32 CEST | `cd $RUN_M2 && ./shamir_sharegen_mersenne_store   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto shamir_sharegen_mersenne_store.cpp)` | 3.70 -> 3.97 |
| `shamir_sharegen_mersenne_store.2.txt` | 2026-09-05 20:57:40 CEST | `cd $RUN_M2 && ./shamir_sharegen_mersenne_store   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto shamir_sharegen_mersenne_store.cpp)` | 3.95 -> 5.10 |
| `shamir_sharegen_mersenne_store.3.txt` | 2026-09-05 20:58:47 CEST | `cd $RUN_M2 && ./shamir_sharegen_mersenne_store   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto shamir_sharegen_mersenne_store.cpp)` | 7.52 -> 6.23 |
| `shamir_sharegen_mersenne.1.txt` | 2026-09-05 20:56:18 CEST | `cd $RUN_M2 && ./shamir_sharegen_mersenne   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto shamir_sharegen_mersenne.cpp)` | 3.54 -> 3.70 |
| `shamir_sharegen_mersenne.2.txt` | 2026-09-05 20:57:26 CEST | `cd $RUN_M2 && ./shamir_sharegen_mersenne   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto shamir_sharegen_mersenne.cpp)` | 4.04 -> 3.95 |
| `shamir_sharegen_mersenne.3.txt` | 2026-09-05 20:58:33 CEST | `cd $RUN_M2 && ./shamir_sharegen_mersenne   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto shamir_sharegen_mersenne.cpp)` | 8.43 -> 7.52 |
| `smh_speed_mersenne.run2.txt` | 2026-09-05 21:10:55 CEST | `cd /Users/ahle/repos/smhasher3/build-chainhash && ./SMHasher3 --test=Speed injective-hash.mersenne   (second run; binary of Sep  5 19:55:11 2026)` | 2.60 -> 3.20 |
| `smh_speed_mersenne.txt` | 2026-09-05 21:01:40 CEST | `cd /Users/ahle/repos/smhasher3/build-chainhash && ./SMHasher3 --test=Speed injective-hash.mersenne   (binary of Sep  5 19:55:11 2026)` | 2.83 -> 2.41 |
| `smh_speed_mum.txt` | 2026-09-05 21:07:02 CEST | `cd /Users/ahle/repos/smhasher3/build-chainhash && ./SMHasher3 --test=Speed injective-hash.mum   (binary of Sep  5 19:55:11 2026)` | 2.41 -> 2.51 |
| `speed_full_runs9_t0.15.run2.txt` | 2026-09-05 21:08:43 CEST | `cd tools/bench/adversarial && ./speed 9 0.15 run   (full table, second run; binary ./speed of Sep  5 19:53:18 2026, NOT rebuilt)` | 2.06 -> 3.17 |
| `speed_full_runs9_t0.15.txt` | 2026-09-05 20:34:00 CEST | `cd tools/bench/adversarial && ./speed 9 0.15 run   (full table, same RUNS/TARGET as speed_rerun.txt; binary ./speed of Sep  5 19:53:18 2026, NOT rebuilt)` | 2.54 -> 4.32 |
| `speed_xxh3_128_runs5_t0.5.txt` | 2026-09-05 20:36:11 CEST | `cd tools/bench/adversarial && ./speed 5 0.5 run XXH3-128` | 3.96 -> 4.21 |
| `speed_xxh3_runs9_t0.5.txt` | 2026-09-05 20:35:43 CEST | `cd tools/bench/adversarial && ./speed 9 0.5 run XXH3` | 4.32 -> 3.96 |
| `xorfilter_arm.1.txt` | 2026-09-05 20:23:51 CEST | `cd $RUN_M2 && ./xorfilter_arm   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_xorfilter_arm.cpp)` | 2.95 -> 2.95 |
| `xorfilter_arm.2.txt` | 2026-09-05 20:23:55 CEST | `cd $RUN_M2 && ./xorfilter_arm   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_xorfilter_arm.cpp)` | 3.59 -> 3.59 |
| `xorfilter_arm.3.txt` | 2026-09-05 20:23:59 CEST | `cd $RUN_M2 && ./xorfilter_arm   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto app_xorfilter_arm.cpp)` | 3.59 -> 3.59 |

`driver.log`:
```
driver start Sat Sep  5 20:05:16 CEST 2026
WAIT group1-app: load<3 reached after 1111 s, load=2.94
group1 done Sat Sep  5 20:23:59 CEST 2026
WAIT group2-speed: load<3 reached after 601 s, load=2.54
group2 done Sat Sep  5 20:36:17 CEST 2026
WAIT group3-prime: timed out after 1200 s, load=3.54 (running anyway)
group3 done Sat Sep  5 20:59:40 CEST 2026
WAIT group4-smh-mersenne: load<3 reached after 120 s, load=2.83
WAIT group4-smh-mum: load<3 reached after 0 s, load=2.41
group4 done Sat Sep  5 21:07:44 CEST 2026
ALL DONE Sat Sep  5 21:07:44 CEST 2026
driver2 start Sat Sep  5 21:08:43 CEST 2026
WAIT run2-speed-full: load<3 reached after 0 s, load=2.06
run2 speed done Sat Sep  5 21:10:25 CEST 2026
WAIT run2-smh-mersenne: load<3 reached after 30 s, load=2.60
run2 smh done Sat Sep  5 21:16:16 CEST 2026
ALL DONE 2 Sat Sep  5 21:16:16 CEST 2026
```
