#!/bin/bash
# Lane C, M2 Pro timed runs. Sequential; waits for 1-min load < 3 (cap 20 min) before each group.
S=/private/tmp/claude-501/-Users-ahle-repos-notes-fast-polyhash/671fdc97-fe99-4719-bea0-4eedf88d5744/scratchpad/final/C
R=/Users/ahle/repos/fast-polynomials
M=$S/m2; RUN=$S/run_m2
CC="$(clang++ --version | head -1)"
MACH="Apple M2 Pro (12 cores 8P+4E), macOS $(sw_vers -productVersion), $(uname -m)"
load1() { sysctl -n vm.loadavg | awk '{print $2}'; }
waitload() {  # $1 = label
  local t0=$(date +%s) l
  while :; do l=$(load1); if awk -v l="$l" 'BEGIN{exit !(l<3)}'; then break; fi
    if [ $(( $(date +%s) - t0 )) -ge 1200 ]; then echo "WAIT $1: timed out after 1200 s, load=$l (running anyway)" >> $M/driver.log; return; fi
    sleep 30; done
  echo "WAIT $1: load<3 reached after $(( $(date +%s) - t0 )) s, load=$l" >> $M/driver.log
}
hdr() { # $1 = logfile, $2 = command, $3 = source md5 note
  { echo "# date: $(date '+%Y-%m-%d %H:%M:%S %Z')"; echo "# machine: $MACH"; echo "# uptime before: $(uptime)"; echo "# command: $2"; echo "# compiler: $CC"; echo "# source: $3"; } > "$1"
}
ftr() { echo "# uptime after: $(uptime)" >> "$1"; }
echo "driver start $(date)" >> $M/driver.log

# ---- group 1: application benchmarks, 3 reps
waitload group1-app
cd $RUN
for r in 1 2 3; do
  for b in countsketch_arm linearprobe_arm xorfilter_arm; do
    src=app_$b.cpp; L=$M/$b.$r.txt
    hdr $L "cd $RUN && ./$b   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto $src)" "$src md5 $(md5 -q $R/tools/bench/$src); fast_hashing_arm.h md5 $(md5 -q $R/tools/bench/framework/fast_hashing_arm.h)"
    ./$b >> $L 2>&1; ftr $L
  done
done
echo "group1 done $(date)" >> $M/driver.log

# ---- group 2: speed harness (adversarial table)
waitload group2-speed
cd $R/tools/bench/adversarial
L=$M/speed_full_runs9_t0.15.txt
hdr $L "cd tools/bench/adversarial && ./speed 9 0.15 run   (full table, same RUNS/TARGET as speed_rerun.txt; binary ./speed of $(stat -f '%Sm' speed), NOT rebuilt)" "speed.cpp md5 $(md5 -q speed.cpp); speed_hashes.h md5 $(md5 -q speed_hashes.h); speed binary md5 $(md5 -q speed)"
./speed 9 0.15 run >> $L 2>&1; ftr $L
L=$M/speed_xxh3_runs9_t0.5.txt
hdr $L "cd tools/bench/adversarial && ./speed 9 0.5 run XXH3" "speed binary md5 $(md5 -q speed)"
./speed 9 0.5 run XXH3 >> $L 2>&1; ftr $L
L=$M/speed_xxh3_128_runs5_t0.5.txt
hdr $L "cd tools/bench/adversarial && ./speed 5 0.5 run XXH3-128" "speed binary md5 $(md5 -q speed)"
./speed 5 0.5 run XXH3-128 >> $L 2>&1; ftr $L
echo "group2 done $(date)" >> $M/driver.log

# ---- group 3: Mersenne 2^89-1 and Goldilocks, 3 reps
waitload group3-prime
cd $RUN
for r in 1 2 3; do
  for pair in shamir_sharegen_mersenne:shamir_sharegen_mersenne shamir_sharegen_mersenne_store:shamir_sharegen_mersenne_store app_goldilocks_stark_eval:goldilocks_stark_eval app_goldilocks_sharegen_store:goldilocks_sharegen_store; do
    src=${pair%%:*}.cpp; b=${pair##*:}; L=$M/$b.$r.txt
    hdr $L "cd $RUN && ./$b   (defaults; built: clang++ -O3 -std=c++17 -march=armv8-a+crypto $src)" "$src md5 $(md5 -q $R/tools/bench/$src); x2s_mersenne_chains.h $(md5 -q $R/tools/bench/framework/x2s_mersenne_chains.h); x2s_goldilocks_chains.h $(md5 -q $R/tools/bench/framework/x2s_goldilocks_chains.h)"
    ./$b >> $L 2>&1; ftr $L
  done
done
echo "group3 done $(date)" >> $M/driver.log

# ---- group 4: SMHasher3 speed, sequential
cd /Users/ahle/repos/smhasher3/build-chainhash
for h in mersenne mum; do
  waitload group4-smh-$h
  L=$M/smh_speed_$h.txt
  hdr $L "cd /Users/ahle/repos/smhasher3/build-chainhash && ./SMHasher3 --test=Speed injective-hash.$h   (binary of $(stat -f '%Sm' SMHasher3))" "hashes/injective_hash.cpp md5 $(md5 -q ../hashes/injective_hash.cpp); INJECTIVE_HASH_LANES default 9"
  ./SMHasher3 --test=Speed injective-hash.$h >> $L 2>&1; ftr $L
done
echo "group4 done $(date)" >> $M/driver.log
echo "ALL DONE $(date)" >> $M/driver.log
