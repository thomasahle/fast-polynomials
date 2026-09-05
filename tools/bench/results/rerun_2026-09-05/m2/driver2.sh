#!/bin/bash
# Lane C follow-up: second full-table harness run (the first one's 512 B half was load-disturbed) and a second SMHasher3 mersenne run.
S=/private/tmp/claude-501/-Users-ahle-repos-notes-fast-polyhash/671fdc97-fe99-4719-bea0-4eedf88d5744/scratchpad/final/C
R=/Users/ahle/repos/fast-polynomials; M=$S/m2
CC="$(clang++ --version | head -1)"; MACH="Apple M2 Pro (12 cores 8P+4E), macOS $(sw_vers -productVersion), $(uname -m)"
load1() { sysctl -n vm.loadavg | awk '{print $2}'; }
waitload() { local t0=$(date +%s) l; while :; do l=$(load1); if awk -v l="$l" 'BEGIN{exit !(l<3)}'; then break; fi
    if [ $(( $(date +%s) - t0 )) -ge 900 ]; then echo "WAIT $1: timed out after 900 s, load=$l (running anyway)" >> $M/driver.log; return; fi; sleep 30; done
  echo "WAIT $1: load<3 reached after $(( $(date +%s) - t0 )) s, load=$l" >> $M/driver.log; }
hdr() { { echo "# date: $(date '+%Y-%m-%d %H:%M:%S %Z')"; echo "# machine: $MACH"; echo "# uptime before: $(uptime)"; echo "# command: $2"; echo "# compiler: $CC"; echo "# source: $3"; } > "$1"; }
ftr() { echo "# uptime after: $(uptime)" >> "$1"; }
echo "driver2 start $(date)" >> $M/driver.log
waitload run2-speed-full
cd $R/tools/bench/adversarial
L=$M/speed_full_runs9_t0.15.run2.txt
hdr $L "cd tools/bench/adversarial && ./speed 9 0.15 run   (full table, second run; binary ./speed of $(stat -f '%Sm' speed), NOT rebuilt)" "speed.cpp md5 $(md5 -q speed.cpp); speed_hashes.h md5 $(md5 -q speed_hashes.h); speed binary md5 $(md5 -q speed)"
./speed 9 0.15 run >> $L 2>&1; ftr $L
echo "run2 speed done $(date)" >> $M/driver.log
waitload run2-smh-mersenne
cd /Users/ahle/repos/smhasher3/build-chainhash
L=$M/smh_speed_mersenne.run2.txt
hdr $L "cd /Users/ahle/repos/smhasher3/build-chainhash && ./SMHasher3 --test=Speed injective-hash.mersenne   (second run; binary of $(stat -f '%Sm' SMHasher3))" "hashes/injective_hash.cpp md5 $(md5 -q ../hashes/injective_hash.cpp); INJECTIVE_HASH_LANES default 9"
./SMHasher3 --test=Speed injective-hash.mersenne >> $L 2>&1; ftr $L
echo "run2 smh done $(date)" >> $M/driver.log
echo "ALL DONE 2 $(date)" >> $M/driver.log
