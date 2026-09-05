#!/bin/bash
# Lane E step 2, M2 Pro: harness timing then SMHasher3 full suites (sequential).
E=/private/tmp/claude-501/-Users-ahle-repos-notes-fast-polyhash/671fdc97-fe99-4719-bea0-4eedf88d5744/scratchpad/final/E
loadnow() { sysctl -n vm.loadavg | awk '{print $2}'; }
waitload() {  # poll up to 20 min for 1-min load < 3
  for i in $(seq 1 40); do
    l=$(loadnow); echo "$(date +%T) load1=$l" >> $E/m2_load.log
    if [ "$(echo "$l < 3" | bc)" = "1" ]; then return; fi
    sleep 30
  done
  echo "$(date +%T) load gate timed out, proceeding at load1=$l" >> $E/m2_load.log
}
cd /Users/ahle/repos/fast-polynomials/tools/bench/adversarial
waitload
echo "$(date +%T) harness start load1=$(loadnow) uptime: $(uptime)" >> $E/m2_load.log
./speed 5 0.5 run ChainHash > $E/final5_m2_harness_chainhash.txt 2>&1
echo "$(date +%T) harness end load1=$(loadnow) exit=$?" >> $E/m2_load.log
cd /Users/ahle/repos/smhasher3/build-chainhash
for h in chainhash-256 chainhash-1k; do
  waitload
  echo "$(date +%T) suite $h start load1=$(loadnow) uptime: $(uptime)" >> $E/m2_load.log
  ./SMHasher3 $h > $E/final5_m2_${h#chainhash-}.txt 2>&1
  echo "$(date +%T) suite $h end exit=$? load1=$(loadnow)" >> $E/m2_load.log
done
echo DONE > $E/m2.done
