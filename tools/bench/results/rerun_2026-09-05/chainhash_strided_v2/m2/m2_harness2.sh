#!/bin/bash
# After the suites: second harness pass, behind the same load gate.
E=/private/tmp/claude-501/-Users-ahle-repos-notes-fast-polyhash/671fdc97-fe99-4719-bea0-4eedf88d5744/scratchpad/strided2
loadnow() { sysctl -n vm.loadavg | awk '{print $2}'; }
for i in $(seq 1 240); do [ -f $E/m2.done ] && break; sleep 10; done
for i in $(seq 1 40); do
  l=$(loadnow); echo "$(date +%T) load1=$l" >> $E/m2_harness2_load.log
  if [ "$(echo "$l < 3" | bc)" = "1" ]; then break; fi
  sleep 30
done
cd /Users/ahle/repos/fast-polynomials/tools/bench/adversarial
echo "$(date +%T) harness run2 start load1=$(loadnow) uptime: $(uptime)" >> $E/m2_harness2_load.log
./speed 5 0.5 run ChainHash > $E/final6_m2_harness_chainhash.run2.txt 2>&1
echo "$(date +%T) harness run2 end exit=$? load1=$(loadnow)" >> $E/m2_harness2_load.log
echo DONE > $E/m2_harness2.done
