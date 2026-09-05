#!/bin/bash
# v2 build of the experimental file, verification, then the three full suites (two in parallel on disjoint core sets).
cd ~/smhasher3-goldi/build-goldi
taskset -c 0-63 cmake --build . -j24 > ~/goldi-exp/logs/build2_xeon.log 2>&1; echo "build exit $?"
./SMHasher3 --test=VerifyAll 2>&1 | grep -i chainhash
echo "load before suites: $(cat /proc/loadavg)"
( taskset -c 80-87 ./SMHasher3 --ncpu=8 chainhash-g4-256 > ~/goldi-exp/logs/smh_xeon_g4_256.txt 2>&1; echo "G4_256_DONE $(cat /proc/loadavg)";
  taskset -c 80-87 ./SMHasher3 --ncpu=8 chainhash-g5-1k > ~/goldi-exp/logs/smh_xeon_g5_1k.txt 2>&1; echo "G5_1K_DONE $(cat /proc/loadavg)" ) &
taskset -c 88-95 ./SMHasher3 --ncpu=8 chainhash-g5-256 > ~/goldi-exp/logs/smh_xeon_g5_256.txt 2>&1; echo "G5_256_DONE $(cat /proc/loadavg)"
wait
echo ALL_SUITES_DONE
