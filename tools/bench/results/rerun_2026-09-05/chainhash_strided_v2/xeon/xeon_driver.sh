#!/bin/bash
# Lane E step 3 ("final6", length into both halves), Xeon: Sanity+Speed (taskset 80-95), then full suites in parallel (80-87 / 88-95).
D=~/laneE_final6
echo "$(date +%T) driver start; uptime: $(uptime)" >> $D/xeon_load.log
cd ~/smhasher3/build-chainhash
for h in chainhash-256 chainhash-1k; do
  echo "$(date +%T) sanity+speed $h start; uptime: $(uptime)" >> $D/xeon_load.log
  taskset -c 80-95 ./SMHasher3 --test=Sanity,Speed $h > $D/final6_x86_speed_${h#chainhash-}.txt 2>&1
  echo "$(date +%T) sanity+speed $h end exit=$?" >> $D/xeon_load.log
done
echo "$(date +%T) full suites start; uptime: $(uptime)" >> $D/xeon_load.log
taskset -c 80-87 ./SMHasher3 --ncpu=8 chainhash-256 > $D/final6_x86_256.txt 2>&1 &
P1=$!
taskset -c 88-95 ./SMHasher3 --ncpu=8 chainhash-1k > $D/final6_x86_1k.txt 2>&1 &
P2=$!
wait $P1; echo "$(date +%T) suite 256 end exit=$?; uptime: $(uptime)" >> $D/xeon_load.log
wait $P2; echo "$(date +%T) suite 1k end exit=$?; uptime: $(uptime)" >> $D/xeon_load.log
echo DONE > $D/xeon.done
