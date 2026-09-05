#!/bin/bash
# Lane C driver, set B (2026-09-05): re-run of the three repetitions with the binaries built by
# run_laneC.sh (build.log / sources.md5 in ..), after the concurrent adversarial jobs on CPUs 80-95 ended.
set -u
cd ~/fastpoly-bench/bench/laneC || exit 1
mkdir -p setB; cd setB || exit 1
ln -sf ../../bytes1.bin bytes1.bin
CXX=clang++
FLAGS="-O3 -std=c++17 -march=native"
BINS="app_countsketch_x86 app_linearprobe_x86 app_xorfilter_x86 shamir_sharegen_mersenne shamir_sharegen_mersenne_store app_goldilocks_stark_eval app_goldilocks_sharegen_store"
CPUS=80-95
for r in 1 2 3; do
  { echo "# $(date -Is) processes above 20% CPU at the start of repetition $r (pid %cpu affinity command)";
    for p in $(ps -eo pid,pcpu --sort=-pcpu | awk 'NR>1 && $2>20 {print $1}'); do
      echo "$p $(ps -o pcpu= -p $p) [$(taskset -pc $p 2>/dev/null | sed 's/.*: //')] $(ps -o args= -p $p | cut -c1-80)"; done; } > top_procs.$r.txt
  for f in $BINS; do
    out=$f.$r.txt
    {
      echo "# $(date -Is) host=$(hostname) cpu=$(lscpu | grep 'Model name' | sed 's/.*: *//')"
      echo "# uptime before: $(uptime)"
      echo "# cmd: taskset -c $CPUS ../$f   (default arguments; cwd=$PWD; set B, repetition $r of 3; binary built $(stat -c %y ../$f | cut -c1-19) by run_laneC.sh)"
      echo "# compiler: $($CXX --version | head -1); flags: $FLAGS"
      echo "# source md5: $(md5sum ../../$f.cpp)"
    } > "$out"
    s=$(date +%s%N)
    taskset -c $CPUS ../$f >> "$out" 2>&1
    rc=$?
    e=$(date +%s%N)
    echo "# exit=$rc wall_ms=$(( (e - s) / 1000000 ))" >> "$out"
    echo "# uptime after: $(uptime)" >> "$out"
  done
done
echo done > DONE
