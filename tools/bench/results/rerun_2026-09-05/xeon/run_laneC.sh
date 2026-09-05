#!/bin/bash
# Lane C driver (2026-09-05): build and run the x86 application benchmarks and prime-field
# kernels on the Intel Xeon Platinum 8375C (hardware.normalcomputing.net), 3 repetitions,
# pinned with taskset -c 80-95, single-threaded binaries with default arguments (= paper protocol).
set -u
cd ~/fastpoly-bench/bench || exit 1
mkdir -p laneC
ln -sf ../bytes1.bin laneC/bytes1.bin
CXX=clang++
FLAGS="-O3 -std=c++17 -march=native"
BINS="app_countsketch_x86 app_linearprobe_x86 app_xorfilter_x86 shamir_sharegen_mersenne shamir_sharegen_mersenne_store app_goldilocks_stark_eval app_goldilocks_sharegen_store"
{
  echo "# build start $(date -Is) host=$(hostname)"
  echo "# $(uptime)"
  $CXX --version
  lscpu | grep -E 'Model name|^CPU\(s\)|NUMA node\(s\)|Thread'
} > laneC/build.log
for f in $BINS; do
  echo "== $CXX $FLAGS $f.cpp -o laneC/$f" >> laneC/build.log
  $CXX $FLAGS $f.cpp -o laneC/$f >> laneC/build.log 2>&1 || { echo "BUILD FAILED $f" >> laneC/build.log; echo failed > laneC/DONE; exit 2; }
done
echo "# build end $(date -Is)" >> laneC/build.log
md5sum app_*.cpp shamir_*.cpp framework/*.h > laneC/sources.md5
cd laneC || exit 1
CPUS=80-95
for r in 1 2 3; do
  for f in $BINS; do
    out=$f.$r.txt
    {
      echo "# $(date -Is) host=$(hostname) cpu=$(lscpu | grep 'Model name' | sed 's/.*: *//')"
      echo "# uptime before: $(uptime)"
      echo "# cmd: taskset -c $CPUS ./$f   (default arguments; cwd=$PWD; repetition $r of 3)"
      echo "# compiler: $($CXX --version | head -1); flags: $FLAGS"
      echo "# source md5: $(md5sum ../$f.cpp)"
    } > "$out"
    s=$(date +%s%N)
    taskset -c $CPUS ./$f >> "$out" 2>&1
    rc=$?
    e=$(date +%s%N)
    echo "# exit=$rc wall_ms=$(( (e - s) / 1000000 ))" >> "$out"
    echo "# uptime after: $(uptime)" >> "$out"
  done
done
echo done > DONE
