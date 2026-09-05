#!/bin/bash
cd ~/goldi-exp
echo "load before bench: $(cat /proc/loadavg)"
taskset -c 80-95 ./bench_goldi_x86 50 > logs/bench_xeon.txt 2>&1
echo "load after bench: $(cat /proc/loadavg)"
echo BENCH_DONE
mkdir -p ~/smhasher3-goldi/build-goldi && cd ~/smhasher3-goldi/build-goldi
taskset -c 0-63 cmake .. -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ > ~/goldi-exp/logs/cmake_xeon.log 2>&1
taskset -c 0-63 cmake --build . -j24 > ~/goldi-exp/logs/build_xeon.log 2>&1
echo "build exit $?"
./SMHasher3 --test=VerifyAll chainhash-g4-256 chainhash-g5-256 chainhash-g5-1k 2>&1 | grep -i -E "chainhash-g|verif|FAIL" | head -20
echo BUILD_DONE
