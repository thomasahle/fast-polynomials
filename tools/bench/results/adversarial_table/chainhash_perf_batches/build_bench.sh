#!/bin/bash
# build_bench.sh <version tag>: compiles bench.cpp against hdr/chainhash_<tag>.h -> bench_<tag>
set -e
cd "$(dirname "$0")"
tag=$1
clang++ -O3 -std=c++17 -march=native+crypto -DCH_HEADER="\"hdr/chainhash_${tag}.h\"" bench.cpp -o bench_${tag}
echo built bench_${tag}
