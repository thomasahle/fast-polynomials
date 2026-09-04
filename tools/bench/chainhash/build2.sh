#!/bin/bash
# Build (and run) the ChainHash-2 (strided pairing candidate) tests.  arm64 / Apple Silicon only.
#   ./build2.sh          build both binaries and run: -O3, ASAN, -O3 under Guard Malloc
#   ./build2.sh build    build only
# Same notes as build.sh (Apple clang needs -march=native+crypto; ASAN via Homebrew LLVM).
set -e
cd "$(dirname "$0")"
CXX=${CXX:-clang++}
if [ -z "$ASAN_CXX" ]; then
    for c in /opt/homebrew/opt/llvm/bin/clang++ /opt/homebrew/opt/llvm@21/bin/clang++ /opt/homebrew/opt/llvm@19/bin/clang++; do
        if [ -x "$c" ]; then ASAN_CXX="$c"; break; fi
    done
    ASAN_CXX=${ASAN_CXX:-$CXX}
fi
FLAGS="-std=c++17 -march=native+crypto -Wall -Wextra"

echo "== building test_chainhash2 (-O3) with $CXX"
$CXX -O3 $FLAGS test_chainhash2.cpp -o test_chainhash2
echo "== building test_chainhash2_asan (-O2 -fsanitize=address) with $ASAN_CXX"
$ASAN_CXX -O2 -g -fsanitize=address -fno-omit-frame-pointer $FLAGS test_chainhash2.cpp -o test_chainhash2_asan

if [ "$1" != "build" ]; then
    echo "== running test_chainhash2 (-O3)"
    ./test_chainhash2
    echo "== running test_chainhash2_asan (ASAN)"
    ./test_chainhash2_asan
    if [ -e /usr/lib/libgmalloc.dylib ]; then
        echo "== running test_chainhash2 under Guard Malloc"
        DYLD_INSERT_LIBRARIES=/usr/lib/libgmalloc.dylib MallocGuardEdges=1 ./test_chainhash2
    fi
fi
