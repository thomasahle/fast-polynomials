#!/bin/bash
# Build (and run) the ChainHash tests.  arm64 / Apple Silicon only.
#   ./build.sh          build both binaries and run: -O3, ASAN, -O3 under Guard Malloc
#   ./build.sh build    build only
#
# Notes:
#  * Apple clang: plain -march=native does not enable the PMULL ('aes')
#    feature, hence -march=native+crypto.
#  * Apple clang 17's ASAN runtime deadlocks at process start on macOS 26
#    (Darwin 25.6): AsanInitInternal -> InitializeShadowMemory -> get_dyld_hdr
#    -> _Block_copy -> malloc -> AsanInitFromRtl, spinning forever -- even for
#    a hello-world.  The ASAN binary is therefore built with Homebrew LLVM
#    when available (ASAN_CXX overrides).  Apple's Guard Malloc
#    (libgmalloc.dylib, guard page after every heap allocation) is run as an
#    independent over-read check on the -O3 binary.
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

echo "== building test_chainhash (-O3) with $CXX"
$CXX -O3 $FLAGS test_chainhash.cpp -o test_chainhash
echo "== building test_chainhash_asan (-O2 -fsanitize=address) with $ASAN_CXX"
$ASAN_CXX -O2 -g -fsanitize=address -fno-omit-frame-pointer $FLAGS test_chainhash.cpp -o test_chainhash_asan

if [ "$1" != "build" ]; then
    echo "== running test_chainhash (-O3)"
    ./test_chainhash
    echo "== running test_chainhash_asan (ASAN)"
    ./test_chainhash_asan
    if [ -e /usr/lib/libgmalloc.dylib ]; then
        echo "== running test_chainhash under Guard Malloc"
        DYLD_INSERT_LIBRARIES=/usr/lib/libgmalloc.dylib MallocGuardEdges=1 ./test_chainhash
    fi
fi
