CXX ?= clang++
CXXFLAGS ?= -O3 -std=c++17 -march=native

all: selftest fold_search adversarial

selftest: selftest.cpp hashes.h
	$(CXX) $(CXXFLAGS) selftest.cpp -o selftest

fold_search: fold_search.cpp hashes.h
	$(CXX) $(CXXFLAGS) fold_search.cpp -o fold_search

adversarial: adversarial.cpp hashes.h
	$(CXX) $(CXXFLAGS) adversarial.cpp -o adversarial

# Reproduce every table in notes/smhasher_adversarial.md (about 15 minutes on 12 cores).
# THREADS and LT (log2 trials) can be overridden, e.g.  make results THREADS=8
THREADS ?= 12
results: all
	./selftest
	./fold_search $(THREADS) 34 > results_fold.md
	./adversarial random $(THREADS) 30 > results_random.md
	./adversarial scan   $(THREADS) 29 > results_scan.md
	./adversarial determ $(THREADS) 28 > results_determ.md
	./run_length.sh $(THREADS) 31 > run_length.log 2>&1

clean:
	rm -f selftest fold_search adversarial

# ---------------------------------------------------------------------------
# Throughput harness (speed.cpp + speed_hashes.h).  The C++ TU needs the CPU's
# crypto features for the framework's PMULL intrinsics: on Apple clang
# -march=native does NOT enable them, -mcpu=native does (x86: -march=native).
# UMASH is vendored verbatim and built as its own C translation unit.
# XXH3 comes from the system xxhash.h (brew install xxhash).
# Runs need the framework's random-bytes file (bytes1.bin) in the cwd.
CC ?= clang
XXH_INC ?= /opt/homebrew/include
SPEED_CXXFLAGS ?= -O3 -std=c++17 -mcpu=native -I$(XXH_INC)

umash_impl.o: vendor/umash/umash_impl.c vendor/umash/umash.c vendor/umash/umash.h vendor/umash/umash_long.inc
	$(CC) -O3 -std=c11 -march=native -c vendor/umash/umash_impl.c -o umash_impl.o

speed: speed.cpp speed_hashes.h hashes.h umash_impl.o ../framework/multiplication_arm.h ../framework/injective_hashing_arm.h ../chainhash/chainhash.h vendor/polymur/polymur-hash.h vendor/komihash/komihash.h vendor/umash/umash.h
	$(CXX) $(SPEED_CXXFLAGS) speed.cpp umash_impl.o -o speed

# usage: ./speed [runs] [seconds-per-run] [selftest]   -> JSON lines on stdout
speed_results.jsonl: speed
	ln -sf ../bytes1.bin bytes1.bin
	./speed 15 0.1 > speed_results.jsonl
