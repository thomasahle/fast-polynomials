# aHash 0.8.10 — vendored faithful port

Faithful C/C++ port of **aHash 0.8.10** (the hardware-AES path), for the
adversarial-collision benchmark in `tools/bench/adversarial/`.

- Upstream: https://github.com/tkaitchuck/aHash
- Version: **0.8.10** (crates.io tarball SHA-256
  `8b79b82693f705137f8fb9b37871d99e4f9a7df12b917eed79c3d3954830a60b`)
- License: MIT OR Apache-2.0 (see `LICENSE-MIT`)
- Type: **heuristic** hash — **no proven collision bound** (report "none").

## Files
- `ahash.h` — the port. Everything lives in namespace `ahash_0810`.
- `selftest.cpp` — validation (see below).
- `reference-rust/` — the verbatim upstream Rust sources that were transcribed
  (from the published 0.8.10 crate; byte-identical to the git `v0.8.10` tag for
  every hashing file). `cbindings_lib.rs` is the crate's own C entry point.

## What is reproduced
The crate's own C binding `smhasher/ahash-cbindings/src/lib.rs`:
```rust
pub extern "C" fn ahash64(buf, len, seed: u64) -> u64 {
    let bh = RandomState::with_seeds(seed, seed, seed, seed);
    bh.hash_one(&buf)          // that crate sets default-features = false => specialize OFF
}
```
With `specialize` off this is exactly:
`AHasher::from_random_state(rs)` → `write_usize(len)` → `write(buf)` → `finish()`.

`ahash_0810::ahash64(p, len, seed)` implements this line for line.

## Platform note (this matters for faithfulness)
aHash's internal `shuffle` is **not** platform-independent:
- x86/x86-64 (ssse3): `_mm_shuffle_epi8(a, SHUFFLE_MASK)`
- everything else (incl. aarch64): `a.swap_bytes()` (full 16-byte reverse)

so the aHash *output differs between x86 and ARM*. The port selects the same
branch as the crate for whatever arch it is compiled on, so it byte-matches the
real crate **built for that same arch**. The `aesenc`/`aesdec` rounds are
mathematically identical across x86 (`_mm_aesenc`/`_mm_aesdec`) and ARM
(`vaesmcq_u8(vaeseq_u8(.,0)) ^ k` / `vaesimcq_u8(vaesdq_u8(.,0)) ^ k`); only
`shuffle` differs. The ARM path corresponds to the crate's `nightly-arm-aes`
feature (which routes aarch64 through `src/aes_hash.rs` instead of the scalar
fallback).

## Validation — VALIDATED byte-for-byte
`selftest.cpp` checks 155 `(seed, length)` cases whose expected outputs were
produced by **building and running the real aHash 0.8.10 crate on this same
aarch64 machine** (`features = ["nightly-arm-aes"]`,
`RUSTFLAGS="-C target-cpu=native"`, replicating `ahash64`). Lengths cover every
code path (0,1,…,8,9,15,16,17,…,32,33,…,64,65,80,…,128,129,…,1000). It also
anchors the AES round to the official **FIPS-197** AES-128 known-answer.

```
clang++ -O3 -std=c++17 -march=native selftest.cpp -o selftest && ./selftest
# FIPS-197 AES round KAT: OK
# aHash 0.8.10 gold vectors: 155/155 matched
# SELFTEST PASSED (0 failures)
```

(The reference build used a one-line patch to the crate's `lib.rs` removing the
now-obsolete `#![cfg_attr(feature="nightly-arm-aes",
feature(stdarch_arm_neon_intrinsics))]` attribute — those NEON AES intrinsics
are stable on current toolchains. The hashing algorithm is untouched; the patch
only removes a compiler feature-gate.)

## How to call it from the harness (hashes.h)
```cpp
#include "vendor/ahash/ahash.h"

struct Ahash {
    static constexpr const char* name = "aHash (random seed)";
    uint64_t sd;
    void seed(Rng& r) { sd = r.next(); }
    uint64_t operator()(const uint8_t* p, size_t len) const {
        return ahash_0810::ahash64(p, len, sd);
    }
};
```
`ahash64` and its callees carry `__attribute__((target("aes")))` (and `ssse3`
on x86), so this compiles under `-march=native` on Apple clang just like the
existing GF(2^64) code in `hashes.h`. The harness `operator()` needs no target
attribute. No collision bound: aHash is heuristic.
