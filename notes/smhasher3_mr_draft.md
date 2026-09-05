# Draft merge request for gitlab.com/fwojcik/smhasher3 (NOT submitted)

Two independent contributions from the same branch; they can be split into two MRs.

---

## MR 1 — Add ChainHash, a provably universal / 5-independent 64-bit hash

**Files:** `hashes/chainhash.cpp` (new), `hashes/Hashsrc.cmake` (+1 line).

ChainHash is the hash function from the paper *Fast Evaluation of Polynomials with
Rational Preprocessing* (T. D. Ahle, preprint 2026). It is a three-level composition, every
level with a proof:

1. **Block level:** carry-less NH over blocks of B bytes (one PMULL/PCLMULQDQ per 16 bytes into
   unreduced 128-bit accumulators), the block sum consumed as one field-element pair (a, b).
   The four words of every 32-byte group are paired *strided*, (w0, w2) and (w1, w3), each word
   XORed with the key word of its own position: the pairing that two 16-byte vector loads feed to
   PMULL/PMULL2 without a shuffle (the same function as adjacent pairing up to a fixed permutation
   of the word positions, applied to key and data alike). The last group is zero-padded to 32
   bytes, and the byte length is XORed into *both* halves (a and b) of the last pair.
   XOR-universal with probability 2^-64 (Lemire–Kaser; with the length in both halves the stream
   lemma's constant is (l + l')(1 + X^64), nonzero iff l != l').
2. **Chain level:** the paper's injective polynomial recurrence over GF(2^64),
   P_0 = z, P_i = a_i + (b_i + y)(P_{i-1} + u), with three independent 64-bit keys.
   One field multiplication per pair; distinct pair streams give distinct polynomials of total
   degree ≤ p in (u, y, z), so two messages collide at this level with probability ≤ p / 2^64
   (p = number of pairs). This is half of Horner's count and half of Horner's bound.
3. **Finalizer:** a monic degree-5 polynomial with uniformly random coefficients, evaluated by
   a 3-multiplication characteristic-2 circuit (y = v·v; z = (y+c0)(v+y+c1); t = (v+c2)(z+c3);
   out = t+c4) whose parameter→coefficient map is a bijection over every field of
   characteristic 2 (explicit closed-form decoder, unit pivots only, no square roots; proof in the
   paper's appendix). Gives 5-wise independence of the output, which is the independence linear
   probing provably needs (Pagh–Pagh–Ružić 2009; 4-wise does not suffice, Pătrașcu–Thorup
   2010/2016). The circuit is applied to v = P_n ⊞ t_in, the 64-bit *integer* sum of the chain
   value and one more key word (the "input twist"). No heuristic mixing step anywhere.

Collision probability for two messages of at most p pairs: ≤ (p + 2) / 2^64. The twist is a
bijection of the finalizer input, so it changes neither the bound nor the 5-wise independence.

**Why the twist:** over GF(2^64) squaring is GF(2)-linear, so v^e has GF(2)-degree popcount(e),
every polynomial of degree ≤ 6 is quadratic in the bits of v with affine discrete derivatives, and
SMHasher3's fixed-seed keysets (Zeroes, Sparse, Permutation, TwoBytes, Bitflip, SeedZeroes) detect
exactly that (untwisted degree 5: 178/200). These tests probe algebraic structure that k-wise
independence never needed, so instead of over-provisioning to degree 7 (4 products, 200/200, 95.7
small-key cycles) we insert a cheap bijection whose carry chain makes the composite non-quadratic:
degree 5 + input twist 200/200 at 81.8 cycles (an output twist adds nothing; degree 3 + twist
183/200). The twist's adequacy for the suite is empirical.

**Why the length in both halves:** the CLNH sum of an all-zero message depends only on its group
count, so with the length XORed into a alone the chain value of a zero message is len XOR C over
every run of 32 consecutive lengths (C a constant of the key); the finalizer input then runs
through an XOR-affine set on which the twisted quintic is nearly affine, and the Zeroes keyset's
differential distribution flags it (199/200 for `chainhash-256`, worst bias 2.2x). With the length
in b as well, consecutive lengths differ by a field multiple of the uniformly random
1 + P_{n-1} + u, and both variants pass 200/200. The block loop pays nothing for it; the
loop-free paths for messages of at most one sub-block pay one (`chainhash-256`) or two
(`chainhash-1k`) length-times-key products.

**Variants registered**

| name | block | sub-blocks per block | finalizer degree | resident key |
|---|---|---|---|---|
| `chainhash-256` | 256 B | 1 | 5 | 41 words |
| `chainhash-1k` | 1024 B | 2 | 5 | 137 words |

**Backends:** x86-64 PCLMULQDQ (`hwclmul`, guarded by `HAVE_X86_64_CLMUL`), AArch64 PMULL
(`hwpmull`, needs the AES/crypto target feature — on macOS configure with
`-DCMAKE_CXX_FLAGS="-Xclang -target-feature -Xclang +aes"`, otherwise it falls back), and a
bit-serial portable path. All three produce identical output (checked on 15,000 messages
including byte-swapped/big-endian variants against a bit-serial reference in the paper's
repository).

**Verification codes** (LE / BE): `chainhash-256` 0xAA4E2A3B / 0x11037F6F;
`chainhash-1k` 0x7A1ED2E0 / 0x85B2F299.

**Results (Apple M2 Pro, Apple clang 17, PMULL backend, full suite incl. the new
SeedDifferential test):** both variants pass 200 / 200.
Bulk speed (256 KB keys): 22.2 bytes/cycle (`chainhash-256`), 17.3 bytes/cycle (`chainhash-1k`);
small keys (1–31 B): 72 and 77 cycles/hash (taken at a 1-min load of 3–7; runs of the same code on a
quieter machine gave 71–73 and 71–74; the earlier degree-7 finalizer with the plain loop: 95 and 106).
Independent throughput measurement, single core: 67.7 GB/s and 69.3 GB/s on 16 KB messages
(37.6 and 39.2 GB/s at 512 B).
(The field arithmetic is kept in vector registers: on AArch64 the PMULL/PMULL2 forms are pinned
with two one-line inline-asm wrappers, because clang otherwise lowers a lane-0 x lane-1 product to
DUP + PMULL2 and routes the recurrence state through a general register; on x86-64 the CLMUL
immediate selects the halves directly.)
**Results (x86-64, Intel Xeon Platinum 8375C, clang 21.1.8, PCLMULQDQ backend, full suite incl.
SeedDifferential):** both variants pass 200 / 200; verification codes identical to arm64.
Bulk speed (256 KB keys): 15.4 bytes/cycle (`chainhash-256`), 12.3 bytes/cycle (`chainhash-1k`),
50.0 and 39.9 GiB/s as reported by SMHasher3; small keys (1-31 B): 108 and 109 cycles/hash.
(Shared machine, load average 10–18 during the run, on other cores.)
Both full suites were re-run on both machines after the finalizer change, again after the
implementation optimisations (register-resident block loop, TBL tail loads, peeled last block), and
once more after the strided pairing and the length-in-both-halves change: 200 / 200 everywhere
(`final3_*.txt`, `final4_*.txt` in `notes/handoff_2026-09-04/k5_results/`, `final6_*.txt` in
`tools/bench/results/rerun_2026-09-05/chainhash_strided_v2/` of the paper repository).

**Why two sub-blocks for 1 KB:** with 1 KB blocks a single-block key sees only one
message-dependent multiplication before the finalizer, and raising the finalizer degree alone
(7, 9, 15) still fails two Sparse sub-tests; feeding each block as two sub-block pairs fixes it at
the cost of one extra multiplication per kilobyte.

---

## MR 2 — New test: SeedDifferential (seeded differential collision test)

**Files:** `tests/SeedDifferentialTest.cpp`, `tests/SeedDifferentialTest.h` (new),
`CMakeLists.txt` (+1 source), `main.cpp` (include, option row, invocation).

**What it measures.** For a hash with a random hidden seed, the probability that a *fixed*
pair of attacker-chosen inputs collides, estimated by drawing fresh uniform seeds. An ideal
w-bit hash gives 2^-w for every pair. The pairs are generic structural differentials on
little-endian 64-bit words of a base message whose second word is the complement of the first
(w1 = ~w0):

- `~w0~w1`: complement the first two words (the pair that breaks the multiply-fold of XXH3,
  wyhash and rapidhash, and the 128-bit XXH3 because its second accumulator only sees the raw
  word sum, which w1 = ~w0 keeps invariant);
- `~w0`, `~w1`, `~w2`, `~w3`: single-word complements;
- `~w1~w2`, `~w2~w3`, `~w3~w4`: adjacent interior pairs (MUM's key-free collision).

Lengths 16, 24, 32, 48, 64, 100, 128, 160, 200, 240, 256, 1024 bytes. Default tier: 2^24 seeds
per pair (about 4–8 s per hash at 4 threads; scaled down for SLOW hashes), which detects rates
≥ ~2^-21. `--extra`: 2^30 seeds on the first-fold pairs at 32/64/128/240 B and the adjacent
pairs at 32 B (about a minute per hash), which detects the ~2^-27 rates. A row fails when its
count exceeds max(3, E + 6·sqrt(E)), E = N·2^-w.

**Results (`--extra`, arm64):**

| hash | verdict | worst pair | rate |
|---|---|---|---|
| wyhash / wyhash.strict | FAIL | 240 B, `~w0~w1` | 2^-26.2 / 2^-26.0 |
| rapidhash (+protected, micro, nano) | FAIL | 64–240 B, `~w0~w1` | 2^-26.1 … 2^-26.4 |
| XXH3-64 (+regen) | FAIL | 32–64 B, `~w0~w1` | 2^-25.9 / 2^-26.1 |
| XXH3-128 (+regen) | FAIL | 32–64 B, `~w0~w1` (both halves) | 2^-25.9 / 2^-26.1 |
| MUM v1/v2/v3, all unroll variants | FAIL | adjacent pairs | 2^0 (every seed) |
| komihash, polymurhash, chainhash-256, chainhash-1k, poly-mersenne, SipHash-2-4/1-3, t1ha2-64/128, FarmHash-64, CityHash-64 | PASS | none | < 2^-30 |

These rates were first found and reported for XXH3 in Cyan4973/xxHash issue #1127; the test
makes them visible in SMHasher3's standard output for any hash.

**Default tier over the whole corpus (2^24 seeds, 308 hashes):** 48 fail — every MUM variant (rate 1)
and the deliberately weak entries (donothing*, aesrng*, sum8/32hash, fibonacci*, o1hash, khash,
mir.*, FNV-YoshimitsuTRIAD, CrapWow). wyhash, rapidhash and XXH3 *pass* the default tier: their
~2^-26 rates lie below its ~2^-21 detection threshold and show up only in `--extra` (2^30 seeds),
where they fail as tabulated above.

**Caveats to state in the MR:** rows within one length share the seed set (hash(m) computed
once per seed); `--ncpu` changes the seed partition; SLOW/VERY_SLOW hashes get 2^20 / 2^16
seeds in the default tier and skip the extended tier; `Changelog.md` entry to add.
