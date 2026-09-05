# adversarial experiments: determ (threads=12, log2 trials=28 for heuristic hashes, 26 for proven ones)

## Deterministic (seed-independent) constructions

Each construction exploits PUBLIC constants (default secret / primes) or seed-independent combining.
Collision counts are over random seeds; a rate of 1 means the pair collides for every seed.

**wyhash/rapidhash: two otherwise-random 32-byte messages whose word at offset len-16 equals secret[1] = 0x8bb84b93962eacc9 (final a^secret[1] = 0 annihilates the last multiplication)** (len 32)

| hash | collisions / trials |
|---|---|
| Paper GF(2^64) [proven] | 0 / 2^24 |
| Paper Mersenne 2^61-1 [proven] | 0 / 2^24 |
| Vector multiply-shift [proven] | 0 / 2^24 |
| Paper recurrence + MUM fold (xor) | 0 / 2^20 |
| Paper recurrence + MUM fold (add) | 0 / 2^20 |
| wyhash 4.3 (default secret) | 1048572 / 2^20 = 2^-0.0 |
| wyhash 4.3 (random secret) | 0 / 2^20 |
| rapidhash v1 (default secret) | 1048572 / 2^20 = 2^-0.0 |
| rapidhash v1 (random secret) | 0 / 2^20 |
| MUM v3 (unroll 8, x86-64 default) | 0 / 2^20 |
| MUM v3 (unroll 16, aarch64 default) | 0 / 2^20 |
| XXH3-64 (seed 0) | 0 / 2^20 |
| XXH3-64 (random seed) | 0 / 2^20 |

**same at 160 bytes (three-lane path): word at offset 144 equals secret[1]** (len 160)

| hash | collisions / trials |
|---|---|
| Paper GF(2^64) [proven] | 0 / 2^24 |
| Paper Mersenne 2^61-1 [proven] | 0 / 2^24 |
| Vector multiply-shift [proven] | 0 / 2^24 |
| Paper recurrence + MUM fold (xor) | 0 / 2^20 |
| Paper recurrence + MUM fold (add) | 0 / 2^20 |
| wyhash 4.3 (default secret) | 1048572 / 2^20 = 2^-0.0 |
| wyhash 4.3 (random secret) | 0 / 2^20 |
| rapidhash v1 (default secret) | 1048572 / 2^20 = 2^-0.0 |
| rapidhash v1 (random secret) | 0 / 2^20 |
| MUM v3 (unroll 8, x86-64 default) | 0 / 2^20 |
| MUM v3 (unroll 16, aarch64 default) | 0 / 2^20 |
| XXH3-64 (seed 0) | 0 / 2^20 |
| XXH3-64 (random seed) | 0 / 2^20 |

**wyhash: w0 = secret[1] zeroes the block state (_wymix(0, .) = 0); messages differ only in w1** (len 32)

| hash | collisions / trials |
|---|---|
| Paper GF(2^64) [proven] | 0 / 2^24 |
| Paper Mersenne 2^61-1 [proven] | 0 / 2^24 |
| Vector multiply-shift [proven] | 0 / 2^24 |
| Paper recurrence + MUM fold (xor) | 0 / 2^20 |
| Paper recurrence + MUM fold (add) | 0 / 2^20 |
| wyhash 4.3 (default secret) | 1048572 / 2^20 = 2^-0.0 |
| wyhash 4.3 (random secret) | 0 / 2^20 |
| rapidhash v1 (default secret) | 0 / 2^20 |
| rapidhash v1 (random secret) | 0 / 2^20 |
| MUM v3 (unroll 8, x86-64 default) | 524788 / 2^20 = 2^-1.0 |
| MUM v3 (unroll 16, aarch64 default) | 524788 / 2^20 = 2^-1.0 |
| XXH3-64 (seed 0) | 0 / 2^20 |
| XXH3-64 (random seed) | 0 / 2^20 |

**rapidhash: w0 = secret[2] zeroes the block state; messages differ only in w1** (len 32)

| hash | collisions / trials |
|---|---|
| Paper GF(2^64) [proven] | 0 / 2^24 |
| Paper Mersenne 2^61-1 [proven] | 0 / 2^24 |
| Vector multiply-shift [proven] | 0 / 2^24 |
| Paper recurrence + MUM fold (xor) | 0 / 2^20 |
| Paper recurrence + MUM fold (add) | 0 / 2^20 |
| wyhash 4.3 (default secret) | 0 / 2^20 |
| wyhash 4.3 (random secret) | 0 / 2^20 |
| rapidhash v1 (default secret) | 1048572 / 2^20 = 2^-0.0 |
| rapidhash v1 (random secret) | 0 / 2^20 |
| MUM v3 (unroll 8, x86-64 default) | 0 / 2^20 |
| MUM v3 (unroll 16, aarch64 default) | 0 / 2^20 |
| XXH3-64 (seed 0) | 0 / 2^20 |
| XXH3-64 (random seed) | 0 / 2^20 |

**XXH3: w0 = kSecret[0..8] = 0xbe4ba423396cfeb8 makes mix16B(chunk 0) = 0 for seed 0; messages differ only in w1** (len 32)

| hash | collisions / trials |
|---|---|
| Paper GF(2^64) [proven] | 0 / 2^24 |
| Paper Mersenne 2^61-1 [proven] | 0 / 2^24 |
| Vector multiply-shift [proven] | 0 / 2^24 |
| Paper recurrence + MUM fold (xor) | 0 / 2^20 |
| Paper recurrence + MUM fold (add) | 0 / 2^20 |
| wyhash 4.3 (default secret) | 0 / 2^20 |
| wyhash 4.3 (random secret) | 0 / 2^20 |
| rapidhash v1 (default secret) | 0 / 2^20 |
| rapidhash v1 (random secret) | 0 / 2^20 |
| MUM v3 (unroll 8, x86-64 default) | 523975 / 2^20 = 2^-1.0 |
| MUM v3 (unroll 16, aarch64 default) | 523975 / 2^20 = 2^-1.0 |
| XXH3-64 (seed 0) | 1048572 / 2^20 = 2^-0.0 |
| XXH3-64 (random seed) | 0 / 2^20 |

MUM single-word term: cached Brent-rho collision on f(w) = _mum(w, primes[1]) (found at ~2^37 evaluations; ADV_RHO=search to reproduce): w=0a3c39b967d06be6, w'=f3c66c5c0a025090, f(w)=27bd44e2a2aeee95, f(w')=27bd44e2a2aeee95 (equal, verified).

**MUM: 32-byte messages differing only in w1 by the rho-found pair (term _mum(w1, primes[1]) identical)** (len 32)

| hash | collisions / trials |
|---|---|
| Paper GF(2^64) [proven] | 0 / 2^24 |
| Paper Mersenne 2^61-1 [proven] | 0 / 2^24 |
| Vector multiply-shift [proven] | 0 / 2^24 |
| Paper recurrence + MUM fold (xor) | 0 / 2^20 |
| Paper recurrence + MUM fold (add) | 0 / 2^20 |
| wyhash 4.3 (default secret) | 0 / 2^20 |
| wyhash 4.3 (random secret) | 0 / 2^20 |
| rapidhash v1 (default secret) | 0 / 2^20 |
| rapidhash v1 (random secret) | 0 / 2^20 |
| MUM v3 (unroll 8, x86-64 default) | 1048572 / 2^20 = 2^-0.0 |
| MUM v3 (unroll 16, aarch64 default) | 1048572 / 2^20 = 2^-0.0 |
| XXH3-64 (seed 0) | 0 / 2^20 |
| XXH3-64 (random seed) | 0 / 2^20 |

MUM paired-word term (len > 8*UNROLL bytes): complementing both words of a pair leaves _mum(w0^p0, w1^p1) unchanged for 43608 / 65536 = 0.6654 random word pairs (deterministic: each pair either always or never collides).

**MUM: 160-byte messages with (w0,w1) complemented (a base for which the pair term coincides; unroll 16 uses the paired path only for len > 128, unroll 8 for len > 64)** (len 160)

| hash | collisions / trials |
|---|---|
| Paper GF(2^64) [proven] | 0 / 2^24 |
| Paper Mersenne 2^61-1 [proven] | 0 / 2^24 |
| Vector multiply-shift [proven] | 0 / 2^24 |
| Paper recurrence + MUM fold (xor) | 0 / 2^20 |
| Paper recurrence + MUM fold (add) | 0 / 2^20 |
| wyhash 4.3 (default secret) | 0 / 2^20 |
| wyhash 4.3 (random secret) | 0 / 2^20 |
| rapidhash v1 (default secret) | 0 / 2^20 |
| rapidhash v1 (random secret) | 0 / 2^20 |
| MUM v3 (unroll 8, x86-64 default) | 1048572 / 2^20 = 2^-0.0 |
| MUM v3 (unroll 16, aarch64 default) | 1048572 / 2^20 = 2^-0.0 |
| XXH3-64 (seed 0) | 0 / 2^20 |
| XXH3-64 (random seed) | 0 / 2^20 |

### Blocking sets: K messages, fraction of the K(K-1)/2 pairs that collide, averaged over S seeds

| construction | hash | K | S | colliding-pair fraction |
|---|---|---|---|---|
| 32-byte, w2 = secret[1], rest random | wyhash 4.3 (default secret) | 256 | 1020 | 1.000000 |
| 32-byte, w2 = secret[1], rest random | wyhash 4.3 (random secret) | 256 | 1020 | 0.000000 |
| 32-byte, w2 = secret[1], rest random | rapidhash v1 (default secret) | 256 | 1020 | 1.000000 |
| 32-byte, w2 = secret[1], rest random | rapidhash v1 (random secret) | 256 | 1020 | 0.000000 |
| 32-byte, w2 = secret[1], rest random | Paper GF(2^64) [proven] | 256 | 1020 | 0.000000 |
| 32-byte, w2 = secret[1], rest random | Paper Mersenne 2^61-1 [proven] | 256 | 1020 | 0.000000 |
| 32-byte, w2 = secret[1], rest random | Vector multiply-shift [proven] | 256 | 1020 | 0.000000 |
| 32-byte, w0 = kSecret[0..8], w2,w3 fixed, vary w1 | XXH3-64 (seed 0) | 256 | 1020 | 1.000000 |
| 32-byte, w0 = kSecret[0..8], w2,w3 fixed, vary w1 | XXH3-64 (random seed) | 256 | 1020 | 0.000000 |
| 32-byte, w0 = kSecret[0..8], w2,w3 fixed, vary w1 | Paper GF(2^64) [proven] | 256 | 1020 | 0.000000 |
| 160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63 | MUM v3 (unroll 8, x86-64 default) | 64 | 1020 | 1.000000 |
| 160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63 | MUM v3 (unroll 16, aarch64 default) | 64 | 1020 | 1.000000 |
| 160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63 | Paper GF(2^64) [proven] | 64 | 1020 | 0.000000 |
| 160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63 | Paper Mersenne 2^61-1 [proven] | 64 | 1020 | 0.000000 |
| 160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63 | Vector multiply-shift [proven] | 64 | 1020 | 0.000000 |
| control: 256 random 32-byte messages | wyhash 4.3 (default secret) | 256 | 1020 | 0.000000 |
| control: 256 random 32-byte messages | MUM v3 (unroll 8, x86-64 default) | 256 | 1020 | 0.000000 |
| control: 256 random 32-byte messages | Paper GF(2^64) [proven] | 256 | 1020 | 0.000000 |
