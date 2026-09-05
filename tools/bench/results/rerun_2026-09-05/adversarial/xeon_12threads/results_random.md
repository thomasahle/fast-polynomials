# adversarial experiments: random (threads=12, log2 trials=30 for heuristic hashes, 28 for proven ones)

## Random-input control

Two uniformly random messages of the given length and a fresh random seed/key per trial.

| hash | len (bytes) | collisions / trials |
|---|---|---|
| Paper GF(2^64) [proven] | 32 | 0 / 2^28 |
| Paper GF(2^64) [proven] | 160 | 0 / 2^28 |
| Paper Mersenne 2^61-1 [proven] | 32 | 0 / 2^28 |
| Paper Mersenne 2^61-1 [proven] | 160 | 0 / 2^28 |
| Vector multiply-shift [proven] | 32 | 0 / 2^28 |
| Vector multiply-shift [proven] | 160 | 0 / 2^28 |
| Paper recurrence + MUM fold (xor) | 32 | 0 / 2^30 |
| Paper recurrence + MUM fold (xor) | 160 | 0 / 2^30 |
| Paper recurrence + MUM fold (add) | 32 | 0 / 2^30 |
| Paper recurrence + MUM fold (add) | 160 | 0 / 2^30 |
| wyhash 4.3 (default secret) | 32 | 0 / 2^30 |
| wyhash 4.3 (default secret) | 160 | 0 / 2^30 |
| wyhash 4.3 (random secret) | 32 | 0 / 2^30 |
| wyhash 4.3 (random secret) | 160 | 0 / 2^30 |
| rapidhash v1 (default secret) | 32 | 0 / 2^30 |
| rapidhash v1 (default secret) | 160 | 0 / 2^30 |
| rapidhash v1 (random secret) | 32 | 0 / 2^30 |
| rapidhash v1 (random secret) | 160 | 0 / 2^30 |
| MUM v3 (unroll 8, x86-64 default) | 32 | 0 / 2^30 |
| MUM v3 (unroll 8, x86-64 default) | 160 | 0 / 2^30 |
| MUM v3 (unroll 16, aarch64 default) | 32 | 0 / 2^30 |
| MUM v3 (unroll 16, aarch64 default) | 160 | 0 / 2^30 |
| XXH3-64 (seed 0) | 32 | 0 / 2^30 |
| XXH3-64 (seed 0) | 160 | 0 / 2^30 |
| XXH3-64 (random seed) | 32 | 0 / 2^30 |
| XXH3-64 (random seed) | 160 | 0 / 2^30 |
