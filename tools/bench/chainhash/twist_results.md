# Finalizer degree and the additive twist: SMHasher3 measurements (Apple M2 Pro, 2026-09-03)

Full SMHasher3 suite (fork with the seeded-differential test), 256-byte blocks, one pair per block.
"twist" = 64-bit integer addition of a key word to the finalizer input (see chainhash.h).

| finalizer | products | result | small keys, 1-31 B (cycles/hash) |
|---|---|---|---|
| degree 7 (previous)      | 4 | pass 200/200 | 95.7 |
| degree 5, no twist       | 3 | FAIL 178/200 | 82.0 |
| degree 5 + input twist   | 3 | pass 200/200 | 81.8 |
| degree 5 + in/out twists | 3 | pass 200/200 | 83.2 |
| degree 3 + input twist   | 2 | FAIL 183/200 | 66.5 |
| degree 3 + in/out twists | 2 | FAIL 183/200 | 67.4 |

The failing tests for the untwisted degree-5 and the degree-3 variants are the fixed-seed window
tests (Zeroes, Sparse, Permutation, TwoBytes, Bitflip, SeedZeroes). The shipped hash is
degree 5 + input twist; its final full-suite logs on the M2 Pro and on an Intel Xeon 8375C
(both 200/200) accompany the SMHasher3 merge request. Reproduce with the registrations of
hashes/chainhash.cpp in the SMHasher3 fork; the experiment file with all six variants is
kept in the author's notes (chainhash_exp.cpp).
