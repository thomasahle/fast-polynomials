# adversarial experiments: length (threads=16, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w0 xor M & w1 xor M' at several message lengths

| hash | 32 B | 48 B | 64 B | 96 B | 160 B |
|---|---|---|---|---|---|
| Paper recurrence + MUM fold (xor) | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 |
| wyhash 4.3 (default secret) | 28 / 2^31 = 2^-26.2 | 18 / 2^31 = 2^-26.8 | 26 / 2^31 = 2^-26.3 | 21 / 2^31 = 2^-26.6 | 19 / 2^31 = 2^-26.8 |
| wyhash 4.3 (random secret) | 22 / 2^31 = 2^-26.5 | 16 / 2^31 = 2^-27.0 | 23 / 2^31 = 2^-26.5 | 20 / 2^31 = 2^-26.7 | 28 / 2^31 = 2^-26.2 |
| rapidhash v1 (default secret) | 21 / 2^31 = 2^-26.6 | 17 / 2^31 = 2^-26.9 | 19 / 2^31 = 2^-26.8 | 11 / 2^31 = 2^-27.5 | 17 / 2^31 = 2^-26.9 |
| rapidhash v1 (random secret) | 25 / 2^31 = 2^-26.4 | 22 / 2^31 = 2^-26.5 | 24 / 2^31 = 2^-26.4 | 26 / 2^31 = 2^-26.3 | 24 / 2^31 = 2^-26.4 |
| XXH3-64 (seed 0) | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 |
| XXH3-64 (random seed) | 32 / 2^31 = 2^-26.0 | 39 / 2^31 = 2^-25.7 | 25 / 2^31 = 2^-26.4 | 27 / 2^31 = 2^-26.2 | 32 / 2^31 = 2^-26.0 |

## Paper recurrence + MUM fold (xor): complement the LAST b-word, per length (precision runs)

# adversarial experiments: pair (threads=16, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w3 xor M' at 32 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 14 / 2^31 = 2^-27.2 |
# adversarial experiments: pair (threads=16, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w5 xor M' at 48 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 18 / 2^31 = 2^-26.8 |
# adversarial experiments: pair (threads=16, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w7 xor M' at 64 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 15 / 2^31 = 2^-27.1 |
# adversarial experiments: pair (threads=16, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w11 xor M' at 96 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 13 / 2^31 = 2^-27.3 |
# adversarial experiments: pair (threads=16, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w19 xor M' at 160 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 17 / 2^31 = 2^-26.9 |
