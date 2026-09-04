# adversarial experiments: length (threads=12, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w0 xor M & w1 xor M' at several message lengths

| hash | 32 B | 48 B | 64 B | 96 B | 160 B |
|---|---|---|---|---|---|
| Paper recurrence + MUM fold (xor) | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 |
| wyhash 4.3 (default secret) | 25 / 2^31 = 2^-26.4 | 16 / 2^31 = 2^-27.0 | 26 / 2^31 = 2^-26.3 | 21 / 2^31 = 2^-26.6 | 18 / 2^31 = 2^-26.8 |
| wyhash 4.3 (random secret) | 21 / 2^31 = 2^-26.6 | 20 / 2^31 = 2^-26.7 | 27 / 2^31 = 2^-26.2 | 21 / 2^31 = 2^-26.6 | 25 / 2^31 = 2^-26.4 |
| rapidhash v1 (default secret) | 23 / 2^31 = 2^-26.5 | 19 / 2^31 = 2^-26.8 | 17 / 2^31 = 2^-26.9 | 10 / 2^31 = 2^-27.7 | 22 / 2^31 = 2^-26.5 |
| rapidhash v1 (random secret) | 24 / 2^31 = 2^-26.4 | 22 / 2^31 = 2^-26.5 | 22 / 2^31 = 2^-26.5 | 28 / 2^31 = 2^-26.2 | 18 / 2^31 = 2^-26.8 |
| XXH3-64 (seed 0) | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 | 0 / 2^31 |
| XXH3-64 (random seed) | 26 / 2^31 = 2^-26.3 | 36 / 2^31 = 2^-25.8 | 29 / 2^31 = 2^-26.1 | 27 / 2^31 = 2^-26.2 | 27 / 2^31 = 2^-26.2 |

## Paper recurrence + MUM fold (xor): complement the LAST b-word, per length (precision runs)

# adversarial experiments: pair (threads=12, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w3 xor M' at 32 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 11 / 2^31 = 2^-27.5 |
# adversarial experiments: pair (threads=12, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w5 xor M' at 48 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 20 / 2^31 = 2^-26.7 |
# adversarial experiments: pair (threads=12, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w7 xor M' at 64 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 15 / 2^31 = 2^-27.1 |
# adversarial experiments: pair (threads=12, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w11 xor M' at 96 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 13 / 2^31 = 2^-27.3 |
# adversarial experiments: pair (threads=12, log2 trials=31 for heuristic hashes, 29 for proven ones)

## Differential 'w19 xor M' at 160 bytes (precision run)

| hash | collisions / trials |
|---|---|
| Paper recurrence + MUM fold (xor) | 15 / 2^31 = 2^-27.1 |
