#!/bin/bash
# Assemble out/*.txt into one table ordered header / variant / length / pair
D=/private/tmp/claude-501/-Users-ahle-repos-notes-fast-polyhash/671fdc97-fe99-4719-bea0-4eedf88d5744/scratchpad/xxh_latest
echo "header           | variant                  |  len | pair | collisions / trials | log2 rate"
for h in homebrew v0.8.3 dev; do
  for v in seed64 seed128 secret64 secret128; do
    for l in 32 48 64 100 128 160; do grep -h '^[a-z0-9.]* *|' $D/out/${h}_${v}_${l}.txt 2>/dev/null; done
  done
  grep -h 'fold' $D/out/${h}_fold.txt 2>/dev/null
done
