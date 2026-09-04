#!/bin/bash
# Length-scaling runs. Output concatenated to results_length.md.
set -e
cd "$(dirname "$0")"
T=${1:-12}; L=${2:-31}
out=results_length.md
: > "$out"
# (M,M) on the first fold: complement words 0 and 1.  For wyhash/rapidhash the
# first mixing step is _wymix(w0^secret, w1^state); for XXH3 it is mix16B of the
# first 16-byte chunk; both are a single (M,M) fold, so the induced collision
# rate should be ~2^-27 and independent of the message length.
./adversarial length "$T" "$L" xorM 0,1 wyhash rapidhash XXH3 "MUM fold (xor)" >> "$out"
# Last-b differential for the paper's MUM-fold recurrence: complement the last
# b-word (index len/8-1).  This is (M,0) on the recurrence's final fold, so the
# collision rate should again be ~2^-27 regardless of the number of blocks.
{
  echo ""
  echo "## Paper recurrence + MUM fold (xor): complement the LAST b-word, per length (precision runs)"
  echo ""
} >> "$out"
for pair in "3 32" "5 48" "7 64" "11 96" "19 160"; do
  set -- $pair
  ./adversarial pair "$T" "$L" xorM "$1" "$2" "MUM fold (xor)" >> "$out"
done
echo "run_length.sh done"
