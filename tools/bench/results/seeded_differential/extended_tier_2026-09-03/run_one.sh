#!/bin/bash
# usage: run_one.sh <hashname>
S=/private/tmp/claude-501/-Users-ahle-repos-notes-fast-polyhash/671fdc97-fe99-4719-bea0-4eedf88d5744/scratchpad/sd_runs
name="$1"
out="$S/sd_${name}.txt"
cd /Users/ahle/repos/smhasher3/build-advtest || exit 1
{ echo "CMD: ./SMHasher3 $name --test=SeedDifferential --extra"; /usr/bin/time -p ./SMHasher3 "$name" --test=SeedDifferential --extra; echo "EXIT $?"; } > "$out" 2>&1
