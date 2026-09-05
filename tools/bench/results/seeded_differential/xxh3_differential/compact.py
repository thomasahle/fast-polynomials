#!/usr/bin/env python3
"""Compact per-(header, variant, length) table: A/B/C collision counts per 2^30 and log2 rates."""
import os, re, math, glob
D = os.path.dirname(os.path.abspath(__file__)); OUT = os.path.join(D, "out")
def lg(c): return "2^%.1f" % math.log2(c / 2**30) if c else "0"
def parse(prefix):
    rows = {}
    for p in glob.glob(os.path.join(OUT, prefix + "_*_*.txt")):
        for line in open(p):
            m = re.match(r"^\S+\s*\| (XXH3_\S+)\s*\|\s*(\d+) \| ([ABC])\s*\|\s*(\d+) / 2\^30", line)
            if m: rows.setdefault((m.group(1), int(m.group(2))), {})[m.group(3)] = int(m.group(4))
    return rows
order = ["XXH3_64bits_withSeed", "XXH3_128bits_withSeed", "XXH3_64bits_withSecret", "XXH3_128bits_withSecret"]
print("header (rng)     | variant                  | len | A: coll/2^30 (log2) | B: coll/2^30 (log2) | C: coll/2^30 (log2)")
hb_same = parse("homebrew") == parse("v0.8.3")
for label, prefix in (("v0.8.3 (rng 1)", "v0.8.3"), ("dev (rng 2)", "devs2")):
    rows = parse(prefix)
    for v in order:
        tot = {"A": 0, "B": 0, "C": 0}
        for l in (32, 48, 64, 100, 128, 160):
            r = rows.get((v, l))
            if not r: print(f"{label:16} | {v:24} | {l:3} | MISSING"); continue
            for k in tot: tot[k] += r[k]
            print(f"{label:16} | {v:24} | {l:3} | " + " | ".join(f"{r[k]:4d} ({lg(r[k]):>7})" for k in "ABC"))
        n = 6 * 2**30
        print(f"{label:16} | {v:24} | sum | " + " | ".join(f"{tot[k]:4d} (2^{math.log2(tot[k]/n):.1f})" if tot[k] else f"{0:4d} (0)" for k in "ABC"))
print(f"homebrew 0.8.3 header (rng 1), 72 cells: {'identical count-for-count to the v0.8.3 (rng 1) rows above' if hb_same else 'DIFFERS from v0.8.3 rows'} (same bytes, same RNG stream)")
print("dev (rng 1) replay, 72 cells: " + ("identical to v0.8.3 (rng 1)" if parse("dev") == parse("v0.8.3") else "DIFFERS from v0.8.3 (rng 1)"))
print()
print("fold-only (no XXH3 call), uniform random a,b; identical on all three headers:")
for p in sorted(glob.glob(os.path.join(OUT, "v0.8.3_fold*.txt"))):
    for line in open(p):
        if "mul128" in line: print("  " + re.sub(r"^\S+\s*\| ", "", line.rstrip()))
print("outlier re-test (v0.8.3, XXH3_64bits_withSeed, len 128, same pair as rng 1, fresh trial streams):")
for p in sorted(glob.glob(os.path.join(OUT, "outlier_*.txt"))):
    for line in open(p):
        if "| C" in line: print("  " + os.path.basename(p) + ": " + re.sub(r"^\S+\s*\| ", "", line.rstrip()))
