#!/usr/bin/env python3
"""Merge one or more speed JSONL passes into bench_results.json.

Per (name,size) row: gbps = max over passes of the per-pass median (each pass's
median is over its `runs` timed runs); the noise is one-sided (contention only
slows a run down), so the best pass-median is the least biased estimate of the
unloaded single-core number.  All pass medians and the global min/max are kept.
"""
import json, sys, collections

passes = sys.argv[1:-1]
out = sys.argv[-1]

FAMILY = [
    ("UMASH", "proven-hybrid"),
    ("clnh_64", "proven-other"),
    ("Vector multiply-shift", "proven-other"),
    ("wyhash", "heuristic"), ("rapidhash", "heuristic"), ("MUM", "heuristic"),
    ("XXH3", "heuristic"), ("komihash", "heuristic"),
]
def family(name):
    for k, f in FAMILY:
        if name.startswith(k): return f
    return "proven-poly"

NOTES = {
    "Paper GF(2^64) injective, sequential":
        "P_i = a_i + (b_i+x^3)(P_{i-1}+x^2) over GF(2^64), one 64-bit key, 16 B/step, 3 dependent PMULL per step (latency-bound); Pr[coll] <= (3N+2)/2^64, N = len/16. Bit-identical to hashes.h PaperGF64 (selftest).",
    "Paper GF(2^64) injective, 2 lanes":
        "Same recurrence on L=2 interleaved lanes, combined as sum_j P_j*y^j with an independent 64-bit key y (Horner); Pr[coll] <= (3N/L+L+2)/2^64. Two 64-bit keys.",
    "Paper GF(2^64) injective, 4 lanes":
        "Same recurrence on L=4 interleaved lanes, combined as sum_j P_j*y^j with an independent 64-bit key y; Pr[coll] <= (3N/L+L+2)/2^64. Two 64-bit keys. Verified against a scalar lane reference (selftest).",
    "Paper GF(2^64) injective, 8 lanes":
        "Same recurrence on L=8 interleaved lanes, combined as sum_j P_j*y^j with an independent 64-bit key y; Pr[coll] <= (3N/L+L+2)/2^64. Two 64-bit keys.",
    "Paper injective over F_{2^89-1} (smart reduction, 15 B/step)":
        "Two-key form P_i = a_i + (b_i+y)(P_{i-1}+x^2) over F_p, p=2^89-1, x uniform in [0,p), y uniform in [0,2^63); a_i 8-byte word, b_i 7-byte word so b_i+y < 2^64 and each step is ONE fast_large_mult_mod(P+x^2, a_i, b_i+y) (2 x 64x64 mul + lazy Mersenne reduction); exact reduction once at the end, low 64 bits output. Degree N+2 in (x,y): Pr[coll] <= (N+2)/2^63 (Schwartz-Zippel, y over 2^63 values) [+ 64-bit truncation of the 89-bit value: x2^25/p factor ~ 1]. Verified vs exact reference (selftest).",
    "Paper injective over F_{2^89-1} (89x89 product, 16 B/step)":
        "Single-key form P_i = a_i + (b_i+x^3)(P_{i-1}+x^2) over F_p, p=2^89-1, 89-bit key; general 89x89 product via framework extra_large_mult_add_mod (4 mul schoolbook, lazy reduction), 8-byte words a_i,b_i; Pr[coll] <= (3N+2)*2^25/p ~ (3N+2)/2^64. Verified vs exact reference (selftest).",
    "Mersenne 2^89-1 Horner, 8-byte words":
        "Classical polynomial hash h = h*x + m_i over F_p, p=2^89-1, 64-bit key x, one fast_large_mult_mod per 8-byte word (2 mul), exact reduction at the end, low 64 bits; Pr[coll] <= (L-1)*2^25/p ~ L/2^64, L = words. Same arithmetic as the paper's Mersenne Horner baseline (fast_hashing_arm.h poly_64).",
    "Mersenne 2^89-1 Horner, 11-byte words":
        "As above with 88-bit (11-byte) message words (< p), same per-step cost, 11 B/step; Pr[coll] ~ L/2^64.",
    "UMASH 64 (umash_full)": "UMASH v2 (backtrace-labs), 64-bit umash_full(params, seed=0, which=0); params from umash_params_derive(bits=0, random 32-byte key); proven collision bound ~ 2^-56 per the UMASH paper (hybrid polynomial/OH). Vendor selftest and README vector pass.",
    "UMASH 128 (umash_fprint)": "UMASH 128-bit fingerprint (both hashes), output folded hash[0]^hash[1] for the sink only; proven ~2^-70 collision bound.",
    "wyhash 4.3 (random secret)": "hashes.h port of wyhash final v4.3 with a random seed and random odd 4-word secret; no proven bound (worst input ~2^-27 in tools/bench/adversarial).",
    "rapidhash v1 (random secret)": "hashes.h port of rapidhash v1.0 with random seed and random odd 3-word secret; no proven bound.",
    "MUM v3 (unroll 8)": "hashes.h port of MUM v3 (default macros), unroll 8 (x86-64 default), random seed; no proven bound (key-free collision exists).",
    "MUM v3 (unroll 16)": "hashes.h port of MUM v3, unroll 16 (aarch64 default), random seed; no proven bound.",
    "XXH3-64 withSeed (random seed)": "Real XXH3_64bits_withSeed from xxhash 0.8.3 (XXH_INLINE_ALL, NEON path); >240-byte inputs derive a per-seed secret inside the call. The hashes.h XXH3 port only covers 9..240 bytes and is NOT used for long inputs.",
    "XXH3-64 withSecret (random 192-byte secret)": "XXH3_64bits_withSecret with a uniformly random 192-byte secret (precomputed), xxhash 0.8.3; no proven bound.",
    "komihash 5.34 (random seed)": "komihash v5.34 header-only, komihash(p,n,seed) with random seed; no proven bound. Vendor selftest (63/63 vectors) passes.",
    "Vector multiply-shift (Dietzfelbinger)": "hashes.h VectorMultShift: ((a_0 + sum a_i w_i) mod 2^128) >> 64, 128-bit random a_i; strongly universal, Pr[coll] <= 2^-64; O(message) key (65 x 128-bit), capped at 64 words = 512 B.",
    "univ_injective_64 (single key)": "Framework class, the paper's injective recurrence with x^3 (single key), inj_smul = framework gf64_mult; message stored in the object (2N words), key = call argument. Output equals PaperGF64Opt on the interleaved message (selftest).",
    "univ_horner_64": "Framework Horner baseline over GF(2^64), 2N-1 multiplications for 2N words, single key.",
    "univ_brw_64": "Framework BRW (Bernstein-Rabin-Winograd) over GF(2^64), ~N/2 mults + log N squarings, recursive implementation, single key; universal (injective polynomial).",
    "univ_c2_decbrw_64": "Framework 2-decimated BRW: 2 interleaved BRW streams combined by Horner with x^d; streams are copied to a stack array before evaluation.",
    "univ_c4_decbrw_64": "Framework 4-decimated BRW: 4 interleaved BRW streams combined by Horner with x^d.",
    "clnh_64": "Framework CLNH (Lemire-Kaser CLHASH inner hash): XOR of N independent products (m_{2i}^x)(m_{2i+1}^x); O(N) key words in the real construction (here the stored array is the message and x the key, as in the framework benchmark); Delta-universal.",
    "horner_unrolled_64": "Framework Horner over GF(2^64) unrolled 4x (Estrin-style grouping), N words, single key.",
    "horner_parallel_64": "Framework Horner via parallel prefix scan (tree reduction with precomputed x^(2^i)), N words, single key; more multiplications, O(log N) depth.",
    "univ_injective_parallel_64 (single key)": "Framework parallel-prefix version of the paper's injective recurrence (transfer-function composition, ~3N mults, O(log N) depth), 2N words, single key.",
}

rows = collections.OrderedDict()
for pf in passes:
    for line in open(pf):
        if not line.startswith("{"): continue
        d = json.loads(line)
        key = (d["name"], d["size_bytes"], d.get("template", ""))
        r = rows.setdefault(key, {"medians": [], "mins": [], "maxs": [], "d": d})
        r["medians"].append(d["gbps"]); r["mins"].append(d["gbps_min"]); r["maxs"].append(d["gbps_max"])

out_rows = []
for (name, size, tmpl), r in rows.items():
    d = r["d"]
    best = max(r["medians"])
    impl = d["impl_source"]
    if tmpl: impl += " " + tmpl
    elif "arith" in d: impl += " (" + d["arith"] + ")"
    note = NOTES.get(name, "")
    stats = (f" [pass medians GB/s: {', '.join(f'{m:.2f}' for m in r['medians'])}; "
             f"single-run min {min(r['mins']):.2f} / max {max(r['maxs']):.2f}; {d['runs']} runs x {d['reps']} calls per pass; "
             f"{size/best:.1f} ns per call at the reported rate]")
    out_rows.append({"name": name, "family": family(name), "gbps": round(best, 3), "size_bytes": size,
                     "impl_source": impl, "notes": note + stats})
json.dump({"rows": out_rows}, open(out, "w"), indent=1)
print(f"{len(out_rows)} rows -> {out}")
for r in out_rows:
    print(f"{r['gbps']:8.3f} GB/s {r['size_bytes']:6d} B  {r['family']:14s} {r['name']}")
