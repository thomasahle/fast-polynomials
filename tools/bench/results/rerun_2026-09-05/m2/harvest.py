#!/usr/bin/env python3
"""Harvest lane-C M2 logs (dir = argv[1]) and print a rows.md body to stdout."""
import sys, re, json, os, glob, statistics as st
D = sys.argv[1]
def rd(p):
    return open(p).read() if os.path.exists(p) else None
def hdr(p):
    t = rd(p); 
    if t is None: return "MISSING"
    b = re.search(r'# uptime before: .*load averages: ([\d.]+)', t); a = re.search(r'# uptime after: .*load averages: ([\d.]+)', t)
    d = re.search(r'# date: (.*)', t)
    return f"{d.group(1) if d else '?'}, load {b.group(1) if b else '?'} -> {a.group(1) if a else '?'}"
def med_idx(vals):  # index of the median of three
    s = sorted(range(len(vals)), key=lambda i: vals[i]); return s[len(vals)//2]
out = []
P = out.append
# ---------------- application benchmarks
def app(name, pat, labels):
    reps = []
    for r in (1,2,3):
        t = rd(f"{D}/{name}.{r}.txt")
        if t is None: reps.append(None); continue
        reps.append([float(x) for x in re.findall(pat, t)])
    return reps
cs = app("countsketch_arm", r'\(([\d.]+) ns/update\)', None)
lp_b = app("linearprobe_arm", r'build:\s+([\d.]+) ns/insert', None)
lp_q = app("linearprobe_arm", r'lookup:\s+([\d.]+) ns/query', None)
xf_b = app("xorfilter_arm", r'build:\s+([\d.]+) ns/key', None)
xf_q = app("xorfilter_arm", r'query:\s+([\d.]+) ns/query', None)
def fmt(v, nd=2): return f"{v:.{nd}f}"
def sel(reps_h):  # choose rep index by median Horner
    hs = [r[0] for r in reps_h]; return med_idx(hs)
res = {}
if all(cs):
    i = sel(cs); res['cs'] = (i, cs[i])
if all(lp_b):
    i = sel(lp_b); res['lp'] = (i, lp_b[i], lp_q[i])
if all(xf_b):
    i = sel(xf_b); res['xf'] = (i, xf_b[i], xf_q[i])
P("## 1. Application benchmarks, ARM (Apple M2 Pro), 3 repetitions each; reported rep = median Horner value\n")
P("Old cells: countsketch 5.49/4.96/4.33; linearprobe insert 32.5/28.5/28.5, query 42.7/41.9/38.6; xorfilter build 96.1/82.4/92.0, query 5.56/5.53/5.04 (Horner/R-W/Ours).\n")
P("| binary | rep | Horner | R-W | Ours | header |")
P("|---|---|---|---|---|---|")
for r in range(3):
    if cs[r]: P(f"| countsketch ns/update | {r+1} | {fmt(cs[r][0])} | {fmt(cs[r][1])} | {fmt(cs[r][2])} | {hdr(f'{D}/countsketch_arm.{r+1}.txt')} |")
for r in range(3):
    if lp_b[r]: P(f"| linearprobe ns/insert | {r+1} | {fmt(lp_b[r][0],1)} | {fmt(lp_b[r][1],1)} | {fmt(lp_b[r][2],1)} | {hdr(f'{D}/linearprobe_arm.{r+1}.txt')} |")
    if lp_q[r]: P(f"| linearprobe ns/query | {r+1} | {fmt(lp_q[r][0],1)} | {fmt(lp_q[r][1],1)} | {fmt(lp_q[r][2],1)} | |")
for r in range(3):
    if xf_b[r]: P(f"| xorfilter ns/key (build) | {r+1} | {fmt(xf_b[r][0],1)} | {fmt(xf_b[r][1],1)} | {fmt(xf_b[r][2],1)} | {hdr(f'{D}/xorfilter_arm.{r+1}.txt')} |")
    if xf_q[r]: P(f"| xorfilter ns/query | {r+1} | {fmt(xf_q[r][0])} | {fmt(xf_q[r][1])} | {fmt(xf_q[r][2])} | |")
P("")
def bold3(v, nd):
    m = min(v); return " & ".join((r"\textbf{"+fmt(x,nd)+"}") if x == m else fmt(x,nd) for x in v)
if 'cs' in res:
    i, v = res['cs']
    P(f"**CountSketch** (rep {i+1}): old `5.49 & 4.96 & \\textbf{{4.33}}` -> new `{bold3(v,2)}`; ARM speedup Ours/Horner old 1.27x -> new {v[0]/v[2]:.2f}x (R-W {v[0]/v[1]:.2f}x).")
    P(f"LaTeX ARM part: `ns/update & {bold3(v,2)} & <x86 cells>`\n")
if 'lp' in res:
    i, b, q = res['lp']
    P(f"**Linear probing** (rep {i+1}): insert old `32.5 & 28.5 & \\textbf{{28.5}}` -> new `{bold3(b,1)}`; query old `42.7 & 41.9 & \\textbf{{38.6}}` -> new `{bold3(q,1)}`.")
    P(f"ARM speedups Ours/Horner: inserts old 1.14x -> new {b[0]/b[2]:.2f}x; lookups old 1.11x -> new {q[0]/q[2]:.2f}x (R-W: {b[0]/b[1]:.2f}x / {q[0]/q[1]:.2f}x).")
    P(f"LaTeX ARM parts: `ns/insert & {bold3(b,1)} & <x86>` / `ns/query  & {bold3(q,1)} & <x86>`\n")
if 'xf' in res:
    i, b, q = res['xf']
    P(f"**XOR filter** (rep {i+1}): build old `96.1 & \\textbf{{82.4}} & 92.0` -> new `{bold3(b,1)}`; query old `5.56 & 5.53 & \\textbf{{5.04}}` -> new `{bold3(q,2)}`.")
    P(f"ARM ratios Horner/Ours: query old 1.10x -> new {q[0]/q[2]:.2f}x; build (old: 'R-W is faster at build time') -> new Ours {b[0]/b[2]:.2f}x, R-W {b[0]/b[1]:.2f}x over Horner.")
    P(f"LaTeX ARM parts: `ns/key (build) & {bold3(b,1)} & <x86>` / `ns/query       & {bold3(q,2)} & <x86>`\n")
# ---------------- prime-field rows
def sections(t):
    """return list of (section_title, [(degree, horner_ns, chain_ns, speedup), ...])"""
    blocks = re.findall(r'^(\S[^\n]*\(degree (\d+)[^\n]*)\n\s+Horner:\s+([\d.]+) ns/(?:eval|share)\n\s+Chain\s*:\s+([\d.]+) ns/(?:eval|share)\n\s+Speedup:\s+([\d.]+)x', t, re.M)
    d = {}
    for title, deg, h, c, s in blocks:
        key = title.split(' (')[0]
        d.setdefault(key, []).append((int(deg), float(h), float(c), float(s)))
    return d
def prime(name, keys):
    reps = []
    for r in (1,2,3):
        t = rd(f"{D}/{name}.{r}.txt"); reps.append(sections(t) if t else None)
    if not all(reps): return None, reps
    means = [st.mean(x[1] for k in keys for x in rep[k]) for rep in reps]
    return med_idx(means), reps
def row5(vals): return " & ".join(f"{v:.2f}$\\times$" for v in vals)
P("## 2. Mersenne 2^89-1 rows (ARM), 3 repetitions; reported rep = median of mean Horner ns/eval over the table's 10 configs\n")
P("Old: ARM Sharegen 2.02/2.37/2.47/2.49/2.44; ARM Random point 2.01/2.34/2.48/2.48/2.48; prose '2.0x-2.5x'; store 'essentially the same speedups'.\n")
i, reps = prime("shamir_sharegen_mersenne", ["x2s/sharegen-seq", "x2s/prf-rand"])
if i is not None:
    P("| rep | section | deg13 | deg15 | deg17 | deg19 | deg21 | Horner ns/eval (13..21) | Chain ns/eval (13..21) | header |"); P("|---|---|---|---|---|---|---|---|---|---|")
    for r, rep in enumerate(reps):
        for k in ["x2s/u64-x", "x2s/sharegen-seq", "x2s/prf-rand"]:
            v = rep[k]; P(f"| {r+1} | {k} | " + " | ".join(f"{x[3]:.2f}" for x in v) + " | " + "/".join(f"{x[1]:.1f}" for x in v) + " | " + "/".join(f"{x[2]:.1f}" for x in v) + f" | {hdr(f'{D}/shamir_sharegen_mersenne.{r+1}.txt') if k=='x2s/u64-x' else ''} |")
    rep = reps[i]; seq = [x[3] for x in rep["x2s/sharegen-seq"]]; rnd = [x[3] for x in rep["x2s/prf-rand"]]
    P(f"\n**Mersenne (rep {i+1})**: Sharegen old 2.02/2.37/2.47/2.49/2.44 -> new {'/'.join(f'{v:.2f}' for v in seq)}; Random point old 2.01/2.34/2.48/2.48/2.48 -> new {'/'.join(f'{v:.2f}' for v in rnd)}.")
    allv = seq + rnd; P(f"Range over both regimes: {min(allv):.2f}x-{max(allv):.2f}x (prose old '2.0x-2.5x').")
    P(f"LaTeX: `ARM: Sharegen ($x_i=i$) & {row5(seq)} \\\\`"); P(f"LaTeX: `ARM: Random point ($x_i \\sim \\F_p$) & {row5(rnd)} \\\\`\n")
i, reps = prime("shamir_sharegen_mersenne_store", ["x2s/sharegen"])
if i is not None:
    P("**Mersenne store variant** (65536 points x 256 iters):\n"); P("| rep | deg13 | deg15 | deg17 | deg19 | deg21 | header |"); P("|---|---|---|---|---|---|---|")
    for r, rep in enumerate(reps):
        v = rep["x2s/sharegen"]; P(f"| {r+1} | " + " | ".join(f"{x[3]:.2f}" for x in v) + f" | {hdr(f'{D}/shamir_sharegen_mersenne_store.{r+1}.txt')} |")
    v = [x[3] for x in reps[i]["x2s/sharegen"]]; P(f"\nstore (rep {i+1}): {'/'.join(f'{x:.2f}' for x in v)}, range {min(v):.2f}x-{max(v):.2f}x (prose: 'essentially the same speedups').\n")
P("## 3. Goldilocks rows (ARM), 3 repetitions; same selection rule\n")
P("Old: ARM Sharegen 1.98/2.23/2.39/2.33/2.32; ARM Random point 1.96/2.29/2.35/2.34/2.34; ARM store range 2.19x-2.36x.\n")
i, reps = prime("goldilocks_stark_eval", ["x2s/seq", "x2s/rand"])
if i is not None:
    P("| rep | section | deg13 | deg15 | deg17 | deg19 | deg21 | Horner ns/eval | Chain ns/eval | header |"); P("|---|---|---|---|---|---|---|---|---|---|")
    for r, rep in enumerate(reps):
        for k in ["x2s/seq", "x2s/rand"]:
            v = rep[k]; P(f"| {r+1} | {k} | " + " | ".join(f"{x[3]:.2f}" for x in v) + " | " + "/".join(f"{x[1]:.1f}" for x in v) + " | " + "/".join(f"{x[2]:.1f}" for x in v) + f" | {hdr(f'{D}/goldilocks_stark_eval.{r+1}.txt') if k=='x2s/seq' else ''} |")
    rep = reps[i]; seq = [x[3] for x in rep["x2s/seq"]]; rnd = [x[3] for x in rep["x2s/rand"]]
    P(f"\n**Goldilocks (rep {i+1})**: Sharegen old 1.98/2.23/2.39/2.33/2.32 -> new {'/'.join(f'{v:.2f}' for v in seq)}; Random point old 1.96/2.29/2.35/2.34/2.34 -> new {'/'.join(f'{v:.2f}' for v in rnd)}.")
    P(f"LaTeX: `ARM: Sharegen ($x_i=i$) & {row5(seq)} \\\\`"); P(f"LaTeX: `ARM: Random point ($x_i \\sim \\F_p$) & {row5(rnd)} \\\\`\n")
i, reps = prime("goldilocks_sharegen_store", ["x2s/sharegen"])
if i is not None:
    P("**Goldilocks store variant**:\n"); P("| rep | deg13 | deg15 | deg17 | deg19 | deg21 | header |"); P("|---|---|---|---|---|---|---|")
    for r, rep in enumerate(reps):
        v = rep["x2s/sharegen"]; P(f"| {r+1} | " + " | ".join(f"{x[3]:.2f}" for x in v) + f" | {hdr(f'{D}/goldilocks_sharegen_store.{r+1}.txt')} |")
    v = [x[3] for x in reps[i]["x2s/sharegen"]]; P(f"\nstore (rep {i+1}): {'/'.join(f'{x:.2f}' for x in v)}; ARM store range old 2.19x-2.36x -> new {min(v):.2f}x-{max(v):.2f}x.")
    P(f"LaTeX: `On ARM, including memory stores gives ${min(v):.2f}\\times$--${max(v):.2f}\\times$ speedup;`\n")
# ---------------- speed harness
P("## 4. tab:injective:adversarial harness (tools/bench/adversarial/speed), M2 Pro\n")
TABLE = [("This paper, one chain, F_2^64", "Paper GF(2^64) injective, sequential", (4.1,10.1)),
         ("This paper, 8 lanes, F_2^64", "Paper GF(2^64) injective, 8 lanes", (23.8,17.9)),
         ("This paper, F_2^89-1", "Paper injective over F_{2^89-1} (smart reduction, 15 B/step)", (4.4,3.9)),
         ("Horner, F_2^64", "univ_horner_64", (1.3,2.3)), ("Horner, unrolled", "horner_unrolled_64", (5.1,7.4)), ("BRW", "univ_brw_64", (6.0,5.3)),
         ("Polymur", "Polymur (random k, s)", (19.7,16.2)),
         ("wyhash v4.3", "wyhash 4.3 (random secret)", (26.5,34.8)), ("rapidhash v1", "rapidhash v1 (random secret)", (27.1,32.1)),
         ("XXH3", "XXH3-64 withSeed (random seed)", (38.2,27.2)), ("XXH3-128", "XXH3-128 withSeed (random seed)", (33.8,24.0)),
         ("MUM v3", "MUM v3 (unroll 16)", (33.0,26.8)), ("komihash v5.34", "komihash 5.34 (random seed)", (24.8,24.3)),
         ("ChainHash, 1 KB", "ChainHash, 1 KB blocks, K=5+twist, S=2", (61.7,40.5)), ("ChainHash, 256 B", "ChainHash, 256 B blocks, K=5+twist", (57.7,36.8)),
         ("ChainHash, 64 B", "ChainHash, 64 B blocks, K=5+twist", (26.6,27.4)),
         ("UMASH-64", "UMASH 64 (umash_full)", (40.7,32.9)), ("UMASH-128", "UMASH 128 (umash_fprint)", (23.9,19.7)),
         ("CLNH", "clnh_64", (27.3,26.3)), ("Multiply-shift", "Vector multiply-shift (Dietzfelbinger)", (None,16.5)),
         ("caption one-chain framework", "univ_injective_64 (single key)", (2.2,None))]
def speed(p):
    t = rd(p); d = {}
    if t is None: return None
    for line in t.splitlines():
        if line.startswith('{'):
            j = json.loads(line); d[(j['name'], j['size_bytes'])] = j
    return d
for fn, note in [("speed_full_runs9_t0.15.txt", "full table, `./speed 9 0.15 run` (RUNS/TARGET of speed_rerun.txt)"), ("speed_full_runs9_t0.15.run2.txt", "full table, second run, `./speed 9 0.15 run`"), ("speed_xxh3_runs9_t0.5.txt", "`./speed 9 0.5 run XXH3`"), ("speed_xxh3_128_runs5_t0.5.txt", "`./speed 5 0.5 run XXH3-128`")]:
    d = speed(f"{D}/{fn}")
    if d is None: P(f"{fn}: MISSING\n"); continue
    P(f"**{fn}** -- {note}; {hdr(f'{D}/{fn}')}\n")
    P("| table row | harness name | old 16 KB / 512 B | new 16 KB / 512 B (median; min-max) | ratio new/old |"); P("|---|---|---|---|---|")
    for lab, nm, old in TABLE:
        a = d.get((nm, 16384)); b = d.get((nm, 512))
        if a is None and b is None: continue
        f = lambda j: f"{j['gbps']:.2f} ({j['gbps_min']:.2f}-{j['gbps_max']:.2f})" if j else "---"
        rat = lambda j, o: f"{j['gbps']/o:.2f}" if (j and o) else "---"
        P(f"| {lab} | {nm} | {old[0] if old[0] else '---'} / {old[1] if old[1] else '---'} | {f(a)} / {f(b)} | {rat(a,old[0])} / {rat(b,old[1])} |")
    P("")
# ---------------- smhasher3
P("## 5. SMHasher3 injective-hash speed (M2 Pro)\n")
P("Old (injective.tex:188-192): 1.59 bytes/cycle bulk, 133 cycles/hash small keys (mersenne); MUM fold 14.4 bytes/cycle, '9x higher'.\n")
sm = {}
for h in ("mersenne", "mum"):
    t = rd(f"{D}/smh_speed_{h}.txt")
    if t is None: P(f"smh_speed_{h}.txt: MISSING"); continue
    t2 = rd(f"{D}/smh_speed_{h}.run2.txt")
    if t2:
        s2 = re.search(r'Small key speed test.*?Average\s+-\s+([\d.]+) cycles/hash', t2, re.S); b2 = re.search(r'Bulk speed test - 262144-byte keys.*?Average\s+-\s+([\d.]+) bytes/cycle', t2, re.S)
        P(f"- `injective-hash.{h}` second run: small keys {s2.group(1) if s2 else '?'} cycles/hash; bulk {b2.group(1) if b2 else '?'} bytes/cycle ({hdr(f'{D}/smh_speed_{h}.run2.txt')})")
    small = re.search(r'Small key speed test.*?Average\s+-\s+([\d.]+) cycles/hash', t, re.S)
    bulk = re.search(r'Bulk speed test - 262144-byte keys.*?Average\s+-\s+([\d.]+) bytes/cycle', t, re.S)
    sm[h] = (float(small.group(1)) if small else None, float(bulk.group(1)) if bulk else None)
    P(f"- `injective-hash.{h}`: small keys {sm[h][0]} cycles/hash; bulk {sm[h][1]} bytes/cycle ({hdr(f'{D}/smh_speed_{h}.txt')})")
if 'mersenne' in sm and 'mum' in sm and sm['mersenne'][1] and sm['mum'][1]:
    P(f"- ratio mum/mersenne bulk: {sm['mum'][1]/sm['mersenne'][1]:.2f}x (old 9x = 14.4/1.59 = {14.4/1.59:.2f})")
    P(f"- cells: `$1.59$~bytes/cycle` -> `${sm['mersenne'][1]:.2f}$~bytes/cycle`; `$133$~cycles per hash` -> `${round(sm['mersenne'][0])}$~cycles per hash`; `$9\\times$ higher ($14.4$~bytes/cycle)` -> `${round(sm['mum'][1]/sm['mersenne'][1])}\\times$ higher (${sm['mum'][1]:.1f}$~bytes/cycle)`")
print("\n".join(out))
