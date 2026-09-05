#!/usr/bin/env python3
"""Generate rows.md (old EPYC/untraceable x86 cells -> new Xeon 8375C cells) from a lane-C Xeon log set."""
import re, sys, os
D = sys.argv[1]
def rd(f): return open(f).read()
def reps(name):
    return {r: rd(os.path.join(D, f'{name}.{r}.txt')) for r in (1, 2, 3) if os.path.exists(os.path.join(D, f'{name}.{r}.txt'))}
def loads(t):
    b = re.search(r'uptime before:.*load average: ([\d.]+)', t); a = re.search(r'uptime after:.*load average: ([\d.]+)', t)
    return f'{b.group(1)}/{a.group(1)}'
def median_rep(vals):
    s = sorted(vals.items(), key=lambda kv: kv[1]); return s[len(s)//2][0]
def sig3(x):  # three significant figures, as in the paper's application tables
    if x >= 100: return f'{x:.1f}'
    if x >= 10: return f'{x:.1f}'
    return f'{x:.2f}'
def bold_row(vals, fmt):  # bold the fastest (smallest) of the three x86 cells
    i = min(range(3), key=lambda j: vals[j]); return ' & '.join((r'\textbf{' + fmt(v) + '}') if j == i else fmt(v) for j, v in enumerate(vals))
def blocks(t):
    out = {}
    for m in re.finditer(r'^(\S+) \(degree (\d+)[^\n]*\)\n\s+Horner: ([\d.]+) ns/\w+\n\s+Chain : ([\d.]+) ns/\w+\n\s+Speedup: ([\d.]+)x', t, re.M):
        out[(m.group(1), int(m.group(2)))] = (float(m.group(3)), float(m.group(4)), float(m.group(5)))
    return out
L = []
P = L.append
# ---------------- application kernels
cs = reps('app_countsketch_x86'); csv = {r: [float(x) for x in re.findall(r'\(([\d.]+) ns/update\)', t)] for r, t in cs.items()}
lp = reps('app_linearprobe_x86'); lpv = {r: ([float(x) for x in re.findall(r'build:\s+([\d.]+) ns/insert', t)], [float(x) for x in re.findall(r'lookup:\s+([\d.]+) ns/query', t)]) for r, t in lp.items()}
xf = reps('app_xorfilter_x86'); xfv = {r: ([float(x) for x in re.findall(r'build:\s+([\d.]+) ns/key', t)], [float(x) for x in re.findall(r'query:\s+([\d.]+) ns/query', t)]) for r, t in xf.items()}
sc = median_rep({r: v[0] for r, v in csv.items()}); sl = median_rep({r: v[0][0] for r, v in lpv.items()}); sx = median_rep({r: v[0][0] for r, v in xfv.items()})
P('## A. Application kernels (experiments.tex lines 255, 278-279, 302-303; x86 columns only)\n')
P('Old x86 cells: no log survives (MANIFEST section 5, "untraceable"; the platform paragraph names the Xeon, the numbers were most likely the January EPYC run).')
P('New: Xeon 8375C, `taskset -c 80-95`, default arguments (= paper protocol), three repetitions; the quoted repetition is the one with the median Horner value (all three logs kept).\n')
P('| cell (Horner / R--W / Ours) | old x86 (paper) | rep1 | rep2 | rep3 | quoted rep | new x86 (Xeon) |')
P('|---|---|---|---|---|---|---|')
def row(label, old, per, sel, fmt=sig3):
    P(f'| {label} | {old} | ' + ' | '.join('/'.join(fmt(x) for x in per[r]) for r in (1, 2, 3)) + f' | rep{sel} (load {loads_map[label]}) | ' + '/'.join(fmt(x) for x in per[sel]) + ' |')
loads_map = {'CountSketch ns/update': loads(cs[sc]), 'Linear probing ns/insert': loads(lp[sl]), 'Linear probing ns/query': loads(lp[sl]), 'XOR filter ns/key (build)': loads(xf[sx]), 'XOR filter ns/query': loads(xf[sx])}
row('CountSketch ns/update', '38.3/24.9/23.7', csv, sc)
row('Linear probing ns/insert', '37.4/29.9/24.5', {r: v[0] for r, v in lpv.items()}, sl)
row('Linear probing ns/query', '46.3/35.4/31.4', {r: v[1] for r, v in lpv.items()}, sl)
row('XOR filter ns/key (build)', '142.0/110.3/97.1', {r: v[0] for r, v in xfv.items()}, sx)
row('XOR filter ns/query', '19.6/15.6/11.1', {r: v[1] for r, v in xfv.items()}, sx)
c = csv[sc]; lb, lq = lpv[sl]; xb, xq = xfv[sx]
P('\nSpeedups over Horner (ours; R--W in parentheses), recomputed from the quoted repetition:\n')
P(f'* CountSketch: old $1.62\\times$ (line 259) -> **{c[0]/c[2]:.2f}x** (R--W {c[0]/c[1]:.2f}x)')
P(f'* Linear probing: old $1.53\\times$ inserts / $1.47\\times$ lookups (line 282) -> **{lb[0]/lb[2]:.2f}x inserts / {lq[0]/lq[2]:.2f}x lookups** (R--W {lb[0]/lb[1]:.2f}x / {lq[0]/lq[1]:.2f}x)')
P(f'* XOR filter: old $1.46\\times$ build / $1.76\\times$ queries (line 306) -> **{xb[0]/xb[2]:.2f}x build / {xq[0]/xq[2]:.2f}x queries** (R--W {xb[0]/xb[1]:.2f}x / {xq[0]/xq[1]:.2f}x)')
P('\nLaTeX (x86 half of each row; the ARM half belongs to the M2 Pro re-measurement of another lane and is left as printed here):\n')
P('```latex')
P(f'ns/update & 5.49 & 4.96 & \\textbf{{4.33}} & {bold_row(c, sig3)}')
P(f'ns/insert & 32.5 & 28.5 & \\textbf{{28.5}} & {bold_row(lb, sig3)} \\\\')
P(f'ns/query  & 42.7 & 41.9 & \\textbf{{38.6}} & {bold_row(lq, sig3)}')
P(f'ns/key (build) & 96.1 & \\textbf{{82.4}} & 92.0 & {bold_row(xb, lambda x: f"{x:.1f}")} \\\\')
P(f'ns/query       & 5.56 & 5.53 & \\textbf{{5.04}} & {bold_row(xq, sig3)}')
P('```')
P(f'Prose: line 259 `On x86, the speedup is $1.62\\times$, reflecting ...` -> `${c[0]/c[2]:.2f}\\times$`; line 282 `$1.53\\times$ for inserts and $1.47\\times$ for lookups` -> `${lb[0]/lb[2]:.2f}\\times$ for inserts and ${lq[0]/lq[2]:.2f}\\times$ for lookups`; line 306 `$1.46\\times$ speedup for build and $1.76\\times$ for queries` -> `${xb[0]/xb[2]:.2f}\\times$ speedup for build and ${xq[0]/xq[2]:.2f}\\times$ for queries`.')
# ---------------- prime-field kernels
def pf(name, lab):
    rr = reps(name); bl = {r: blocks(t) for r, t in rr.items()}
    sel = median_rep({r: bl[r][(lab, 13)][0] for r in bl})
    per = {r: [bl[r][(lab, d)] for d in (13, 15, 17, 19, 21)] for r in bl}
    return sel, per, {r: loads(t) for r, t in rr.items()}
old = {'mers_seq': ('1.6627/4.50338/4.56429/4.629/4.60091', [1.66, 4.50, 4.57, 4.63, 4.60]),
       'mers_rand': ('1.66263/4.49914/4.56599/4.62889/4.60286', [1.66, 4.50, 4.57, 4.63, 4.60]),
       'gold_seq': ('1.27199/1.38258/1.41527/1.42784/1.37008', [1.27, 1.38, 1.42, 1.43, 1.37]),
       'gold_rand': ('1.27246/1.38329/1.41598/1.42859/1.36813', [1.27, 1.38, 1.42, 1.43, 1.37]),
       'gold_store': ('1.50544/1.30835/1.31205/1.35776/1.90423', None)}
P('\n## B. Mersenne 2^89-1 rows (experiments.tex lines 357-358) and Goldilocks rows (375-376), x86 store ranges\n')
P('Old: AMD EPYC 9R14, `tools/bench/x86_output.txt` (Jan 2026, compiler unknown).  New: Xeon 8375C, three repetitions, quoted repetition = median degree-13 Horner time; Speedup = Horner ns / chain ns as printed by the binary, rounded to two decimals as in the paper.\n')
P('| row | old EPYC log values | old paper cells | rep1 | rep2 | rep3 | quoted rep (load before/after) | **new Xeon cells** |')
P('|---|---|---|---|---|---|---|---|')
tex = {}
for key, name, lab, label in [('mers_seq', 'shamir_sharegen_mersenne', 'x2s/sharegen-seq', 'Mersenne sharegen (x_i=i)'), ('mers_rand', 'shamir_sharegen_mersenne', 'x2s/prf-rand', 'Mersenne random point'),
                              ('gold_seq', 'app_goldilocks_stark_eval', 'x2s/seq', 'Goldilocks sharegen (x_i=i)'), ('gold_rand', 'app_goldilocks_stark_eval', 'x2s/rand', 'Goldilocks random point'),
                              ('gold_store', 'app_goldilocks_sharegen_store', 'x2s/sharegen', 'Goldilocks store-to-memory (range only)'), ('mers_store', 'shamir_sharegen_mersenne_store', 'x2s/sharegen', 'Mersenne store-to-memory (not in the paper for x86)')]:
    sel, per, ld = pf(name, lab)
    o = old.get(key, ('--', None))
    cells = [x[2] for x in per[sel]]; tex[key] = (cells, per[sel])
    P(f'| {label} | {o[0]} | ' + ('/'.join(f"{v:.2f}" for v in o[1]) if o[1] else ('(range 1.31-1.90)' if key == 'gold_store' else '--')) + ' | ' + ' | '.join('/'.join(f'{x[2]:.2f}' for x in per[r]) for r in (1, 2, 3)) + f' | rep{sel} ({ld[sel]}) | **' + '/'.join(f'{v:.2f}' for v in cells) + f'** (range {min(cells):.2f}-{max(cells):.2f}) |')
P('\nAbsolute times of the quoted repetitions (ns per evaluation, Horner -> chain), for the prose:\n')
for key, label in [('mers_seq', 'Mersenne sharegen'), ('mers_rand', 'Mersenne random'), ('mers_store', 'Mersenne store'), ('gold_seq', 'Goldilocks sharegen'), ('gold_rand', 'Goldilocks random'), ('gold_store', 'Goldilocks store')]:
    P(f'* {label}: ' + ', '.join(f'd{d} {h:.1f}->{c:.1f}' for d, (h, c, s) in zip((13, 15, 17, 19, 21), tex[key][1])))
def texrow(cells): return ' & '.join(f'{v:.2f}$\\times$' for v in cells)
P('\nLaTeX rows (replace lines 357-358 and 375-376; row labels `x86 (EPYC 9R14)` -> `x86 (Xeon 8375C)`):\n')
P('```latex')
P(f'x86 (Xeon 8375C): Sharegen ($x_i=i$) & {texrow(tex["mers_seq"][0])} \\\\')
P(f'x86 (Xeon 8375C): Random point ($x_i \\sim \\F_p$) & {texrow(tex["mers_rand"][0])}')
P('...')
P(f'x86 (Xeon 8375C): Sharegen ($x_i=i$) & {texrow(tex["gold_seq"][0])} \\\\')
P(f'x86 (Xeon 8375C): Random point ($x_i \\sim \\F_p$) & {texrow(tex["gold_rand"][0])}')
P('```')
ms = tex['mers_seq'][0] + tex['mers_rand'][0]; gs = tex['gold_store'][0]; mst = tex['mers_store'][0]; ge = tex['gold_seq'][0] + tex['gold_rand'][0]
P('\nNote: the `x2s/u64-x` blocks of `shamir_sharegen_mersenne` (evaluation points that are small 64-bit integers, so Horner multiplies a full-width key by a small x) are not in the paper; on the Xeon the chain is slower there (0.55x-0.63x), as on the M2 Pro (0.52x-0.63x in the 2026-09-05 reproduction).')
P(f'\nRecomputed ranges: Mersenne x86 both regimes {min(ms):.2f}x-{max(ms):.2f}x (degrees 15-21: {min(ms[1:5]+ms[6:10]):.2f}x-{max(ms[1:5]+ms[6:10]):.2f}x); Mersenne x86 store {min(mst):.2f}x-{max(mst):.2f}x; Goldilocks x86 eval {min(ge):.2f}x-{max(ge):.2f}x; Goldilocks x86 store {min(gs):.2f}x-{max(gs):.2f}x (old EPYC 1.31x-1.90x, line 381).')
print('\n'.join(L))
# ---------------- section C: prose and the abstract
armM = [2.02, 2.37, 2.47, 2.49, 2.44, 2.01, 2.34, 2.48, 2.48, 2.48]  # paper's ARM Mersenne rows (lines 354-355, lane B's)
allM = ms + armM
gm = min(ge); gM = max(ge)
C = []
C.append('\n## C. Prose that quotes these cells, and the abstract\n')
C.append(f'* main.tex:45-47 (abstract) `up to $4.6\\times$ speedups for the prime-field evaluation kernel of Shamir secret sharing`: **derives from these rows** -- it is the EPYC degree-19 Mersenne cell (4.629x, paper 4.63x, rounded down to 4.6).  With the Xeon replacing the EPYC the largest Mersenne cell on x86 is {max(ms):.2f}x and the largest over both platforms is the ARM {max(armM):.2f}x (paper ARM row; the ARM re-measurement lane may change it), so the abstract should read `up to ${max(allM):.1f}\\times$` -- to be recomputed as the maximum over both Mersenne tables (ARM and x86) once the ARM rows are final, rounded to one decimal.')
C.append(f'* experiments.tex:361-362 `On the EPYC, the speedups for degrees $15$--$21$ reach $4.5\\times$--$4.6\\times$, significantly exceeding the ARM results.` -> e.g. `On the Xeon the speedups are ${min(ms):.2f}\\times$ at degree $13$ and ${min(ms[1:5]+ms[6:10]):.2f}\\times$--${max(ms):.2f}\\times$ for degrees $15$--$21$, below the ARM results.` (Xeon d13 {ms[0]:.2f}x; Horner {tex["mers_seq"][1][0][0]:.0f}->{tex["mers_seq"][1][4][0]:.0f} ns, chain {tex["mers_seq"][1][0][1]:.0f}->{tex["mers_seq"][1][4][1]:.0f} ns over degrees 13->21).')
C.append(f'* experiments.tex:343-344 (`Including the cost of writing shares to memory gives essentially the same speedups`): holds on the Xeon too (store {min(mst):.2f}x-{max(mst):.2f}x vs eval {min(ms):.2f}x-{max(ms):.2f}x); no x86 cell, nothing to change.')
C.append('* experiments.tex:345-348 (`The x86 rows of the two tables below, and the x86 store-to-memory range for Goldilocks, are the run on an AMD EPYC 9R14 recorded in tools/bench/x86_output.txt, not the Xeon 8375C of the other x86 tables; the ARM rows are the Apple M2 Pro.`): delete, or replace by `The x86 rows of the two tables below are the Xeon 8375C (logs in tools/bench/results/rerun_2026-09-05/xeon/); the ARM rows are the Apple M2 Pro.`')
C.append('* experiments.tex:27-31 (`One x86 result is from a different host: the prime-field kernels ... AMD EPYC 9R14 (Zen~4, Linux) recorded in tools/bench/x86_output.txt.`) and :84 (`8375C; AMD EPYC 9R14 for the prime-field kernels, as noted above`): delete the EPYC clauses (all x86 numbers are now the Xeon).')
C.append(f'* experiments.tex:381-383 `on the EPYC, the range is $1.31\\times$--$1.90\\times$. The smaller x86 gains reflect that Goldilocks multiplication (64-bit) is relatively cheaper, reducing the benefit of fewer multiplications.` -> `on the Xeon, the range is ${min(gs):.2f}\\times$--${max(gs):.2f}\\times$.`  The explanation sentence no longer matches the data on the Xeon: Goldilocks ({gm:.2f}x-{gM:.2f}x) is only slightly below Mersenne ({min(ms):.2f}x-{max(ms):.2f}x) there, and the gap is not the EPYC\'s 1.3x-vs-4.6x; suggested replacement: `The x86 gains are slightly smaller than for the Mersenne field, reflecting that Goldilocks multiplication (64-bit) is relatively cheaper.` or drop the sentence.')
C.append('* experiments.tex:259, 282, 306 speedup sentences: see section A.  Line 259 `reflecting the larger benefit from reducing multiplications` still fits (x86 speedups exceed ARM).  Line 306 `On x86, our method is fastest for both` still holds (build: ours < R--W < Horner on the Xeon).')
C.append('* Not derived from these rows (unchanged): introduction.tex:87 `$2.15\\times$ on x86 (Intel Xeon) at $k=9$` (tab:kwise_both, Xeon run of 2026-09-02); injective.tex x86 numbers (Xeon runs of 2026-09-02).')
C.append('* main.tex:45 `up to $2\\times$ speedups for $k$-wise independent hashing`: not from these rows (tab:kwise_both).')
C.append('\n## D. Files\n')
C.append('* `/Users/ahle/repos/fast-polynomials/tools/bench/results/rerun_2026-09-05/xeon/`: set B logs `<binary>.<rep>.txt`, `top_procs.<rep>.txt`, `build.log`, `sources.md5`, `run_laneC.sh`, `run_laneC_setB.sh`, `README.md`; `setA_contaminated/` with the first set.')
C.append('* scratch: `/private/tmp/claude-501/-Users-ahle-repos-notes-fast-polyhash/671fdc97-fe99-4719-bea0-4eedf88d5744/scratchpad/final/C/xeon/` (same files, `rows.md`, plus `parse_xeon.py`, `make_rows.py` which generated sections A-C of this file).')
print('\n'.join(C))
