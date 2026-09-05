#!/usr/bin/env python3
"""Parse the lane-C Xeon logs (3 repetitions) and print per-cell values, the selected repetition
(median Horner / median speedup rule), the LaTeX rows and the recomputed ratios."""
import re, sys, os, statistics, glob
D = sys.argv[1] if len(sys.argv) > 1 else '.'
def rd(f): return open(f).read()
def reps(name):
    out = {}
    for r in (1, 2, 3):
        p = os.path.join(D, f'{name}.{r}.txt')
        if os.path.exists(p): out[r] = rd(p)
    return out
def loads(t):
    b = re.search(r'uptime before:.*load average: ([\d.]+)', t); a = re.search(r'uptime after:.*load average: ([\d.]+)', t)
    return (b.group(1) if b else '?', a.group(1) if a else '?')
def median_rep(vals):  # vals: {rep: value}; return the rep holding the median value (3 reps)
    s = sorted(vals.items(), key=lambda kv: kv[1]); return s[len(s)//2][0]
def fmt(x, nd): return f'{x:.{nd}f}'
res = {}
# --- countsketch
cs = reps('app_countsketch_x86')
cells = {}
for r, t in cs.items():
    v = re.findall(r'\(([\d.]+) ns/update\)', t); cells[r] = [float(x) for x in v]  # Horner, RW, Ours
print('## CountSketch (ns/update: Horner, RW, Ours)  load before/after')
for r in cells: print(f'  rep{r}: {cells[r]}  load {loads(cs[r])}')
sel = median_rep({r: c[0] for r, c in cells.items()}); res['countsketch'] = (sel, cells[sel])
print(f'  selected rep{sel} (median Horner): {cells[sel]}  speedups RW {cells[sel][0]/cells[sel][1]:.2f}x ours {cells[sel][0]/cells[sel][2]:.2f}x')
# --- linearprobe
lp = reps('app_linearprobe_x86'); cells = {}
for r, t in lp.items():
    b = [float(x) for x in re.findall(r'build:\s+([\d.]+) ns/insert', t)]; q = [float(x) for x in re.findall(r'lookup:\s+([\d.]+) ns/query', t)]
    cells[r] = (b, q)
print('## Linear probing (build ns/insert; lookup ns/query: Horner, RW, Ours)')
for r in cells: print(f'  rep{r}: build {cells[r][0]} lookup {cells[r][1]}  load {loads(lp[r])}')
sel = median_rep({r: c[0][0] for r, c in cells.items()}); res['linearprobe'] = (sel, cells[sel])
b, q = cells[sel]
print(f'  selected rep{sel} (median Horner build): build {b} lookup {q}; ours speedup build {b[0]/b[2]:.2f}x lookup {q[0]/q[2]:.2f}x; RW build {b[0]/b[1]:.2f}x lookup {q[0]/q[1]:.2f}x')
# --- xorfilter
xf = reps('app_xorfilter_x86'); cells = {}
for r, t in xf.items():
    b = [float(x) for x in re.findall(r'build:\s+([\d.]+) ns/key', t)]; q = [float(x) for x in re.findall(r'query:\s+([\d.]+) ns/query', t)]
    cells[r] = (b, q)
print('## XOR filter (build ns/key; query ns/query: Horner, RW, Ours)')
for r in cells: print(f'  rep{r}: build {cells[r][0]} query {cells[r][1]}  load {loads(xf[r])}')
sel = median_rep({r: c[0][0] for r, c in cells.items()}); res['xorfilter'] = (sel, cells[sel])
b, q = cells[sel]
print(f'  selected rep{sel} (median Horner build): build {b} query {q}; ours speedup build {b[0]/b[2]:.2f}x query {q[0]/q[2]:.2f}x; RW build {b[0]/b[1]:.2f}x query {q[0]/q[1]:.2f}x')
# --- prime-field kernels: Speedup lines per labelled block
def blocks(t):
    out = {}
    for m in re.finditer(r'^(\S+) \(degree (\d+)[^\n]*\)\n\s+Horner: ([\d.]+) ns/\w+\n\s+Chain : ([\d.]+) ns/\w+\n\s+Speedup: ([\d.]+)x', t, re.M):
        out[(m.group(1), int(m.group(2)))] = (float(m.group(3)), float(m.group(4)), float(m.group(5)))
    return out
for name, want in [('shamir_sharegen_mersenne', ['x2s/sharegen-seq', 'x2s/prf-rand', 'x2s/u64-x']), ('shamir_sharegen_mersenne_store', ['x2s/sharegen']),
                   ('app_goldilocks_stark_eval', ['x2s/seq', 'x2s/rand']), ('app_goldilocks_sharegen_store', ['x2s/sharegen'])]:
    rr = reps(name); bl = {r: blocks(t) for r, t in rr.items()}
    print(f'## {name}')
    for lab in want:
        for r in bl:
            sp = [bl[r][(lab, d)][2] for d in (13, 15, 17, 19, 21)]; hn = [bl[r][(lab, d)][0] for d in (13, 15, 17, 19, 21)]; ch = [bl[r][(lab, d)][1] for d in (13, 15, 17, 19, 21)]
            print(f'  {lab:18s} rep{r}: speedup {[round(x,3) for x in sp]}  horner ns {[round(x,1) for x in hn]}  chain ns {[round(x,1) for x in ch]}  load {loads(rr[r])}')
        # selection: repetition with the median degree-13 Horner time (same rule as the app kernels)
        sel = median_rep({r: bl[r][(lab, 13)][0] for r in bl}); sp = [bl[sel][(lab, d)][2] for d in (13, 15, 17, 19, 21)]
        res[(name, lab)] = (sel, sp)
        print(f'  {lab:18s} selected rep{sel}: ' + ' & '.join(f'{x:.2f}$\\times$' for x in sp) + f'   range {min(sp):.2f}-{max(sp):.2f}')
