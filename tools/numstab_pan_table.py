#!/usr/bin/env python3
"""Render the Pan measurements into rows in the format of sections/numstab_table.tex (same formatting
functions as tools/numstab_table.py: A printed as 1 when |log10 A| < 0.05, as a number below 10^3, else
10^k; errors in units of u*sum|a_i||x|^i with sci()).

Inputs (all optional; missing files are skipped):
  <dir>/numstab_pan.json                degree-6 corpus block (tools/numstab_pan.mjs corpus), 'odd' block (Belaga at
                                        7, 15, 31), 'rhoGeneric' block (rounding depths on generic constants) and
                                        'hyper' block (the shift sweep towards the exceptional hypersurface)
  <dir>/numstab_pan07_<degs>.json       Pan (0.7) rows (tools/numstab_pan07.py) for the odd degrees
  notes/numstab_coeffs.json             the published rows (Horner, Estrin, Rabin-Winograd, Motzkin-Eve, this paper) at 7, 15, 31
  sections/numstab_table.tex            read only: the rho printed in the paper for the published rows

rho.  The harness (tools/numstab.mjs) measures the rounding depth of a line chain on the chain emitted for the
first corpus polynomial, and a constant that happens to vanish drops a '+ 0' and hence a rounding: Horner's
rho at n = 31 is 61 minus the number of zero coefficients of trial 0 (59 in notes/numstab_coeffs.json),
Rabin-Winograd's varies between 10 and 12 at n = 7.  The paper prints the generic values (Horner 2n - 1,
Rabin-Winograd 12/22/40).  This script therefore takes rho from, in order: the 'rhoGeneric' block of
numstab_pan.json (chains compiled for a monic polynomial with coefficients (2i+3)/7, none of whose
constants vanishes); the maximum over the corpus trials ('rhoTrials'; a vanishing constant can only lower
the depth) when the generic polynomial is not admissible (Belaga: complex constants); and, for the published
rows, the value printed in sections/numstab_table.tex.  Disagreements between the sources are printed.

Writes <dir>/numstab_pan_table.tex (a complete table: prescribed-coefficients regime only) and
<dir>/numstab_pan_sweep.tex (the shift sweep towards the hypersurface, one family).  Nothing under sections/ is touched.
"""
import json, math, os, sys, glob, re
here = os.path.dirname(os.path.abspath(__file__))
D = sys.argv[1] if len(sys.argv) > 1 else '.'

def sci(v):
    if v == 0: return '0'
    if 0.01 <= v < 1000:
        return f'{v:.0f}' if v >= 100 else f'{v:.3g}'
    e = int(math.floor(math.log10(v))); m = v / 10**e
    return f'{m:.1f}\\times10^{{{e}}}'
def fmtA(l):
    return '1' if abs(l) < 0.05 else (f"{10**l:.2g}" if l < 2 else (f"{10**l:.0f}" if l < 3 else f"10^{{{l:.0f}}}"))
def fmtE(e):
    if e is None or e == float('inf') or e != e: return r'\infty'
    return sci(e)
def fix(r):
    for k in ('median', 'max'):
        if r['err'][k] is None: r['err'][k] = float('inf')
    return r

ORDER = ['Horner', 'Estrin', 'Rabin–Winograd', 'Motzkin–Eve', 'Belaga', 'Knuth (12)', 'this paper', 'Pan (16)', 'Pan (0.7)']
TEX = {'Horner': 'Horner', 'Estrin': 'Estrin', 'Rabin–Winograd': 'Rabin--Winograd', 'Motzkin–Eve': 'Motzkin--Eve',
       'Belaga': 'Belaga', 'Knuth (12)': 'Knuth (12)', 'this paper': '\\textbf{this paper}',
       'Pan (16)': 'Pan sextic (16)', 'Pan (0.7)': 'Pan (0.7)'}
TEX2NAME = {v: k for k, v in TEX.items()}

blocks = {}   # n -> {scheme -> row}
def put(n, name, r):
    if r is None or r.get('samples', 0) == 0: return
    blocks.setdefault(int(n), {})[name] = fix(r)

rhoGeneric, hyper = {}, []
pan = os.path.join(D, 'numstab_pan.json')
if os.path.exists(pan):
    j = json.load(open(pan))
    for name, r in j.get('corpus', {}).items(): put(6, name, r)
    for n, rows in j.get('odd', {}).items():
        if 'Belaga' in rows: put(n, 'Belaga', rows['Belaga'])
    rhoGeneric = {int(n): v for n, v in j.get('rhoGeneric', {}).items()}
    hyper = j.get('hyper', [])
for f in sorted(glob.glob(os.path.join(D, 'numstab_pan07_*.json'))):
    j = json.load(open(f))
    for n, rows in j.items():
        if 'Pan (0.7)' in rows: put(n, 'Pan (0.7)', rows['Pan (0.7)'])
pub = os.path.join(here, '..', 'notes', 'numstab_coeffs.json')
if os.path.exists(pub):
    j = json.load(open(pub))
    for n, rows in j.items():
        for name, r in rows.items(): put(n, name, r)

# rho printed in the paper (prescribed-coefficients block of sections/numstab_table.tex), read only
paperRho = {}
ptab = os.path.join(here, '..', 'sections', 'numstab_table.tex')
if os.path.exists(ptab):
    block = open(ptab).read().split('prescribed keys')[0]
    for m in re.finditer(r'&\s*(\\textbf\{this paper\}|[A-Za-z\-]+)\s*&\s*(\d+)\s*&\s*(\d+)\s*&', block):
        name = TEX2NAME.get(m.group(1)); 
        if name: paperRho[(int(m.group(2)), name)] = int(m.group(3))

def rho_of(n, name, r):
    """generic rounding depth, with the provenance of the value"""
    g = rhoGeneric.get(n, {}).get(name)
    trials = r.get('rhoTrials')
    p = paperRho.get((n, name))
    cands = {'generic': g, 'max over trials': (max(trials) if trials else None), 'paper table': p, 'json': r.get('rho')}
    for src in ('generic', 'max over trials', 'paper table', 'json'):
        if cands[src] is not None:
            val = cands[src]
            others = {s: v for s, v in cands.items() if v is not None and v != val and s != 'json'}
            if others or (cands['json'] is not None and cands['json'] != val):
                print(f"% rho n={n} {name}: using {src} = {val}; other sources: {cands}")
            return val, src
    return None, None

out = [r'\begin{table}[htbp]', r'\centering\footnotesize', r'\begin{tabular}{@{}llrrrrrr@{}}', r'\toprule',
       r'regime & scheme & $n$ & $\rho$ & $A$ med. & $A$ max & err.\ med. & err.\ max \\', r'\midrule']
first = True
for n in sorted(blocks):
    for name in ORDER:
        if name not in blocks[n]: continue
        r = blocks[n][name]
        rho, src = rho_of(n, name, r)
        reglab = 'prescribed coefficients' if first else ''
        first = False
        em = 'overflow' if r.get('overflow') and r.get('overflow') == r.get('samples') else f"${fmtE(r['err']['median'])}$"
        ex = 'overflow' if r.get('overflow') else f"${fmtE(r['err']['max'])}$"
        note = ''
        if r.get('skipped') or (r.get('samples') and r['samples'] < 36): note = "$^{\\dagger}$"
        out.append(f"{reglab} & {TEX[name]}{note} & {n} & {rho} & ${fmtA(r['logA']['median'])}$ & ${fmtA(r['logA']['max'])}$ & {em} & {ex} \\\\")
    out.append(r'\addlinespace[2pt]')
out[-1] = r'\bottomrule'
out += [r'\end{tabular}',
        r"\caption{Rounding depth $\rho$, schedule amplification $A$, and observed double-precision forward error, prescribed-coefficients regime, with the schemes of Pan added: the sextic (16) (rational preprocessing, three multiplications, defined off the hypersurface $27a_3-18a_5a_4+5a_5^3=0$) and the general real scheme (0.7) ($\lfloor n/2\rfloor+1$ multiplications; rational at $n\le 6$, where it coincides with our degree-6 chain; real-algebraic numeric preprocessing beyond, the branch with the smallest majorant at $\abs x=2$ among those found). Degree 6 is the generator of the harness with \texttt{DEGREES=[6]}; degrees 7, 15, 31 are the corpus of Table~\ref{tab:numstab}. $\rho$ is the generic rounding depth (constants none of which vanishes; Motzkin--Eve at $n=6$ with a nonzero shift). $^{\dagger}$: some polynomials skipped (Belaga: complex constants; Motzkin--Eve: failed verification); medians and maxima over the remaining samples.}",
        r'\label{tab:numstab-pan}', r'\end{table}']
tex = '\n'.join(out) + '\n'
open(os.path.join(D, 'numstab_pan_table.tex'), 'w').write(tex)
print(tex)

# ---- the shift sweep towards H (one family, the one with u5 = 3), as a small table ----
if hyper:
    fam = 1 if any(r['fam'] == 1 for r in hyper) else hyper[0]['fam']
    rows = [r for r in hyper if r['fam'] == fam]
    sw = [r'\begin{table}[htbp]', r'\centering\footnotesize', r'\begin{tabular}{@{}rrrrrrrr@{}}', r'\toprule',
          r'$k$ & $\log_{10}\abs{\alpha_1}$ & $\log_{10}\abs{\alpha_5}$ & $\log_{10}A$ med. & slope & exact & err.\ med. & err.\ max \\', r'\midrule']
    for r in rows:
        if r['k'] not in (0, 4, 8, 12, 16, 20, 24, 32, 40): continue
        slope = r'\text{--}' if r.get('slope') is None else f"{r['slope']:.2f}"
        ex = ''.join('1' if b else '0' for b in r.get('exactConsts', []))
        nex = sum(1 for b in r.get('exactConsts', []) if b)
        zero = all(m['zero'] for m in r.get('mech', [])) if r.get('mech') else False
        exact = f"{nex}/6" + (r', $\widehat P=0$' if zero else '')
        sw.append(f"{r['k']} & {r['logA1']:.1f} & {r['logA5']:.1f} & {r['logA']['median']:.1f} & ${slope}$ & {exact} & ${fmtE(r['err']['median'])}$ & ${fmtE(r['err']['max'])}$ \\\\")
    u = rows[0].get('u', {}); xs = rows[0].get('xs', ['3/2', '-5/4', '1/2'])
    fixed = ', '.join(f"$a_{i}={u[f'u{i}']}$" for i in (5, 4, 2, 1, 0) if f'u{i}' in u)
    sw += [r'\bottomrule', r'\end{tabular}',
           r"\caption{Pan's sextic approaching its exceptional hypersurface: $a_3=2\alpha_0a_4-5\alpha_0^3+2^{-k}$ (so $D=2^{-k}$) with " + fixed + r" fixed, at $x\in\{" + ','.join(xs) + r"\}$. Slope: $d\log_{10}A/d\log_{10}D$ between $k-4$ and $k$ (medians over $x$). Exact: how many of the six constants are exactly representable in double precision; $\widehat P=0$ marks the rows where the two terms of $P=qz+\alpha_5$, both of size $\abs{\alpha_1}^3$, cancel exactly in double precision and the computed value is $0$, so that the reported error is $\abs{P(x)}/(u\sum_i\abs{a_i}\abs x^i)\le1/u\approx9.0\times10^{15}$, the ceiling of the metric. Horner's rule on the same polynomials and points has error $0$ throughout.}",
           r'\label{tab:numstab-pan-sweep}', r'\end{table}']
    stex = '\n'.join(sw) + '\n'
    open(os.path.join(D, 'numstab_pan_sweep.tex'), 'w').write(stex)
    print(stex)
