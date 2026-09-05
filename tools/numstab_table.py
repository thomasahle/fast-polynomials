#!/usr/bin/env python3
"""Render notes/numstab_{coeffs,keys}.json into sections/numstab_table.tex."""
import json, math, os
here = os.path.dirname(os.path.abspath(__file__))
def load(reg):
    p = os.path.join(here, '..', 'notes', f'numstab_{reg}.json')
    if not os.path.exists(p): return {}
    d = json.load(open(p))
    for v in d.values():
        for r in v.values():
            for k in ('median', 'max'):
                if r['err'][k] is None: r['err'][k] = float('inf')
    return d
def sci(v):
    if v == 0: return '0'
    if 0.01 <= v < 1000:
        return f'{v:.0f}' if v >= 100 else f'{v:.3g}'
    e = int(math.floor(math.log10(v))); m = v / 10**e
    return f'{m:.1f}\\times10^{{{e}}}'
ORDER = ['Horner', 'Estrin', 'Rabin–Winograd', 'Motzkin–Eve', 'this paper']
TEX = {'Horner': 'Horner', 'Estrin': 'Estrin', 'Rabin–Winograd': 'Rabin--Winograd',
       'Motzkin–Eve': 'Motzkin--Eve', 'this paper': '\\textbf{this paper}'}
out = []
out.append(r'\begin{table}[htbp]')
out.append(r'\centering\footnotesize')
out.append(r'\begin{tabular}{@{}llrrrrrr@{}}')
out.append(r'\toprule')
out.append(r'regime & scheme & $n$ & $\rho$ & $A$ med. & $A$ max & err.\ med. & err.\ max \\')
out.append(r'\midrule')
for reg, label in [('coeffs', 'prescribed coefficients'), ('keys', 'prescribed keys')]:
    data = load(reg)
    first = True
    for n in sorted(map(int, data.keys())):
        for name in ORDER:
            if name not in data[str(n)]: continue
            r = data[str(n)][name]
            reglab = label if first else ''
            first = False
            pw = lambda l: ('1' if abs(l) < 0.05 else f"10^{{{l:.0f}}}") if l < 3 or True else ''
            fmtA = lambda l: '1' if abs(l) < 0.05 else (f"{10**l:.2g}" if l < 2 else (f"{10**l:.0f}" if l < 3 else f"10^{{{l:.0f}}}"))
            def fmtE(e):
                if e == float('inf') or e != e: return r'\infty'
                return sci(e)
            em = 'overflow' if r.get('overflow') == r.get('samples') else f"${fmtE(r['err']['median'])}$"
            ex = 'overflow' if r.get('overflow') else f"${fmtE(r['err']['max'])}$"
            out.append(f"{reglab} & {TEX[name]} & {n} & {r['rho']} & ${fmtA(r['logA']['median'])}$ & ${fmtA(r['logA']['max'])}$ & {em} & {ex} \\\\")
        out.append(r'\addlinespace[2pt]')
    out.append(r'\midrule')
out[-1] = r'\bottomrule'
out.append(r'\end{tabular}')
out.append(r'\caption{Rounding depth $\rho$, schedule amplification $A$, and observed double-precision forward error of the evaluation schemes on random monic polynomials, in two regimes. Errors (err.) are the observed double-precision forward error in units of $u\sum_i|a_i||x|^i$; a coefficientwise backward-stable scheme reports at most about $\rho$. Medians and maxima over 12 polynomials and 3 points each; Motzkin--Eve rows are omitted where its numeric preprocessing failed verification.}')
out.append(r'\label{tab:numstab}')
out.append(r'\end{table}')
open(os.path.join(here, '..', 'sections', 'numstab_table.tex'), 'w').write('\n'.join(out) + '\n')
print('table written')
