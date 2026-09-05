import re,sys
def parse(path):
    rows={}; cur=None; on=False
    for line in open(path):
        if 'Universal Hash Comparison' in line: on=True; continue
        if '128-bit' in line: on=False
        if not on: continue
        m=re.match(r'^N=(\d+)',line)
        if m: cur=int(m.group(1)); rows[cur]={}; continue
        m=re.match(r'^\s+(Horner \(2N-1 mults\)|Horner-Unrolled|Horner-Parallel|Injective \(N mults\)|Injective-Parallel \(3N\)|Injective-Lanes \(N\+L\)|CLNH \(multilinear\)|BRW \(recursive\)|c-decBRW \(c=4\)):\s+Mean: ([\d.]+) ± ([\d.]+)',line)
        if m and cur is not None and cur in rows: rows[cur][m.group(1)]=(float(m.group(2)),float(m.group(3)))
    return rows
cols=['Horner (2N-1 mults)','Horner-Unrolled','Horner-Parallel','Injective (N mults)','Injective-Parallel (3N)','Injective-Lanes (N+L)','BRW (recursive)','CLNH (multilinear)']
o1=cols[:7]  # O(1)-key columns eligible for bold
def block(path,label):
    rows=parse(path); out=[f"\\multicolumn{{9}}{{l}}{{\\emph{{{label}}}}} \\\\"]
    for N in sorted(rows):
        r=rows[N]
        if not all(c in r for c in cols): continue
        best=min(r[c][0] for c in o1 if c in r)
        cells=[]
        for c in cols:
            v,sd=r[c]; s=f"{v:.0f}"
            if c in o1 and v<=best*1.01: s="\\textbf{"+s+"}"
            if sd/v>0.05: s+="$^{\\dagger}$"
            cells.append(s)
        out.append(f"{2*N:3d} & "+" & ".join(cells)+" \\\\")
    return "\n".join(out)
print(block(sys.argv[1], sys.argv[2]))
