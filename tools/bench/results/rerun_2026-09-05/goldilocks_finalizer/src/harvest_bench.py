"""Markdown rows from a bench_goldi log: avg 1-31, 8/16/64 B small-key cycles, bulk GB/s (bytes/cycle)."""
import re, sys
for path in sys.argv[1:]:
    txt = open(path).read()
    print(f"### {path.split('/')[-1]}")
    m = re.search(r'load at start: (.*)|load before bench: (.*)', txt); print("load at start:", (m.group(1) or m.group(2)).strip() if m else "?")
    m = re.search(r'cycles/ns ([\d.]+)', txt); print("cycles/ns:", m.group(1) if m else "?")
    lines = txt.splitlines()
    hdr = next(l for l in lines if l.startswith('function') and 'avg1-31' in l)
    lens = [int(t) for t in hdr.split()[1:] if t.isdigit()]
    small = {}
    for l in lines:
        if '|' in l and not l.startswith('function') and not l.startswith('=='):
            name = l[:22].strip(); vals = l[22:].split('|')[0].split(); avg = float(l.split('|')[1])
            small[name] = (dict(zip(lens, map(float, vals))), avg)
    bulk = {}
    for l in lines:
        mm = re.match(r'(.{22})\s+([\d.]+) \(\s*([\d.]+)\)\s+([\d.]+) \(\s*([\d.]+)\)', l)
        if mm: bulk[mm.group(1).strip()] = tuple(map(float, mm.groups()[1:]))
    print("| function | avg 1-31 B | 8 B | 16 B | 64 B | 16 KB GB/s (B/cyc) | 512 B GB/s (B/cyc) |")
    print("|---|---|---|---|---|---|---|")
    for name, (d, avg) in small.items():
        b = bulk.get(name)
        bs = f"{b[0]:.2f} ({b[1]:.2f}) | {b[2]:.2f} ({b[3]:.2f})" if b else "- | -"
        print(f"| {name} | {avg:.2f} | {d[8]:.1f} | {d[16]:.1f} | {d[64]:.1f} | {bs} |")
    print()
