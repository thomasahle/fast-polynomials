#!/usr/bin/env python3
import re, sys, os, glob, math
S = "/private/tmp/claude-501/-Users-ahle-repos-notes-fast-polyhash/671fdc97-fe99-4719-bea0-4eedf88d5744/scratchpad/sd_runs"
order = [l.strip() for l in open(os.path.join(S, "hashlist.txt")) if l.strip()]
rowre = re.compile(r"^\s*(\d+)\s+(~[\w~]+)\s+(\d+)\s+/\s+2\^(\d+)\s+(<?\s*-?[\d.]+)\s*(!!!!!)?\s*$")
out = []
for name in order:
    f = os.path.join(S, f"sd_{name}.txt")
    if not os.path.exists(f):
        out.append((name, "MISSING", "", "", "", "", "", "", "", ""));  continue
    txt = open(f).read()
    if "EXIT " not in txt:
        out.append((name, "RUNNING", "", "", "", "", "", "", "", "")); continue
    bits = re.search(r"Ideal rate is 2\^-(\d+)", txt)
    bits = int(bits.group(1)) if bits else -1
    verdict = "PASS" if re.search(r"^PASS$", txt, re.M) else ("FAIL" if "FAIL" in txt else "??")
    tier = "default"
    rows = []
    for line in txt.splitlines():
        if line.startswith("Extended tier"): tier = "extended"
        m = rowre.match(line)
        if m:
            L, d, c, log2n, lr, flag = m.groups()
            rows.append((tier, int(L), d, int(c), int(log2n), bool(flag)))
    ext = any(r[0] == "extended" for r in rows)
    nfail = sum(1 for r in rows if r[5])
    # worst = max observed rate c/2^n; tie -> larger count; zero rows: worst bound
    def rate(r): return r[3] / 2.0 ** r[4]
    nz = [r for r in rows if r[5]] or [r for r in rows if r[3] > 0]
    if nz:
        w = max(nz, key=lambda r: (rate(r), r[3]))
        wstr = f"{w[1]} B, {w[2]} ({w[0]})"
        cnt = f"{w[3]} / 2^{w[4]}"
        lr = f"{math.log2(rate(w)):.1f}"
    else:
        maxn = max(r[4] for r in rows) if rows else 0
        w = None
        wstr = "none (all rows 0)"
        cnt = f"0 / 2^{maxn}"
        lr = f"< -{maxn}"
    tm = re.search(r"Testing took ([\d.]+) seconds", txt)
    tm = tm.group(1) if tm else "?"
    slow = "" if ext else "no (slow-flagged)"
    out.append((name, verdict, bits, wstr, cnt, lr, nfail, len(rows), "yes" if ext else "no", tm))
hdr = "| hash | bits | verdict | worst pair (len, diff, tier) | count / seeds | log2 rate | failing rows / rows | extended tier run | time (s) |"
print(hdr); print("|" + "---|" * 9)
for o in out:
    name, verdict, bits, wstr, cnt, lr, nfail, nrows, ext, tm = o
    if verdict in ("MISSING", "RUNNING"):
        print(f"| {name} | | {verdict} | | | | | | |"); continue
    print(f"| {name} | {bits} | {verdict} | {wstr} | {cnt} | {lr} | {nfail} / {nrows} | {ext} | {tm} |")
