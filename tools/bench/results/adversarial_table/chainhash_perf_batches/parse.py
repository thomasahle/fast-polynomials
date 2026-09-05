#!/usr/bin/env python3
"""parse.py <batch.out>: summarise bench (tp/lat4 per length) and harness (JSON) sections per version."""
import sys, re, json, collections
txt = open(sys.argv[1]).read()
sections = re.split(r'^### ', txt, flags=re.M)
bench = collections.OrderedDict(); harness = collections.OrderedDict()
for sec in sections[1:]:
    head, _, body = sec.partition('\n')
    kind, tag = head.split()[0], head.split()[1] if len(head.split()) > 1 else ''
    load = re.search(r'load averages: ([\d.]+)', head)
    load = load.group(1) if load else '?'
    if kind == 'bench' or kind == 'bench2':
        cur = None
        for line in body.splitlines():
            m = re.match(r'== (.*?) ==', line)
            if m: cur = m.group(1); bench[(tag, kind, cur)] = {'load': load, 'rows': {}}; continue
            m = re.match(r'\s*(\d+) \|\s*([\d.]+)\s+([\d.]+) \|\s*([\d.]+)\s+([\d.]+) \|\s*([\d.]+) \|\s*([\d.]+)', line)
            if m and cur and kind == 'bench':
                l = int(m.group(1)); bench[(tag, kind, cur)]['rows'][l] = dict(tp=float(m.group(2)), lat=float(m.group(4)), latmed=float(m.group(5)), gbps=float(m.group(6)), ghz=float(m.group(7)))
            m = re.match(r'\s*(\d+) \|\s*([\d.]+)\s+([\d.]+) \|\s*([\d.]+)\s+([\d.]+) \|\s*([\d.]+)\s+([\d.]+)\s*$', line)
            if m and cur and kind == 'bench2':
                l = int(m.group(1)); bench[(tag, kind, cur)]['rows'][l] = dict(lat=float(m.group(2)), lats=float(m.group(4)), lati=float(m.group(6)))
            m = re.search(r'avg (?:lat4 )?over 1\.\.31 B.*?: (.*)', line)
            if m and cur: bench[(tag, kind, cur)]['avg'] = m.group(1)
    elif kind == 'harness':
        for line in body.splitlines():
            if line.startswith('{'):
                d = json.loads(line); harness.setdefault(tag, {'load': load, 'rows': {}})['rows'][(d['name'], d['size_bytes'])] = d['gbps']
print("BENCH (cycles per call; lat4 = SMHasher3-style serialized, min-based; tp = independent calls; GB/s from tp)")
for (tag, kind, var), d in bench.items():
    r = d['rows']
    if kind == 'bench':
        pick = lambda l, k: r[l][k] if l in r else float('nan')
        print(f"  {tag:4s} {var:26s} load {d['load']:>5s} | lat4 @8/16/31/64 B: {pick(8,'lat'):6.1f} {pick(16,'lat'):6.1f} {pick(31,'lat'):6.1f} {pick(64,'lat'):6.1f} | avg1..31 {d.get('avg','?'):28s} | tp cyc @64/512/16384: {pick(64,'tp'):6.1f} {pick(512,'tp'):6.1f} {pick(16384,'tp'):7.1f} | GB/s @64/512/16384: {pick(64,'gbps'):5.2f} {pick(512,'gbps'):5.2f} {pick(16384,'gbps'):5.2f} | GHz {pick(16384,'ghz'):.2f}")
    else:
        pick = lambda l, k: r[l][k] if l in r else float('nan')
        print(f"  {tag:4s} {var:26s} load {d['load']:>5s} | bench2 @8/16/31/64 B lat4: {pick(8,'lat'):6.1f} {pick(16,'lat'):6.1f} {pick(31,'lat'):6.1f} {pick(64,'lat'):6.1f} | lat4s: {pick(8,'lats'):6.1f} {pick(16,'lats'):6.1f} {pick(31,'lats'):6.1f} {pick(64,'lats'):6.1f} | lat4i: {pick(8,'lati'):6.1f} {pick(16,'lati'):6.1f} {pick(31,'lati'):6.1f} {pick(64,'lati'):6.1f} | {d.get('avg','?')}")
print("HARNESS (GB/s, ./speed 5 0.5 run ChainHash)")
for tag, d in harness.items():
    print(f"  {tag:4s} load {d['load']:>5s} | " + " | ".join(f"{name.replace('ChainHash, ','').replace(', K=5+twist','')} @{sz}: {g:5.2f}" for (name, sz), g in d['rows'].items()))
