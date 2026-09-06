#!/bin/bash
# Assemble a flat arXiv source package (run via `make arxiv`; needs a fresh build/main.bbl):
# figures, references.bib, the built main.bbl) and arxiv.tar.gz.  Run after a successful
# `make pdf` (pdflatex, bibtex, pdflatex x3) so that build/main.bbl is fresh.
set -euo pipefail
cd "$(dirname "$0")/.."
rm -rf arxiv arxiv.tar.gz
mkdir -p arxiv
python3 - <<'PY'
import re, os, shutil
seen, todo = set(), ['main.tex']
pat = re.compile(r'\\(?:input|include|includegraphics(?:\[[^\]]*\])?|bibliography|usepackage(?:\[[^\]]*\])?)\{([^}]*)\}')
def strip_comments(s): return re.sub(r'(?<!\\)%.*', '', s)
while todo:
    f = todo.pop()
    if f in seen or not os.path.isfile(f): continue
    seen.add(f)
    if not f.endswith('.tex'): continue
    for m in pat.finditer(strip_comments(open(f, encoding='utf-8').read())):
        for name in m.group(1).split(','):
            name = name.strip()
            cands = [name, name + '.tex', name + '.bib', name + '.pdf', name + '.png', name + '.sty']
            for c in cands:
                if os.path.isfile(c): todo.append(c); break
for f in sorted(seen):
    os.makedirs(os.path.dirname('arxiv/' + f) or 'arxiv', exist_ok=True)
    shutil.copy(f, 'arxiv/' + f)
print('copied', len(seen), 'source files')
PY
cp build/main.bbl arxiv/main.bbl
( cd arxiv && tar czf ../arxiv.tar.gz . )
echo "package: $(find arxiv -type f | wc -l | tr -d ' ') files, $(du -sh arxiv.tar.gz | cut -f1)"
