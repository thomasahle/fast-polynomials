#!/bin/bash
# Clean-room build of an arXiv bundle: extract into a temp dir, compile with pdflatex only
# (no bibtex: the .bbl must be inside), then check fonts and warnings.
set -u; TAR=${1:?tarball}; T=$(mktemp -d); tar -xzf "$TAR" -C "$T"; cd "$T"
[ -f main.tex ] || cd "$(ls -d */ | head -1)"
for i in 1 2 3 4; do pdflatex -interaction=nonstopmode -halt-on-error main.tex > pass$i.log 2>&1 || { echo "PASS $i FAILED"; grep -n "^!" -A3 main.log | head -20; exit 1; }; done
echo "pages: $(grep -o 'Output written on main.pdf ([0-9]* pages' main.log)"
echo "errors: $(grep -c '^!' main.log)  undefined refs/cites: $(grep -c 'Reference.*undefined\|Citation.*undefined' main.log)  rerun warnings: $(grep -c 'Rerun to get' main.log)"
echo "missing files: $(grep -c '^No file \|LaTeX Warning: File .* not found\|! I can.t find file\|! LaTeX Error: File .* not found' main.log)"; grep -n "^No file \|LaTeX Warning: File .* not found\|I can.t find file\|LaTeX Error: File .* not found" main.log | head -5
echo "non-embedded fonts: $(pdffonts main.pdf 2>/dev/null | awk 'NR>2 && $5=="no"' | wc -l)"
echo "bundle files: $(find . -type f ! -name '*.log' ! -name '*.aux' ! -name '*.out' ! -name 'main.pdf' | wc -l), size $(du -sh . | cut -f1)"
echo "dir: $T"
