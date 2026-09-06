# Paper build and arXiv packaging.  Targets:
#   make pdf     - build/main.pdf (pdflatex, bibtex, pdflatex x3; never latexmk)
#   make arxiv   - arxiv/ + arxiv.tar.gz + arxiv.zip (flat source package with main.bbl)
#   make check   - compile the tarball in an empty directory with pdflatex only
#   make all     - pdf, arxiv, check
#   make clean   - remove build products (keeps figures/*.pdf)
SHELL   := /bin/bash
ROOT    := $(abspath .)
BUILD   := build
PDFLATEX := pdflatex -interaction=nonstopmode -output-directory=$(BUILD)
SECTIONS := $(wildcard sections/*.tex sections/constructions/*.tex figures/*.tex)

.PHONY: all pdf arxiv check clean

all: pdf arxiv check

$(BUILD)/main.pdf: main.tex header.tex references.bib $(SECTIONS) figures/bench_all.pdf
	@mkdir -p $(BUILD)
	rm -f $(BUILD)/main.aux $(BUILD)/*.aux
	$(PDFLATEX) main.tex >/dev/null || { grep -n -A3 '^!' $(BUILD)/main.log | head -40; exit 1; }
	cd $(BUILD) && BIBINPUTS=$(ROOT): BSTINPUTS=$(ROOT): bibtex main >/dev/null
	$(PDFLATEX) main.tex >/dev/null
	$(PDFLATEX) main.tex >/dev/null
	$(PDFLATEX) main.tex >/dev/null || { grep -n -A3 '^!' $(BUILD)/main.log | head -40; exit 1; }
	@echo "errors: $$(grep -c 'LaTeX Error\|Emergency stop' $(BUILD)/main.log)  undefined: $$(grep -c 'Reference.*undefined\|Citation.*undefined' $(BUILD)/main.log)  $$(grep 'Output written' $(BUILD)/main.log)"
	@test "$$(grep -c 'LaTeX Error\|Emergency stop' $(BUILD)/main.log)" = 0
	@test "$$(grep -c 'Reference.*undefined\|Citation.*undefined' $(BUILD)/main.log)" = 0

pdf: $(BUILD)/main.pdf

arxiv.tar.gz arxiv.zip: $(BUILD)/main.pdf tools/make_arxiv.sh
	bash tools/make_arxiv.sh
	rm -f arxiv.zip && (cd arxiv && zip -qr ../arxiv.zip .)
	@ls -la arxiv.zip | awk '{print "arxiv.zip", $$5, "bytes"}'

arxiv: arxiv.zip

check: arxiv.tar.gz tools/arxiv_cleanbuild.sh
	bash tools/arxiv_cleanbuild.sh $(ROOT)/arxiv.tar.gz

clean:
	rm -rf arxiv arxiv.tar.gz arxiv.zip $(BUILD)/main.aux $(BUILD)/*.aux $(BUILD)/main.bbl $(BUILD)/main.blg $(BUILD)/main.log $(BUILD)/main.out $(BUILD)/main.toc $(BUILD)/main.pdf
