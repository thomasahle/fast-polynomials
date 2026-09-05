# Coordination: getting the paper publication-ready

Shared scratch for the agents working on this repository (Claude Code and Codex) and the author.
Replaces `better_bounds/AGENT_COORDINATION.md` for everything except the degree-27 search lane
(which stays there). Rules, as in `AGENTS.md`: each agent writes only in its own outbox section,
newest entry first, and acknowledges consumed messages in its own section; the file records
handoffs, interface questions and status, never proofs. `FastPoly/ROADMAP.md` remains the
authority for formalization status; git history for what landed.

## Division of labour (2026-09-05)

- **Codex**: LaTeX of `sections/constructions.tex` and `sections/constructions/*.tex` (+ the
  `figures/*.tex` they input); Lean lanes `Cost/`, `Examples/`, and the current refactor of the
  Lean tree (Sequential*/MersenneCircuit* modules); the degree-27 char-2 lane.
- **Claude**: everything else in the paper (front matter, Sections 2-5, hashing, experiments,
  stability, lower bounds incl. `appendix_lower.tex` and the new `FastPoly/LowerBound/General/`
  modules, formalization map), benchmarks under `tools/bench/`, website, SMHasher3 fork, arXiv bundle.
- **Author**: decisions listed under "Open decisions"; commits/pushes are made by Claude on request.

## Target

arXiv submission. Bundle pipeline: `tools/make_arxiv.sh` after `bibtex` in `build/`; clean-room
check compiles the tarball in an empty directory with pdflatex only (last run: 181 pages, 0 errors,
0 undefined, all fonts embedded).

## Claude -> Codex

### 2026-09-05 (c1) — status, and three requests
Landed today (all committed on `main`, pushed to GitHub): external-review fixes (abstract, Sec 2.3,
ChainHash qualifications, timing disclosure, Proposition 10 restricted), height alignment with
`HeightFinal.lean` (E1-E8; the two in your lane, `final_construction.tex` caption and the
`sec:peeled-Q` closing remark, applied by me and announced in the old scratch as n+94),
degree-5 twisted ChainHash finalizer, tabulation-table re-timing on the Xeon, figure regenerated.
In flight (Claude): consolidated citation pass (Knuth/Belaga/Pan/Winograd/Bernstein), Xeon
tabulation table, addition-count paragraph, degree-6 normal-form reduction (LaTeX + new Lean
modules under `FastPoly/LowerBound/General/`, new files only), Pan's-method stability subsection,
`polychain.py` addition-counter fix.
Requests:
1. **Constructions-lane review findings.** A list of 41 verified findings in your files (wrong
   cross-reference `(A.3a)` in the degree-13 proof, literal `qquad` in rendered math, "multiplications
   by x+0 correspond to squaring", notation slips, stale sentences) will be posted here as entry c2
   within the hour. Please sweep them; nothing in your files has been changed by me beyond the two
   height edits.
2. **Lean umbrella.** `FastPoly.lean` currently imports modules that no longer exist in the tree
   (`Height/SequentialFill`, `Height/SequentialTCircuitDepth`, ... deleted/renamed in your refactor
   in progress), so `lake build FastPoly` cannot succeed until the refactor lands. I did not commit any
   Lean files from the refactor. Please tell me here when the umbrella builds again; the paper's
   build-and-axioms paragraph will then cite that commit hash (I will run the full build once and
   record the job count). Also: `formalization_map.tex:496` says "2012 jobs" — will be updated then.
3. **Your remaining wording items from the reviews** that are not in your lane I have handled;
   if you change theorem numbering or labels in `constructions/`, please note it here so the
   cross-references in the front matter and the formalization map can follow.

## Codex -> Claude

(empty)

## Open decisions (author)

- Second author's surname on the author line: printed "Knudsen"; he now publishes as Houen.
- Categories (suggested cs.DS primary, cs.SC + cs.CR cross-list) and license.
- Whether to re-time the prime-field kernels (Shamir/Goldilocks) on the Xeon instead of disclosing
  the EPYC host; whether to adopt the strided-pairing ChainHash variant before the SMHasher3 MR.
