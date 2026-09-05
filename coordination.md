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

### 2026-09-05 (c4) — degree-6 normal-form repair landed (paper + Lean); please mirror into your map row check
`sections/appendix_lower.tex` / `lower.tex`: the first-gate absorption now uses the gauge identity
(Ax+a)(Bx+b) = A·x(Bx+b+aB/A) + ab; the six normal-form slots become quadratic in the six parameters
(Q = ν∘H) and the lemma is proved by cases (kernel; midpoint of two parameter points on one gauge orbit,
char ≠ 2; orbit inside the image; transversal case with the explicit inverse Θ), plus transport of the
everywhere-defined inverse. Lean: new tree `FastPoly/LowerBound/General/` (10 files, 0 sorry; not in the
umbrella; build with `lake build FastPoly.LowerBound.General.Main FastPoly.LowerBound.General.Transport`,
1728 jobs), main theorem `no_rationalInverse_general` with `no_rationalInverse_affine_of_general`
recovering the old statement. Formalization-map row for the degree-6 bound updated accordingly; the full
note is n+95 in `better_bounds/AGENT_COORDINATION.md`. When you pin the Lean commit (item F of c3), include
this target in the build paragraph.

Also landed for item B of c3: certified degree-7 row timed on both machines (tools/bench/bench_tabrows.cpp, class `septic7_64`): `This Paper ($k=7$, certified) & 2311$\pm$32 & 7-wise & 4678$\pm$4 & 7-wise \\` (search circuit in the same runs: 2313 / 4942); details in `notes/handoff_2026-09-05/tabrows/k7.md`. Note: the degree-7 lemma left the appendix with the degree-5 finalizer, so "certified" needs a pointer (verify7.py / website CIRCUITS[7]) or a one-paragraph restatement.

### 2026-09-05 (c3) — handoff: Claude is winding down (token budget); please take these over
Claude's session is near its limit and will only commit the results of jobs already running. Everything
below is handed to Codex. Working material is in `notes/handoff_2026-09-05/` (untracked: /notes/ is in
.git/info/exclude; read it in place) and `tools/bench/results/`.

A. **Re-run the tables whose raw logs did not survive** (`tools/bench/results/MANIFEST.md`, section
   "Untraceable numbers"): the three application-benchmark tables (app_countsketch/linearprobe/xorfilter,
   ARM + x86), the Mersenne 2^89-1 share-generation and Goldilocks rows (ARM; x86 rows currently come from
   an AMD EPYC run — re-time on the Xeon so the paper has one x86 host), the XXH3-128 cell of
   tab:injective:adversarial (harness tools/bench/adversarial: `./speed 5 0.5 run XXH3`), the Mersenne
   SMHasher3 port numbers in injective.tex (1.59 B/c, 133 cycles, 14.4 B/c; `poly-mersenne*` hashes in the
   fork ~/repos/smhasher3/build-chainhash, `--test=Speed`), the adversarial 2^31-trial counts of
   appendix_adversarial.tex (tools/bench/adversarial Makefile `results` target; long — run on the Xeon with
   nohup), and the two tab:numstab cells (regenerate with the script named in manifest §11).
   Protocol: paper protocol per table (fastest 100 of 200 reps where the source does that), record
   machine/compiler/date/load, save raw logs under `tools/bench/results/rerun_2026-09-05/{m2,xeon}/` with a
   README, then update the LaTeX rows and every prose sentence quoting the old numbers (grep the old
   values). Xeon: `ssh thomas-ahle@hardware.normalcomputing.net`, sources under `~/fastpoly-bench/`,
   `taskset -c 80-95`, clang 21.1.8. M2 Pro: wait for load < 3.
B. **Certified 7-wise row**: an agent is timing the certified degree-7 circuit (chainhash's former
   finalizer; verify7.py / exh7.c) as a new bench_tabrows row on both machines; its result lands in
   `notes/handoff_2026-09-05/tabrows/k7.md` (or is reported in coordination by Claude). Replace the
   "not certified" k=7 row of the Section 5.7 table with it.
C. **Pan's-method stability subsection**: drafts (appendix_pan.tex, integration.md, theory.md, measure.md,
   new tool scripts) will appear under `notes/handoff_2026-09-05/stability_pan_drafts/` when the running
   workflow finishes (Claude will copy them and note it here). Integrate into sections/numerical_stability.tex
   per integration.md (the Proposition-10 repair already landed there), add the numstab rows, `git add -f`
   the tool scripts.
D. **Degree-6 normal-form reduction**: LaTeX repair in appendix_lower.tex/lower.tex and new Lean modules
   FastPoly/LowerBound/General/ are landing from a running workflow; its note goes to the old scratch as
   n+95 — please mirror the essentials here and check the formalization-map row it edits.
E. **Front matter coherence + regression proofread**: after A–D, one fresh read of abstract, introduction,
   conclusion and open problems for a single consistent story and hedges; then a light whole-paper pass for
   typos/duplicates/broken refs; fix the remaining overfull lines (formalization_map.tex ×3).
F. **Lean pin**: when your refactor lands and `lake build FastPoly` (+ `FastPoly.LowerBound.Main` and the
   new General target) is green, put the commit hash and job count into formalization_map.tex's
   "Build and axioms" paragraph (it says 2012 jobs) and the README's reproduction commands.
G. **Bundle**: `cd build && bibtex main` (BIBINPUTS/BSTINPUTS = repo root), pdflatex ×2, then
   `tools/make_arxiv.sh`, then `tools/arxiv_cleanbuild.sh arxiv.tar.gz` (extracts to a temp dir, pdflatex
   only; require 0 errors, 0 undefined, all fonts embedded). Submission metadata still needs the author:
   surname (Knudsen vs Houen), categories, license.
H. **Commits**: stage only your own hunks (`git diff --cached` before every commit); the author keeps
   uncommitted work in the tree. Push to origin/main when a step is complete.

### 2026-09-05 (c2) — review findings in your LaTeX lane (constructions/, figures/*.tex): please sweep

These are the items announced in c1 (request 1). Source: two review passes (the 45-reader consistency review of 2026-09-04, `notes/handoff_2026-09-04/review_results.md`, plus the external referee's page notes), each item re-verified against the current tree today (line numbers are current; your Mersenne-family removal already retired the old sec:peeled-Q remark items, `modulo t^8`, `level-4 fill`, `is a algebraically`, `the latter given (H_2,H_4)`, and the `odd\_realizable\_pairs` overfull). The three external-referee items named in c1 (`(A.3a)`, literal `qquad`, "x+0 correspond to squaring") turned out to be outside your lane, see the end.
Nothing was applied by me in your files beyond the E2/E3 height edits (and the figures/ rendering fixes) announced in n+94 and restated in c1; everything below is report-only, for you to sweep.

Substantive (claims, semantics, cross-references):
1. `odd_gadgets_and_induction.tex:347,361` — the n≡3 (mod 8) case cites `alg:constr-known-2n-1` (the binary known-powers construction for Q_{2^k-1}, fill_gadgets.tex:13, no parameter l) — cite `alg:constr-Q-odd` (:5), which lem:Q-odd-degree-with-powers actually uses.
2. `final_construction.tex:54` — right after "Write n=8k+7" the parenthetical says "using \bar Q_{15} or \bar Q_{8k+7}"; with that k, \bar Q_{8k+7} is the degree-n gadget — the step calls \bar Q_{2k+1} / \bar Q_{4k+3} (alg:constr-8k+7), barred whenever the auxiliary degree is ≡7 (mod 8).
3. `final_construction.tex:132` — "the one product (S_3+S_2)(S_3-S_2)" is the 8k+7 product only; the 8k+3 step uses (S^{(1)}_2+S^{(1)}_1)(S^{(1)}_2-S^{(1)}_1) (alg:constr-8k+3).
4. `final_construction.tex:77` — "S^{(1)}_3=\mathcal Q_{2k-1}" is unconditional; for k=1 (n=11) alg:constr-8k+3 sets S^{(1)}_3=α_1, read directly.
5. `overview.tex:124-125` — "every integer divided by is one of …" contradicts the bullets below it (k/2, (k-1)/2, k-1, γ_k are not in the display) — "divides one of".
6. `overview.tex:137-138` — the five slopes 2k,2k,-2k,k,k are attributed also to Q_{4k+1}(x,H_2); lem:Q4k+1-from-H2's table (t_recursion.tex:1211) starts with a unit pivot for β, i.e. 1,2k,-2k,k,k. Bad(n) is unaffected.
7. `overview.tex:68` — heading "Fill $A_l$": undefined symbol; the gadget is A_{2^l} everywhere else (overview:152, final_construction.tex:5).
8. `overview.tex:46-49,76` — post-migration staleness: still describes fill-supplied Q_{2^s-1} and a "peeled variant … computes the same family … same ledger as the fill route", but fill_gadgets.tex now defines only the binary Q (sec:peeled-Q is the whole section; alg caption "Known-powers construction (binary recursion)"). Also three index letters for one gadget: s (:48-49), k (:76), t (:153).
9. `t_recursion.tex:158-160` — lem:fill-Q-count (fill_gadgets.tex:545, stated for k≥2) is cited for the two Q_{2^{l-1}-1} blocks at l=2, which are Q_1=x+α_0 — add "(for l=2 these are Q_1, zero products, in agreement with the formula)".
10. `t_recursion.tex:302,436-437,916` — "H_1=H_D, H_2=\widetilde H_D" redefines H_2 inside lemmas whose hypotheses supply the quadratic H_2 — use H^{(1)},H^{(2)} (or h,\tilde h).
11. `t_recursion.tex:881` — decoder precondition "\tilde H_4-H_4 has degree zero in x" excludes ρ=0; the lemma (:270) says "is a scalar".
12. `t_recursion.tex:320-326` (fig:Rk2l-stages caption) — "in every branch … after which the low unitriangular Q-block is read": the even branch has no low Q-block; and "The red markers are the parameter-free boundary rows", but fig_Rk2l_stages.tex draws no seam marker on any panel (only the legend swatch at :64), and that legend (:65-67) omits the -m-τ correction at the Q_+/δ → Q_0 boundary (:823, :898). Either add seam markers at the junctions or reword caption + legend.
13. `t_recursion.tex:1069` — "crown over the T_{2k,2} call": the figure (fig_4k1_crown.tex:11) and the caption (:1076) say the T_{k,4} core; a,e,ρ are parameters of the T_{2k,2} call itself.
14. `t_recursion.tex:1075` — "the quadratic and quartic powers are shared": H_2,H_4 are the monic base polynomials; "powers" is used two sentences later for H_4^k.
15. `odd_gadgets_and_induction.tex:73` — motivation names only the 8k+3 step and n=31, but alg:constr-8k+7 also calls barred gadgets (\mathcal Q_{2k+1}, \mathcal Q_{4k+3}) and the paragraph proves the whole family \bar Q_{8k+7}.
16. `odd_gadgets_and_induction.tex:241-249` + `fig_odd_gadgets.tex:50` — the 4×4 block solve is written as -(1/k^2) adj(M)(…) with adj(M) never expanded, while the figure says "The matrix inverse is displayed explicitly" (AGENTS.md rule 1 wants an explicitly supplied inverse); the column reduction at :236-239 already gives an explicit back-substitution dividing only by k (y_1=Δp_4, y_2=Δp_5-A_1y_1, v=(Cy_1+Dy_2-Δp_6)/k, u=(Ey_1+Fy_2-kLv-Δp_7)/k, b_3=y_1-k(u+v), b_4=y_2-k(u+v)) — display that, or soften the figure text.
17. `odd_gadgets_and_induction.tex:150` — b_i=α_{N+2+i} reverses the slot order of alg:constr-fill (β_4,…,β_0), i.e. b_i ↔ β_{4-i} — write b_i=α_{N+6-i}, or say "in reverse slot order" at the "just a relabelling" sentence.
18. `odd_gadgets_and_induction.tex:448` + `fig_odd_induction_steps.tex:30` — "whose decoder reconstructs the powers needed by the low auxiliary gadget" / "reconstruct H_2,H_4": the recursion yields only H_2; H_4 comes from decoding S_2=Q_{4k+1}(x,H_2) first (:639, :733).
19. `fig_odd_induction_steps.tex:14,25` — second seam "+1" vs the proof's [x^{2k+1}]E_2=-1 (:539, the -P' frame); panel (b) has no seam between the squared recursion and the low residual although :709 names the fixed leading coefficient of xS_3 there (1 for k>1) — pick one frame and make the seam convention uniform (or say in the caption that only square-gadget boundaries are marked).
20. `finite_bases.tex:76` (fig:septic-circuit caption) — "the seven parameters α_0,…,α_6 enter only as constant terms of these affine forms": α_0 is added at the output (P_7=α_0+y+w+v, :66; fig_septic_circuit.tex:33), not a gate input.
21. `finite_bases.tex:214-216`, `:403-405` + `fig_special_case_decoders.tex:9-15` — "A coloured block denotes a monic polynomial recovered from the indicated square window" is wrong for the terminal blocks (scalars; n=31 recovers C by division by x); "the only contribution from the next block is the displayed monic coefficient 1 or -1" misses the n=15 H_4 window absorbing -1 at row 5 and the known -(2b+2) at row 4 (:278); and the n=15 row draws no seam between the H_4 block and the bottom block.
22. `decoder_calculus.tex:51,59-60` — the Extractable / given definitions index coefficients by an undefined [\deg P], [\deg B_k] (under [n]={1,…,n} this drops [x^0]P, which the decoders read) — use \idx{\deg P}, \idx{\deg B_k} as the sibling definition at :166-176 does.
23. `decoder_calculus.tex:254-256` (fig:jacobian-pattern caption) — "blue cells are nonzero field constants" needs char≠2 (the top-row slopes of P_7 are 2; the slope-6 entries of P_15 in rows x^14, x^13 vanish over GF(3), which Bad(15)={2} admits); and "each row exposes one fresh parameter with a constant slope" is not what the decoder does (rows x^2, x^1 have no constant cell; the decoder recovers z_2,z_1,R,W) — say "one fresh quantity, a parameter or an internal value".
24. `decoder_calculus.tex:472` + `overview.tex:104-113` — fig:triangular-blocks is keyed to fig:decoder-language, which is typeset in the next appendix (≈p.59 vs p.69 in the current build) with a caption scoped to "this appendix" — move the legend ahead of fig:triangular-blocks (caption "this and the following appendix") or write "keyed later in \Cref{fig:decoder-language} of \Cref{appendix:constructions}".
25. `fig_triangular_blocks.tex:23,25` — colour roles vs that key: the shifted recursion (the smaller instance) is `fp second` ("next block") and the low block (not recursive) is `fp recursive` ("smaller instance") — swap, or state that the colours are positional; :11 "rows<h" is styled `fp known` though not yet read (the key draws "rows<j" as `fp unread`); :5/:10 call the parameters "pivots".
26. `fig_causal_closures.tex:16-17,24-27` — panel (b) draws n_2+G_1 and n_1+G_2 at the identical extent under "shifted windows disjoint"; panel (c) draws the translate n+G to the right (lower degree in the figure grammar) and wider than its source — offset the windows, and put the higher window to the left.
27. `fig_causal_closures.tex:28-29` + `decoder_calculus.tex:494,507` — "Ψ_{n+i}=2Φ_i+ higher rows" uses subscript-coefficient notation found nowhere else (the paper writes \coeff), Φ_i is the i-th input polynomial in the two lemmas that follow, and the trailing "+" sits outside math; "constant pivot 2" / "slope 2" holds only for char≠2 (:731) — write [x^{n+i}]Ψ=2[x^i]Φ+… and add "(char≠2)".
28. `fig_top_window_calculus.tex:25` — δ is drawn `fp seam` (key: fixed boundary coefficient) but it is a slope-2 pivot (:754); the seam in that row is [x^d]E — restyle as `fp pivot`, or label the box 2δ+E_b.
29. `fig_Rk2l_stages.tex:34` — shared-base panel says "through L_1,L_2"; the D=4 factors are F_1,F_2 (t_recursion.tex:112-113); L_1,L_2 are the l≥3 factors.
30. `fig_Rk2l_stages.tex:56-57` — the ζ node is the only pivot without its slope; it is m (eq:R-odd-table, t_recursion.tex:792) — `{$\zeta$\\$m$}`.
31. `fig_fill_slots.tex:3` — panel (a) "One fill level, D=2^l" depicts the l≥3 branch only (the l=2 head is H_4+β_3, and the second component adds the scalar α_{D-2}) — add "(l≥3 branch)".
32. `fig_peeled_Q.tex:24` — "[x^m] residual" uses m, defined only inside the proof (fill_gadgets.tex:77, m=2^{k-1}-1) — write [x^{2^{k-1}-1}] or define m in the caption (:144-151). (The old Q_3→Q_7 strip / Θ(k^2) items are moot: figure redrawn.)

Typos, notation, rendering:
33. Bare math in headings → hyperref "math shift" bookmark warnings (every one in the current log is in these files): t_recursion.tex:1, odd_gadgets_and_induction.tex:437,626, finite_bases.tex:11,50,116,148,179 — \texorpdfstring{$…$}{…} as in main_theorem.tex:1.
34. \tilde vs \widetilde for the same shifted powers: t_recursion.tex 34/57 (the 4k+1 lemma + proof at :1030-1140 uses \tilde 6× while fig_4k1_crown.tex and its caption use \widetilde), odd_gadgets_and_induction.tex:101 \tilde H_8 vs \widetilde H_8 at its 7 other uses, final_construction.tex 3× \tilde, decoder_calculus.tex 4× \widetilde — one accent (or a macro).
35. t_recursion.tex:460,722 — summation index q collides with the block size q=D/4 (:60, :674) — rename to t; :811 "stage--2" (en dash; "stage-2" elsewhere).
36. decoder_calculus.tex:36,178 — "Throughout the appendix" / "the remainder of the appendix" predate the split into two appendix sections ("derivable" is used in fill_gadgets.tex:213 too) — "this and the following appendix"; :343,347,353,360 — blank lines inside lem:triangular-shift break the statement into paragraphs mid-sentence.
37. finite_bases.tex:236 — G_n=\rng n is defined and never used; :240 — \text{known} in running text (\emph or plain).
38. fig_jacobian_p7.tex:2, fig_jacobian_p15.tex:2 — header comment describes a C/v letter legend the files no longer use (they fill blue/orange/white).
39. fig_decoder_language.tex:41 "next shell" vs key :54 "next block"; :7/:30 the "low degree" label runs into panel (b)'s arrow (shift panel (b) right by 0.4); :52-64 legend text abuts the next swatch (open the columns by 0.25). fig_causal_closures.tex:9 \varnothing (only use in the paper; the lemma writes \emptyset); :10 the panel-(a) arrow is unlabeled and stops 1.5 mm short of the last block.
40. fig_top_window_calculus.tex:7,13 — the diagonal arrow shafts cross their own labels ("leading 1", "pivot m"); vertical arrows with `left=1.5mm` labels render clean. fig_septic_circuit.tex:14 — the P_7 node at 12.9 leaves no clearance for the "α_0+y+w+v" edge label (13.6 works); :8 — the Bezier control points inflate the bounding box by ≈0.6 cm below the ink (\useasboundingbox as first path). fig_final_recursion.tex:34/41 — the "m<n, …" note and the "multiply by x" label abut (raise the note to y=1.55, or put the label below the gate). fig_odd_induction_steps.tex:24 — bare T^{(1)},T^{(2)} (the proof squares T^{(i)}_{2k+1}).
41. [H] floats: decoder_calculus.tex:250 leaves ≈30% of p.55 blank (figure forced to p.56); finite_bases.tex:117,149,180 leave pp.119-120 about half empty — [t]/[htbp] if you accept the reflow.

External-referee items checked against your files: the literal "qquad"/"qquadh" in math, the "(A.3a)" reference and "Multiplications by x+0 …" are all outside your lane (the first two are already fixed; the last is appendix_polynomials.tex:1045-1048) — nothing to do there.

The paper-wide passes (abstract, Sec 2.3, hashing, experiments, stability, lower-bound reduction) are handled outside your lane.

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
