# Fast Polynomial Evaluation — interactive chain compiler

Companion website for *Fast Evaluation of Polynomials with Rational Preprocessing*.
Type a polynomial, get back a straight-line evaluation chain using
⌊n/2⌋+1 multiplications instead of Horner's n−1.

Everything runs client-side: exact BigInt rational arithmetic (char 0; over ℂ the
Gaussian rationals ℚ(i)), Mersenne-prime arithmetic (GF(2^61−1), GF(2^89−1),
GF(2^127−1)), and carryless GF(2^k) arithmetic (char 2).

## Structure

- `index.html`, `style.css` — the page (no build step; Preact + htm and KaTeX vendored). One card:
  example chips (over ℚ/ℝ: Taylor polynomials — with monic on, the degree-(n−1) Taylor
  polynomial plus xⁿ, so the series' coefficients stay recognisable — and the probabilists'
  Hermite polynomial Heₙ, monic with integer coefficients at every degree; the desktop opens
  on He₇, whose chain has four multiplications and constants of at most seven digits;
  over ℂ four chips with genuinely complex coefficients — the e^{ix} series (iᵏ/k!,
  written `(0+1/6i)x^3`), the expanded binomial (x+i)ⁿ (Gaussian integers, monic), the
  e^{(1+i)x} series ((1+i)ᵏ/k!) and a reseeding random polynomial over the Gaussian
  integers ℤ[i] — with the same monic rule for the series;
  over the hashing fields a random key —
  a fresh draw per click —, sparse, dense and a fixed reproducible key, all regenerated
  at the chosen degree) → the polynomial input (highlighted through a transparent
  textarea over a painted backdrop) → the field chooser, rendered from the `FIELDS`
  registry in `field.js` (three groups: exact ℚ, ℝ, ℂ · Mersenne primes
  2^61−1, 2^89−1, 2^127−1 · binary fields GF(2^32), GF(2^64), GF(2^128); ℝ is ℚ's exact
  preprocessing with the constants shown as doubles, reported as ≈ numeric, and ℂ the same
  exact preprocessing over the Gaussian rationals ℚ(i) — coefficients `i`, `2i`, `(1+2i)`,
  `(1/2-3/4i)x` — with the chain constants shown as complex doubles in the canonical token
  `(re±imi)` of `js/tokens.js`: `(0+2i)`, `(-2+1i)`, `(1.5-0.25i)`, real constants as plain
  doubles)
  → method chips → view tabs attached to the output pane (mathematical with
  factor/original form and exact/decimal (hex) constants — a display-only rewrite ·
  C code with float/fraction constants over ℚ, C99 `double complex` over ℂ · graph) → the comparison table (one row
  per method: multiplications with the scalar count, additions, multiplicative depth,
  exact or ≈ numeric; clicking a row selects the method; each method name links to its
  reference, listed under the table from `js/references.js`, which the generated C of a
  comparison method also cites; a caption spells out the columns and lists each row's note,
  including the measured rounding error of every ≈ numeric row) + Share (links name a held
  example as `ex=` instead of carrying its text). Copy is paired with
  Download, which packages every available C method with benchmark and assembly-audit
  scripts. On phones (≤ 640px, `COMPACT_QUERY` in `ui.js` and the matching media query in
  `style.css`) the same state renders as a short intro with Paper / GitHub (star count) /
  Share links and three cards: the input (three example chips beside the label, no degree
  stepper or monic toggle — the page opens on the ℚ e^x example at degree 5, monic, whose
  chain has small constants) with Field / Method dropdowns; the output with underline tabs
  and the form strip beside them, a static right-aligned Copy + Share row above the pane
  body (no Download; nothing floats over an equation), ℝ / ℂ constants to six
  significant digits, and a stats line (long rows scroll sideways, as in every pane);
  and a collapsed "Compare methods" disclosure.
- `js/rat.js` — exact rationals over BigInt (Lehmer gcd; `test/rat.test.js` checks it against Euclid)
- `js/gauss.js` — the Gaussian rationals ℚ(i) (`GaussRat`, Rat-compatible surface) and the
  ℂ field object `Cx`; `js/tokens.js` — the shared constant-token grammar of chain text
  (real, hex and complex tokens, `complexToken(re, im)`)
- `js/field.js` — field interface: ℚ, ℝ, ℂ, GF(p) and GF(2^k) (carryless mul, Frobenius roots),
  plus the `FIELDS` registry the chooser, worker and C emitter are driven by
- `js/poly.js` — dense polynomial arithmetic over any field
- `js/polyparse.js` — input parsing / pretty-printing. The grammar accepts the spellings
  people type for the same polynomial: `x^3/6`, `1/6x^3`, `(1/6)x^3`, `x**3`, `x³`, `2*x`,
  `x·2`, decimals and exponents (`0.5x`, `1.5e-3`), a Unicode minus, hex bit patterns over
  GF(2^k), and over ℂ (`parsePoly(src, { complex: true })`) the Gaussian literals `i`, `2i`,
  `(1+2i)`, `(1/2-3/4i)`; rejections say what was wrong (division by zero, a variable other
  than x, a fraction in a binary field, …); a sign after a sign folds (`x^3 + -1`), whitespace
  inside a number is rejected with a hint, and exponents above `MAX_PARSE_DEGREE` (10 000) are
  refused before anything is allocated. Tested in `test/polyparse.test.js`. `js/worker.js` adds
  the field-side checks: constants (degree 0) are rejected, GF(2^k) literals wider than k bits
  and denominators ≡ 0 mod p get named messages, and every field has a degree ceiling
  (`DEGREE_CEILING` in `js/methodlist.js`: 38 over ℚ / ℝ / ℂ, 255 over the Mersenne primes;
  the char-2 lane's cap is `MAX_DEGREE` = 26 in the same file, enforced in `compile2.js`),
  so a crafted link cannot spin the worker for minutes.
- `js/char2.js`, `js/n13decode.js`, `js/compile2.js` — the char-2 circuits and
  decoders (odd degrees 3 to 21; all but 7 and 17 have polynomial decoders valid over
  every characteristic-2 field, 7 and 17 take Frobenius roots and need a finite field),
  ported from the paper's research prototypes
- `js/char0/core.js`, `js/compile0.js` — the char-0 construction at any degree:
  a line-by-line port (byte-identical to the Python reference in tests) of `tools/polychain.py` + `tools/poly_schedule.py`
  (exact ℚ, or GF(2^89−1) for fast large-degree preprocessing); `js/char0/*.frag.js`
  are the reviewable per-function-group fragments `core.js` is assembled from
- `js/methods/` — the comparison methods. The UI shows Horner, Estrin,
  Rabin–Winograd, Knuth–Eve with numeric real-root preprocessing, and Pan's
  real degree-8 / general degree-≥9 schemes solved numerically from their
  explicit coefficient maps. Over ℂ the numeric rows are Knuth–Eve with complex roots
  (`knutheve-complex.js`), Pan's complex scheme of 1978 (`pan1978.js`, odd degree ≥ 11;
  an input whose coefficients are all real first tries the real schemes of `pan1978real.js`,
  since the complex homotopy cannot track a branch for Taylor-type inputs — when both fail
  the note says so) and Belaga's
  scheme (`belaga.js`, monic — non-monic inputs are scaled and a `P = lc * P̃` line
  restores the leading coefficient). Pan's search (radix/sign specs × Eve candidates × node
  subsets, each a multi-start Newton solve) is budgeted: node subsets are tried
  best-fitting first under every spec, the search stops shortly after a chain verifies
  at 1e-6, and at most 1600 cells (3–9 s) are spent, shared across the conditioning
  rescales; inputs whose chains the solver cannot reach (the e^x Taylor polynomial at
  degree 20) fail in seconds with a note instead of running for minutes.
  `js/compare.js` runs the displayed methods on the same input (`numericMethodsFor(mode)`:
  Knuth–Eve and Pan over ℚ / ℝ, plus Belaga over ℂ; every complex-coefficient row is
  verified by `verifyLinesComplex` in `motzkin.js`, the one complex verifier, at real and
  non-real sample points); `js/references.js` holds each method's citation (Belaga 1958 /
  Pan 1966 for the Belaga row)
- `js/cgen.js` — descriptor-driven C emission matching the paper's benchmark code
  (`tools/bench/framework/multiplication*.h`). All methods share the
  emitter; measured width-specific kernels supply PCLMULQDQ / PMULL for GF(2^32),
  GF(2^64), and GF(2^128), Mersenne arithmetic for 2^61−1, 2^89−1, and 2^127−1,
  or doubles for ℚ/ℝ; over ℂ the output is C99 `<complex.h>` (`double complex`, literals
  `re + im*I`, `#pragma STDC CX_LIMITED_RANGE ON` for clang — gcc does not implement the
  pragma, so it is guarded and the bundle's scripts pass `-fcx-limited-range` instead —
  compiled with `-lm`). Estrin rows are
  emitted by dependency layer so the compiler can
  schedule independent FMAs and apply SLP when profitable. For the hashing fields (GF(2^k)
  and the Mersenne primes) every file also exposes `eval_P_key(const T a[], T x)`, the same
  circuit reading its constants from a caller-supplied key (a uniform key gives a uniformly
  random monic polynomial), with `eval_P` as the baked-in wrapper; ℝ / ℂ headers record the
  chain's measured double-rounding error; doc-block lines wrap at 88 columns.
- `js/cbundle.js` — dependency-free `.tar.gz` creation for the Download button, plus
  the portable timing harness and an assembly report for FMA, SIMD, and CLMUL/PMULL;
  every generated file opens with `cSourceHeader` (cgen.js): provenance, license, the
  polynomial, field, multiplication count, the reference (the paper for ours, the
  literature for each comparison method, with links) and compile line
- `js/chain.js` — chain rendering: index names or the paper's letter names
  (y, z, t, u, …) with gadget headings (Q_7, H_2, T-recursion, …)
- `js/graph.js`, `js/graphview.js` — computational-graph IR (× and + nodes) and its
  layered SVG layout / text listing
- `js/highlight.js` — dependency-free C tokenizer / syntax highlighter for the code pane
- `js/theme.js` — the day / night choice: remembered in localStorage (index.html applies it
  before first paint), toggled by the header button and the phone intro's twin, painted through
  `<html data-theme>` (style.css follows the system preference otherwise)
- `js/mathview.js` — display-only conversion of the generated chain grammar to
  aligned TeX rows; KaTeX renders them with MathML while Copy preserves the exact
  canonical plain text
- `js/uistate.js` — the page's state: one plain object (mode, source, job id, result,
  selected method, view and its sub-options), a pure reducer, and the selectors every
  control is rendered from (`selectedRow`, `paneContent`, `availableSubOptions`, …);
  testable under node without a DOM. Stale-while-revalidate lives here too: `prevResult` /
  `staleRow` keep a numeric method's previous chain while its worker recomputes, `isStale`
  says when every view dims (a job, a parse error, a Cancel), `inputHint` warns before a
  slow typed compile, and Share links name a held chip as `ex=`
- `js/methodlist.js` — the dependency-free list of method names and degree caps shared by
  the page thread and the workers, so `ui.js` never loads the compilers
- `js/ui.js` — the page as a Preact + htm app mounted into `#app`: renders `uistate.js`
  and owns the side effects (the Web Workers, created lazily and terminated in one place —
  the job effect — when a newer job supersedes them or Cancel is pressed; a `hashchange`
  listener restores shared state in an already-open tab). Output is stale-while-revalidate:
  while a job runs, a numeric row recomputes, the draft fails to parse, or a job was cancelled,
  the previous chain — with the method chips, the comparison table and the phone stats line —
  stays mounted and dims (a status line says so after a Cancel), and a Cancel button shows
  while compiling;
  `App` → `DesktopLayout` | `CompactLayout` over shared pieces (`InputCard`, `FieldPills`,
  `MethodPills`, `FieldMethodPickers`, `Output`, `FooterBar`); the phone boot state and the
  six-digit rule for numeric rows are `initialStateFor` / `presentedState` in `uistate.js`
- `js/worker.js` — the Web Worker that keeps unbounded exact-rational preprocessing
  off the UI thread; it posts every view (math, paper-format math, C, fraction-C,
  graph IR + SVG) for ours and each comparison method so switching views never recompiles.
  Over ℚ / ℝ / ℂ the page runs two instances: `part: 'main'` (our chain, Horner, Estrin,
  Rabin–Winograd, with placeholder rows for the numeric methods) and `part: 'numeric'`
  (Knuth–Eve and Pan — and Belaga over ℂ — whose root-finding preprocessing can take seconds at high degree);
  the placeholders show as spinners until the second reply fills them in
- `js/vendor/preact-htm.module.js` — Preact + htm standalone ES-module bundle (vendored,
  MIT; see `js/vendor/LICENSE-preact.txt`)
- `js/vendor/katex/` — pinned KaTeX runtime, stylesheet and WOFF2 fonts (vendored,
  MIT; see its `LICENSE` and `README.md`); no CDN and no build step
- `test/` — dependency-free Node test suites: `rat.test.js` (Lehmer gcd against Euclid),
  `methodlist.test.js`, `char2.test.js`, `char0.test.js` (985 checks incl.
  Python-generated goldens), `chain.test.js` (paper-format naming + gadget
  provenance), `cgen.test.js` (generated C compiled and executed), `graph.test.js`,
  `methods.test.js`, `motzkin.test.js`, `belaga.test.js`, `pan1978.test.js`,
  `pan1978real.test.js`, `knutheve-complex.test.js`, `gauss.test.js`, `fields.test.js`
  (every registry field through the worker, C rendered for each), `ui-smoke.test.js` (worker result shape per
  mode + highlighter, then the page itself rendered under `test/dom-shim.js` — a minimal
  DOM and Worker stand-in — at both layouts: boot, chips, stepper, debounce, field and
  method switches, a real compile result, tabs, Share), `uistate.test.js` (reducer / selector invariants: mode switch,
  result selection, sub-option visibility, cancel / restore and stale replies, share round-trips), and
  `cbundle.test.js` (archive contents plus compile/run of the shipped scripts), and
  `mathview.test.js` (plain-chain to TeX conversion plus KaTeX rendering across fields
  and methods)

## Tests

    npm test

The ordinary suite uses deterministic, bounded randomized checks and is split into
parallel jobs in GitHub Actions. The original high-volume characteristic-two checks
remain available with `npm run test:stress`; CI runs them weekly and on manual request.

## Local preview

    cd website && python3 serve.py 8000      # no-cache dev server
    # open http://localhost:8000

(A server is needed because the page uses ES modules; `file://` won't load them.)

## License

The website and compiler are MIT-licensed (see `../LICENSE`). The C code the page
generates — every method file, the benchmark harness and scripts in a downloaded
bundle — is released under the BSD Zero Clause License (0BSD), stated in the header
of each generated file (`cSourceHeader` / `C_LICENSE` in `js/cgen.js`), so it can be
pasted into any project without an attribution notice. Preact + htm and KaTeX are
vendored under their own MIT licenses in `js/vendor/`.

## Deploying to GitHub Pages

The root-level Pages workflow publishes this directory as-is. In the repository
settings, select Pages → Source → **GitHub Actions**. There is no build step.
