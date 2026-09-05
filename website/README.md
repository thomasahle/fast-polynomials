# Fast Polynomial Evaluation — interactive chain compiler

Companion website for *Fast Evaluation of Polynomials with Rational Preprocessing*.
Type a polynomial, get back a straight-line evaluation chain using
⌊n/2⌋+1 multiplications instead of Horner's n−1.

Everything runs client-side: exact BigInt rational arithmetic (char 0) and
GF(2^89−1) Mersenne arithmetic, and carryless GF(2^64) arithmetic (char 2).

## Structure

- `index.html`, `style.css` — the page (no build step; Preact + htm and KaTeX vendored). One card:
  example chips (over ℚ/ℝ: Taylor polynomials — with monic on, the degree-(n−1) Taylor
  polynomial plus xⁿ, so the series' coefficients stay recognisable — and the probabilists'
  Hermite polynomial Heₙ, monic with integer coefficients at every degree; the desktop opens
  on He₇, whose chain has four multiplications and constants of at most seven digits;
  over the hashing fields a random key —
  a fresh draw per click —, sparse, dense and a fixed reproducible key, all regenerated
  at the chosen degree) → the polynomial input (highlighted through a transparent
  textarea over a painted backdrop) → the field chooser, rendered from the `FIELDS`
  registry in `field.js` (three groups: exact ℚ, ℝ · Mersenne primes
  2^61−1, 2^89−1, 2^127−1 · binary fields GF(2^32), GF(2^64), GF(2^128); ℝ is ℚ's exact
  preprocessing with the constants shown as doubles, reported as ≈ numeric)
  → method chips → view tabs attached to the output pane (mathematical with
  factor/original form and exact/decimal (hex) constants — a display-only rewrite ·
  C code with float/fraction constants over ℚ · graph) → the comparison table (one row
  per method: multiplications with the scalar count, additions, multiplicative depth,
  exact or ≈ numeric; clicking a row selects the method) + Share. Copy is paired with
  Download, which packages every available C method with benchmark and assembly-audit
  scripts. On phones (≤ 640px, `COMPACT_QUERY` in `ui.js` and the matching media query in
  `style.css`) the same state renders as a short intro with Paper / GitHub (star count) /
  Share links and three cards: the input (three example chips beside the label, no degree
  stepper or monic toggle — the page opens on the ℚ e^x example at degree 5, monic, whose
  chain has small constants) with Field / Method dropdowns; the output with underline tabs
  and the form strip beside them, a floating Copy (no Download), ℝ constants to six
  significant digits, and a stats line (long rows scroll sideways, as in every pane);
  and a collapsed "Compare methods" disclosure.
- `js/rat.js` — exact rationals over BigInt
- `js/field.js` — field interface: ℚ, GF(p) and GF(2^k) (carryless mul, Frobenius roots)
- `js/poly.js` — dense polynomial arithmetic over any field
- `js/polyparse.js` — input parsing / pretty-printing. The grammar accepts the spellings
  people type for the same polynomial: `x^3/6`, `1/6x^3`, `(1/6)x^3`, `x**3`, `x³`, `2*x`,
  `x·2`, decimals and exponents (`0.5x`, `1.5e-3`), a Unicode minus, hex bit patterns over
  GF(2^k); rejections say what was wrong (division by zero, a variable other than x, a
  fraction in a binary field, …). Tested in `test/polyparse.test.js`.
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
  explicit coefficient maps. Belaga and Pan's complex schemes remain as
  reference implementations but are not shown in the comparison table;
  `js/compare.js` runs the displayed methods on the same input
- `js/cgen.js` — descriptor-driven C emission matching the paper's benchmark code
  (`tools/bench/framework/multiplication*.h`). All methods share the
  emitter; measured width-specific kernels supply PCLMULQDQ / PMULL for GF(2^32),
  GF(2^64), and GF(2^128), Mersenne arithmetic for 2^61−1, 2^89−1, and 2^127−1,
  or doubles for ℚ/ℝ. Estrin rows are emitted by dependency layer so the compiler can
  schedule independent FMAs and apply SLP when profitable.
- `js/cbundle.js` — dependency-free `.tar.gz` creation for the Download button, plus
  the portable timing harness and an assembly report for FMA, SIMD, and CLMUL/PMULL;
  every generated file opens with `cSourceHeader` (cgen.js): provenance, license, the
  polynomial, field, multiplication count and compile line
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
  testable under node without a DOM
- `js/ui.js` — the page as a Preact + htm app mounted into `#app`: renders `uistate.js`
  and owns the side effects (the Web Worker, created lazily and terminated on Cancel);
  `App` → `DesktopLayout` | `CompactLayout` over shared pieces (`InputCard`, `FieldPills`,
  `MethodPills`, `FieldMethodPickers`, `Output`, `FooterBar`); the phone boot state and the
  six-digit rule for numeric rows are `initialStateFor` / `presentedState` in `uistate.js`
- `js/worker.js` — the Web Worker that keeps unbounded exact-rational preprocessing
  off the UI thread; it posts every view (math, paper-format math, C, fraction-C,
  graph IR + SVG) for ours and each comparison method so switching views never recompiles
- `js/vendor/preact-htm.module.js` — Preact + htm standalone ES-module bundle (vendored,
  MIT; see `js/vendor/LICENSE-preact.txt`)
- `js/vendor/katex/` — pinned KaTeX runtime, stylesheet and WOFF2 fonts (vendored,
  MIT; see its `LICENSE` and `README.md`); no CDN and no build step
- `test/` — dependency-free Node test suites: `char2.test.js`, `char0.test.js` (985 checks incl.
  Python-generated goldens), `chain.test.js` (paper-format naming + gadget
  provenance), `cgen.test.js` (generated C compiled and executed), `graph.test.js`,
  `methods.test.js`, `motzkin.test.js`, `belaga.test.js`, `pan1978.test.js`,
  `pan1978real.test.js`, `ui-smoke.test.js` (worker result shape per
  mode + highlighter, then the page itself rendered under `test/dom-shim.js` — a minimal
  DOM and Worker stand-in — at both layouts: boot, chips, stepper, debounce, field and
  method switches, a real compile result, tabs, Share), `uistate.test.js` (reducer / selector invariants: mode switch,
  result selection, sub-option visibility, cancel and stale replies), and
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
