# Fast Polynomial Evaluation — interactive chain compiler

Companion website for *Fast Evaluation of Polynomials with Rational Preprocessing*.
Type a polynomial, get back a straight-line evaluation chain using
⌊n/2⌋+1 multiplications instead of Horner's n−1.

Everything runs client-side: exact BigInt rational arithmetic (char 0) and
GF(2^89−1) Mersenne arithmetic, and carryless GF(2^64) arithmetic (char 2).

## Structure

- `index.html`, `style.css` — the page (no build step; Preact + htm vendored). One card:
  example chips (Taylor polynomials over ℚ/ℝ; over the hashing fields a random key —
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
  exact or ≈ numeric; clicking a row selects the method) + Share
- `js/rat.js` — exact rationals over BigInt
- `js/field.js` — field interface: ℚ, GF(p) and GF(2^k) (carryless mul, Frobenius roots)
- `js/poly.js` — dense polynomial arithmetic over any field
- `js/polyparse.js` — input parsing / pretty-printing
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
- `js/cgen.js` — C code generation matching the paper's benchmark code
  (`tools/bench/framework/multiplication*.h`): PCLMULQDQ / PMULL
  carryless multiplication for GF(2^64), `__uint128_t` Mersenne helpers for GF(2^89−1),
  doubles for ℚ (float or exact `(double)NUM/DEN` constants)
- `js/chain.js` — chain rendering: index names or the paper's letter names
  (y, z, t, u, …) with gadget headings (Q_7, H_2, T-recursion, …)
- `js/graph.js`, `js/graphview.js` — computational-graph IR (× and + nodes) and its
  layered SVG layout / text listing
- `js/highlight.js` — dependency-free C tokenizer / syntax highlighter for the code pane
- `js/uistate.js` — the page's state: one plain object (mode, source, job id, result,
  selected method, view and its sub-options), a pure reducer, and the selectors every
  control is rendered from (`selectedRow`, `paneContent`, `availableSubOptions`, …);
  testable under node without a DOM
- `js/ui.js` — the page as a Preact + htm app mounted into `#app`: renders `uistate.js`
  and owns the side effects (the Web Worker, created lazily and terminated on Cancel)
- `js/worker.js` — the Web Worker that keeps unbounded exact-rational preprocessing
  off the UI thread; it posts every view (math, paper-format math, C, fraction-C,
  graph IR + SVG) for ours and each comparison method so switching views never recompiles
- `js/vendor/preact-htm.module.js` — Preact + htm standalone ES-module bundle (vendored,
  MIT; see `js/vendor/LICENSE-preact.txt`); the only third-party code, no build step
- `test/` — dependency-free Node test suites: `char2.test.js`, `char0.test.js` (985 checks incl.
  Python-generated goldens), `chain.test.js` (paper-format naming + gadget
  provenance), `cgen.test.js` (generated C compiled and executed), `graph.test.js`,
  `methods.test.js`, `motzkin.test.js`, `belaga.test.js`, `pan1978.test.js`,
  `pan1978real.test.js`, `ui-smoke.test.js` (worker result shape per
  mode + highlighter), `uistate.test.js` (reducer / selector invariants: mode switch,
  result selection, sub-option visibility, cancel and stale replies)

## Tests

    npm test

The ordinary suite uses deterministic, bounded randomized checks and is split into
parallel jobs in GitHub Actions. The original high-volume characteristic-two checks
remain available with `npm run test:stress`; CI runs them weekly and on manual request.

## Local preview

    cd website && python3 serve.py 8000      # no-cache dev server
    # open http://localhost:8000

(A server is needed because the page uses ES modules; `file://` won't load them.)

## Deploying to GitHub Pages

The root-level Pages workflow publishes this directory as-is. In the repository
settings, select Pages → Source → **GitHub Actions**. There is no build step.
