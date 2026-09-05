# Fast Polynomials

Evaluate a polynomial of degree *n* with about *n*/2 multiplications instead of
Horner's *n*, after a one-time, exact preprocessing of its coefficients.

This repository holds the code, proofs and experiments behind the paper
*Fast Evaluation of Polynomials with Rational Preprocessing* by Thomas D. Ahle
and Jakob B. T. Knudsen (2026): the manuscript, its Lean 4 formalization, a
reference compiler with explicit decoders, a browser-based compiler that emits
C, and the benchmark programs used in the experiments.

**Try it in the browser: <https://thomasahle.com/fast-polynomials/>** — type a
polynomial, pick a field, and read off the evaluation chain as mathematics, as
C code, or as a circuit graph, next to Horner, Estrin, Rabin–Winograd,
Knuth–Eve and Pan on the same input.

## An example

The probabilists' Hermite polynomial `He_7 = x^7 − 21x^5 + 105x^3 − 105x` takes
six multiplications by Horner's rule. The compiler turns it into

```text
y0 = x · (x − 154)
y1 = (x + y0 + 23398) · (x + 153)
y2 = (y1 − 3579895) · x
y3 = (x + y1 − 3579894) · (y2 − 5)
P  = y0 + y2 + y3
```

four multiplications and ten additions. The five constants come from the
coefficients through an explicit decoder — a few divisions and a small
triangular solve, no root finding — and are exact rationals (here integers).
The same chain works over ℚ, over the reals in double precision, over Mersenne
prime fields, and over the binary fields GF(2^32), GF(2^64) and GF(2^128) that
carry-less hashing uses; the website emits ready-to-compile C for each, with
PCLMULQDQ / PMULL and Mersenne kernels included.

## Main result

For every monic polynomial of degree `n` over a field of characteristic zero, or
of characteristic `p > n`, the paper constructs an evaluation program using

```text
floor(n / 2) + 1 multiplications.
```

The coefficient preprocessing is everywhere defined: the construction supplies
an explicit polynomial decoder rather than relying on numerical root finding or
a generic polynomial-system solver. The programs use at most

```text
min(2n, 5n/4 + 6 ceil(log2 n)^2 + 1)
```

additions or subtractions and have multiplicative depth `O(log n)`. A non-monic
leading coefficient costs one additional multiplication.

The bijective parameterization is particularly useful for polynomial hashing:
sampling the program parameters uniformly is equivalent to sampling a uniformly
random monic polynomial, so the usual Vandermonde argument gives `n`-wise
independence on distinct inputs.

Characteristic two requires different constructions. The website and symbolic
certificates under `char2/` include explicit circuits and decoders at every odd
degree through 25; Appendix A of the paper describes the same cases through 25.
Lean checks the website's odd-degree constructions through 15 and their
one-product even lifts, covering every degree 5–16. A formal lower bound is also
included, but a uniform all-degree upper bound remains open. See the examples in
[`sections/appendix_polynomials.tex`](sections/appendix_polynomials.tex) and the
discussion in [`sections/open_problems.tex`](sections/open_problems.tex).

## What is where

| You want to… | Start at |
| --- | --- |
| compile a polynomial and get C | the [website](https://thomasahle.com/fast-polynomials/), or `website/` locally (no build step) |
| read the constructions and proofs | `main.tex` + `sections/`; build with `latexmk` (below) |
| check the proofs mechanically | `FastPoly/` (Lean 4 + Mathlib; `lake build FastPoly`) |
| script the compiler | `tools/poly_schedule.py`, `tools/polychain.py` |
| reproduce the benchmarks | `tools/bench/` |

## Quick start

### Interactive compiler

The website runs entirely in the browser and has no build step. It displays the
generated mathematics, C, and circuit graph; compares several classical methods;
and can download a self-contained C benchmark bundle.

```sh
cd website
python3 serve.py 8000
```

Then open <http://localhost:8000>. See
[`website/README.md`](website/README.md) for supported fields, methods, and C
kernels.

### Python reference compiler

Compile
`9 + 7x + 5x^2 + 3x^3 + x^4` and check its evaluation against Horner:

```sh
python3 tools/poly_schedule.py 9 7 5 3 1 --check
```

Coefficients are supplied from constant term to leading term. To print the
universal parameterized degree-15 construction instead:

```sh
python3 tools/polychain.py chain 15 --peeled
```

`polychain.py` also exposes the explicit coefficient/parameter maps through its
`encode` and `decode` subcommands:

```sh
python3 tools/polychain.py --help
```

### Paper

A recent TeX distribution with `latexmk` builds the manuscript and bibliography:

```sh
latexmk -pdf -outdir=build main.tex
```

The resulting paper is `build/main.pdf`.

### Lean formalization

The project pins its Lean toolchain and uses Mathlib through Lake:

```sh
lake build FastPoly  # constructions, costs, height, and both lower bounds
```

`FastPoly.lean` is the umbrella import. The build described here was verified at
The build described here was verified at commit c834f5f (lake build FastPoly FastPoly.LowerBound.Main FastPoly.LowerBound.General.Main FastPoly.LowerBound.General.Transport, 2084 jobs, 2026-09-05). The development formalizes the recovery
calculus, recursive constructions, fixed straight-line programs and their costs,
multiplicative-depth bounds, the general degree-six lower bound, and the
characteristic-two lower bound (including its one-gate sharpness example).
The degree-six entry point is
`FastPoly.LowerBound.General.no_rationalInverse_general`: it includes the
seven-slot general circuit and its proved quadratic reduction to normal form,
not just the older six-slot normal-form theorem.

`FastPoly.Char2Finite.construction` supplies a fixed circuit, an explicit
coefficient decoder, and the exact `floor(n/2)+1` multiplication count for each
monic degree 5–16. `Char2Finite.monic_evaluation` proves that this same program
computes any requested monic polynomial. The degree-7 base and degree-8 lift
require a perfect characteristic-two field (in particular, any finite field);
the other bases work over every characteristic-two field. The larger
characteristic-two Lean certificates are still under development and are not
imported by the umbrella.

## Verification

The principal checks can be run independently:

```sh
# Explicit encoder/decoder round trips and multiplication counts
python3 tools/polychain.py selftest --max-n 30

# Browser compiler, generated C, and UI tests (Node 22 is used in CI)
cd website && npm test

# Machine-checked proofs
cd .. && lake build FastPoly
```

The generated-C tests invoke a system C compiler. Hardware-field kernels target
x86-64 with PCLMULQDQ or AArch64 with PMULL; the downloaded benchmark bundle
contains the appropriate compile flags and an assembly-inspection script.

## Repository layout

- `main.tex`, `header.tex`, `sections/`, `references.bib` — manuscript sources.
- `FastPoly.lean`, `FastPoly/` — the Lean 4 formalization (`FastPoly/LowerBound/` is the degree-six lower bound, built as its own target).
- `tools/poly_schedule.py` — compile concrete coefficient vectors.
- `tools/polychain.py` — construct, encode, and explicitly decode the paper's
  parameterized families.
- `tools/bench/` — architecture-specific experiments and application benchmarks.
- `tools/gen_x2s_*.py` — regenerate the benchmark chain headers.
- `website/` — dependency-free browser compiler and C-code generator (its
  generated C is 0BSD-licensed; see [`website/README.md`](website/README.md)).

## Proof and experiment policy

Decodability claims in this project come with an explicit inverse: a triangular
pivot, coefficient-window peel, monic division, or displayed block solve. A
constant Jacobian determinant or tests over sampled field elements are useful
diagnostics, but are not treated as proofs of bijectivity. Likewise, benchmark
numbers are architecture- and compiler-dependent; run the generated benchmark
bundle on the target machine before drawing performance conclusions.

## Citation

Please cite *Fast Evaluation of Polynomials with Rational Preprocessing*
(Thomas D. Ahle and Jakob B. T. Knudsen, 2026) when using these constructions or
the accompanying software. The manuscript is arXiv submission
[submit/8036575](https://arxiv.org/abs/submit/8036575); the permanent arXiv
identifier and a BibTeX entry will replace this line once it is announced.

## License

MIT (see `LICENSE`). The C code generated by the companion website is released
under the BSD Zero Clause License (0BSD), with no attribution required; vendored
third-party components in `website/js/vendor/` keep their own MIT licenses.
