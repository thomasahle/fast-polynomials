# Fast Polynomials

Code, proofs, and experiments for the paper
*Fast Evaluation of Polynomials with Rational Preprocessing* by Thomas D. Ahle
and Jakob B. T. Knudsen.

**[Try the interactive polynomial compiler](https://thomasahle.com/fast-polynomials/)**

Given a polynomial, this project preprocesses its coefficients into a
straight-line evaluation program with substantially fewer field multiplications
than Horner's rule. The repository contains the paper, its Lean formalization, a
reference compiler with explicit decoders, generated C kernels, and the benchmark
programs used in the experiments.

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

Characteristic two requires different constructions. The repository includes
explicit circuits with explicit inverses at every odd degree up to 21 (Appendix A
of the paper, symbolic certificates under `char2/`) and a formal lower bound, but
a uniform all-degree analogue of the upper bound remains open. See the characteristic-two examples in
[`sections/appendix_polynomials.tex`](sections/appendix_polynomials.tex) and the
discussion in [`sections/open_problems.tex`](sections/open_problems.tex).

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
lake build FastPoly                  # umbrella: constructions, costs, height, characteristic-2 lower bound
lake build FastPoly.LowerBound.Main  # degree-6 lower bound: a separate module tree, not imported by the umbrella
```

`FastPoly.lean` is the umbrella import. The development formalizes the recovery
calculus, recursive constructions, fixed straight-line programs and their costs,
multiplicative-depth bounds, and the characteristic-two lower bound.

## Verification

The principal checks can be run independently:

```sh
# Explicit encoder/decoder round trips and multiplication counts
python3 tools/polychain.py selftest --max-n 30

# Browser compiler, generated C, and UI tests (Node 22 is used in CI)
cd website && npm test

# Machine-checked proofs
cd .. && lake build FastPoly && lake build FastPoly.LowerBound.Main
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
- `website/` — dependency-free browser compiler and C-code generator.

## Proof and experiment policy

Decodability claims in this project come with an explicit inverse: a triangular
pivot, coefficient-window peel, monic division, or displayed block solve. A
constant Jacobian determinant or tests over sampled field elements are useful
diagnostics, but are not treated as proofs of bijectivity. Likewise, benchmark
numbers are architecture- and compiler-dependent; run the generated benchmark
bundle on the target machine before drawing performance conclusions.

## Citation

Please cite *Fast Evaluation of Polynomials with Rational Preprocessing* when
using these constructions or the accompanying software. A stable arXiv citation
will be added here when available.

## License

MIT (see `LICENSE`). The C code generated by the companion website is released
under the BSD Zero Clause License (0BSD), with no attribution required; vendored
third-party components in `website/js/vendor/` keep their own MIT licenses.
