// The literature behind each method in the comparison, as the paper cites it
// (references.bib).  The comparison table links every method name to its
// reference and lists the citations under the table; the generated C for a
// comparison method repeats the citation in its header.
//   { short, cite, url }   short: how the table names it; cite: the full line;
//                          url: DOI / arXiv link (null when there is none)
export const REFERENCES = {
  'This paper': {
    short: 'Ahle & Knudsen 2026',
    cite: 'T. D. Ahle and J. B. T. Knudsen, "Fast Evaluation of Polynomials with Rational Preprocessing", arXiv preprint, 2026.',
    url: 'https://arxiv.org/abs/submit/8036575',
  },
  'Horner': {
    short: 'Horner 1819',
    cite: 'W. G. Horner, "A new method of solving numerical equations of all orders, by continuous approximation", Philosophical Transactions of the Royal Society of London 109, pp. 308–335, 1819.',
    url: 'https://doi.org/10.1098/rstl.1819.0023',
  },
  'Estrin': {
    short: 'Estrin 1960',
    cite: 'G. Estrin, "Organization of computer systems: the fixed plus variable structure computer", Western Joint IRE-AIEE-ACM Computer Conference, pp. 33–40, 1960.',
    url: 'https://doi.org/10.1145/1460361.1460365',
  },
  'Rabin–Winograd': {
    short: 'Rabin & Winograd 1972',
    cite: 'M. O. Rabin and S. Winograd, "Fast evaluation of polynomials by rational preparation", Communications on Pure and Applied Mathematics 25(4), pp. 433–458, 1972.',
    url: 'https://doi.org/10.1002/cpa.3160250405',
  },
  'Knuth–Eve': {
    short: 'Knuth 1962; Eve 1964',
    cite: 'D. E. Knuth, "Evaluation of polynomials by computer", Communications of the ACM 5(12), pp. 595–599, 1962; ' +
      'J. Eve, "The evaluation of polynomials", Numerische Mathematik 6(1), pp. 17–21, 1964 ' +
      '(after T. S. Motzkin, Bull. Amer. Math. Soc. 61, p. 163, 1955).',
    url: 'https://doi.org/10.1007/BF01386049',
  },
  'Pan': {
    short: 'Pan 1978',
    cite: 'V. Ya. Pan, "Computational complexity of computing polynomials over the fields of real and complex numbers", 10th ACM Symposium on Theory of Computing (STOC), pp. 162–172, 1978.',
    url: 'https://doi.org/10.1145/800133.804343',
  },
};

// the spellings the emitters and tests use for the same methods
const ALIASES = { RW: 'Rabin–Winograd', 'Rabin-Winograd': 'Rabin–Winograd', 'Knuth-Eve': 'Knuth–Eve', ours: 'This paper' };

/** The reference of a comparison method (null for names without one). */
export const referenceFor = name => REFERENCES[ALIASES[name] ?? name] ?? null;
