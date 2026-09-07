// The literature behind each method in the comparison, as the paper cites it
// (references.bib).  The comparison table links every method name to its
// reference and lists the citations under the table; the generated C for a
// comparison method repeats the citation in its header.
//   { short, blurb, cite, url }   short: how the table names it; blurb: one line
//                          saying what the method is (the tooltip of its chip and
//                          table row — fixed text, never the worker's runtime note);
//                          cite: the full line; url: DOI / arXiv link (null when
//                          there is none)

/** The paper's link — the single source for every Paper link on the page (the
 *  phone intro, the "This paper" row and reference [1], the generated C header;
 *  index.html's paper card carries a copy, checked equal by ui-smoke.test.js).
 *  The arXiv submission id resolves only once the paper is announced; change
 *  this one constant to https://arxiv.org/abs/<id> then. */
export const PAPER_URL = 'https://arxiv.org/abs/submit/8036575';

/** The tooltip of the Paper links, derived from PAPER_URL so the announcement
 *  flip really is that one edit: a submission URL says the permanent identifier
 *  is still to come; an announced abs/<id> URL names the identifier. */
export const PAPER_TITLE = (() => {
  const submission = /\/abs\/submit\/(\d+)\/?$/.exec(PAPER_URL)?.[1];
  if (submission) return `arXiv submission ${submission} (the permanent identifier follows on announcement)`;
  const id = /\/abs\/([^/?#]+)\/?$/.exec(PAPER_URL)?.[1];
  return id ? `arXiv:${id}` : 'the paper';
})();

export const REFERENCES = {
  'This paper': {
    short: 'Ahle & Knudsen 2026',
    blurb: '⌊n/2⌋+2 multiplications for a general polynomial (⌊n/2⌋+1 monic) after exact rational preprocessing — no root-finding',
    cite: 'T. D. Ahle and J. B. T. Knudsen, "Fast Evaluation of Polynomials with Rational Preprocessing", arXiv preprint, 2026.',
    url: PAPER_URL,
  },
  'Horner': {
    short: 'Horner 1819',
    blurb: 'the sequential baseline: n multiplications and n additions, no preprocessing',
    cite: 'W. G. Horner, "A new method of solving numerical equations of all orders, by continuous approximation", Philosophical Transactions of the Royal Society of London 109, pp. 308–335, 1819.',
    url: 'https://doi.org/10.1098/rstl.1819.0023',
  },
  'Estrin': {
    short: 'Estrin 1960',
    blurb: "Horner's multiplication count at logarithmic depth: independent halves evaluated in parallel",
    cite: 'G. Estrin, "Organization of computer systems: the fixed plus variable structure computer", Western Joint IRE-AIEE-ACM Computer Conference, pp. 33–40, 1960.',
    url: 'https://doi.org/10.1145/1460361.1460365',
  },
  'Rabin–Winograd': {
    short: 'Rabin & Winograd 1972',
    blurb: 'n/2 + O(log n) multiplications after rational preprocessing, via balanced splits and repeated squaring',
    cite: 'M. O. Rabin and S. Winograd, "Fast evaluation of polynomials by rational preparation", Communications on Pure and Applied Mathematics 25(4), pp. 433–458, 1972.',
    url: 'https://doi.org/10.1002/cpa.3160250405',
  },
  'Knuth–Eve': {
    short: 'Knuth 1962; Eve 1964',
    blurb: 'coefficient adaptation: ⌊n/2⌋+2 multiplications after a shift and the real roots of the odd part, found numerically',
    cite: 'D. E. Knuth, "Evaluation of polynomials by computer", Communications of the ACM 5(12), pp. 595–599, 1962; ' +
      'J. Eve, "The evaluation of polynomials", Numerische Mathematik 6(1), pp. 17–21, 1964 ' +
      '(after T. S. Motzkin, Bull. Amer. Math. Soc. 61, p. 163, 1955).',
    url: 'https://doi.org/10.1007/BF01386049',
  },
  'Pan': {
    short: 'Pan 1978',
    blurb: "Pan's real schemes (degree 8 and odd degree ≥ 9): ⌈n/2⌉ multiplications after solving an algebraic system numerically",
    cite: 'V. Ya. Pan, "Computational complexity of computing polynomials over the fields of real and complex numbers", 10th ACM Symposium on Theory of Computing (STOC), pp. 162–172, 1978.',
    url: 'https://doi.org/10.1145/800133.804344',
  },
  'Belaga': {
    short: 'Belaga 1958',
    blurb: '⌈n/2⌉ multiplications and n+1 additions over ℂ (monic input) after numeric complex preprocessing',
    cite: 'E. G. Belaga, "Some problems involved in the computation of polynomials", Dokl. Akad. Nauk SSSR 123, pp. 775–777, 1958; ' +
      'displayed as scheme (0.5) in V. Ya. Pan, "Methods of computing values of polynomials", Russian Math. Surveys 21(1), pp. 105–136, 1966.',
    url: 'https://doi.org/10.1070/RM1966v021n01ABEH004147',
  },
};

// the spellings the emitters and tests use for the same methods
const ALIASES = { RW: 'Rabin–Winograd', 'Rabin-Winograd': 'Rabin–Winograd', 'Knuth-Eve': 'Knuth–Eve', ours: 'This paper' };

/** The reference of a comparison method (null for names without one). */
export const referenceFor = name => REFERENCES[ALIASES[name] ?? name] ?? null;
