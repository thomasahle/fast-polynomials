# Lane E step 2 -- paper edit plan for the strided pairing (NOT APPLIED: the shipped definition fails one SMHasher3 test, see README)

Files: sections/injective.tex, sections/appendix_chainhash.tex (build in build_E).

## injective.tex
* tab:injective:adversarial rows (M2 Pro harness `./speed 5 0.5 run ChainHash`, load 2.99):
  ChainHash 1 KB: 61.7 / 40.5 -> 70.4 / 44.2;  256 B: 57.7 / 36.8 -> 67.0 / 38.8;  64 B: 26.6 / 27.4 -> 25.8 / 29.6
* line 359 "(one \texttt{PMULL} per $16$ bytes into two $128$-bit accumulators)" -> add: "; the four words of each
  $32$-byte group are paired first with third and second with fourth, so that both operands of a product come
  straight from two $16$-byte loads (\Cref{rem:ph:gaps})"
* line 408 "$62$\,GB/s" -> "$70$\,GB/s";  line 414 "($26.6$ against $23.8$\,GB/s" -> "($25.8$ against $23.8$\,GB/s"
* (not ours) introduction.tex:71 "$58$--$62$\,GB/s" -> "$67$--$70$\,GB/s"; experiments.tex:474-476 SMHasher3 numbers.

## appendix_chainhash.tex
* header comment: add "% 2026-09-05: strided word pairing at level 1 ..." line.
* intro (l.35-37): "the last block being processed at $16$-byte pair granularity" -> "the two words of a product being the
  first and third, and the second and fourth, of a $32$-byte group (the \emph{strided} pairing), and the last block being
  processed at $32$-byte group granularity".
* Key paragraph: "$\kappa^{(i)}=(k_{iW_s},\dots,k_{(i+1)W_s-1})$" -> "$\kappa^{(i)}=\pi(k_{iW_s},\dots,k_{(i+1)W_s-1})$, the
  key words of that position listed in the pair order $\pi$ defined below; $\pi$ is a fixed permutation, so $\kappa^{(i)}$
  is uniform on $\F^{W_s}$".
* Sub-blocks paragraph: sub-block tuple listed in pair order; words $x_0..x_{4G_t-1}$, $G_t=\lceil r_t/32\rceil$ groups,
  zero-padded to $32G_t$ bytes; pairs $(g_{2s},g_{2s+1})=(x_{\alpha(s)},x_{\alpha(s)+2})$, $\alpha(s)=4\lfloor s/2\rfloor+(s \bmod 2)$,
  $w_t=2G_t\in\{0,2,\dots,W_s/2\}$; $m_t=\pi(x)$ with $\pi$ swapping the two middle words of every group;
  "(m_1..m_p, l) determines m" via $\pi^{-1}$.  Lemmas lem:ph:clnh / lem:ph:stream unchanged (they quantify over
  tuples in pair order and uniform key segments).
* Level 1 implementation text: ph_group32 (PMULL of low lanes / PMULL2 of high lanes of the same two registers, no
  shuffle); ph_tail: whole 64/32-byte groups in place, first half of a partial group of >16 bytes in place, last 1..16
  bytes via the TBL shift of the 16 bytes ending at byte l; load_small = first half of the single padded group, second
  half zero (a message of <= 8 bytes: second pair $(0+k'_2)(0+k'_3)$ is a key constant); reference pairs by pair_alpha;
  T8 = permutation identity for $32\mid\ell$.
* l.226 "pair granularity" -> "group granularity"; lem:ph:stream "$16\nmid\ell(m)$" -> "$32\nmid\ell(m)$" (also in
  the length-XOR remark, twice); rem:ph:gaps (A6) "$\lceil\ell/16\rceil$ carry-less products" -> "$2\lceil\ell/32\rceil$".
* rem:ph:gaps (A7): "56 SIMD instructions" -> "48 (4 EOR, 4 PMULL, 2 EOR3 per 64 bytes; the natural pairing needed one
  EXT per two pairs, 12 ops per 64 bytes, 56 per block); x86 PCLMULQDQ selects halves by immediate, so neutral there";
  add the why-strided sentence.
* Measurements paragraph (l.811-814): the shipped implementation is no longer "the same function bit for bit" as the
  twist experiment (pairing changed); new SMHasher3 Speed numbers.
