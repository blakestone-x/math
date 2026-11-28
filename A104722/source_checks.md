# Source and prior-work checks: A104722

Checked again on **2026-11-28 UTC** before publication. This is a bounded source and duplicate screen. The Catalan formulas and generating function are established background; no worldwide-priority claim is made.

## Source theorem and cutoff

The official [A104722 snapshot](https://github.com/oeis/oeisdata/blob/091a90f51479669655f4e46343867ea2abd5d4ff/seq/A104/A104722.seq) defines the self-convolution of the repeated Catalan numbers and attributes the recurrence to **R. J. Mathar, November 9, 2012**:

\[
(n+4)a(n)+(n+1)a(n-1)-4(n+1)a(n-2)+4(2-n)a(n-3)=0.
\]

The record prints no starting index. The literal convolution begins `1,2,3,4,7,10,...`. Consequently the displayed left side equals `4` at `n=3`. The formal result proves **all `n ≥ 4`**, and separately proves the exception at `3`. That cutoff is essential.

The related [A059348 snapshot](https://github.com/oeis/oeisdata/blob/091a90f51479669655f4e46343867ea2abd5d4ff/seq/A059/A059348.seq) is also preserved. The two records use different OEIS offsets; this package always uses A104722's offset `0` and literal definition. The official records, commit URLs, byte lengths and SHA256 hashes are under `sources/`. The exact checker matches all 35 listed terms.

## Prior formulas and literature

The source itself includes **James Sellers's May 19, 2008** generating-function argument for agreement with A059348 after the first term, as well as the formula `(1+x)² C(x²)²`. These facts predate Mathar's recorded conjecture and are credited in the manuscript.

A fresh search also found the primary paper:

Tongyuan Zhao, Xiaoqing Li and Yue Sun, *Enumeration of Permutations Without Consecutive Descents Avoiding Patterns of Length 3*, **Advances in Mathematics (China) 54(1)** (2025), 50–60, [doi:10.11845/sxjz.2023026b](https://doi.org/10.11845/sxjz.2023026b); [publisher PDF](https://ccj.pku.edu.cn/Article/DownLoad?id=661522580062277&type=ArticleFile).

Its table identifies A104722, and Theorem 3.7 discusses the associated Catalan expression for permutation counts for `n ≥ 3`. The theorem, preceding proof explanation, table, and bibliographic information were read. This is prior knowledge of the parity formulas, not a new discovery in this package. The selected Mathar recurrence was not identified in the inspected theorem or surrounding argument; text searches for `Mathar` and `n+4` were also negative. Those negative searches alone are not treated as a proof of absence.

The earlier [Project P problem page](https://mathweb.ucsd.edu/~projectp/problems/p13.html), updated August 11, 2015, notes the relation of a permutation-avoidance sequence to A104722 from the term `4`. It is acknowledged as related combinatorial context, not the definition used by the Lean proof.

## Implementation and repository screen

Both available web-search engines were used with exact-ID `proof recurrence` queries. Fresh GitHub code-search results, totals and immutable result URLs are preserved in `sources/search-receipts.json`. Direct implementation reads are hashed in `sources/implementation-receipts.json`; `sources/substring-hit-inspections.json` preserves hashes and match contexts from fresh reads of all nineteen unrelated Lean hits.

| Inspected item | Finding |
|---|---|
| [jOEIS A104722.java](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a104/A104722.java) | Delegates to A059348 while adjusting the first term |
| [jOEIS A059348.java](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a059/A059348.java) | A generated 2021 holonomic-recurrence implementation with different coefficients/order, derived from a radical generating function |
| Exact ID in `the-omega-institute/trureturing` | Zero returned files |
| Exact ID in `kolinhuang0427/open-math-results` | Zero returned files |
| Global `A104722 language:Lean` | Nineteen files, in unrelated data/coverage projects; all nineteen fresh file reads placed the matching substrings inside hexadecimal data |
| Semantic `Catalan` in `kolinhuang0427/open-math-results` | Seventy-seven broad hits; their returned paths were reviewed as candidate context, not represented as seventy-seven fully read proofs |

The broad Catalan query is recorded for transparency. The exact-ID search and the directly relevant source/literature/implementation reads are the evidence used for this narrow target; the broad search does not establish exhaustive coverage.

## Claimed contribution

This package supplies an explicit derivation of the recorded recurrence from the literal repeated-Catalan convolution, with the necessary cutoff correction and a complete Lean formalization. The Catalan ratio identity, parity formulas, sequence relation, generating function and general recurrence methods are credited background.

This is **one target family**. Its two parity cases, supporting lemmas and endpoint exception are not counted as separate solved problems. The bounded screen did not identify an earlier explicit proof of this exact recurrence; that is not a worldwide-priority assertion.

Both restored Lean modules were compiled afresh with their pinned configuration, and the author log records exact hashes and axiom audits. Independent build and review evidence is recorded separately. The finite exact checks through `n=200` supplement, rather than establish, the unbounded formal result.
