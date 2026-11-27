# Source and prior-work checks: cyclotomic cosets modulo 10^n

Checked November 27, 2026. These records describe bounded searches and inspected sources. They are not a certification of historical priority.

## Exact source assertions

The four primary OEIS entries define the number of cyclotomic cosets of q modulo 10^n, for q = 3,7,9,13, and all have offset 1. Their examples explicitly include the zero orbit. The selected assertions are the following closed forms, with the source's strict index cutoffs preserved:

| Entry | Exact selected assertion | Attribution | Frozen source revision |
| --- | --- | --- | --- |
| [A220018](https://oeis.org/A220018) | `Conjecture: a(n) = 8*n^2-14*n-1 for n>2.` | Colin Barker, April 14, 2013 | 36, July 3, 2023 |
| [A220019](https://oeis.org/A220019) | `Conjecture: a(n) = 5*(16*n^2-60*n+37) for n>3.` | Colin Barker, April 14, 2013 | 27, July 3, 2023 |
| [A220020](https://oeis.org/A220020) | `Conjecture: a(n) = 4*(4*n^2-7*n-1) for n>2.` | Colin Barker, April 13, 2013 | 26, July 12, 2025 |
| [A221855](https://oeis.org/A221855) | `Conjecture: a(n) = 2*n*(4*n-7) for n>2.` | Colin Barker, April 14, 2013 | 23, July 3, 2023 |

V. Raman contributed the first three sequences on January 27, 2013 and A221855 on January 28, 2013. The entries also record recurrences and rational generating functions. The four closed-form assertions above are the formal endpoints selected for this package; their equivalent descriptions and the supporting lemmas are not counted as further problems.

The exports in `sources/` were obtained from the official `oeis/oeisdata` repository. The last file-touch commits returned by the history endpoint were `571197984aeda7b8b680fe3a1f6a43f9898cd441` for A220018, A220019, and A221855, and `ddbc991a4786eda1e3a5a955a36db749a63fc673` for A220020. A later, separate fetch at each immutable commit was byte-compared against the saved export; all four were identical. Exact URLs and SHA-256 hashes are in [source_manifest.json](sources/source_manifest.json).

| Saved file | SHA-256 |
| --- | --- |
| [A220018.seq](sources/A220018.seq) | `839117d3d36b6172d2051c5be7aa6ae18ffd4507a37ee37c6cd195c498ad9a9a` |
| [A220019.seq](sources/A220019.seq) | `da34da8da8135d089d323cd232647a5ac803d0fb44ee665b7b5c3153a4d2ba7d` |
| [A220020.seq](sources/A220020.seq) | `c338116702ffea6c52a7ce37f7dc359c3274ba0dc39f4bb0b82afef487c99f9b` |
| [A221855.seq](sources/A221855.seq) | `687753e2dd9a7bd235d7f57ca00d4faee904ddd852753d21cac40d9c5dca36b7` |

## Existing mathematical theory

The orbit-size identity φ(d)/ord_d(q), the Chinese remainder theorem, and lifting the exponent are standard. The source entries already supply divisor-sum programs, attributed to Ray Chandler in July 2023 after Jean-François Alcover. We do not claim the divisor formula or the order-lifting method as a discovery.

A relevant general primary source is Li Zhu, Jinle Liu, and Hongfeng Wu, [*Explicit representatives and sizes of cyclotomic cosets and their application to cyclic codes over finite fields*](https://arxiv.org/abs/2410.12122), first posted October 15, 2024, published in *Finite Fields and Their Applications* 111 (2026), article 102761, [DOI 10.1016/j.ffa.2025.102761](https://doi.org/10.1016/j.ffa.2025.102761). The paper gives a classification for general coprime q and n. We inspected its primary [arXiv v1 HTML](https://arxiv.org/html/2410.12122v1), including the basic valuation lemmas, Proposition 3.3 on orders, the general even-modulus discussion, and Example 3.1 for q=3 modulo 40. The journal abstract and introduction confirm the general scope. The paper's general theorems cover the ambient theory of these examples; this package is an explicit elementary specialization, with full formal verification. No claim is made that its general orbit methods or prime power lifting are new. The inspected portions and targeted text checks did not state the four Barker polynomials or name Barker.

We link the paper and retain bibliographic metadata; no complete third-party paper is redistributed in this package.

## Web searches

Both available web engines were used. Exact discovery and final queries included the four OEIS identifiers with `proof`, paired identifier queries, and the actual polynomial fragments. Semantic searches included `"cyclotomic cosets" "10^n" proof`, `"cyclotomic cosets" "powers of ten"`, and `"cyclotomic" "8n" "14n"`. Results included the current OEIS entries, Sequence Machine numerical fits, standard coding theory, and unrelated lexical matches. The stronger engine confirmed the exact conjectural source text.

A later semantic GitHub result led to the Zhu–Liu–Wu paper above; its primary source was then inspected. The final web query list and returned URLs are preserved in [web_search_receipts.json](sources/web_search_receipts.json). These receipts omit full search snippets and paper text.

## Global GitHub searches and closest inspected code

Exact global searches were run for each identifier, returning at most the first 30 or 35 results. Semantic global queries included `"cyclotomic cosets" "10"` (first 60), `"cyclotomic" "Barker"` (first 40), and `"16*n^2" "60*n" "37"` (first 40). The returned immutable URLs are in [github_search_receipts.json](sources/github_search_receipts.json).

The closest prior artifacts were:

| Item | Inspected content | Relation to the present proof |
| --- | --- | --- |
| [jOEIS A220018](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a220/A220018.java), with subclasses for q=7,9,13 | A program computing the sum of φ(d)/ord_d(q) over divisors of 10^n. The complete base class was read. | An existing exact counting algorithm, not a proof of the four quadratic evaluations. |
| [LODA A220018](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/220/A220018.asm), [A220019](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/220/A220019.asm), [A220020](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/220/A220020.asm), [A221855](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/221/A221855.asm) | Integer generators and polynomial or recurrence descriptions matching the recorded terms. | The expressions and program patterns predate this package. They do not supply a theorem identifying them with literal coset counts at every index. |
| [Sequencelib A221855](https://github.com/provables/sequencelib/blob/dfb06c18bba196b5aa5bcb3725fe9d201fb9a61a/Sequencelib/Synthetic/A221/A221855.lean) | A synthesized arithmetic-program definition with OEIS metadata; the complete file was read. | Existing Lean code, but no orbit-quotient definition or theorem connecting its arithmetic program to cyclotomic cosets. |
| [OEIS ATP benchmark A221855](https://github.com/ai4reason/oeis-atp-benchmark/blob/4a80a91728dffea1407ee2f0b8f55622761935cc/pb/A221855.smt2) | Definitions of two synthesized programs and a solver query asking whether they can differ; the complete file was read. | A program-equivalence problem, with no literal coset-count source bridge. |
| OEIS mirrors and sequence-data collections | Reproductions of the definitions, formulas, or terms. | Source duplication rather than a distinct proof. |

Other semantic hits concerned BCH code implementations, cyclic code parameter searches, quartic cyclotomic classes, and unrelated polynomial recurrences. The general cyclotomic-coset literature was retained as prior theory rather than treated as an irrelevant lexical match.

## Current formal-proof repositories

Each of the four identifiers was searched in `VladimirReshetnikov/ProveIt` and `the-omega-institute/trureturing`; no exact target hit was returned. The combined semantic query `"cyclotomic cosets"` returned 20 inspected result excerpts concerning quartic cosets, pseudo-Paley graphs, other arithmetic work, and general polynomial theory. None of those excerpts supplied a settlement of these exact formulas.

The observed indexed snapshots were ProveIt `6b034b74a8224c893e7e83127f33cd1a6958785d` and trureturing `548388cde9b27d282a17a3ead04870288e40d197`. Search-index results are not a certificate that every file of a repository head was examined. The exact negative results and positive semantic-result URLs are preserved in the compact GitHub receipts.

## Conclusion and limits

All four primary entries still label the selected polynomials conjectural. Earlier exact algorithms, polynomial patterns, program-synthesis artifacts, and substantially more general mathematical theory were located and credited. No earlier explicit source-to-polynomial proof of these four assertions was located in the bounded checks. This package proves those specializations from the literal orbit counts and supplies kernel-checked endpoints for every index in the original ranges.

This is one coherent family containing four related source assertions. The source bridge, valuation formulas, grid tables, and summations are supporting results. The package does not claim first discovery of the expressions, a new general counting theory, or worldwide historical priority.
