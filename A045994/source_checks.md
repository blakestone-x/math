# Source and prior-work checks: A045994

Checked again on **2026-11-28 UTC** before publication. This is a bounded source/duplicate screen, not a claim that no earlier proof exists anywhere.

## Exact target and immutable source

The official [A045994 record](https://github.com/oeis/oeisdata/blob/72c53dd50967ac7166f7d31bf79be95174ec5bc6/seq/A045/A045994.seq) defines `a(0)=1` and

\[
a(n)=M(n)+\sum_{k=1}^{n-1}M(k)a(n-k-1).
\]

It labels the six-term polynomial-coefficient recurrence as a conjecture by **R. J. Mathar, September 27, 2013**. The package proves that exact recurrence for every `n ≥ 5`. The Motzkin source is [A001006 at commit 8496aacd31f383b1dc5d340495c56c84e7514e4b](https://github.com/oeis/oeisdata/blob/8496aacd31f383b1dc5d340495c56c84e7514e4b/seq/A001/A001006.seq).

The complete raw records are preserved under `sources/`. `sources/manifest.json` records immutable commits, URLs, byte lengths and SHA256 hashes. The exact verification script checks those hashes and matches all 28 listed A045994 terms.

## Mathematical mismatch in the source

The printed reciprocal `1/(1-x(1+x)M(x))` disagrees with the literal recurrence: its `x³` coefficient is `8`, while the recurrence gives `7`. This is proved in Lean as `printed_generating_function_false`. The proof derives the correct transform `M/(1+x-xM)` directly, then derives the conjectured recurrence.

We count the recurrence and this source correction as **one family**. The comment about grand Motzkin paths avoiding a crossing pattern is outside this package's formal scope.

## Web and literature screen

Both available web-search engines were used with exact-ID queries combining `A045994`, `proof` and `recurrence`. Relevant hits were opened or inspected; source evidence was preferred over search snippets.

| Source inspected | What it contains | Relation to this package |
|---|---|---|
| Official A045994 and A001006 records | Literal convolution, recorded recurrence conjecture, standard Motzkin identities | Source theorem and classical background |
| [Kruchinin and Kruchinin, arXiv:1103.2582v2](https://arxiv.org/abs/1103.2582v2) | General composita operations and functional-equation methods | Source-linked background; no claim that the method is new |
| [Tong Niu, arXiv:2605.04369v1](https://arxiv.org/abs/2605.04369v1) | Proof of a different Mathar recurrence, for A176677, by algebraic and differential identities | Acknowledged methodological overlap; different sequence and recurrence |
| [jOEIS A045994.java](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a045/A045994.java) | Direct computation using Motzkin terms and the defining convolution | Existing implementation; no derivation of the selected recurrence in the inspected file |
| [OEISSnippets A045994.wxm](https://github.com/Maxima-enthusiast/OEISSnippets/blob/2eae6f12843a3cf9dbd5ae0af76d50221cc77286/A045/A045994.wxm) | Kruchinin's nested binomial-sum formula | Existing formula implementation; no proof of the selected recurrence in the inspected file |

The refreshed arXiv checks read the titles, abstracts and publication metadata. The earlier reading retained in the work record also inspected the composita paper's theorem inventory and composition/reciprocal/functional-equation examples; it is not represented as an exhaustive line-by-line review of the whole paper.

## Repository screen

The fresh API results, immutable hit URLs and returned totals are preserved in `sources/search-receipts.json`. Direct implementation reads are hashed in `sources/implementation-receipts.json`; the unrelated substring hit is documented in `sources/substring-hit-inspections.json`. Results marked `incomplete_results: false` mean that query's returned search result was complete; they do not imply complete worldwide coverage.

- `A045994 language:Lean` returned zero files.
- `A045994 repo:kolinhuang0427/open-math-results` returned zero files.
- `A045994 repo:the-omega-institute/trureturing` returned one file in the finite Erdős–Nicolas divisor-data directory. The match is a hexadecimal-data substring, unrelated to the OEIS sequence.
- A semantic `Motzkin` query in `kolinhuang0427/open-math-results` returned seven files. The substantive [A092920 proof](https://github.com/kolinhuang0427/open-math-results/blob/f4fea05c78ea954ace0f1d51da6c9c189e68ccf0/targets/oeis-A092920/PROOF.md) was read: it concerns strongly monotone partitions, labeled Motzkin paths, and a binary-sum identity. Its objects and target theorem differ from A045994.

## Resolution and limits

The inspected materials establish prior definitions, formulas, implementations and methods. We did not identify an earlier explicit proof of this exact recurrence in this bounded screen. The deliverable is an explicit proof and formalization of a conjecture still labeled as such in the cited source snapshot. It is not a claim of worldwide priority or of a new general method.

The restored proof was rebuilt from source with the pinned Lean/mathlib configuration; no prior build log was reused. Author and independent build logs identify their exact input hashes and audited declarations. Finite exact checks are recorded separately and are not substituted for the universal Lean theorem.
