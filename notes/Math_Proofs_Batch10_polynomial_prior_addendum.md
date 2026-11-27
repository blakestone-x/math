# A326926/A326933: supplementary GitHub prior-proof screen

Checked November 27, 2026, after the Batch 10 publication. This addendum supplements the primary literature and exact-source review already packaged with A326926. It does not alter the mathematical proof or claim exhaustive historical priority.

The searches used the connected GitHub code-search service, both globally and scoped to [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt). Raw responses, including immutable result URLs, are preserved only in the working research archive at `research/batch11/algebra/prior_search/batch10_recheck*.json`; they are not bundled with this published correction. The query scopes and returned-set findings are summarized below.

| Query and scope | Returned-set finding |
| --- | --- |
| A326926, global, up to 50 results | Sequence generators in joeis and loda, sequence-title lists in oeis-alien, the present project's published package, and irrelevant hexadecimal substring collisions. No earlier proof of the classification was located in this returned set. |
| A326933, global, up to 50 results | loda/Pari sequence computations, a sequence-title list, the present project's package, and irrelevant substring matches. No earlier classification proof located. |
| A326926, ProveIt | No results. |
| A326933, ProveIt | No results. |
| Norfleet derivative, ProveIt | No results. |
| Kimberling, ProveIt, up to 15 results | Partition and binary-substitution research, with no matching derivative-numerator classification. |
| arctangent irreducibility, ProveIt | Unrelated polylogarithm, algebra, and analytic-number-theory material. This broad query was noisy. |
| literal `1-x+x^2`, ProveIt | Reciprocal Rueppel series and an elementary rational identity in a different asymptotic calculation; no matching derivative theorem. |
| cotangent polynomial irreducible, ProveIt | Unrelated analytic/algebraic results; this broad query was noisy. |
| literal phrase `prime other than 3` with polynomial, global | Unrelated intersective-polynomial, graph-counting, and arithmetic examples. No exact source-family theorem located. |

The relevant returned ProveIt snapshots were `cb0cb077fdaed91ea722783ba2b61d60973b7f18` and `979b94ec4ec8a53194727e65b25d60ea7a930bd2`; results were gathered from the indexed default branch, not an exhaustive checkout of every historical branch. The oeis-alien matches were merely the sequence names at `run1/exp83-chk/names.md` and `run1/exp144-chk/names.md` in commit `753bbbe72fc4a88009a18bcb9b1cd3ac9cc363ab`, not a proof claim in the returned text.

**Conclusion:** this expanded bounded screen did not locate an earlier exact proof of the classification “nonconstant row n is irreducible if and only if n+1 is prime and different from 3.” It supplies no guarantee of novelty. Classical Lucas divisibility, reciprocal Eisenstein, and the related tangent/cyclotomic literature remain credited in the existing source report. The two OEIS identifiers still represent one shared assertion, and the separate factor-count problem in A326933 is not claimed solved by that classification alone.
