# An orphan-count identity, a composition asymptotic, and nine power-sum patterns

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

[Read the collected manuscript](Math_Proofs_Batch7.pdf) · [LaTeX source](Math_Proofs_Batch7.tex)

This collection resolves **six additional recorded assertions relative to the checked sources and repository: five proofs and one refutation**. The principal result proves the remaining weighted-row conjecture in A389524, completing all three numbered conjectures in that entry together with the earlier package. A second package fully formalizes a composition-statistic asymptotic with an explicit exponentially small relative error. A concurrent repository manuscript had established that result before publication of this package, so it is credited and not counted again. A third package classifies nine power-sum families: eight are true and one is false, with four of the true families credited as prior work.

The three standalone packages contain **four new Lean proof modules and two reproduced dependencies**. Each package includes the full written proof, formal source, pinned build configuration, primary source snapshots, prior-work notes, a fresh package-build log, an independent audit and compilation log, and SHA-256 checksums.

## Results and navigation

| Package | Contribution in this publication | Main formal declarations |
|---|---|---|
| [A389524 — weighted rows count orphans](../A389524Weighted/README.md) | **1 proved:** the original triangle satisfies the weighted orphan-count identity for every positive index. This completes Conjecture 2; the earlier package proved Conjectures 1 and 3. | `A389524Weighted.weighted_row`, `original_conjecture`; `Nathanson.orphan_formula` |
| [A377824 — all minimum-part positions](../A377824Formal/README.md) | **1 formalized:** the sum of all minimum-part positions over all compositions satisfies the proposed asymptotic, with an exact main term and error bound. The concurrent repository proof is not counted again. | `A377824.closed_form_error`, `normalized_limit`, `original_conjecture` |
| [A289629 — nine power-sum patterns](../A289629/README.md) | **4 proved, 1 refuted:** four further square-divisibility families are proved, and the fifth listed branch has a squarefree counterexample. Four other true branches were already established in A349989. | `A289629.eight_true_patterns`, `counterexample_squarefree`, `pattern_5_false` |

## 1. Completing the A389524 triangle conjectures

For every positive integer n, the original signed recursive triangle satisfies

\[
\sum_{k=1}^{n} kT(n,k)=h(n),
\]

where h(n) counts the actual integer quadruples

\[
ab-cd=n,\qquad a>c\ge0,\qquad b>d\ge0.
\]

The exact reversed ordering in the OEIS comment is also proved. The formal definition does not impose artificial coordinate bounds: finiteness is derived from the determinant and inequalities.

Both sides are connected to the same divisor convolution:

\[
2h(n)+d(n)=\sum_{t=1}^{n-1}d(t)d(n-t)+3\sigma(n).
\]

The orphan side uses explicit bijections. The triangle side derives a finite weighted polynomial identity from the original recurrence, works in a nilpotent quotient ring, and extracts the required coefficients. All geometric inverses, product identities, derivatives, divisor interpretations, and reindexing steps are proved in Lean.

`Orphans.lean` and `Weighted.lean` are new. `Uchimura.lean` reproduces the earlier dependency exactly, and `Triangle.lean` reproduces the earlier triangle proof with a clarified introductory comment; its mathematical code is unchanged. The [original package](../A389524/README.md) remains the historical proof of Conjectures 1 and 3. Those two results are not counted again.

## 2. Formalizing the A377824 asymptotic

For a composition of n into positive parts, add the one-based positions of **every occurrence of its minimum part**. Let a(n) be this statistic summed over all compositions, with a(0)=0.

For every n≥2, the proved estimate is

\[
0\le a(n)-\frac{(n+1)(n+6)2^n}{32}
\le n^2(7/4)^n.
\]

Equivalently,

\[
\frac{a(n)}{n^2 2^{n-5}}
=1+\frac7n+\frac6{n^2}+\varepsilon_n,
\qquad 0\le\varepsilon_n\le32(7/8)^n.
\]

This proves the recorded conjecture a(n)∼n²2^(n−5). A [concurrent repository manuscript](../A377824/README.md), present in commit `c92ab48c98acba51cb42ceb73536a7bad251ec2d` at the final publication check, had already proved the same exact main term and the sharper asymptotic error O(n²φ^n), where φ=(1+√5)/2. That manuscript is preserved, and this separately developed Lean package is published as a formal companion. The conjecture is not counted again among this batch's additional resolutions.

The proof formally enumerates every composition exactly once, identifies the recursive statistic with the literal sum of minimum positions, solves the recurrence for the contribution of parts equal to one, and bounds the remaining compositions using their Fibonacci recurrence. No asymptotic or generating-function description is assumed as a premise.

## 3. Nine power-sum branches, with a certified counterexample

Put F_k(n)=(k+1)^n+(-k)^n. The source comment conjectures nonsquarefreeness in the following nine families, for every integer m≥1.

| Branch | n | k | Proven square divisor / outcome | Contribution status |
|---|---|---|---|---|
| 1 | 22m−11 | 2 | 23² | Additional proof |
| 2 | 20m−6 | 3 | 5² | Prior formula in A349989 |
| 3 | 20m−2 | 3 | 5² | Prior formula in A349989 |
| 4 | 3^m | 7 | 13² | Additional proof |
| 5 | 15m | 7 | False at m=2 | Additional refutation |
| 6 | 20m−15 | 14 | 11² | Additional proof |
| 7 | 16m−8 | 19 | 17² | Prior formula in A349989 |
| 8 | 42m−35 | 23 | 43² | Additional proof |
| 9 | 8m−4 | 113 | 17² | Prior formula in A349989 |

The counterexample is

\[
8^{30}+7^{30}
=1260479379576072532986987473
=113\cdot3361\cdot25741\cdot12001921\cdot10742679301.
\]

The five factors are distinct primes. The factorization, primality certificates, coprimality, and squarefreeness are checked by the Lean kernel. The largest factor is proved prime using an explicit Lucas certificate, including the factorization of its predecessor and all required modular powers.

The eight affirmative branches follow from exact seed factorizations and the elementary fact that F_k(d) divides F_k(dt) for odd t. The fifth branch becomes valid when m is restricted to odd integers, with square divisor 13². That correction is not counted as another source conjecture. The package makes no claim about least eligible k, new sequence values, or all even m in the false branch.

## Classical ingredients and source status

The weighted triangle proof credits Uchimura, Bressoud–Subbarao, and subsequent work on weighted divisor identities and higher moments. The orphan convolution formula is also established background; its literal counting interpretation is re-proved to supply the formal definition bridge.

The composition proof credits Knopfmacher and Munagi's work on smallest parts in compositions, including their minimum-one dominance argument and refined composition counts. The exact all-position statistic and its error estimate are derived directly here. The power-sum proof credits the classical odd-power factorization and all four previously recorded A349989 branches.

The contribution is the explicit resolution and complete formal verification of the selected assertions from their original definitions. Primary-source inspections and searches with two search engines found no earlier exact resolution of the six additional assertions counted here. The final repository check identified the concurrent composition proof, which is credited and excluded from that count. The package `source_checks.md` files record the sources and the bounded scope of those checks. These checks do not certify exhaustive historical priority or OEIS editorial acceptance.

## Reproduce and verify

All packages pin **Lean 4.19.0** and mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. With Elan selecting the included toolchain, run from an individual package directory:

```sh
lake exe cache get
lake build
```

Each `lake-manifest.json` pins transitive dependencies. The exact delivered proof sources passed fresh package builds and separate isolated compilations. Public theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no unfinished proofs, custom axioms, `native_decide` calls, or unchecked numerical certificates.

`verification.txt` records the package build. `AUDIT.md` and `audit-verification.txt` record the independent review and compilation. To verify package deliverables, run in the relevant directory:

```sh
sha256sum -c SHA256SUMS.txt
```

The manifests cover every regular package deliverable except the manifest itself. Build caches and compiled artifacts are excluded. `Math_Proofs_Batch7_SHA256SUMS.txt` separately identifies this guide, the self-contained LaTeX source, and the rendered manuscript.
