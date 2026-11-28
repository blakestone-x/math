# Batch 14 — binary columns, polynomial reduction, and quartic harmonic means

**Blake Stone · Proofs developed with ChatGPT · November 27, 2026**

[Read the complete manuscript](Math_Proofs_Batch14.pdf) · [LaTeX source](Math_Proofs_Batch14.tex)

This collection proves selected recorded assertions for **four OEIS entries in three mathematical families**. A192250 and A192251 are the two components of one polynomial-reduction construction and share a single proof certificate. Closed forms, exact cutoffs, generating functions, and supporting lemmas are counted within their respective family.

| Package | Exact result | Modules |
| --- | --- | ---: |
| [A067576](../A067576/README.md) | Kimberling's eventual doubling of the shifted binary-weight columns, with exact least starting row d(j)=max(1,j−1) and a closed formula throughout the doubling region. | 4 |
| [A192250 and A192251](../A192250/README.md) | Mathar's two recorded recurrences for the constant and linear components of the literal terminating polynomial reduction, at every original source index n≥4. | 3 |
| [A227013](../A227013/README.md) | The exact conjectured generating function for harmonic-mean floors between consecutive fourth powers, with the corrected same-index floor formula and recurrence cutoff. | 8 |

## Verification

All **fifteen proof modules** are explicit default Lake roots. Each package pins Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All three author builds and all three independent builds passed. These six builds start from source and configuration copied into separate fresh directories, sharing only pinned external dependency caches; no previously compiled local proof objects are copied. Logs preserve the exact source hashes.

All three independent reviews passed. Each reviewer was separate from that package's proof authors and checked the literal source definitions, the mathematical argument, formal endpoint scope, indexing, and provenance. The principal theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`; the proof sources contain no admitted lemma, custom axiom, or `native_decide`.

The manuscript gives the complete human arguments, including the quartic harmonic mean's full positive-coefficient certificates. Individual packages preserve immutable source snapshots, bounded prior-work searches, fresh build logs, review reports, and supplementary exact-integer or rational replays. The unbounded claims are proved in Lean. See [manuscript verification](Math_Proofs_Batch14_verification.txt) and [checksums](Math_Proofs_Batch14_SHA256SUMS.txt).

## Attribution and limits

Binary-weight enumeration and ranking are classical. Known diagonal cases and the 2016 ranking paper are credited, and the exact onset had already been posed as an admitted Lean statement in open-math-agents. The binary package supplies its complete proof from the literal increasing enumeration.

For the polynomial-reduction family, the standard monic-remainder interpretation and Wiktorowicz's supporting note are credited, as is Campbell's earlier Fibonacci-weighted formula for A192251. The two selected component recurrences follow together from one polynomial divisibility certificate and a proved bridge to the source's terminating algorithm.

The quartic harmonic package credits the existing proof for the neighboring cubic problems, which were excluded from this batch. Classical moment methods and existing numerical generators are disclosed. It proves the recorded quartic generating-function assertion from the literal reciprocal sum and explicitly corrects the source's separate formula index and recurrence cutoff.

The prior-work screen used both web engines, exact and semantic global/scoped GitHub searches, and inspection of relevant papers, statements, and programs. No earlier proof of the selected exact assertions was located within the checked material. These bounded searches do not establish first discovery or worldwide historical priority. The reviews are independent within this collaboration and do not constitute journal peer review. This publication makes no OEIS edits.
