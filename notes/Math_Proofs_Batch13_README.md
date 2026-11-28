# Batch 13 — cyclotomic cosets, a triangle, and reciprocal cube roots

**Blake Stone · Proofs developed with ChatGPT · November 27, 2026**

[Read the complete ten-page manuscript](Math_Proofs_Batch13.pdf) · [LaTeX source](Math_Proofs_Batch13.tex)

This collection proves six recorded source assertions in three mathematical families. Equivalent recurrences and supporting lemmas are counted within their family.

| Package | Exact result | Modules |
| --- | --- | ---: |
| [A220018 family](../A220018/README.md) | Barker's four quadratic orbit counts for multipliers 3, 7, 9, 13 modulo 10^n; covers A220018, A220019, A220020, A221855. | 6 |
| [A052392](../A052392/README.md) | Israel's empirical algebraic generating function and order-four recurrence for the literal source triangle's subdiagonal. | 4 |
| [A184534](../A184534/README.md) | Barker's empirical generating function from the reciprocal fractional cube root, including the corrected closed-form index. | 4 |

## Verification

All fourteen proof modules are explicit default Lake roots. Each package pins Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Each has two successful source-only builds in separate fresh directories, one by the authoring team and one by a reviewer who did not contribute to its proof sources. Logs preserve the exact hashes. The principal theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`; no admitted lemma, custom axiom, or `native_decide` occurs.

The manuscript supplies the mathematical arguments, and the individual packages preserve source snapshots, bounded prior-work searches, and separate review reports. The PDF was compiled twice, checked for warnings, and visually inspected on all ten pages. See [PDF verification](Math_Proofs_Batch13_verification.txt) and [checksums](Math_Proofs_Batch13_SHA256SUMS.txt).

## Attribution and limits

The four coset formulas are related specializations, not four independent new theories. General coset classification and prime power order methods are prior work. Hendel's triangle recurrence and classical weighted Delannoy theory are credited. The cube-root expressions already occur in numerical generators. This collection supplies full source-to-theorem proofs of the selected recorded assertions; it does not claim first discovery of their formulas or worldwide historical priority.

The prior-work screen used both web engines, global and scoped GitHub searches, and inspection of relevant papers and programs. It found no earlier explicit settlement of these exact assertions within the checked material. The reviews are independent within this collaboration, not journal peer review. This publication makes no OEIS edits.
