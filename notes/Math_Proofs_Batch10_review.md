# Batch 10 manuscript and verification record

Date: November 27, 2026.

## Mathematical and formal scope

The batch resolves five assertions: the A326926/A326933 irreducibility classification, the A211417 positive-shift integrality family, the A289128/A289131 literal length recurrence, and the two position-limit refutations in A289129 and A289130. This is three proofs and two refutations, with repeated statements counted once.

All fifteen local proof modules are covered by author and independent fresh Lake builds. The three independent reviews passed without a mathematical or Lean-source correction. Each package preserves its exact source statements, pinned dependency manifest, verification logs, and source hashes. One rational-function derivative module is deliberately reused unchanged from the preceding polynomial project.

The combined manuscript received a separate read-only mathematical review. That review checked the complete arguments and formal scope, independently recomputed the thirty floor-function values and seven forced residues, and found no correction needed. The report is preserved in Math_Proofs_Batch10_math_review.md.

## PDF checks

The complete standalone source is Math_Proofs_Batch10.tex. It was compiled twice with pdfLaTeX. The final compilation log contains no overfull or underfull boxes, unresolved references, missing characters, or package warnings.

The PDF contains nine US-letter pages. All fonts are embedded Type 1 fonts. All nine pages were rendered with Poppler and visually inspected. The inspection covered the title and scope table, polynomial identities and reduced-numerator statement, the thirty-value floor table, the prime-residue table, exact recurrence domains, the four position-ratio formulas, long theorem names, page numbers, and references. Full-size views of pages four and seven confirmed the arithmetic tables and the detailed subsequential-limit formulas. No clipping, overlap, or missing glyphs remained.

Final LaTeX SHA-256:

```text
71b8eebd50ee5eaf26b5481840a06452c9fdc90f3e505e22da56a1da496b3ede
```

Final PDF SHA-256:

```text
cbf1eafc6b6473a97826082860209744e2c877b6ecc3d9b11d2e99958a40dbfa
```

The source and PDF hashes identify the final inspected versions. This is a mathematical manuscript, Lean kernel-checking record, and independent agent review; it does not claim human peer review or editorial acceptance.
