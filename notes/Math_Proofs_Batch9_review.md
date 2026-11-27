# Batch 9 manuscript verification

Date: November 27, 2026.

The complete standalone source is Math_Proofs_Batch9.tex. The accompanying PDF contains 10 US-letter pages with embedded Type 1 fonts.

## Mathematical scope

- A326925: the even-degree factorization clause, with exact reduced-numerator correspondence and the Fibonacci/Lucas constant terms in an explicit normalization. The earlier odd-degree proof is credited and included as a dependency.
- A288520/A288523: one shared replacement-length conjecture, proved from the literal scanner for every index; the source recurrence begins at index 5.
- A400939: an infinite-family partial result for the generalized division walk, with a unique division and an exact permanent tail for every odd prime congruent to 2 or 3 modulo 5.

The three proof packages contain their own source reviews, author verification records, independent reviews and builds, and file checksums.

## PDF checks

The final source was compiled twice with pdfLaTeX. The final log contains no overfull or underfull boxes, unresolved references, missing characters, or package warnings.

Every page was rendered with Poppler and visually inspected. The inspection covered equations, theorem statements, tables, page numbers, section transitions, long Lean declaration names, bibliography links, and the precise domains in the recurrence and walk formulas. Detailed page views confirmed the conjugation proof and the two walk alternatives. No clipping, overlap, or missing glyphs remained.

Final source SHA-256:
c654f5e6b808434073726111886a77288257ddca1eda64561231b441a61456d0

Final PDF SHA-256:
128b725ad64a4fd59bbac9479616c820450277833c905b2589402a6454681116

This is a manuscript and machine-checking record, not a claim of human peer review or OEIS editorial acceptance.

