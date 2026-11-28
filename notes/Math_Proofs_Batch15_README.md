# Batch 15: Motzkin convolutions and bounded zero-sum arrays

Two mathematical families covering three source entries: A045994 and the paired A202253/A202254 array counts.

The [complete manuscript](Math_Proofs_Batch15.pdf) includes the definitions, full proofs, exact boundary conditions, attribution, and formal-scope explanations. Its [LaTeX source](Math_Proofs_Batch15.tex) is self-contained.

## Proof packages

- [A045994](../A045994/README.md)
- [A202253](../A202253/README.md)

This batch has **10 local proof modules**, two successful author package builds, two separate successful source-only package builds, and substantive reviews by agents separate from the proof authors. All principal theorem axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`. The packages pin Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The [release verification record](Math_Proofs_Batch15_verification.txt) summarizes the actual successful builds and source hashes. Package build logs contain complete compiler output. The [SHA-256 inventory](Math_Proofs_Batch15_SHA256SUMS.txt) covers the release files. Finite Python checks are supplementary to the unbounded proofs.

An independent build here means a separate fresh directory with no copied local proof objects, sharing only the pinned compiler and external dependencies. The reviews are separate-agent checks, not external peer review. Bounded source and prior-work searches are documented inside each package, with no worldwide-priority claim.
