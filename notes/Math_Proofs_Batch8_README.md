# Batch 8 manuscript and verification guide

**Odd-degree irreducibility, a word identity, and arithmetic assertions**  
Blake Stone, developed with OpenAI Astra 6.2 · November 27, 2026

The [eight-page manuscript](Math_Proofs_Batch8.pdf) contains complete mathematical proofs of five recorded assertions and one refutation, with exact scope and historical qualifications.

| Package | Result | Count |
|---|---|---:|
| [A326925](../A326925/README.md) | Every odd-degree normalized numerator is irreducible, even over $\mathbb Q(\sqrt5)$; the exact even-order derivative and canonical-numerator bridges are proved. | 1 proved clause |
| [A288668](../A288668/README.md) | The literal A288665 rewrite words satisfy $w_{n+3}=w_nw_nw_{n+1}$, proving the shared length assertion. | 1 proved assertion |
| [A134559](../A134559/README.md) | The prime 54217 refutes the antidiagonal-product characterization, with both primalities and the complete original remainder fiber certified. | 1 refutation |
| [A000033](../A000033/README.md) | A uniform polynomial congruence proves the prime-shift assertions in A000033, A000159, and A000181. | 3 proved assertions; historical novelty unverified |

The A326925 even-degree factorization clause is outside the proved scope. Supporting identities and stronger consequences are not counted as additional conjecture resolutions. Relevant older Carlitz and Stevens papers prevent a first-publication claim for the ménage congruences because their full texts were unavailable during review. The other targets survived the bounded prior-proof searches recorded in their packages; no exhaustive historical-priority claim is made.

## Reproduce the mathematical verification

Each of the four directories is a standalone Lean package, pinned to Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. In any package, run:

```sh
lake exe cache get
lake build
```

Each package includes:

- Exact source definitions and complete Lean proofs.
- Primary-source snapshots and source/prior-work notes.
- A fresh author build and a separate independent fresh build.
- A written mathematical and source-correspondence audit.
- A SHA-256 manifest identifying the delivered files.

The independent reviewers are separate collaborating agents. This describes an internal mathematical review and kernel-verification process, not external journal peer review or OEIS editorial acceptance. Main theorem dependencies use only Lean's standard axioms; there are no admissions, added axioms, unsafe proof declarations, or native-evaluation shortcuts.

## Rebuild the manuscript

Keep `Math_Proofs_Batch8.tex` and `menage_fragment.tex` in the same directory, then run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Math_Proofs_Batch8.tex
pdflatex -interaction=nonstopmode -halt-on-error Math_Proofs_Batch8.tex
```

The delivered PDF has eight pages. Its final TeX build had no overfull or underfull boxes or unresolved references. All eight rendered pages were visually inspected, and PDF extraction confirmed that every page contains text. The exact PDF and both TeX source files are covered by `Math_Proofs_Batch8_SHA256SUMS.txt`.
