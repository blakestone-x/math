# Batch 10 attribution correction and revised manuscript record

**November 27, 2026.** This correction supersedes the initial contribution count and the negative prior-proof finding for A211417. The mathematical statements and their verified Lean proofs remain valid.

## Corrected result count

The initial release described Batch 10 as five new resolutions: three proofs and two refutations. The correct description is **four newly resolved assertions, comprising two proofs and two refutations, plus one independent Lean formalization of a previously proved assertion**.

| Assertion | Corrected contribution status |
|---|---|
| A326926/A326933, complete prime-index irreducibility classification | One resolution; repeated comments count once. |
| A289128/A289131, literal scanner lengths equal the prescribed recurrence | One resolution; repeated comments count once. |
| A289129, zero-position ratios do not converge | One refutation, strengthened to exclusion of every real limit. |
| A289130, one-position ratios do not converge | One refutation, strengthened to exclusion of every real limit. |
| A211417, the arbitrary positive-shift family for all three slopes | One independent formalization of prior mathematics; excluded from the new-resolution count. |

These are bounded attribution findings, not a certification of historical priority or human peer review.

## The explicit predecessor

*Polynomial divisibility of height-one factorial ratios*, Part I, is an unrefereed AI-assisted report with author line OpenAI ChatGPT in VladimirReshetnikov/ProveIt. Its original manuscript was committed on **September 19, 2026, at 22:49:55 UTC**, before the November 27 Batch 10 publication.

The [original September 19 source](https://github.com/VladimirReshetnikov/ProveIt/blob/a3fe9660ee6c3ab92752594c2099c3cd214012c9/docs/reports/congruences-and-valuations/factorial-ratio-polynomial-divisibility/article.tex) is pinned at commit `a3fe9660ee6c3ab92752594c2099c3cd214012c9`, Git blob `7d4e8bbf353183f4b8147df740e549818d18a3fb`. The current combined report was also checked at an immutable commit; its detailed identifiers and exact overlap are recorded in [the primary-citation report](../A211417/PRIOR_PROOF.md).

Proposition `prop:positive` proves the entire A211417 positive-shift family for every prescribed slope and every shift range. It supplies the multiplier

$$
\operatorname{lcm}(1,\ldots,30r/k)^{|I|},
\qquad I=\{1\le i\le r:\gcd(i,k)=1\}.
$$

Corollary `cor:classificationAB` proves a stronger classification of all polynomials splitting over the rationals that can uniformly divide the factorial ratio after a constant multiplier. A separate subsection removes the coprimality restriction from the positive-shift product. These statements are already present in the original September 19 article, so their chronology does not depend on the later integration of Part II.

The relevant all-index paper argument was read and no gap affecting the positive-shift family was found. This is an assessment of that paper proof, not an independent formal certification of the predecessor. Its unrelated results and optimal-constant certificates were not reverified. The report explicitly states that it contains no Lean or Rocq formalization.

The initial exact-ID and semantic web searches, OEIS checks, and trureturing checks missed this predecessor. A broader global GitHub semantic code search found it. The initial negative search finding is therefore superseded. The verified contribution retained here is the independently developed Lean proof, including the literal factorial-ratio definition, exact natural division, the full product valuation with multiplicities, a positive uniform witness, and the rational-integrality endpoint. No claim of first formalization is made.

The [Landau provenance supplement](../A211417/landau_provenance.md) also records an exact two-variable specialization of the classical multivariate criterion, stated in Bober's Theorem 3.1. This independently explains why the existence conclusion with the factorial multiplier follows from older general mathematics.

## Changes made

The A211417 README, source-check report, and standalone manuscript section now explicitly credit the prior positive-shift theorem. Two provenance supplements identify the original dated source and the classical Landau implication. The combined guide and manuscript revise the title, abstract, result table, section attribution, references, and result count. The corrected PDF is rebuilt from that revised source.

The following existing files were changed:

- `A211417/README.md`
- `A211417/source_checks.md`
- `A211417/manuscript-section.tex`
- `A211417/SHA256SUMS.txt`
- `notes/Math_Proofs_Batch10_README.md`
- `notes/Math_Proofs_Batch10.tex`
- `notes/Math_Proofs_Batch10.pdf`
- `notes/Math_Proofs_Batch10_SHA256SUMS.txt`

The following records were added:

- `A211417/PRIOR_PROOF.md`
- `A211417/landau_provenance.md`
- This dated correction record.
- `notes/Math_Proofs_Batch10_correction_build.log`
- `notes/Math_Proofs_Batch10_polynomial_prior_addendum.md`
- `notes/Math_Proofs_Batch10_word_prior_addendum.md`

The [polynomial prior-search addendum](Math_Proofs_Batch10_polynomial_prior_addendum.md) and [replacement-word prior-search addendum](Math_Proofs_Batch10_word_prior_addendum.md) report the subsequent global GitHub and ProveIt checks for the other four assertions. No exact earlier resolution was located in those returned sets. Each report states its query and indexing limits; raw tool responses are preserved only in the working research archive, while the compact findings are included here.

## Proof-source invariance

All **15 local proof modules**, all Lake configurations and dependency manifests, all seven archived OEIS exports, and all author and independent formal build logs were compared with the pre-correction bytes and are unchanged. This documentation correction does not require a new Lean build; the existing fresh author and independent builds apply to the identical sources.

The exact A211417 proof-source SHA-256 **before and after** is:

```text
4d276b1eb1e954f8d8ceaaf007ef63bfa6a3c9fc7179745d791875877996b964
```

The original audit and manuscript reviews are retained byte-for-byte as historical records. Their mathematical and compilation checks remain applicable. Their earlier attribution language and new-resolution count are superseded by this correction. In particular, they must not be cited as a current finding that no A211417 predecessor exists.

| Preserved historical record | SHA-256, unchanged |
|---|---|
| `A211417/AUDIT.md` | `d4d5310c27be4160bb74d29a42890b0bd2ebe16a59610768485e1512d5c84a74` |
| `notes/Math_Proofs_Batch10_math_review.md` | `e13015bcadfa6f5b8c33d7798e7c1706f4a129c2faccc4cd13fbb7dc4092e8e2` |
| `notes/Math_Proofs_Batch10_review.md` | `81e6d0903b1d3455895fcefa0c34087deb04e74f83ccf08453fcd781b9ee52cf` |

## Revised PDF verification

The revised self-contained LaTeX source was compiled twice with pdfLaTeX using the existing local TeX environment. The [final build log](Math_Proofs_Batch10_correction_build.log) has no overfull or underfull boxes, unresolved references, missing characters, or package warnings.

The corrected PDF has **10 US-letter pages**, with embedded Type 1 fonts. All ten pages were rendered with Poppler at 110 dpi and visually inspected. The inspection covered the corrected title and abstract, source/count table, complete proof pages, factorial and residue tables, four subsequential-limit formulas, theorem names, attribution paragraphs, bibliography, and page numbering. No clipping, overlap, missing glyph, or unreadable equation was found.

| Artifact | Initial release SHA-256 | Corrected SHA-256 |
|---|---|---|
| Combined LaTeX source | `71b8eebd50ee5eaf26b5481840a06452c9fdc90f3e505e22da56a1da496b3ede` | `86a299d34d968136e604f9b867706d76224e80c48bd67505ee79526be50f6974` |
| Combined PDF | `cbf1eafc6b6473a97826082860209744e2c877b6ecc3d9b11d2e99958a40dbfa` | `8cea3eb8c5632b0c278120c18c9da707328e13264578bd0635b08045c7cb718a` |

The regenerated A211417 and notes checksum manifests identify all revised files and the preserved historical records. The A326926 and A289128 packages are unchanged. Repository-wide publication and the root README correction are coordinated separately.
