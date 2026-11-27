# Batch 12: collection review record

Reviewed November 27, 2026. Final disposition: **PASS for the three assertions stated in the manuscript.**

## Per-package independent reviews

| Package | Reviewer | Reviewed conclusion | Fresh source build |
| --- | --- | --- | --- |
| [A081097](../A081097/independent_review.md) | `sequences12` | Exact positive nested-floor membership, exhaustive and ordered four-orbit classification, and the source generating function. | All six local modules passed. |
| [A288511](../A288511/independent_review.md) | `number12` | Literal finite-word scanner and all-index equality with the independently defined source recurrence. | All four local modules passed. |
| [A118207](../A118207/independent_review.md) | `sequences12` | Both complete source factor families, the nilpotent identity, and the coefficientwise passage to formal power series. | All seven local modules passed. |

Each reviewer had no contribution to the proof sources of the package they reviewed. These are separate-agent reviews within the collaboration, not external journal peer review. Their signed records identify the inspected sources and exact artifact hashes. The fresh builds copied only source and configuration files; pinned external dependency caches were shared.

All three packages also have successful separate author builds. The principal theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The finite Pell certificate uses only `propext`. The reviewers found no admitted theorem, custom axiom, `native_decide`, or unresolved source-to-model assumption.

## Integration checks

The combined manuscript contains the complete reviewed mathematical arguments, together with a common introduction, verification discussion, and bibliography. The A288511 discussion adds the citation for the separately screened Tribonacci-rule paper. Its mathematical content and recurrence remain those reviewed in the package.

The collection's result count is three:

- A081097 resolves the fixed-5 empirical generating-function assertion and classifies its positive source members. It does not claim the separate arbitrary-nonsquare-parameter conjecture.
- A288508, A288511, and A288512 repeat one length conjecture. The final theorem proves every literal length equals the source recurrence. The documented extra-x correction in the source generating-function display is an algebraic corollary, not another counted resolution or an additional Lean formal-series theorem.
- A118207 resolves the specific paired cyclotomic formula. Bala's previously proved helper and the classical arithmetic facts are explicitly credited supporting results.

The reviews compared source exports, initial values, offsets, sign conventions, and quantified conclusions. The source dossiers distinguish related algorithms and known theorems from proofs of the exact targets. Their prior-work conclusion remains bounded to inspected evidence and does not certify global historical priority or OEIS editorial acceptance.

## Review correction incorporated

The A118207 reviewer identified a wording issue in the human manuscript's blanket finite-prefix statement: the unpaired ordinary-cyclotomic helper needs its index-one constant −1 even in degree zero. The statement now uses the bound `max{1,N}`. The two target paired families and normalized factors already satisfy the stronger index-N bound used by Lean. No proof source or configuration changed; the successful author and independent builds therefore remain builds of the final proof bytes.

## Final manuscript and layout

- Title: *Floor sequences, replacement words, and cyclotomic products*.
- Length: nine pages.
- TeX SHA-256: `cf1417c25544d20539b4ba17942ac7fc4853f2fbd322c8b0079c2fb06d60e34e`.
- PDF SHA-256: `d115983ed5682d1f15eb3b7c85bdb369fca73524a43a764db758103a3daec0ca`.
- Both final pdfLaTeX passes exited zero; the final compiler log reports no warnings, overfull boxes, underfull boxes, or missing characters.
- All nine rendered pages were inspected for legibility, equation and table placement, page breaks, and bibliography layout. All seventeen font entries are embedded subsets with Unicode maps.

The [build record](Math_Proofs_Batch12_build.log) preserves the two compiler transcripts and the layout inspection record. Package and collection checksum inventories identify the final deliverables.
