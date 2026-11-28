# A227013 source and prior-work check

Checked November 27, 2026. This is a bounded source-status and provenance record, not a proof of global novelty.

## Primary source

[OEIS A227013](https://oeis.org/A227013), revision 21, November 3, 2024, defines the floor of the harmonic mean of the consecutive integers from (n−1)^4+1 through n^4. Clark Kimberling supplied the sequence on July 1, 2013. All three displayed formula lines are labelled conjectured in the inspected source.

The frozen [source export](sources/A227013.seq) comes from the official repository's last file-touch commit [571197984aeda7b8b680fe3a1f6a43f9898cd441](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A227/A227013.seq), exported November 24, 2024. Its SHA-256 is `46325556aa29c1c490c7b3fbd35295840230765aede9205bdb98b77986e890bc`. Exact byte count and metadata are in [source_manifest.json](sources/source_manifest.json). The source revision date and repository export date are distinct.

The selected endpoint is the exact rational generating function. Its first coefficient is 1; with source offset 1 it represents Σ a(j+1)x^j. The separate printed cosine-polynomial expression is shifted by two indices, and the recurrence's printed condition n>2 is invalid. We prove the corrected floor formula for n≥3, preserve a(1)=1 and a(2)=6, prove the recurrence for newest index n≥10, and formally exhibit its failure at n=9. These consequences and corrections are counted within one source family.

## Exact and semantic search

Both web engines were used. Exact and semantic query sets included `"A227013" proof`, `"A227013" "proof" mathematics`, `"quartic" "harmonic mean" Kimberling`, `"A227013" Ramaharo recurrence`, `"harmonic mean" "fourth powers" floor`, and `"harmonic means" "quartic" floor`. Relevant returned material was the OEIS source and its neighboring entries, sequence-generation sites, and adjacent cubic work. No exact quartic proof was found among the returned results. The weaker search engine sometimes returned neighboring A-numbers instead of the target; the official immutable source was fetched directly rather than inferred from those snippets.

Global GitHub searches included the exact identifier A227013 (first 100 results), `A227013 harmonic proof`, `quartic harmonic mean Kimberling`, `"harmonic mean" "fourth" proof`, and `"quartic" "Kimberling"`. Incidental hexadecimal matches were excluded from mathematical interpretation. [prior_github_receipts.json](sources/prior_github_receipts.json) retains result counts and relevant returned immutable URLs; result caps and search indexing limit coverage.

The exact identifier was also searched in `VladimirReshetnikov/ProveIt`, `the-omega-institute/trureturing`, and the neighboring cubic proof repository below, returning no exact match. These are bounded indexed searches, not exhaustive checkout audits. The existing `blakestone-x/math` publication catalogue was checked for duplicate target entries.

## Closest existing implementations

- [jOEIS A227013.java](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a227/A227013.java) is a `HolonomicRecurrence` generator using signature `[0,-1,4,-6,5,-5,6,-4,1]` and nine initial terms. This already encodes the conjectural recurrence but supplies no harmonic-mean equivalence proof.
- [LODA A227013.asm](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/227/A227013.asm) records the same terms and an equivalent arithmetic recurrence program. It supplies no theorem identifying that program with the literal reciprocal sum.
- OEIS-Spider records reproduce the source or cross-references. Their existence is source duplication, not independent proof evidence.

The formula patterns and generators predate this work. Their existence is disclosed; a claimed new formula discovery would be inappropriate.

## The prior cubic proof, explicitly excluded

A semantic global GitHub query `"harmonic mean" "floor" Kimberling` located [rajdeepbaror/kimberling-a227012-lean](https://github.com/rajdeepbaror/kimberling-a227012-lean), inspected at commit `f33c98bac3c0eabccf7c66e339d661494960c523`. We read its README and mathematical manuscript and inspected its stated theorem scope. It proves all four recorded formulas for the cubic blocks A227012 and a general eventual recurrence theorem for positive-leading-coefficient integer cubic block functions, including the A227015 application. The repository supplies complete Lean developments for those results. We excluded A227012 and A227015 after finding this prior work.

The general theorem's hypothesis is a cubic block function. It does not cover the quartic g(n)=n^4 of A227013. The present proof instead uses finite symmetric reciprocal identities, central moments through degree six, and two explicit positive-coefficient rational certificates to establish every required index from five onward, with four exact initial computations. No claim is made to a new general moment method or to first formalization of harmonic-mean floor arguments.

The prior paper is linked and credited, not redistributed. The source screen found no earlier exact proof of the quartic source-to-generating-function assertion within the material inspected. It cannot certify worldwide historical priority.
