# A211417: explicit predecessor and classification of the contribution

Checked 2026-11-27. The Batch10 Lean theorem is correct. The new information changes attribution and result counting, not proof validity.

## Primary artifact

*Polynomial divisibility of height-one factorial ratios*, Part I, manuscript dated September 19, 2026, author line “OpenAI ChatGPT”, in VladimirReshetnikov/ProveIt. The repository describes it as an unrefereed AI-assisted research report, with conventional all-index mathematical proofs and separate exact certificates for optimal constants. It explicitly states that no Lean or Rocq formalization was produced.

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/cb0cb077fdaed91ea722783ba2b61d60973b7f18/SetTheory/Cardinals/docs/reports/congruences-and-valuations/factorial-ratio-polynomial-divisibility/article.tex

Pinned guide:
https://github.com/VladimirReshetnikov/ProveIt/blob/cb0cb077fdaed91ea722783ba2b61d60973b7f18/SetTheory/Cardinals/docs/reports/congruences-and-valuations/factorial-ratio-polynomial-divisibility/README.md

Current and pinned files were fetched independently and matched byte for byte. Article Git blob: `410c0b482bedfee6bacf59015a404d0b79df29e2`. Guide Git blob: `ff2825e21fb283a8ef3f1316ede9c06086ab384d`.

## Exact overlap

1. **Proposition `prop:positive`** proves the complete positive-shift family for A211417, for k in {2,3,5}, every r, and every nonnegative n. For I={1<=i<=r:gcd(i,k)=1}, m=|I|, it gives the explicit multiplier lcm(1,...,30r/k)^m. This directly precedes the Batch10 claim; it is not merely a nearby fixed-factor result.
2. **Corollary `cor:classificationAB`** gives a stronger classification of every nonzero polynomial over the integers that splits over the rationals and can uniformly divide A(n) after one positive integer multiplier. Its roots must be distinct and nonzero; negative roots in lowest terms may have denominator only 1,2,3,5; positive roots must have denominator 30. In particular, the proposed Batch11 classification for kn+1 is explicitly already proved.
3. **Subsection “Removing a restriction on positive offsets”** explicitly clears every consecutive product product_{i=1}^r(kn+i), with k in {1,2,3,5}. Thus dropping the coprimality restriction is also prior work.
4. The general polynomial criterion is Theorem `thm:criterion`, with separate necessity and sufficiency proofs. The full negative-shift family is Proposition `prop:negative`. No new claim should be made for these statements.

## Mathematical read-through

The relevant all-index argument was read in full. For a primitive linear factor kn+ell, divisibility by a sufficiently large prime power q forces n/q to approach a reduced point t/k from the side determined by ell. The Landau function is constant in a neighborhood of that side, so its one-sided value supplies the required prime-power contribution. Different factors cannot share a large prime power beyond their nonzero resultant. A fixed lcm power handles the finitely many smaller prime-power levels and retains product multiplicities.

For necessity, Dirichlet's theorem supplies arbitrarily large primes p in the required reduced residue class; n=(tp-ell)/k is integral. At these indices the first valuation level is the chosen one-sided Landau value and higher levels vanish because Mn<p^2. Any deficient root multiplicity therefore forces infinitely many distinct primes into the reduced denominator. In the height-one case, reflection of the step function identifies the permitted slopes from the signs of its cyclotomic exponents. The displayed cyclotomic cancellation for A211417 yields exactly {1,2,3,5} and {30}.

No gap affecting the positive family or slope classification was found in this read-through. This is a paper-proof assessment, not independent Lean certification of the prior artifact. Optimal-constant certificates and unrelated Part II conclusions were not reverified.

## Independent classical implication

Bober, arXiv:0709.1977, Theorem 3.1, printed p. 7, states Landau's multivariate factorial-ratio criterion. The separate file [landau_provenance.md](landau_provenance.md) gives the exact specialization that already implies the Batch10 positive existence conclusion with its factorial constant. This classical implication reinforces the attribution caution, but the explicit September 2026 paper alone is enough to classify the Batch10 contribution as an independent formalization of prior mathematical work.

## Publication correction implemented

The exact verified Lean source is unchanged. The README and source-check report now identify A211417 as an independent formalization of a previously proved assertion and credit the explicit ProveIt report and the Landau/Bober background. The corrected collection count is four resolutions and one independent formalization, with the stated bounded-priority qualifications.

The standalone mathematical section, combined guide, and combined manuscript have been corrected, and their checksum records regenerated. The original formal audits and manuscript reviews are retained as historical records. The [dated collection correction](../notes/Math_Proofs_Batch10_correction_2026-11-27.md) records the rebuilt PDF, exact revised hashes, and unchanged Lean source.

## Discovery and search limitation

The initial exact-ID and semantic web searches plus trureturing checks missed this explicit predecessor. The broader GitHub code search `A211417 slope` found the report immediately. Future screening must include global GitHub semantic searches and the ProveIt report repository. The prior paper is not an OEIS update, journal publication, or trureturing result, explaining why those narrower screens were insufficient.

## Repository chronology checked independently

GitHub commit `a3fe9660ee6c3ab92752594c2099c3cd214012c9` has author and committer date **2026-09-19 22:49:55 UTC** and places the original report among 64 unpacked reports. The current article history records the Part II integration at `aeca276466ac1c5f17257954fa586659499ae004`, **2026-10-02 03:21:17 UTC**. The chronology is earlier than our November 27 Batch10 publication.

The original September 19 article was separately fetched at the original path `docs/reports/congruences-and-valuations/factorial-ratio-polynomial-divisibility/article.tex` in that historical commit. Its Git blob is `7d4e8bbf353183f4b8147df740e549818d18a3fb`. The full positive-family proposition, slope-classification corollary, and unrestricted-product subsection are all present there, so their dating does not depend on the later Part II integration.
