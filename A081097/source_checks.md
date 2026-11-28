# Source and bounded priority screen: A081097

- Primary sequence: <https://oeis.org/A081097>, revision 12, 24 June 2013
  23:32:00. Last-touch OEIS-data commit:
  `72c53dd50967ac7166f7d31bf79be95174ec5bc6`.
- Immutable source:
  <https://github.com/oeis/oeisdata/blob/72c53dd50967ac7166f7d31bf79be95174ec5bc6/seq/A081/A081097.seq>.
- Local source SHA-256:
  `ac65edf8f88112594d9f04f03f1cf9f5a958b6e54fc7d3f21f93661809f0ef20`.
- Exact-ID web searches found the OEIS entry, its internal page, and the old
  OEIS conjectures list, retaining the empirical formula. The global GitHub screen also found a joeis implementation explicitly marked `Conjectural`: `archmageirvine/joeis`, commit `abb609413c9b320e769eaf41c0eef4ee43d1b5e7`, path `src/irvine/oeis/a081/A081097.java`. That implementation evaluates the proposed generating function and does not prove the nested-floor claim.
- Exact-ID scoped GitHub searches in
  `the-omega-institute/trureturing` and `VladimirReshetnikov/ProveIt`
  returned no results. Relevant visible repository snapshots were respectively
  `7c3c605dff254e6281ff23265a7faf4b20e7534e` and
  `a4404ca0247c31b8760589015b7eb6ab4efb6f92`.
- Semantic repository searches included `floor sqrt Pell recurrence`,
  `Cloitre nested floor`, `Cloitre floor sqrt`, and
  `sqrt floor Diophantine`. Returned results concerned other Cloitre
  recurrences, generic Pell encodings, Beatty sequences, and unrelated
  Diophantine bounds. None supplied the fixed-5 floor bridge, the four-orbit
  classification for this sequence, or Barker's formula.
- Web searches included the initial numeric string, `floor(sqrt(5)` with
  `322`, Cloitre/Pell/floor combinations, nested floors and Pell equations,
  and the exact identifier restricted to arXiv/MathOverflow/Math.SE. No
  directly relevant prior settlement surfaced in those retrieved results.
- A potentially relevant primary paper was examined:
  Benoit Cloitre and Jeffrey Shallit, *Some Fibonacci-Related Sequences*,
  DOI <https://doi.org/10.1080/00150517.2025.2487802>, published online
  5 January 2026, preprint <https://arxiv.org/html/2312.11706v3>.
  It studies A105774 through Zeckendorf automata. Its available full text
  contains neither A081097 nor a Pell discussion. It does not give this
  target's formula.
- The related OEIS A046090 does already connect the parameter-2 floor
  equation to a classical Pell sequence; A023039 and A060645 give the
  standard norm-one Pell unit sequence in the field Q(sqrt(5)). Those are
  acknowledged mathematical background, not new results claimed here.

This is a bounded literature search, not a proof of worldwide priority.
The contribution is a proof and formalization of this precise empirical fixed-5
formula. Pell descent and rational generating functions for matrix orbits
are classical methods.


## Scope of the formal result

The included `sources/A081097.seq` preserves the exact source export. `Source` in `FloorBridge.lean` transcribes the real nested floors. The enumeration theorem restricts to positive inputs, consistent with the source offset and displayed terms; zero is a trivial solution omitted by the entry. `source_generating_function` uses the literal numerator and factored denominator. The general conjecture in COMMENTS for all nonsquare parameters is not claimed.

Searches were performed on November 27, 2026. Repository search can miss unindexed or differently phrased work; empty results are screening evidence rather than a priority guarantee.
