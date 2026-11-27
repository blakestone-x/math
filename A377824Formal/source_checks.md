# Source and prior-work checks for A377824Formal

Initial checks: November 26, 2026, America/Chicago.

## Final-publication addendum — November 26, 2026 (America/Chicago)

The final repository check found a concurrent solution already present
in `blakestone-x/math` at commit
`c92ab48c98acba51cb42ceb73536a7bad251ec2d`. Its
[A377824 README](https://github.com/blakestone-x/math/blob/c92ab48c98acba51cb42ceb73536a7bad251ec2d/A377824/README.md)
and [minimum-positions.tex](https://github.com/blakestone-x/math/blob/c92ab48c98acba51cb42ceb73536a7bad251ec2d/A377824/minimum-positions.tex)
give the same exact main term $(n+1)(n+6)2^n/32$ and the stronger
error $O(n^2\varphi^n)$, with $\varphi=(1+\sqrt5)/2$.
That proof uses the minimum-one generating function and bounds the
remaining compositions by Fibonacci numbers.

The Lean development here was independently completed during the same
work period. Because the manuscript was already in the repository at
the final publication check, this package is named **A377824Formal**
and is a **formal companion, with zero additional conjecture resolutions
counted in Batch 7**. Its formal result includes the explicit
$(7/4)^n$ error bound, rather than a formal proof of the manuscript's
stronger $\varphi^n$ rate.

Both files were fetched at the pinned commit on November 27, 2026,
at 06:09 UTC, and saved as exact decoded bytes. Their Git blob SHA-1
identifiers were independently recomputed from the saved bytes and
matched the connector's returned identifiers:

| Snapshot | Original path at the pinned commit | Git blob SHA-1 |
|---|---|---|
| [prior_repo_README.md](sources/prior_repo_README.md) | `A377824/README.md` | `e661960566742279504735ef35a78a2b29ace915` |
| [prior_repo_minimum-positions.tex](sources/prior_repo_minimum-positions.tex) | `A377824/minimum-positions.tex` | `8a145f85d4ef3470324ff32faf5df30fdf3eb8bf` |

The corresponding SHA-256 hashes are:

```text
acb51eb5025f27e8d9f5fc9f348acbd0cab34269b50412c856afb936de023978  sources/prior_repo_README.md
236c2b8f23eb9bfd23436a8d7bff355986ecd0fdfd69331556c8b473fb478585  sources/prior_repo_minimum-positions.tex
```

The earlier search record below is retained as a dated account of the
initial checks. This addendum supersedes its initial repository-overlap
and contribution assessment. The proof source, pinned build files,
OEIS export, and original build/audit logs remain byte-for-byte unchanged.

## Exact target

- Primary entry: https://oeis.org/A377824
- Official export mirror: https://github.com/oeis/oeisdata/blob/main/seq/A377/A377824.seq
- Preserved export: `source.seq`, revision 28, April 19, 2025, 08:48:50.
- Retrieved Git blob: `78dbd80ba8e77258febf2dcec2bbd14bfbef0cd7`.
- Entry author: John Tyler Rascoe, November 8, 2024.
- Conjecture author: Václav Kotěšovec, April 19, 2025.

The name defines a(n) as the sum of positions of minimum parts over all
compositions of n. The example (1,2,1,1,2) contributes 1+3+4=8, fixing
both one-based positions and the requirement to include every minimum.
The selected assertion is a(n) ~ n²·2^(n−5). It remained labeled
conjectural in the retrieved export. This label alone is not evidence
of historical novelty.

The proof follows the literal composition statistic. It does not assume
the entry's multivariate generating-function expression or its programs.
The implementation establishes that its recursively generated list
contains every positive-part composition exactly once and that its
weight is the sum of the one-based minimum positions.

## Closely related primary literature

Arnold Knopfmacher and Augustine O. Munagi, **Smallest Parts in
Compositions**, in *Advances in Combinatorics*, Springer (2013), pp. 197–207.
DOI: https://doi.org/10.1007/978-3-642-30979-3_11

A contributor-hosted uncorrected proof of the volume was inspected:
https://sites.math.rutgers.edu/~zeilberg/akherim/Wilf80.pdf
The chapter occupies PDF pages 232–242 (one-based page numbering).

The chapter studies the number of minimum parts, the sum of their
values, their refinement by composition length, and the position of the
first minimum. Sections 3.2–3.3 give asymptotics for the number/sum
statistics; Section 4 treats the first position and its geometric
limiting distribution. The asymptotic for the sum of all minimum
positions is not stated there. Refined counts in the chapter imply
related positional identities by symmetry. The minimum-one versus
larger-minimum decomposition is therefore credited as established
mathematics, as are the standard composition and Fibonacci counts.

The present proof independently derives the necessary recurrences,
the exact ones-position main term (n+1)(n+6)·2^n/32, and a fully explicit
error bound directly from the composition enumeration.

## Initial repository overlap check

The then-current `blakestone-x/math` README was checked, including the
concurrent additions recorded in commit
`cb11073d1c4c31f880d2ab5396ca07ffad07e855`.
A377824 was absent. The existing A238342 package was read in full.
It concerns compositions with a fixed minimum multiplicity k and
their φ^n-scale asymptotic. It does not state or prove the A377824
sum-of-positions asymptotic.

## Bounded external search

Both available search engines were used for exact identifier searches
and semantic searches, including:

- `A377824 proof asymptotic theorem`
- `"sum of the positions of minimum parts" compositions`
- `"positions of minimum" compositions asymptotic`
- `"A377824" "Lean"`
- `site:trureturing.org "A377824"`
- `"A377824" "Low-Hanging"`
- `Knopfmacher Munagi "Smallest Parts in Compositions" pdf`

The live trureturing resolved-conjecture index was also opened and
searched for `A377824`, `minimum parts`, and `smallest parts`; none
matched in the retrieved page:
https://www.trureturing.org/conjectures.html?lang=en

These checks found the OEIS target and the related Knopfmacher–Munagi
chapter, but no earlier exact resolution of the selected conjecture.
As a calibration of the search, other prospective targets A386829,
A394578, and A380392 were rejected after prior formal resolutions were
found in that public collection.

This is a bounded prior-work record, not an exhaustive priority claim.
The package formally proves one recorded assertion, but the final
repository check documented above means that it contributes no additional
conjecture resolution to Batch 7. The polynomial correction terms and
explicit error estimate are not counted separately. No OEIS submission
or editorial acceptance is claimed.
