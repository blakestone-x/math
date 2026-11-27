# Source checks: A294532–A294565

Checked November 26, 2026.

## Primary definitions

The coefficient table was checked against all 34 individual OEIS title equations in the official [oeis/oeisdata](https://github.com/oeis/oeisdata) export. Its `time.txt` reported `2026-11-26T03:00:21-05:00`. The published [source_manifest.json](source_manifest.json) records each identifier, source URL, OEIS revision, downloaded file SHA-256, and shifted coefficients; [family.csv](family.csv) provides the compact parameter table.

The equation used in the proof is

$$
a_{n+2}=a_{n+1}+a_n+p b_{n+1}+q b_n+r n+s.
$$

Every source title was independently checked against that shift. The individual A294565 entry has constant `-2`, while the A294532 guide has `-3`. Both equations are proved, with distinct parameter names; only the 34 distinct OEIS identifiers are counted. The A294532 Mathematica snippet uses seeds `1,3;2`, inconsistent with its title and data `1,2;3`; the proof follows the title and data throughout.

Primary public pages:

- [A294532 family guide](https://oeis.org/A294532)
- [A294565 individual definition](https://oeis.org/A294565)
- [Official export format and provenance](https://github.com/oeis/oeisdata)

## Related published theorem

Clark Kimberling and Peter J. C. Moses, [*Linear Complementary Equations and Systems*](https://www.fq.math.ca/Papers1/57-5/kimberling-moses.pdf), *The Fibonacci Quarterly* 57(5) (2019), 96–110, discusses the family and cites A294532 as a guide. Theorem 2.1's hypothesis (ii) assumes existence of the ratio limit. Its conclusion identifies that limit from the characteristic equation. Our proof derives convergence itself from complementarity and the recurrence, and does not treat the earlier conditional identification as a new result.

## Search scope

The review included exact identifiers, semantic searches for complementary Fibonacci recurrences and golden-ratio convergence, the related 2007 and 2019 Kimberling literature, and targeted searches of public OEIS proof collections. Those searches did not locate an earlier complete proof of the convergence assertions treated here. The mathematical arguments are elementary, and this limited search does not establish global priority. Neither the GitHub publication nor Lean verification is evidence of OEIS editorial acceptance.

## Formal boundary

The theorem applies to every pair satisfying the stated seed values, increasing disjoint positive cover, and selected equation. It assumes no growth or convergence theorem. Existence and uniqueness of the defining complementary pairs are not separately formalized. The package is a proof of the ratio-limit property of all such solutions.

## Follow-up source update

Subsequent searches located related public notes. The [prior-work addendum](PRIOR_WORK_ADDENDUM.md) records the new references and their precise relevance. It supplements the bounded initial search above without changing the formal proof or its scope.
