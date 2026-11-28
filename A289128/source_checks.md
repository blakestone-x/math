# Source and prior-publication checks: A289128–A289131

Checked November 27, 2026. The target is the literal left-to-right nonoverlapping rule `00 → 0010`, `01 → 011`, `10 → 010`, starting with `00`. The package proves one shared length assertion and refutes the two proposed position limits by proving nonconvergence of both actual infinite position ratios.

## Exact primary snapshots

The complete exports were retrieved from the official `oeis/oeisdata` repository using its file API. Saved bytes were verified with Git's blob hash formula, SHA-1 of `blob <byte-length>\0<contents>`. All four calculated hashes match the official response hashes.

| Saved file | Export revision and timestamp | Official Git blob SHA-1 |
| --- | --- | --- |
| `sources/A289128.seq` | 7; April 7, 2020, 21:27:49 | `9d7d17a994348a375461510c9f7d98502c8e6137` |
| `sources/A289129.seq` | 4; June 28, 2017, 22:26:15 | `9bf9dc96712ee5d5e7ae27d18c24565f70bc69c9` |
| `sources/A289130.seq` | 6; June 28, 2017, 22:26:24 | `e0fb2b25700ab3f7cdf10aae04289285aaad9b91` |
| `sources/A289131.seq` | 19; April 7, 2020, 21:28:35 | `64fb3d4aefee15f68b0ca5ac63386d220216b59f` |

Primary entry links: [A289128](https://oeis.org/A289128), [A289129](https://oeis.org/A289129), [A289130](https://oeis.org/A289130), [A289131](https://oeis.org/A289131).

Official export links: [word definition](https://github.com/oeis/oeisdata/blob/main/seq/A289/A289128.seq), [zero positions](https://github.com/oeis/oeisdata/blob/main/seq/A289/A289129.seq), [one positions](https://github.com/oeis/oeisdata/blob/main/seq/A289/A289130.seq), [length recurrence](https://github.com/oeis/oeisdata/blob/main/seq/A289/A289131.seq).

The source programs all use the same three `StringReplace` rules. The word starts at iterate zero with `00`; the supplied first six words agree with the formal scanner. When there is no matching pair, the scanner copies one input letter. It never scans newly emitted output during the same pass.

The occurrence sequences have one-based offsets. Their programs compute positions in a finite iterate, while the descriptions refer to the limiting word A289128. The formalization supplies the missing infinite-word construction: every literal iterate is a prefix of the next, each coordinate stabilizes, the limit is unique, both symbols occur infinitely often, and the position maps are the one-based `Nat.nth` enumerations of that limit. The four endpoint subsequences have strictly increasing occurrence ranks, so their real limits concern the full infinite sequences.

A289131 defines the scalar recurrence only for indices at least 6 and supplies all six initial values `2,4,7,11,18,28`. The formal reference sequence retains those initial values, the exceptional zeroth iterate, and the exact recurrence domain. The same length comment in A289128 is the same assertion and is counted once.

Colin Barker's July 2, 2017 contribution already gives the scalar generating function and parity formulas in A289131. These formulas are prior work and are credited explicitly. The new bridge proves that the original replacement iterates have these lengths. The nonconvergence proof additionally obtains exact symbol counts and actual infinite occurrence positions.

## Existing repository

The project index and nearby packages were checked at `blakestone-x/math` commit `f80dd85da504e4d1bf39761cc1de72f9bdb5d30f`. Exact searches for A289128, A289129, A289130, and A289131 found no existing entry. The latest additional result after the earlier `888d3b3` head was the A400939 division-count classification, unrelated to this rule.

The full READMEs of `Kimberling-pair-rules` and `Morphic-discrepancy` were read. The former concerns `00 → 001` with the separate rules `1 → 000` and `1 → 010`, and the position sequences A285667/A286058/A285432/A285564. The latter concerns single-letter substitutions and the six position sequences A284894/A284895, A284902/A284903, A285669/A285670. Their rules and source assertions differ from this package. The recently published A288523 proof uses `00 → 0101`, `10 → 010`, another different rule, and does not establish the present infinite position results.

## Both web-search engines

The source and prior-publication screen used both available engines, including exact-ID queries and semantic queries formed from the actual replacement rule and proposed/refuting limit constants. Queries included:

- `"A289128" "A289131" proof`
- `"A289131" "proof"`
- `"A289128" (proved OR trureturing OR substitution)`
- `"A289129" (proof OR disproved OR limit)`
- `"A289130" (proof OR disproved OR limit)`
- `"A289128" (frequency OR proof OR nonconvergence OR density)`
- `"A289129" ("7/3" OR "5/2" OR disproved)`
- `"A289130" ("7/4" OR "5/3" OR disproved)`
- `"00->0010" "01->011" proof`
- `"0010" "011" "010" Kimberling proof`
- `"Kimberling" "0010" "011" "density"`
- `"0010" "011" "010" "frequency" Kimberling`
- `site:trureturing.org "A289128" OR "A289129" OR "A289130" OR "A289131"`
- `site:trureturing.org "Kimberling" "replacement"`

Exact matches primarily reproduced the OEIS statements. [Sequence Machine](https://sequencedb.net/index.html?p=16&s=lt) lists numerical matches and filtering/complement identities for A289130; these do not supply a proof of convergence or nonconvergence. Unrelated business-license identifiers, engineering encodings, and municipal documents were excluded. No prior proof of the exact literal length assertion or refutation of either exact position limit was located.

## Current trureturing catalogue and semantic overlap

The live [resolved-results catalogue](https://www.trureturing.org/conjectures) was opened; the retrieved page displayed 2,235 resolved results, consisting of 1,477 proved and 758 refuted. Finds for each of A289128, A289129, A289130, and A289131 returned no match. Semantic finds for Kimberling and frequency were inspected.

The semantic match [Kimberling's replacement-iterate length conjecture](https://www.trureturing.org/research/oeis-a288476-replacement-iterate-length/) was opened and read in full. It proves the A288476 order-three length recurrence for `00 → 0101`, `1 → 011`, starting at `00`. Its repeated claims in A288473 and A288551 are the same event. The report explicitly places position limits, frequency, infinite-word existence, and other replacement rules outside its scope. That recoding proof is relevant standard methodology; it is a different source assertion.

A nearby primary OEIS match, [A288936](https://oeis.org/A288936), records Michel Dekking's October 16, 2022 proof for `00 → 0010`, `01 → 011`, `10 → 011`. The final image is `011`, whereas the present rule sends `10` to `010`. Dekking obtains linearly growing zero counts and quadratic lengths for his rule. The original programs, worked iterates, and resulting formulas distinguish these two problems.

The absence of an ID from a catalogue alone does not prove novelty. The actual definitions and relevant semantic matches were also checked. These are bounded searches; an unindexed or differently named prior result may exist.

## Supported claims and limitations

The three claimed resolutions are the one length conjecture and the two position-limit assertions. Each limit refutation is strengthened to nonexistence of any real limit, with two distinct subsequential limits established in Lean. The limit constants are not asserted to be a complete classification of all cluster points or exact liminf/limsup values. The accompanying all-index strict inequalities in A289129/A289130 are not supplied with a corrected classification here. No new general theory of substitutions, exhaustive historical priority, or OEIS editorial acceptance is claimed.
