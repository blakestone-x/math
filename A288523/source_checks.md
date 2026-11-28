# Source and prior-publication checks: A288523

Checked November 27, 2026. These checks concern the exact length assertion for the replacement $00\to0101,10\to010$, starting at $00$.

## Exact primary sources

Both complete exports were retrieved from the official `oeis/oeisdata` GitHub repository. The saved bytes were checked with Git's blob hash formula, SHA-1 of `blob <length>\0<contents>`.

| Preserved file | Revision | Git blob SHA-1 |
|---|---|---|
| `sources/A288523.seq` | 11, April 7, 2020, 21:37:35 | `b7eb9058918bc0c3420f45e3a0949ca056178fd1` |
| `sources/A288520.seq` | 14, April 6, 2020, 20:04:12 | `b05de0c91d728128265de06fa29c1ff6296a5979` |

Primary links: [A288523](https://oeis.org/A288523), [A288520](https://oeis.org/A288520), [official A288523 source](https://github.com/oeis/oeisdata/blob/main/seq/A288/A288523.seq), [official A288520 source](https://github.com/oeis/oeisdata/blob/main/seq/A288/A288520.seq).

The live indexed entry texts were also read. Both retain the same length assertion as a conjecture. The source program explicitly uses `StringReplace` with the ordered rules `00 -> 0101` and `10 -> 010`. The formal scanner consumes only the remaining original input, uses nonoverlapping matches, and copies an unmatched letter. It starts with the literal two-bit word `00`.

A288523 defines the order-four recurrence only for indices at least 5 and supplies five initial values, including the exceptional zeroth word. All five values and the precise recurrence domain are retained. The formal result is equality at every natural index with an independent integer recurrence. The shared assertion in A288520 and A288523 is counted once.

## Current project check

The project README was read at `blakestone-x/math` commit `1caf7bf77a45eef986d0246a1762f5a03c0d0d86`. Neither target ID appears there. The earlier `Morphic-discrepancy` README was read in full: its six position sequences are A284894/A284895, A284902/A284903, and A285669/A285670, with different substitutions. The earlier `Kimberling-pair-rules` and A288668 packages likewise concern different literal replacement rules. This does not preclude a future concurrent addition; publication must recheck the latest branch.

## Both search engines

Exact and semantic queries included:

- `"A288523" proof trureturing`
- `"A288523" (proof OR proved OR conjecture)`
- `"A288520" (proof OR proved OR conjecture)`
- `"00" "0101" "10" "010" "Kimberling" proof`
- `site:trureturing.org "replacement" "length" Kimberling`

Relevant exact-ID results reproduced the OEIS statement and sequence mirrors. Unrelated license numbers, vehicle-service documents, and election lists were excluded. No earlier proof of the exact target was located.

## Public resolved-results index

The live [trureturing index](https://www.trureturing.org/conjectures), displaying 2,235 resolved results, was opened and searched for both A288523 and A288520; neither appeared in the retrieved text. Semantic searching did find [the A288476 replacement-length report](https://www.trureturing.org/research/oeis-a288476-replacement-iterate-length/), whose full text was read. That proof uses the different rule $00\to0101,1\to011$ and an order-three recurrence. Its statement expressly excludes other replacement rules. It is credited as a nearby example of the standard recoding method, not claimed as part of the present contribution.

Index absence alone is not a proof that no earlier result exists. Exact searches and review of the actual definitions were also performed for that reason.

## Nearby primary paper

Lubomíra Dvořáková, Edita Pelantová, and Jeffrey Shallit, [*On a sequence of Kimberling and its relationship to the Tribonacci word*](https://arxiv.org/abs/2510.11318), arXiv:2510.11318v5, revised March 20, 2026; Discrete Mathematics & Theoretical Computer Science **28:2**, article 19 (2026), [doi:10.46298/dmtcs.16926](https://doi.org/10.46298/dmtcs.16926).

The complete 14-page primary [PDF](https://arxiv.org/pdf/2510.11318) was retrieved. Its introduction and length proof use A288462, the replacements $00\to0101,1\to10$, and the related A288465 recurrence. Its first lengths are $2,4,6,10$, distinct from this target's $2,4,5,8$. Searches of the full retrieved text found neither A288523 nor A288520. The paper's token-boundary and substitution methods are relevant prior art; the exact source sequence and recurrence proved here are different.

## Supported scope

The deliverable establishes one recorded all-index length assertion, together with the explicit alternating-boundary coding and a stronger affine recurrence. It does not claim a new general theory of substitutions, a proof of the adjacent position/frequency assertions, an infinite-word construction, OEIS editorial acceptance, or exhaustive historical priority.
