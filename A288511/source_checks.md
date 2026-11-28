# Source and prior-publication checks: A288511

Checked November 27, 2026. The target is the full literal length assertion for the nonoverlapping replacement $00\to0101,10\to001$, with seed $00$ and index starting at zero.

## Primary source and exact statement

The complete source exports in `sources/` were fetched from the official `oeis/oeisdata` repository, then fetched again at immutable commit `571197984aeda7b8b680fe3a1f6a43f9898cd441`. The current and immutable bytes agreed for all three files. The latest file-specific commit returned for A288511 was that commit, dated November 24, 2024.

| Entry | OEIS revision in export | Relevant clause |
|---|---|---|
| A288511 | 9, April 7, 2020, 21:37:10 | Independent order-thirteen recurrence, initial values, and all-iteration length conjecture |
| A288508 | 7, April 7, 2020, 20:49:23 | Literal `StringReplace` implementation and repeated length conjecture |
| A288512 | 11, April 7, 2020, 21:02:25 | Same scanner and repeated length conjecture, in the odd limiting-word entry |

Immutable source links: [A288511](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A288/A288511.seq), [A288508](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A288/A288508.seq), [A288512](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A288/A288512.seq).

The live indexed OEIS entries were also read. They retain the explicit conjecture. The replacement rules are applied to the remaining original input; replacements are not rescanned in the same pass. An unmatched letter is copied, including a final singleton. In particular, an unmatched `01` consumes only its first `0`, leaving its `1` available for the next match. These semantics are exactly the four two-letter branches of the formal `rewrite` definition.

The source recurrence applies at newest indices at least 16. Sixteen initial values, indexed 0 through 15, are specified. The definition `source` repeats exactly these values and that recurrence over the integers. The final theorem asserts equality for every natural index. No infinite limiting-word existence or position hypothesis occurs in the theorem.

### Generating-function indexing

The source's displayed rational expression is $xN(x)/D(x)$ although its offset is zero and its first term is 2. This expression is shifted by one. The recurrence and initial values instead give $N(x)/D(x)$, whose constant coefficient is 2. The package targets the recurrence-defined length assertion; the README documents the indexing correction and does not count it as a second resolution. No Lean theorem about formal power series is claimed.

## Existing project results

The existing packages `Kimberling-pair-rules`, `Morphic-discrepancy`, and Batches 8–11 were screened. Their rules and targets differ. In particular, A288523 uses $10\to010$ instead of $10\to001$; A289128/A289131 also replace `01` and have a different `00` image; and the Batch 11 A289004 refutations concern $00\to0010$ with three choices for the `01` image. None already proves the present literal sequence. Root publication review is responsible for the final current-branch check.

## Both web search engines

Both search systems were used for exact identifiers and semantic variants. Queries included:

- `"A288511" proof`
- `"A288511" Kimberling lengths recurrence proof`
- `"A288508" proof lengths`
- `"A288508" mathematical proof`
- `"A288512" "proof"`
- `"00->0101" "10->001" proof`
- `"00->0101, 10->001" conjecture`
- `site:trureturing.org "288511"`
- `site:trureturing.org "288508"`

The relevant exact-ID results reproduced the conjecture or numerical sequence data. Semantic searches also returned unrelated uses of the two binary strings, the Fibonacci-word morphism, and proofs for other Kimberling substitutions. No proof of this precise source assertion was located.

## Global GitHub and ProveIt

Global GitHub code search was performed for A288511, A288508, and the literal rule string, as well as proof-qualified queries. Relevant hits were:

- [jOEIS A288511](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a288/A288511.java), a recurrence/generating-function implementation;
- [jOEIS A288508](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a288/A288508.java), a sequence implementation of the scanner;
- [jOEIS A288512](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a288/A288512.java), its odd limiting-word companion;
- [LODA A288511](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/288/A288511.asm), a program for the defined numerical sequence;
- OEIS-Spider source mirrors.

These hits do not establish equality of the literal scanner lengths with the independent recurrence. Irrelevant hash substrings and unrelated identifiers were excluded by examining the matches.

Repository-restricted searches in `VladimirReshetnikov/ProveIt` for A288511, A288508, A288512, and `00->0101 10->001` returned no matching proof. This explicitly supplements the web screen; a stale OEIS label was not used as the sole novelty test.

The repository head reported by the GitHub API during the final screen was
[`5e38fc96429f83250cea68d8bdcbbf3e08fcef48`](https://github.com/VladimirReshetnikov/ProveIt/commit/5e38fc96429f83250cea68d8bdcbbf3e08fcef48).
The earlier initial searches exposed indexed result URLs at
`8d6bdcad4c37fda9bcfa11151a191c32ae840b4f`; none was a relevant mathematical
match for this target. Search-index coverage can lag the reported repository
head, so this record does not claim a complete tree-by-tree content audit.

## Current trureturing collection

The [live resolved-results index](https://www.trureturing.org/conjectures), reporting 2,235 results, was opened and searched. Neither A288511 nor A288508 occurred in the retrieved index. Exact site searches and semantic replacement-length searches were also performed.

The nearby [A288476 report](https://www.trureturing.org/research/oeis-a288476-replacement-iterate-length/) is a genuine prior proof for the different rule $00\to0101,1\to011$. Its full source statement and length recurrence were compared with this target. It proves an order-three recurrence and expressly leaves other replacement rules outside its scope. The related public knowledge node is named `D5/S1/Words/KimberlingA288476Length`.

The final screen additionally searched the public source repository
`the-omega-institute/trureturing` for A288511, A288508, and the literal pair
of rule strings `00->0101 10->001`. Each query returned no relevant hit.
The GitHub API reported head
[`3eb6613180291b2da0159ffc0d8f43ce01dc709f`](https://github.com/the-omega-institute/trureturing/commit/3eb6613180291b2da0159ffc0d8f43ce01dc709f)
at this check. As with ProveIt, this pins the observed repository state but
does not guarantee that its entire head was indexed by code search.

## Related primary paper

Lubomíra Dvořáková, Edita Pelantová, and Jeffrey Shallit, [*On a sequence of Kimberling and its relationship to the Tribonacci word*](https://dmtcs.episciences.org/articles/17782), Discrete Mathematics & Theoretical Computer Science 28:2 (2026), [doi:10.46298/dmtcs.16926](https://doi.org/10.46298/dmtcs.16926), published March 23, 2026.

The paper's length proof concerns A288462/A288465, whose rule includes $1\to10$ and whose first four lengths are $2,4,6,10$. It is different from this target's rule and prefix $2,4,5,7$. Its use of finite recoding is relevant prior art and is credited. We make no claim that finite recoding or substitution matrices are new methods.

## Supported conclusion

This is one complete source assertion, repeated in three entries. The proof establishes every literal length and an explicit boundary-state description. The bounded searches did not locate an earlier proof of this exact assertion. That finding does not prove worldwide priority, rule out unindexed aliases, establish the neighboring position/frequency conjectures, or imply acceptance of an OEIS edit. No OEIS edit or announcement was sent.
