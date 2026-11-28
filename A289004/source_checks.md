# Sources and prior-work checks

Checked on **2026-11-27**. This record separates the source statements, the
literal formalization, known related results, and the limits of the search.

## Exact primary snapshots

The six `sources/*.seq` files were retrieved from the official
[`oeis/oeisdata`](https://github.com/oeis/oeisdata) repository. Their bytes were
preserved exactly, including the final newline; their Git blob hashes were
recomputed locally and matched the returned official metadata.

| Entry | Source revision and date | Official Git blob SHA-1 |
| --- | --- | --- |
| A289001 | #37, 2022-03-09 | `6f944cdb050a6b7d5f4177e51d930a0a7b8ab567` |
| A289004 | #15, 2020-04-07 | `6f5f23da2ff5a9e1c5f1a93658ff14a4f28b81ba` |
| A289035 | #21, 2022-03-22 | `eb669752b0c3adaf6f2efcc02427ff5fea938a80` |
| A289037 | #13, 2022-03-22 | `0ffbc6fe8245432a4da043d40052947ce7e42388` |
| A289239 | #7, 2020-04-07 | `e2f4db2f1a8934180c28657ea538a6bc3c02a428` |
| A293077 | #26, 2022-03-23 | `8655774d9d9d19d2fbc387e90063ce9ae811bf26` |

The original descriptions and programs are accessible at
[A289001](https://oeis.org/A289001), [A289004](https://oeis.org/A289004),
[A289035](https://oeis.org/A289035), [A289239](https://oeis.org/A289239),
[A289037](https://oeis.org/A289037), and [A293077](https://oeis.org/A293077).
The package manifest records SHA-256 hashes of all preserved files as well.

## Statement and scanner bridge

The three source words share `00 -> 0010`, `10 -> 010`, and seed `00`.
Their respective `01` images are `001`, `010`, and `100`. Each program uses
nonoverlapping `StringReplace`. A289035 explicitly says that an odd final
letter is retained and gives `0010010 -> 00100100100` as an example.

`rewrite` in `Scanner.lean` implements all matched pairs, the unmatched-leading-letter
branch for `11`, and the retained singleton. `word_good` proves from the seed
that the unmatched `11` branch is absent along the actual source orbit and
that every final letter is zero. `word_counts` proves equality between the
actual list lengths/counts and the arithmetic state at every index. There is
no recurrence assumption on the original words.

A289004's prose accidentally assigns 151 and 257 both to index 9. The term
list and `LinearRecurrence` program resolve the intended indexing: 151 is at
index 8 and 257 at index 9. The formal `reference` uses this intended
independent recurrence, not the actual scanner counts. The first disagreement
is at index 22. The repeated length assertion in A289004/A289001 is one
assertion; A289035 and A289239 state two further instances for distinct rules.

## Known prior mathematical results

Michel Dekking and Michael Keane,
[*Two-block substitutions and morphic words*](https://arxiv.org/abs/2202.13548),
arXiv:2202.13548v2 (2023-02-20), Theorem 4, proves that the A289001 infinite
fixed word is the Pell word. The complete four-page primary paper was read.
It does not establish the retained-singleton A289004 length recurrence. The
Pell-word identification and its position consequences are explicitly known
and are not claimed anew here.

Dekking's March 2022 comment in A293077 proves a count/floor recurrence for a
different iteration convention: remove the final letter whenever the new
word has odd length. A289037 records a related density argument and extends
it to several two-block maps. Those observations are relevant prior counting
ideas. Our package independently proves exact retained-singleton dynamics
and convergence; it does not count the familiar density constant as a new
conjecture resolution. A293077's lengths are already different at iteration
2 (6 versus the retained length 7).

## Web searches with both engines

Exact-ID and semantic queries included:

- `"A289004" proof`
- `"A289004" (false OR counterexample OR refuted OR recurrence)`
- `"A289004" "268184"`
- `"A289004" "268182"`
- `"A289004" conjecture false length`
- `"A289239" proof`
- `"A289035" "length"`
- `"Pell" "two-block" "length" recurrence`
- `"0010" "001" "010" "lengths" "recurrence" Kimberling`
- `"Pell word" "length" "algebraic integer"`
- `site:github.com/VladimirReshetnikov/ProveIt "A289004"`
- `site:github.com "A289004" "268184"`
- `site:github.com "A289001" proof`
- `site:github.com/VladimirReshetnikov/ProveIt ("A289035" OR "A289239")`

The exact relevant matches reproduced the source conjectures, the known
Pell-word paper, the different A293077 iteration, and scalar recurrence
implementations. Sequence Machine's A289004 page reports finite numerical
matches (some through 19 terms); these do not establish equality with the
literal source lengths. Unrelated identifier collisions and different
Kimberling/Tribonacci and hiccup-sequence papers were distinguished from this
specific rule and iteration convention.

## Current trureturing catalogue and semantic overlap

The [current catalogue](https://www.trureturing.org/conjectures) displayed
2,235 resolved results, with 1,477 proved and 758 refuted, when opened.
Finds for A289004, A289001, A289035, and A289239 returned no matching text.
Semantic finds for Pell, Kimberling, two-block, StringReplace, word length,
and substitution were also inspected.

The relevant-looking
[Kimberling replacement-iterate report](https://www.trureturing.org/research/oeis-a288476-replacement-iterate-length/)
concerns A288476 and the rule `00 -> 0101`, `1 -> 011`. It is a different
source assertion. The catalogue also contains a Thue–Morse two-block
frequency result; its substitution differs from all three rules here.
An absent ID alone was not treated as evidence of novelty.

## GitHub code searches, including ProveIt

Because OEIS and web indexing can lag independent reports, the screen also
used current GitHub code search. Separate queries for **each** of A289004,
A289001, A289035, and A289239 restricted to
[`VladimirReshetnikov/ProveIt`](https://github.com/VladimirReshetnikov/ProveIt)
returned no results. Two initially throttled requests were retried
successfully; an error response was not counted as a negative result.

Additional global or repository-restricted queries included:

- `A289004` globally;
- `"268184" "268182"` globally;
- `"268184" "recurrence"` globally;
- `"A289035" "length"` and `"A289239" "length"` globally;
- `"00->0010" "01->001"`, `"00->0010" "01->010"`, and
  `"00->0010" "01->100"` globally;
- `"0010" "001" "010" retained` within ProveIt;
- `"Pell" "length" "recurrence"` within ProveIt.

Global matches were OEIS source mirrors, joeis/LODA programs for the defined
scalar recurrence or fixed words, and incidental data/hexadecimal strings.
The ProveIt semantic matches inspected in the returned excerpts concerned
Hilbert-tenth Pell arithmetic, tag-system encodings, and unrelated benchmark
logs. No matching earlier length refutation was identified. Queries returned
at most 8–20 results; these are bounded indexed searches, not a complete
download or exhaustive analysis of every public repository.

The existing `blakestone-x/math` checkout at
`2422f82913949a4f4a4db7c7616b09c43546aea7` was also searched for the four IDs and
the relevant rule/Pell terms. Earlier results for A288523, A288665/A288668,
the other pair-rule families, and A289128–A289131 are distinct and are not
recounted here.

## Conclusion and limits

The formal result refutes the three stated mapping instances of the A289004
length conjecture, with A289004/A289001 counted once. Its strengthened
conclusion excludes every eventual **monic integer** recurrence, with the
literal source words in the theorem statement. It does not assert an
obstruction for arbitrary rational or real coefficients, and it does not
claim to solve a new infinite-word or position-density conjecture.

No matching earlier refutation was found in the checks recorded above. An
unindexed, differently phrased, or unpublished predecessor may exist. This
record supports a transparent bounded search, not unconditional priority or
OEIS editorial acceptance.
