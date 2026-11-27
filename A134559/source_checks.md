# Source and prior-resolution checks

Checked November 27, 2026. This note records a bounded search for an earlier resolution of the exact A134559 antidiagonal-product characterization.

## Primary definitions

The official OEIS repository `oeis/oeisdata` was read through GitHub, and the retrieved files are preserved here:

| File | Source revision | Git blob SHA |
|---|---|---|
| `A134559.seq` | revision 16, September 20, 2025, 22:31:17 | `9fe84e9da323640fbc680e61a849c5832ac95081` |
| `A005383.seq` | revision 143, August 4, 2026, 16:41:43 | `94936a69e21b3ffce3078c30e9e2011996b66a75` |

Primary URLs:

- https://oeis.org/A134559
- https://github.com/oeis/oeisdata/blob/main/seq/A134/A134559.seq
- https://oeis.org/A005383
- https://github.com/oeis/oeisdata/blob/main/seq/A005/A005383.seq

The live A134559 page was also opened. It agrees with the official snapshot on the exact original remainder-fiber definition, product endpoint, two gcd conditions, excluded values 3 and 5, and A005383 prime-pair target. The conjecture is attributed to Lechoslaw Ratajczak on November 1, 2019. A005383's defining prime-pair property is explicit in its official source. No proof or counterexample link was present in the checked A134559 snapshot.

## Search-engine checks

Both available engines were used. Representative exact queries included:

- `"A134559" ("proof" OR "counterexample" OR "conjecture")`
- `"A134559" conjecture counterexample`
- `"54217" "134559"`
- `"Ratajczak" "antidiagonal" "conjecture"`
- `"54217" "Ratajczak"`
- `"A134559" "refuted"`
- `"A134559" "proved"`

The relevant hits were the OEIS statement and its mirrors; no earlier resolution of this exact characterization was located. Unrelated legal case numbers and the Papadimitriou–Ratajczak graph-drawing conjecture were rejected as irrelevant.

## trureturing

The live https://www.trureturing.org/conjectures index showed 2,235 resolved results when opened. Searches of the retrieved index text for `A134559` and `A005383` returned no match. Searches for `Ratajczak` and `antidiagonal` returned other statements, including an A110491 determinant conjecture and several grid-counting recurrences, but no matching product/gcd characterization.

This checks the public index, not undisclosed work or every unindexed source. An unchanged OEIS conjecture label does not itself prove that a question remains unresolved elsewhere.

## Discovery and proof boundary

A divisor-sum scan found the explicit factor at p = 54217, k = 2737. Its exploratory implementation is in the working research folder, not part of the trusted proof. `verify.py` independently recomputes the original remainder-fiber sum. `Proof.lean` certifies the original finite fiber, its exact sum, both primality claims, divisibility of the original product, the resulting gcd, and the refutation. No minimality or classification claim is made.
