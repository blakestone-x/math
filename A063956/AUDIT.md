# Independent proof review

Reviewed November 26, 2026.

## Source fidelity

The official [A063956 internal entry](https://oeis.org/A063956/internal), revision 30 dated April 18, 2026, was independently opened. Its selected conjecture is the product identity for all positive `n,m`. Its prime-power description and worked example explicitly identify unitary prime divisors with prime factors of exponent one. The Lean definition `a n := n.factorization.sum score` with `score p e := if e = 1 then p else 0` therefore defines the same arithmetic function.

A subsequent live retrieval of the [official OEIS export](https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A063/A063956.seq) found revision 32, dated October 18, 2026. It retains the same conjecture, definitions, and attribution; the changes visible relative to the retrieved earlier entry are cosmetic program separators. The source snapshot has SHA256 `b70cc4cbfea9b19312c3c6332aafdea0e3729e208aa73482c765c43d2c4bcc48`.

## Mathematical and formal review

The whole source was independently read and recompiled using the pinned Lean 4.19.0/Mathlib environment. Compilation exited successfully. The final theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

The pointwise exponent identity covers arbitrary nonnegative exponents. Every finite sum is legitimately enlarged to the union of the two original supports, because `score p 0 = 0`. The product, power, and gcd identities are applied with the required nonzero hypotheses. The additive balance theorem implies the displayed subtraction formula over natural numbers, including cases where either gcd correction vanishes.

No unproved hypothesis equivalent to the target claim, finite truncation, circular definition, placeholder, additional axiom, or mismatch of sequence definitions was found. The proof establishes the full identity for every pair of positive integers.

The source-status search is documented in `README.md`. The mathematical audit verifies the theorem and the source match; it does not establish absolute historical priority.
