# Independent audit: A134559

**Result: PASS.** A separate agent from the author read the complete proof, both preserved primary-source records, `README.md`, and `source_checks.md`, independently recomputed the witness, and built a fresh isolated copy of the exact package on November 27, 2026.

Audited `Proof.lean` SHA-256:

```text
1e32288a22699e12b30a57b93687682778d96f750a3b1cf4d4aa52efc53745d9
```

## Original statement and scope

The source's November 1, 2019 comment defines the sum over **all** integers `1 ≤ u ≤ n` with remainder `n % u = k`. The formal `remainderSum` uses exactly this finite interval and predicate. The product uses `range ((n + 1) / 2)`, which is precisely the natural-number version of `0 ≤ k < ceiling(n/2)`. Both gcd conditions and the positive-integer domain are preserved.

The A005383 source defines primes `p` with `(p + 1) / 2` prime. Excluding its first two values 3 and 5 agrees with the formal `primePair` predicate at the witness and with the source's specified family. The formal conclusion negates the proposed equivalence over all positive integers. It correctly needs only one member of that prime family which fails one of the two gcd conditions.

## Mathematical and formal checks

- Independently checked primality of 54217 and 27109 by trial division through 232 and 164 respectively. The Lean theorem separately proves these facts with proof-producing `norm_num`.
- Independently enumerated the original remainder fiber over every `u` from 1 to 54217. It consists of exactly the 14 displayed numbers, with sum 162651 = 3 × 54217.
- Checked that `witness_fiber` proves both inclusions. The forward direction derives `2737 < u`, bounds the quotient, and exhausts the quotient cases using `54217 = 2737 + u * (54217 / u)`. The proof's deliberately loose bound of 19 is sufficient; the README's sharper bound of 18 follows from `u * q = 51480` and `u ≥ 2738`. There is no unproved fiber-completeness assumption.
- Checked `2737 < 27109`, so the divisible remainder sum is an actual factor of the original product.
- Checked the divisibility-to-gcd step: if `54217` divides that product, its gcd with 54217 is exactly 54217. Since 54217 > 1, the first required gcd equation fails, independently of the second one.
- Inspected all declarations for admissions, additional axioms, `unsafe` code, and native evaluation shortcuts. None occur. The finite sum uses ordinary `decide`.

## Independent compilation

A new temporary package was populated from the audited source and pinned configuration. The cached mathlib dependencies were reused, but no proof object for `Proof.lean` was copied. A fresh `lake build` completed successfully with Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All four printed main-theorem dependency lists contain only `propext`, `Classical.choice`, and `Quot.sound`. The full output is in `audit-verification.txt`.

## Provenance and presentation

Fresh reads from the official `oeis/oeisdata` repository agree byte-for-byte, through Git blob hashes, with both preserved source snapshots. The conjecture remains present in the checked A134559 revision. Independent searches with both search engines did not locate an earlier resolution, and searches of the live trureturing index found neither A134559 nor A005383. This remains a bounded prior-publication check, as the package explicitly states.

The proof, prose, and source attribution agree. The package claims one counterexample resolving one recorded characterization; it does not claim minimality, a classification of counterexamples, or the converse implication. No mathematical or scope correction was required during this audit.
