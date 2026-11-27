# Source and prior-work checks for A289629

Checked November 26, 2026 (America/Chicago).

## Exact statement

The official source is [OEIS A289629](https://oeis.org/A289629), with a
nine-pattern conjectural comment by Kevin P. Thompson dated December 3,
2021. The formal source uses exactly its expression
`(k+1)^n + (-k)^n` over the integers. The comment explicitly allows
the proposed value of `k` to exceed the sequence's least eligible value;
the package makes no minimality claim.

Primary exports were fetched from the official
[oeis/oeisdata repository](https://github.com/oeis/oeisdata):

| Local snapshot | Revision | Git blob |
|---|---|---|
| `source.seq` (A289629) | 60, January 10, 2022 | `2ae9d036f085a860821591b3eb7560aba74a8c14` |
| `prior_A349989.seq` | 30, February 24, 2022 | `fb8420e91b0a7125fb6e808442dd6d76009286da` |
| `background_A280547.seq` | 56, December 7, 2021 | `b15d3a68b2528ce29c7e9334dd7b03852ee9bb39` |
| `background_A289985.seq` | 25, December 7, 2021 | `ecdd6a6b82ac4ea2728f6eb3c925769f68781469` |

The direct OEIS search result independently displayed the same
nine-pattern conjectural statement. Its last-modified footer and crawl
date are not used as the source revision; the preserved export's
revision line is authoritative for the exact text retained here.

## Already established branches

[A349989](https://oeis.org/A349989), authored by Jon E. Schoenfield on
December 7, 2021, states:

- For exponents congruent to 2 modulo 4, `3^n+4^n` is divisible by 25.
  This covers A289629 branches 2 and 3, since both exponent formulas
  have this congruence and their exponents are even.
- For exponents congruent to 8 modulo 16, `19^n+20^n` is divisible by
  `17^2`. This covers branch 7.
- For exponents congruent to 4 modulo 8, `113^n+114^n` is divisible by
  `17^2`. This covers branch 9.

These four branches are credited and excluded from counts of newly
resolved family assertions. The package supplies complete Lean proofs
of them as part of the full classification.

[A280547](https://oeis.org/A280547) concerns differences of consecutive
powers. It provides finite values, a conjecture about the first 100
minimal values, and Robert Israel's February 8, 2017 Hensel-lemma
argument showing every term exists. That general existence result is
prior work. The present package does not claim it, or prove the finite
minimality conjecture.

[A289985](https://oeis.org/A289985) reverses the roles of exponent and
base. Robert Israel's September 4, 2017 comment records propagation
when the base changes by a multiple of a known square divisor. This
is related established arithmetic. The present proof uses the elementary
odd-power factorization to propagate in the exponent.

The Lucas primality criterion and modular exponentiation implementation
are mathlib results. In particular, the proof imports
[`Mathlib/NumberTheory/LucasPrimality.lean`](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/LucasPrimality.lean),
authored by Bolton Bailey, and constructs explicit certificates for the
two largest primes needed in the counterexample.

## Search record and bounded conclusion

Both available web search engines were used. Queries included:

- `"A289629"`
- `"A289629" proof conjecture`
- `"A289629" proof OR Lean OR solved OR counterexample`
- `"A289629" "15m"`
- `"A289629" "22m"`
- `"8^30" "7^30" squarefree`

Results were dominated by the official entries and sequence mirrors.
The official linked entries were then read in full through their exact
exports. No earlier exact proof of branches 1, 4, 6, or 8, and no earlier
refutation of branch 5, was located in these bounded checks. An unchanged
conjecture label is not by itself evidence of novelty, as the four
already established branches demonstrate.

The mathematical conclusions are unconditional. Historical priority is
not certified. The package resolves the nine literal branch assertions,
credits four previously established cases, and contributes four further
family proofs and the squarefree counterexample relative to the checked
sources. The valid odd-parameter correction is a corollary and is not
counted as an additional recorded conjecture.
