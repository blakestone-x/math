# Independent audit of A300984

The complete final `Proof.lean`, README, source-check record, and four included primary OEIS snapshots were read. The exact packaged Lean source was copied to an isolated audit directory and compiled afresh with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Compilation returned exit code 0. The fresh output directory was placed first on `LEAN_PATH`, and no precompiled theorem module from this package was used.

The command, complete output, compiler version, and final source hash are recorded in [audit-verification.txt](audit-verification.txt). All five printed theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Original definition and quantification

The primary [A300984 snapshot](source.seq) defines positive integers for which the sum of squarefree positive divisors and the sum of nonsquarefree positive divisors are both squarefree. The definitions `squarefreeSum` and `nonsquarefreeSum` use `Nat.divisors` directly, with the standard `Squarefree` predicate and its negation as the two filters. `Member` includes the positive-integer hypothesis and both original squarefreeness conditions.

The public `conjecture` theorem quantifies over every natural number satisfying `Member`. It has no computational cutoff, prime-support assumption, presumed product formula, or hypothesis containing the desired conclusion. Natural-number exponents in its factorization satisfy the source's requested integer-exponent form. The stronger result proves both exponents at least two, so no interpretation of a negative exponent is needed.

## Product formula and prime support

`squarefreeSum_eq_prod` is derived from mathlib's sum over squarefree divisors and the expansion of a product of sums. It applies only when n is nonzero, as required. It counts each distinct prime factor once, independently of its exponent in n.

In `odd_prime_unique`, distinct odd primes p and q give two distinct factors p+1 and q+1 in the product. Their product divides the squarefree-divisor sum, and both factors are even, forcing divisibility by 4. This contradicts squarefreeness. The proof does not erroneously infer the product divisibility from two separate divisibility statements; it explicitly uses the two-element subset of the prime-factor set.

The factorization step correctly handles an absent odd prime by assigning exponent zero to a fixed odd prime. Thus the first-sum-only theorem covers powers of two and n=1 without an omitted case. The later use of the second sum eliminates these cases for actual members.

## The nonsquarefree sum and exponent restrictions

`two_squared_prime_divisors` checks both required cases. If no prime square divides n, n and all its divisors are squarefree, so the nonsquarefree sum is zero. Zero is not squarefree. If just one prime square p² divides n, every nonsquarefree divisor has that same prime square as a divisor, and hence p² divides their sum. This again contradicts squarefreeness.

The resulting two distinct squared prime divisors must be 2 and the unique possible odd prime. The factorization exponents are therefore both at least two. This argument uses the original second sum, not an additional assumption about n's factorization.

## Congruence and lower bound

With exactly the prime support {2,p}, the first sum is 3(p+1). Its squarefreeness excludes 4 dividing p+1 and excludes 3 dividing p+1. Since p is odd and cannot equal 3, these give p=1 modulo 4 and p=1 modulo 3, hence p=1 modulo 12.

The strengthened theorem correctly states necessary conditions only. Those conditions force p≥13, and the two exponent bounds give n≥4·13²=676. The README does not claim that these necessary conditions suffice for membership.

The numerical illustration at 676 is correct: its squarefree-divisor sum is 42=2·3·7, and its nonsquarefree-divisor sum is 1239=3·7·59. The README explicitly distinguishes this numerical calculation from the formally proved universal lower bound; the source makes no unsupported claim to contain a `member_676` theorem.

## Source and prior-work scope

The [A048250 snapshot](background_A048250.seq) attributes the product formula to Vladeta Jovovic in 2001. The [A065302 snapshot](prior_A065302.seq) contains Walter Kehowski's 2007 statement and the two-odd-prime obstruction. The README and source record accurately credit those arguments and explain their application to the radical of a general integer. They claim the exact two-sum conjecture and the extra exponent restrictions, not a new general multiplicative theory.

The separate conjecture concerning the proportion of relevant primes in A082539 is expressly outside the package. No converse classification, infinitude statement, or exhaustive historical-priority claim is made. The broader literature search is recorded by the author; this audit independently checked the included primary evidence and its relationship to the proof.

No mathematical error, source-definition mismatch, missing boundary case, proof placeholder, custom axiom, `native_decide`, or unsafe proof replacement was found.

Verified `Proof.lean` SHA-256:

`70737066f7bb1896c29184752cf3cb9f5741e5930646e8d2c037021b352490c3`
