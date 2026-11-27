# Source and prior-work checks for A393833

Checked November 26, 2026 (America/Chicago).

## Exact primary source

- [OEIS A393833](https://oeis.org/A393833).
- [Official OEIS-maintained export](https://github.com/oeis/oeisdata/blob/main/seq/A393/A393833.seq).
- Header: `%I A393833 #30 Apr 02 2026 08:12:46`.
- Git blob: `3df9a69a10b59b04c356f5a0208c488ca4729330`.
- Preserved verbatim in `source.seq`; its SHA-256 is in `SHA256SUMS.txt`.

The recorded conjecture is an existence assertion for every positive
index. The sequence name imposes exactly $2n+2$ total divisors, and both
the Maple and PARI predicates impose that same divisor count. The formal
predicate includes it as well as the proper-list length and palindrome.
The PARI test is equality with the reversed list; it permits constant
lists. No nonconstant condition appears in the entry.

The remaining example `$a(9)=19^4*37^3$` disagrees with the corrected data.
It is not used as evidence of a minimum, nor in the proof. The entry
explicitly records the March 5, 2026 correction to the ninth value.

## Prior ingredients

The existence of arbitrarily large primes $1\pmod m$ is classical. The
formal proof invokes mathlib's `Nat.exists_prime_gt_modEq_one` at pinned
commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. That module, originally
authored by Riccardo Brasca, derives the result from a cyclotomic-polynomial
argument. The theorem is not introduced as an axiom or assumed locally.
Prime-power divisor descriptions also come from mathlib and are standard.

## Bounded search

Two web search engines were used with combinations including:

- `"A393833" proof`, `"A393833" theorem`, and `"A393833" prime`;
- `"A393833" proof -site:oeis.org`;
- `"proper divisors" "palindrome" "modulo"`;
- `"palindromic" "divisors" "prime power"`;
- exact-identifier checks against the indexed trureturing proof collection.

The relevant results were the OEIS entry and reproductions of the same
statement; no proof of this exact assertion was located. Work about
*palindromic sums* of proper divisors addresses a different property.
The searches do not establish absolute publication priority.

## Scope

One recorded conjecture is settled. The arbitrary-bound result and
existence of a least witness are strengthening and consequence of the
same proof. The package does not claim a formula for the minimum or
compute additional sequence values.
