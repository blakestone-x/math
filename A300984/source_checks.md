# A300984: statement and prior-work checks

Checked during the November 26, 2026 (America/Chicago) session.

## Current primary entry

- Entry: https://oeis.org/A300984
- Official maintained export: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A300/A300984.seq
- Saved exactly as `source.seq`.
- Revision: `#15 Aug 19 2019 03:17:02`.
- Author: Michel Lagneau, March 17, 2018.
- Definition: positive integers whose squarefree-divisor sum and nonsquarefree-divisor sum are both squarefree.
- Target assertion: every term is of the form `2^i*p^j`, with integer exponents and prime `p`.
- The export still labels this assertion a conjecture. It gives a computational verification range but no proof or literature link for the assertion.

The separate statement about a majority of primes occurring in A082539 is not addressed. Necessary conditions in the result do not assert a complete converse or infinitude.

## Directly relevant earlier results

1. **Vladeta Jovovic, April 19, 2001, OEIS A048250.** The sum of the squarefree divisors is the product of `p+1` over the distinct prime divisors. The radical formulation was also recorded by Reinhard Zumkeller on July 19, 2002. This is standard background, not a new identity here.
   - https://oeis.org/A048250
   - https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A048/A048250.seq
   - Snapshot: `background_A048250.seq`, revision `#111 Oct 30 2026 00:17:08`.
2. **Walter Kehowski, March 21, 2007, OEIS A065302.** For a squarefree nonprime integer whose ordinary divisor sum is squarefree, the only possible shapes are `1` and `2*p`, with prime `p` congruent to `1 mod 12`. The comment explicitly proves the obstruction from two odd prime factors by the square factor `4` in `(p+1)*(q+1)`.
   - https://oeis.org/A065302
   - https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A065/A065302.seq
   - Snapshot: `prior_A065302.seq`, revision `#22 Oct 11 2026 09:33:48`.
   - This comment does not state A300984's arbitrary-integer, two-divisor-sum result. Its argument applies to the radical and already supplies the support and congruence obstruction used here. The package explicitly credits it; the extra use of the nonsquarefree sum forces both exponents to be at least two.
3. **OEIS A162296.** Sum of the nonsquarefree divisors, used to confirm the second original definition and its relation to the ordinary divisor sum.
   - https://oeis.org/A162296
   - https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A162/A162296.seq
   - Snapshot: `background_A162296.seq`, revision `#33 Apr 20 2023 14:55:16`.

## Search scope

The searches included the exact identifier alone and with `proof`, `conjecture`, and the author of the Low-Hanging Fruit collection; combinations of `sum of squarefree divisors`, `sum of nonsquarefree divisors`, `squarefree`, `Kehowski`, and the factorization shape; and exact-ID searches restricted to public proof collections and preprint indexes.

The following collection pages were inspected or searched for the exact identifier:

- https://www.trureturing.org/conjectures
- https://fabianarevalo.com/math
- https://github.com/Eppie/oeis-proofs
- https://aixiv.online/search?q=%E6%9E%97%E6%8B%BE

The abstracts and enumerated problem lists for 林拾's *Low-Hanging Fruit*, volumes I–V, were also read. They concern other sequence assertions:

- Volume I: https://aixiv.online/abs/2610.02669
- Volume II: https://aixiv.online/abs/2610.02670
- Volume III: https://aixiv.online/abs/2610.03153
- Volume IV: https://aixiv.online/abs/2611.00009
- Volume V: https://aixiv.online/abs/2611.00099

No earlier exact A300984 proof was located through these searches. Several search hits were unrelated uses of the identifier or papers about other squarefree-divisor sums. The concrete prior argument that was found is Kehowski's, documented above.

## Supported conclusion

This is an elementary settlement and formalization of a conjecture still displayed in the official A300984 entry, together with stronger necessary exponent conditions. It is closely based on known radical and divisor-sum facts. Search coverage cannot certify absolute priority, and no claim of a new general multiplicative theory is made.

OEIS snapshots are reproduced with attribution to their contributors and the OEIS Foundation; see https://oeis.org/wiki/The_OEIS_End-User_License_Agreement .
