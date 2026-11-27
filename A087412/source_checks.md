# Source and prior-work checks for A087412

Checked during the November 26, 2026 (America/Chicago) session.

## Primary statement

- Entry: https://oeis.org/A087412
- Official maintained export: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A087/A087412.seq
- Exact export saved as `source.seq`.
- Revision marker: `#30 Sep 17 2019 12:03:03`.
- Sequence creator: Yuval Dekel, October 21, 2003.
- Conjecture attribution: Andrew Howroyd, July 17, 2018.
- Exact displayed formula: `Conjecture: a(3^e) = 2*3^e for e > 1.`
- Definition: number of ordered residue pairs satisfying `x^3 + y^3 == 1 (mod n)`; the supplied PARI code loops independently over `0 <= x,y < n`.

The entry separately gives formulas for primes congruent to 2 modulo 3 and a character-sum formula at primes other than 3. We do not claim those formulas as new.

## Search coverage

Searches included the exact identifier with proof/conjecture/solutions terms; the exact two-variable cubic equation with powers `3^n` and `3^k`; cubic congruences at prime powers; sum-of-two-cubes solution counts; and a check for the identifier in three public proof collections:

- https://www.trureturing.org/conjectures
- https://fabianarevalo.com/math
- https://github.com/Eppie/oeis-proofs

No exact earlier proof was located in those searches or collection pages.

A related MathOverflow question (https://mathoverflow.net/questions/387018/) concerns the ternary norm form `x^3+y^3+z^3-3xyz`, not the two-variable congruence here. Searches also returned results about integral Fermat equations and sums of three cubes. Those do not establish the stated two-variable residue count. OEIS A254073 concerns a three-variable count and does not supply a proof of this conjecture.

## Scope of the contribution

The package supplies an elementary proof and a complete Lean kernel check of the exact recorded powers-of-three formula. The algebraic facts used in the proof—units congruent to 1 modulo a prime, finite injective maps being bijective, and counting lifts of a residue class—are standard background. Search coverage cannot certify absolute priority; the supported statement is that the official entry still labels this formula a conjecture and no earlier exact proof was located in the sources searched.
