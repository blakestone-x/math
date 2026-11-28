# A067599 has no fixed point through a quadrillion

The decimal factor encoding \(E(n)\) writes the prime factors of \(n\) in increasing order, each followed by its exponent, including exponent 1. An exhaustive search found **no fixed point for \(2\le n\le 10^{15}\)**. The unrestricted existence question remains open. OEIS credits M. F. Hasler with a check below \(3\times10^6\). An existing Open Math Agents reduction treats numbers of the special form \(7^4q\).

## Two infinite families can also be excluded

A squarefree integer always has encoding greater than itself. For its first prime, appending exponent 1 gives a number greater than the prime. Appending a new prime of \(d\) digits and its exponent 1 multiplies the previous encoding by at least \(10^{d+1}\), which is greater than that prime. The inequality persists at every step.

No prime power \(p^e\) is fixed either. Equality would give \(p^e=p10^{\ell(e)}+e\), where \(\ell(e)\) counts decimal digits, so \(p\mid e\). For \(e\le7\) this leaves finitely many pairs, all ruled out by direct substitution. For \(e\ge8\), doubling from \(2^7=128>11\cdot8\) gives \(2^{e-1}>11e\) by induction. Thus
\[
p^e \ge p2^{e-1}>11pe\ge p10^{\ell(e)}+e,
\]
since \(10^{\ell(e)}\le10e\). Any fixed point must therefore have at least two distinct prime factors and a repeated prime factor. The accompanying FactorEncoding.lean proves both exclusions in Lean 4.33.1 against local copies of the two defining functions in Formal Conjectures. Both proofs depend only on propext, Classical.choice, and Quot.sound.

## How the search covers every factorization

Fix an upper limit \(N\). During a search over increasing primes, let \(K\) be the product of the prime powers already selected and let \(C\) be their decimal encoding. Start with \(K=1\) and \(C=0\).

If the final prime \(q\) occurs once and has \(d\) digits, the equation \(E(Kq)=Kq\) gives
\[
 (K-10)q = C\,10^{d+1}+1.
\]
For each admissible digit length this allows at most one \(q\). The program checks exact division, digit count, ordering, size and primality. The digit range \(10^{d-1}\le q<10^d\) implies \(10C<K-10\le100C+1\). No primality hypothesis is needed to reject a digit length before the divisibility test.

All other branches can use only primes \(p\) with \(Kp^2\le N\). Indeed, either \(p\) occurs at least twice, or a larger prime must occur after it. The search enumerates each possible exponent of such a prime, tests the resulting product as a potential endpoint if the exponent is at least two, and recursively extends the prefix if another prime could still fit. Recursion can stop if the partial encoding followed by two more digits would already exceed \(N\). These rules include single prime powers. Primality tests use trial division by sieved primes up to the integer square root. Integer arithmetic uses 128-bit intermediates for decimal concatenation and products that could exceed 64 bits.

## A search at longer digit lengths

A second pass checks \(n=Kq\), with \(K\le30{,}000{,}000\), final prime \(q\) of exponent 1, and up to 25,000 digits in \(q\). For instance, \(K=2187=3^7\) has encoding 37. The following integer is a candidate for every nonnegative \(t\).
\[
 q_t = \frac{37\,10^{667+930t}+1}{2177}.
\]
Indeed, \(10^{930}\equiv1\pmod{2177}\) and \(37\cdot10^{667}\equiv-1\pmod{2177}\). One prime in this family would give a fixed point \(2187q_t\). FactorEncoding.lean also verifies this implication and the digit-length calculation. The prior reduction in PR 1029 uses \(K=2401\). After the necessary filters, 1,236 prefixes yielded 162 integral candidates. Exactly 132 had a prime divisor at most 50,000. GMP certified the remaining 30 as composite via a negative primality test. This search found no witness. To reproduce, compile a067599_long.cpp with g++ -std=c++17 -O3 and link -lgmpxx -lgmp, then run the executable.

## Reproduction

Compile and run from this directory.

```sh
g++ -std=c++17 -Wall -Wextra -O3 a067599.cpp -o a067599
python3 check_a067599.py ./a067599
./a067599 1000000000000000
```

The final run should report 814,769,597 prefixes and zero matches. The Python check computes the encoding independently by factoring every integer from 2 through 100,000 and compares all matches for \(E(n)+s=n\) at offsets \(s=0,7,38,7184\). The positive controls exercise both branches, including \(E(32)=25\) and \(E(10935)=3751\).

## Sources

- [OEIS A067599, definition and prior bound](https://oeis.org/A067599).
- [Left to Solve's existence problem](https://lefttosolve.com/p/OeisA67599.conjecture).
- [Open Math Agents PR 1029, a conditional reduction for the family 7⁴q](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1029).
