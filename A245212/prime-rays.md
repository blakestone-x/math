# Prime-power rays in Krizek’s second divisor moment

Krizek conjectured that A245212 equals the ordinary sum of divisors precisely at powers of two. This continuation proves the following restrictions on a counterexample. [Proof manuscript](prime-rays.pdf) · [Editable LaTeX](prime-rays.tex) · [Original problem](https://oeis.org/A245212)

| Setting | Result |
|---|---|
| Fix a prime $p$ and $m$ coprime to $p$. | The entire family $mp^e$ contains at most one solution, except for $m=1,p=2$, when every exponent works. |
| Fix only the cofactor $m$, allowing both the prime $p$ and its positive exponent to vary. | A finite algorithm enumerates every counterexample of the form $mp^e$ with $p\nmid m$. |
| Write a counterexample as $2^a m$ with $m>1$ odd. | Some odd prime factor must be at least $a+2$. When all are smaller, the strict sign of the difference is determined. |
| Fix any finite set of primes, allowing arbitrary exponents. | A finite algorithm enumerates every counterexample supported on these primes. |
| Fix the exponent pattern of the odd part, allowing arbitrary prime bases and any power of two. | Only finitely many counterexamples exist with the given pattern. The paper supplies an effective enumeration. |
| Give the odd part exactly two distinct prime factors and at most 256 divisors. | The conjecture holds throughout this class, with no bound on either prime or on the power of two. |

The preceding paper proves a density-one result, classifies an odd part that is a prime power, and verifies all integers with odd part at most 100,000,000. Arbitrary prime supports and exponent patterns together remain open. [Earlier manuscript](manuscript.pdf)

Compile the [exact verifier](two_odd_primes.cpp) with a C++20 compiler and the GMP C++ library. The program first bounds the dyadic exponent and smaller odd prime, sieves possible unit residues, and determines at most one candidate for the larger odd prime. [Recorded output](prime-rays-verification.txt)

```sh
c++ -O3 -std=c++20 two_odd_primes.cpp -lgmpxx -lgmp -o /tmp/krizek-two-odd
/tmp/krizek-two-odd 256
```
