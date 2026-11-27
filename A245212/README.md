# A density-one theorem for Krizek’s second divisor moment

Jaroslav Krizek conjectured that A245212 equals the usual sum of divisors exactly at powers of two. The manuscript proves this equivalence on a set of natural density one and for every integer whose odd part is at most $10^8$. The general conjecture remains open. [Original statement](https://oeis.org/A245212) · [Proof manuscript](manuscript.pdf) · [LaTeX](manuscript.tex)

| Result | Scope |
|---|---|
| Density | For every fixed $k$, almost every $n$ has at least $k$ odd primes dividing both $\sum_{d\mid n}d\tau(d)$ and $\sigma(n)$ while avoiding $n\tau(n)$. Each such prime rules out equality. |
| Powers of two | On each progression $m,2m,4m,\ldots$ with $m>1$ odd, at most one member could satisfy the equality. There is none when $m$ is a prime power or a squarefree integer. All powers of two satisfy equality. |
| Odd supports | There is no odd solution $n>1$ when $\prod_{p\mid n}p/(p-1)\le2$. Thus no odd number with at most two distinct prime factors supplies a counterexample. |
| Parity | One explicit exclusion covers a set of density $\pi^2/12$. If the odd part is a square, equality requires it to be a fourth power. |
| Finite verification | The one-candidate formula verifies every dyadic exponent for each of the $49{,}999{,}999$ nontrivial odd parts up to $10^8$. |

The proof of density uses divergence of reciprocal primes in a reduced progression and the Chinese remainder theorem. [MIT number theory notes](https://math.mit.edu/classes/18.785/2021fa/LectureNotes18.pdf)

The standard-library C++17 verifier uses a smallest-prime-factor sieve on odd numbers and exact integer arithmetic. [Verifier](verify.cpp) · [Expected output](verification.txt)

```sh
c++ -O3 -std=c++17 verify.cpp -o /tmp/a245212-check
/tmp/a245212-check
```
