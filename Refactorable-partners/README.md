# Amicably refactorable pairs

Blake Stone · Proof developed with OpenAI Codex

Waldemar Puszkarz asked whether every integer $n\ge3$ has a distinct positive partner $k$ with $\tau(n)\mid k$ and $\tau(k)\mid n$, where $\tau$ counts the positive divisors. The answer is yes. [Manuscript (PDF)](refactorable-partners.pdf) · [LaTeX source](refactorable-partners.tex) · [Puszkarz’s conjecture, OEIS A269781](https://oeis.org/A269781)

| Input | Partners |
| --- | --- |
| $1$ or $2$ | None |
| Odd prime $p$ | Precisely $2^{p-1}$ |
| Composite $n$ | Infinitely many, even with the extra requirement $\tau(k)=n$ |

The construction reserves the least prime factor $p$ of $n$. It produces a multiple $c$ of $\tau(n)$ with exactly $n/p$ divisors. Adding any sufficiently large fresh prime to exponent $p-1$ gives a new partner. [Construction and complete existence proof in Lean](Partners.lean)

## Least partners, counts, and distances

A finite minimization over exponents on the primes dividing $\tau(n)$ computes the least partner for every $n\ge3$. At a product of two distinct odd primes $p<q$ the least partner is $2^{p-1}$. For example the least partner of 15 is 4, as in the OEIS data. The entry’s largest-prime-factor rule would give 16. [Prime-power minima and the odd-semiprime theorem in Lean](Least.lean)

For every fixed composite the manuscript gives an asymptotic count of all partners up to $X$, including its leading constant. It also shows that the partner graph on integers at least three is connected with diameter between five and eight. The counting theorem uses Landau’s theorem for squarefree products of a fixed number of primes. Both the asymptotic and the graph bounds have written proofs.

## Verification

The pinned Lean 4.19.0 package checks the divisor-count lifting theorem, the existence and degree classification, and the stated minimum criteria. The standard-library Python audit reproduces all 54 values in Puszkarz’s table, checks minima at 698 indices against a bounded divisor sieve, and checks the composite constructions up to 1,200 in factored form.

```sh
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

[Build and audit results](verification.txt) · [Divisor-count lifting lemma](DivisorLift.lean) · [Audit source](verify.py)
