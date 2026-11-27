# A063956: Yanev's product identity for unitary prime divisors

Blake Stone, developed with OpenAI Astra 6.2. November 26, 2026.

This package proves the formula attributed to Velin Yanev on February 17, 2019 in [OEIS A063956](https://oeis.org/A063956). For positive integers $n,m$, let $a(n)$ be the sum of the prime divisors of $n$ that occur with exponent exactly one. Then

$$
a(nm)=a(n)+a(m)-a(\gcd(n^2,m))-a(\gcd(n,m^2)).
$$

These primes are precisely the unitary prime divisors: a prime $p\mid n$ is unitary when $\gcd(p,n/p)=1$. The equivalent exponent-one description is already stated and implemented in the OEIS entry; this work proves the conjectured product identity.

## Proof

For a prime $p$, put $x=v_p(n)$, $y=v_p(m)$, and write $[P]$ for 1 when $P$ holds and 0 otherwise. The identity needed for this prime is

$$
[x+y=1]+[\min(2x,y)=1]+[\min(x,2y)=1]=[x=1]+[y=1].
$$

If $x=0$, both minimum terms vanish and the first term is $[y=1]$; the case $y=0$ is symmetric. If $x,y>0$, then $x+y\ge2$, $2x\ge2$, and $2y\ge2$. Consequently the first term vanishes, the second equals $[y=1]$, and the third equals $[x=1]$. These cases exhaust all nonnegative exponents.

Multiply by $p$ and sum over the finite union of the prime divisors of $n$ and $m$. The prime exponents of the product and the two gcds are respectively $x+y$, $\min(2x,y)$, and $\min(x,2y)$, so

$$
a(nm)+a(\gcd(n^2,m))+a(\gcd(n,m^2))=a(n)+a(m).
$$

Rearranging proves the asserted identity. The additive form also proves that both successive natural-number subtractions in the Lean statement are exact.

For example, $n=6,m=10$ gives $a(60)=5+7-2-2=8$, contributed by the primes 3 and 5. For $n=12,m=18$, the formula gives $a(216)=3+2-2-3=0$.

## Formal theorem

`Proof.lean` defines the sequence directly from `Nat.factorization`, a finite map of prime exponents. `A063956.score_balance` proves the pointwise exponent identity. `A063956.finsupp_balance` sums it over a common finite support. Mathlib's product, power, and gcd factorization theorems then give `A063956.balance` and the final theorem:

```lean
theorem conjecture {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    a (n*m) = a n + a m - a (Nat.gcd (n^2) m) - a (Nat.gcd n (m^2))
```

There is no bounded-search hypothesis, unproved sequence assumption, `sorry`, additional axiom, or `native_decide`. The only reported dependencies are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

The package pins Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With Lean's `elan` toolchain manager installed, run:

```sh
lake exe cache get
lake build
```

The `#print axioms` command in the source reports the final theorem's dependencies during compilation.

## Source status and scope

The live [official OEIS data export](https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A063/A063956.seq), revision 32 dated October 18, 2026, explicitly labels Yanev's 2019 identity a conjecture. It was retrieved on November 26, 2026 and agrees on the mathematical content with revision 30 of the [internal entry](https://oeis.org/A063956/internal) retrieved through search. The entry also credits Amiram Eldar (July 24, 2024) with the additive prime-power description and Wesley Ivan Hurt (April 18, 2026) with unitary-divisor sum formulas. Those descriptions are prior work, used here to identify the sequence precisely.

A search on November 26, 2026 covered the exact sequence identifier and formula, unitary-prime-divisor terminology, and the public proof indexes of [trureturing](https://www.trureturing.org/conjectures), [Fabian Arevalo](https://fabianarevalo.com/math), and [Eppie's OEIS proofs](https://github.com/Eppie/oeis-proofs). No earlier proof of the selected identity was found. This records the checked source status and bounded search; it does not establish global publication priority. The result is an elementary exact identity resolving the formula still marked conjectural in that source.

## Collected proof document

[Read the complete proof collection (PDF)](../notes/Math_Proofs_Batch4.pdf) · [LaTeX source](../notes/Math_Proofs_Batch4.tex)
