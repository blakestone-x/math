# A counterexample to Lowell's divisor conjecture

**Blake Stone · Proof developed with OpenAI Codex.**

Let $d_i(n)$ be the $i$th smallest positive divisor of $n$, and let $\tau(n)$ be the number of positive divisors. An integer $n$ belongs to OEIS A094783 when, for every $m<n$, one has $d_i(n)\le d_i(m)$ for every index present in both lists. J. Lowell conjectured in 2008 that whenever $k$ belongs to the sequence, the least positive integer $F(k)$ having exactly $k$ divisors also belongs. [OEIS A094783](https://oeis.org/A094783)

**Counterexample.** Take $k=1680$, the twelfth term of A094783. The least integer with $1680$ divisors is

$$
N=F(1680)=2\,205\,403\,200=2^6\,3^4\,5^2\cdot7\cdot11\cdot13\cdot17.
$$

This value is classical. It appears among the highly composite numbers in Ramanujan's table, so every smaller integer has fewer divisors. Its displayed factorization gives $\tau(N)=7\cdot5\cdot3\cdot2^4=1680$. Both the minimality and the input membership can also be checked by the short computation below. [S. Ramanujan, *Highly Composite Numbers*, §7 (1915)](https://doi.org/10.1112/plms/s2_14.1.347)

Set $M=\operatorname{lcm}(1,2,\ldots,19)=232\,792\,560<N$. Its first nineteen divisors are exactly $1,2,\ldots,19$. Each integer from $1$ through $18$ divides $N$, as does $20$, but the prime $19$ does not. Therefore

$$
d_{19}(N)=20>19=d_{19}(M).
$$

This single comparison excludes $F(1680)$ from A094783. $\square$

## Reproducible check

The sieve constructs all divisor lists up to $1680$ in increasing order. To check $F(1680)$ independently, enumerate all nonincreasing factorizations $1680=f_1\cdots f_r$ with $f_i\ge2$. A least integer with this divisor count uses the first $r$ primes, since replacing any prime by a missing smaller one decreases the integer. Its exponents decrease weakly, since swapping a larger exponent onto a smaller prime also decreases the integer. Thus each factorization contributes the single candidate $2^{f_1-1}3^{f_2-1}\cdots p_r^{f_r-1}$. There are at most seven factors since $1680=2^4\cdot3\cdot5\cdot7$.

```python
from math import lcm, prod

k = 1680
divisors = [[] for _ in range(k + 1)]
for d in range(1, k + 1):
    for m in range(d, k + 1, d):
        divisors[m].append(d)
assert all(a <= b for m in range(1, k)
           for a, b in zip(divisors[k], divisors[m]))

def factorizations(n, ceiling):
    if n == 1:
        yield ()
    for f in range(2, min(n, ceiling) + 1):
        if n % f == 0:
            for rest in factorizations(n // f, f):
                yield (f,) + rest

primes = [2, 3, 5, 7, 11, 13, 17]
N = min(prod(p ** (f - 1) for p, f in zip(primes, factors))
        for factors in factorizations(k, k))
M = lcm(*range(1, 20))
assert M == 232792560 < N == 2205403200
assert [d for d in range(1, 21) if N % d == 0][18] == 20
assert [d for d in range(1, 21) if M % d == 0][18] == 19
```
