# A density-one result for Sun's divisor–totient conjecture

Zhi-Wei Sun's conjecture in [OEIS A248029](https://oeis.org/A248029) asks whether every integer $n>1$ admits an integer $1\le m\le n$ satisfying $n+m\mid \varphi(m)\sigma(n)$. Here $\sigma(n)$ denotes the sum of all positive divisors of $n$.

## Theorem 1

For every $\varepsilon>0$, all but

$$
O_\varepsilon\!\left(\frac{X}{(\log X)^{1-\varepsilon}}\right)
$$

integers $2\le n\le X$ have a divisor $d$ of $\sigma(n)$ in the interval $(n,2n]$. For these integers $m=d-n$ satisfies Sun's conjecture. In particular, the conjectured bound holds on a set of natural density one.

### A direct witness

Put $v=v_2(\sigma(n))$. Whenever $\sigma(n)/2^v\le 2n$, take the least $j\ge0$ with $\sigma(n)/2^j\le 2n$. Then $j\le v$, so $d=\sigma(n)/2^j$ is an integer divisor of $\sigma(n)$. If $j>0$ then $2d>2n$ by minimality. If $j=0$ then $d=\sigma(n)>n$ since $n>1$. Thus in either case $n<d\le 2n$.

### Counting the remaining integers

For an integer $k\ge1$ define the nonnegative multiplicative function

$$
g(n)=\left(\frac{\sigma(n)}{n\,2^{v_2(\sigma(n))}}\right)^k,\qquad \theta=2^{-k}.
$$

The odd part of a product is the product of its odd parts, which gives multiplicativity for coprime inputs. For every prime power, $\sigma(p^a)/p^a< p/(p-1)\le2$, so $g(p^a)\le2^k$. For odd primes $p$, the even factor $p+1=\sigma(p)$ gives

$$
g(p)\le 2^{-k}(1+1/p)^k=\theta+O_k(1/p).
$$

For $X\ge3$, expanding the Euler product with nonnegative coefficients gives

$$
\sum_{m\le X}\frac{g(m)}m
\le\prod_{p\le X}\left(1+\frac{g(p)}p+\sum_{a\ge2}\frac{g(p^a)}{p^a}\right)
\ll_k (\log X)^\theta.
$$

Indeed, the logarithm of the product is at most $\theta\sum_{p\le X}1/p+O_k(1)$, and the classical upper bound for the prime harmonic sum is $\sum_{p\le X}1/p\le\log\log X+O(1)$.

Chebyshev's elementary bound $\sum_{p\le y}\log p\ll y$ also gives

$$
\sum_{p^a\le y} a(\log p)\,g(p^a)\ll_k y\qquad(y\ge1).
$$

The terms with $a\ge2$ are $O_k(\sqrt y(\log(2y))^2)$, which is $O_k(y)$. For completeness, Chebyshev's bound also yields the harmonic-prime estimate used above. For $s=1+1/\log X$,

$$
\sum_{p\le X}(p^{-1}-p^{-s})\le\frac{1}{\log X}\sum_{p\le X}\frac{\log p}{p}\ll1
$$

by partial summation, while $\sum_p p^{-s}\le\log\zeta(s)\le\log(1+\log X)$ by the Euler product and the integral test.

Expand $\log n$ as a sum of $a\log p$ over the exact powers $p^a\parallel n$. Writing $n=p^a m$, multiplicativity gives $g(n)=g(p^a)g(m)$. Dropping the coprimality requirement in the resulting upper bound gives

$$
\sum_{n\le X}g(n)\log n
\le \sum_{m\le X}g(m)\sum_{p^a\le X/m}a(\log p)\,g(p^a)
\ll_k X(\log X)^\theta.
$$

For $n>\sqrt X$, divide this bound by $\tfrac12\log X$. For smaller $n$, use $\sum_{n\le\sqrt X}g(n)\le\sqrt X\sum_{n\le\sqrt X}g(n)/n$. Together these yield

$$
\sum_{n\le X}g(n)\ll_k\frac{X}{(\log X)^{1-2^{-k}}}.
$$

Each integer missed by the direct witness has $g(n)>2^k$. Choosing $k$ with $2^{-k}\le\varepsilon$ proves the claimed bound.

## Theorem 2

For an odd integer $u$, form the square

$$
b=\prod_{\substack{p^e\parallel u\\ e\ {\rm even}}}p^e
$$

using the primes with **positive even exponent**. If $\sigma(b)\le2b$, Sun's conjecture holds for every $n=2^a u>1$ with $a\ge0$.

To see this, start with $d=\sigma(b)$, so $d\mid\sigma(b)$ and $b\le d\le2b$. Suppose $z$ has such an interval divisor $d$, and take a coprime odd prime power $t=p^e$ with odd exponent $e$. Write $S=\sigma(t)$. The inequalities $t<S<2t$ and the parity $2\mid S$ give the following choice for $zt$:

$$
d'=\begin{cases}Sd& Sd\le2zt,\\ Sd/2& Sd>2zt.\end{cases}
$$

In both cases $d'\mid \sigma(zt)=S\sigma(z)$ and $zt<d'\le 2zt$. In the first case $d'-zt\ge (S-t)z$, which is at least two unless $z=1$ and $t$ is prime. In the second case $2d'\mid\sigma(zt)$. The starting choice for composite $b$ has $\sigma(b)-b\ge2$.

Iterating therefore gives, for every composite $u$ in the stated class, an interval divisor $d$ with $h=d-u\ge2$ or with $h=1$ and $2d\mid\sigma(u)$. For $a=0$ take $m=h$. For $a\ge1$ take $m=2^a h$. If $h\ge2$ then $2^a\mid \varphi(2^a h)$. For even $h$, this follows by doubling an even argument $a$ times in the totient. For odd $h\ge3$, use $\varphi(2^a h)=2^{a-1}\varphi(h)$ and the evenness of $\varphi(h)$. Since $d\mid\sigma(u)\mid\sigma(2^a u)$, this proves $2^a d=n+m\mid\varphi(m)\sigma(n)$. When $h=1$, use $\varphi(2^a)=2^{a-1}$ and $2d\mid\sigma(u)$ instead.

If $u=1$, the divisor $\sigma(2^a)=2^{a+1}-1$ works for $n>1$. If $u$ is prime, apply the displayed extension step to $z=2^a$, $d=\sigma(2^a)$ and $t=u$ to get an interval divisor for $n$ directly.

For example, the theorem covers all $n=2^a105^{2r+1}$ with $a\ge0$ and $r\ge1$. Their odd parts are abundant and have no primes of exponent one. At $n=105^3=1\,157\,625$, $\sigma(n)=2\,496\,000$ yields $m=90\,375$ by a single halving.

## A family with abundant square core

For every $n$, a divisor $d$ of $2\sigma(n)$ with $n+2<d\le2n$ gives a witness, since $m=d-n>2$ has even totient. In particular, suppose $n\ge6$, $2n<\sigma(n)\le3n$, and $3\mid\sigma(n)$. Then $m=2\sigma(n)/3-n$ is an integer with $n/3<m\le n$.

This covers every $n=(105q)^2$ with $q>7$ prime. Indeed, $\sigma(105^2)=13\cdot31\cdot57=22971$, and multiplication by $q^2$ increases the abundancy ratio by a factor $1+1/q+1/q^2\le133/121$. The resulting ratio is strictly between 2 and 3, with $3\mid\sigma(n)$. These $n$ are odd squares with odd divisor sum. Each proper divisor of $\sigma(n)$ is at most $\sigma(n)/3<n$, while $\sigma(n)>2n$. Thus this infinite family requires the totient factor for the original witness.

## What remains

An interval divisor need not exist for every $n$. For instance, $n=11025$ has $\sigma(n)=22971$, an odd number between $2n$ and $3n$. Every proper divisor of $\sigma(n)$ is then smaller than $n$. The original conjecture still holds in this example: $m=4289$ gives $n+m=2\sigma(n)/3$, and $\varphi(4289)$ is even. A proof that some witness always exists for the remaining integers would be needed for the full conjecture.

The companion Python script checks the original conjecture for every $2\le n\le1{,}000{,}000$ when run with argument 1000000. Of the 999,999 inputs, the dyadic divisor test handles 999,261 and the nonabundant square-core test handles 999,944. Together they handle 999,979 inputs. The script searches $m$ in increasing order for each of the other 20 and checks the original divisibility directly. For example, the least witnesses for $n=11025$ and $n=540225$ are 375 and 52185, respectively.

[Reproduce the finite checks](check-density.py) · [Formal reduction submitted to Left to Solve](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18189)
