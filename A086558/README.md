# Prescribing the decimal prefix, length, and prime signature

Blake Stone · Proof developed with OpenAI Codex

**Theorem.** For every positive integer $n$, there is an $n$-digit integer beginning with the decimal digits of $n$ whose prime signature is the same as that of $n$. Here the prime signature is the multiset of positive exponents in the prime factorization. This proves Amarnath Murthy's 2003 conjecture that A086558 has no zero term. [OEIS A086558](https://oeis.org/A086558)

## Replacing one prime factor

For $n\ge2$, let $d$ be its number of decimal digits, put $k=n-d$, and let $p$ be its largest prime factor. Write $n=up^a$ with $p\nmid u$, and set

$$
X=p\,10^{k/a}.
$$

The integers in $[n10^k,(n+1)10^k)$ are exactly the $n$-digit integers beginning with $n$. Since $uX^a=n10^k$, a prime $q$ satisfying

$$
X<q<X(1+1/n)^{1/a}
$$

gives a witness $uq^a$ in that interval. Indeed, $q>p$, so $q$ is distinct from every prime divisor of $u$. Its exponent $a$ replaces the exponent of $p$.

We use Dusart's unconditional theorem that for every real $X\ge3275$ there is a prime in $(X,X(1+1/(2\log^2 X))]$. All logarithms here are natural. It therefore suffices to verify

$$
X\ge3275,\qquad \frac{a}{2\log^2 X}<\frac1{n+1}.
$$

In fact $\log(1+t)\le t$ for $t\ge0$, while $\log(1+1/n)\ge1/(n+1)$ by integrating $1/t$ on $[n,n+1]$. Thus the upper endpoint in Dusart's theorem is strictly below $X(1+1/n)^{1/a}$. [P. Dusart, *Sharper bounds for* $\psi,\theta,\pi,p_k$, Theorem 9, p. 14 (1998)](https://citeseerx.ist.psu.edu/document?doi=35d6df8f67afd4508d42a41988ae8c21677f167c&repid=rep1&type=pdf)

## Uniform estimates

Suppose $n\ge16$. Then $d\le n/8$. For $d=2$ this follows from $n\ge16$, and for $d\ge3$ it follows from $n\ge10^{d-1}\ge8d$. Also $a\le n/4$. This holds directly for $a\le4$, and for $a\ge5$ it follows from $n\ge2^a\ge4a$. Consequently $k/a\ge7/2$, so $X\ge2\cdot10^{7/2}>3275$. Moreover,

$$
\log X\ \ge\frac{k\log 10}{a}
\ \ge\frac{7\log 10}{8}\frac n a
\ >\frac{2n}{a}.
$$

For each positive integer $a$, one has $a^3\le4\cdot2^a$. Check $a=1,2,3,4$ directly. For $a\ge4$, the cube grows by a factor at most $(5/4)^3<2$ at each step. Hence $a^3\le4n$ and

$$
\frac{a}{2\log^2 X}<\frac{a^3}{8n^2}\le\frac1{2n}<\frac1{n+1}.
$$

This proves the theorem for $n\ge16$.

## Small inputs

For $5\le n\le15$ with $n\ne8$, the largest prime factor has exponent $a=1$, except at $n=9$ where $a=2$. In each case $k/a\ge4$, so $X\ge2\cdot10^4$ and $\log X>9$. Thus $a/(2\log^2 X)<1/81<1/(n+1)$, and the same prime-interval argument applies.

The remaining five inputs have the following witnesses. The primes in the table can be checked by trial division by primes up to $19$.

| $n$ | Witness | Factorization |
|---:|---:|---|
| 1 | 1 | empty product |
| 2 | 23 | $23$ |
| 3 | 307 | $307$ |
| 4 | 4489 | $67^2$ |
| 8 | 80062991 | $431^3$ |

This supplies a witness for every $n$. The least witness required by A086558 therefore exists. $\square$
