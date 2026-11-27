# How many distances have small multiplicity in a square grid?

**Blake Stone · Proof developed with OpenAI Codex.**

In an $L\times L$ square grid of $N=L^2$ points, the number of distinct Euclidean distances occurring at most $N^\theta$ times is $N^{\theta+o(1)}$ for every fixed $0<\theta\le1$. At the threshold of $N$ pairs, we also give a lower bound of order $N\log\log N/\log N$.

Erdős and Pach asked whether, for any $N\ge5$ points in the plane, at least two distinct distances occur between at most $N$ unordered pairs, and whether the number of such distances tends to infinity with $N$. The unrestricted questions remain open. The square grid is a classical example with relatively few distinct distances. The estimates here concern the complete grid and follow from its displacement counts and classical number theory. [Erdős and Fishburn (1995), Conjecture 4](https://www.sciencedirect.com/science/article/pii/0166218X9400046G) · [Erdős Problem 132](https://www.erdosproblems.com/132) · [Clemen, Dumitrescu and Liu (2025)](https://doi.org/10.1007/s10474-025-01562-y)

## Counting the distance classes

Let $G_L=\{0,\ldots,L-1\}^2$. For a positive integer $s$, let $\mu_L(s)$ denote the number of unordered pairs of points of $G_L$ at distance $\sqrt{s}$. Define

$$
R_L(T)=\#\{s\ge1:1\le\mu_L(s)\le T\}.
$$

For a fixed signed displacement $(u,v)$, its number of possible starting points is $(L-|u|)(L-|v|)$ when $|u|,|v|<L$. Each unordered pair appears in both orientations. Thus

$$
\mu_L(s)=\frac12
\sum_{\substack{u^2+v^2=s\\ |u|,|v|<L}}
(L-|u|)(L-|v|).
$$

This formula also appears in Boldyriew et al., Lemma 2.4. Reddy and Skiena previously determined the frequencies of the largest distances by their rank. Clemen, Dumitrescu and Liu also identified two grid distances of multiplicity eight in their Observation 5.4. [Boldyriew et al.](https://arxiv.org/abs/2009.12450) · [Reddy and Skiena, bibliographic record and formula](https://oeis.org/A007543) · [Clemen et al., Observation 5.4](https://arxiv.org/html/2505.04283v5#S5)

**Theorem.** For each fixed $0<\theta\le1$,

$$
\lim_{L\to\infty}\frac{\log R_L(N^\theta)}{\log N}=\theta.
$$

**Upper bound.** Choose a nonnegative displacement $(a,b)$ for each distance counted by $R_L(T)$. All $(L-a)(L-b)$ translations of this displacement are distinct unordered pairs. Its deficits $i=L-a,j=L-b$ therefore satisfy $ij\le T$. The same pair of deficits determines only one distance, giving

$$
R_L(T)\le \sum_{i=1}^{L}\left\lfloor\frac{T}{i}\right\rfloor
\le T(1+\log L).
$$

**Lower bound.** Let $r_2(s)$ count all signed, ordered representations $s=u^2+v^2$, and put $K=\max_{1\le s\le2N}r_2(s)$. Jacobi's formula gives $r_2(s)\le4\tau(s)$, where $\tau$ is the divisor-counting function. For every $\varepsilon>0$, $\tau(s)\ll_\varepsilon s^\varepsilon$. To see this, observe that primes $p\ge 2^{1/\varepsilon}$ satisfy $e+1\le2^e\le p^{\varepsilon e}$, while each of the finitely many smaller primes has $\sup_{e\ge0}(e+1)p^{-\varepsilon e}<\infty$. Consequently $K=N^{o(1)}$. [Jacobi's two-square formula, NIST DLMF 27.13.7](https://dlmf.nist.gov/27.13.E7)

For $64K\le T\le N$, set $H=\lfloor\sqrt{T}/(4\sqrt K)\rfloor$. The $H^2$ vectors with both coordinates in $\{L-H,\ldots,L-1\}$ determine at least $H^2/K$ different squared lengths. Each such squared length satisfies $s\ge2(L-H)^2$. For **every** representation of this $s$ inside the grid, each coordinate separately satisfies

$$
L(L-|u|)\le L^2-u^2\le2L^2-s\le4LH,
$$

and the same bound holds for $v$. Every summand in the displacement formula is therefore at most $16H^2$. Since there are at most $K$ summands, $\mu_L(s)\le16KH^2\le T$.

All these distances occur. Since $\sqrt{T}/(4\sqrt K)\ge2$, flooring loses at most half, and

$$
R_L(T)\ge\frac{H^2}{K}\ge\frac{T}{64K^2}.
$$

For $T=N^\theta$, the lower bound applies for all sufficiently large $N$. Together the bounds give the stated limit. $\square$

## An explicit bound at the threshold of $N$ pairs

**Proposition.** As $L\to\infty$,

$$
R_L(N)\gg \frac{N\log\log N}{\log N}.
$$

Set $c=(15/16)^2$. Consider a product $s=pq$ of distinct primes $p,q\equiv1\bmod4$ such that $cN\le s\le(L-1)^2$. The four divisors $1,p,q,pq$ all equal $1\bmod4$, so Jacobi's formula gives exactly sixteen signed, ordered representations $s=a^2+b^2$. Every representation fits in the grid's displacement range because $\sqrt{s}\le L-1$.

Write $r=\sqrt{s}/L$ and $w=(|a|+|b|)/L$. Here $15/16\le r\le1$ and $r\le w\le\sqrt2\,r$. For each representation the normalized translation count is

$$
\frac{(L-|a|)(L-|b|)}{N}=1-w+\frac{w^2-r^2}{2}.
$$

As a convex quadratic in $w$, it is at most the larger of its endpoint values $1-r$ and $(1-r/\sqrt2)^2$. Both are at most $1/8$ in this range, since $r\ge15/16>\sqrt2-1/2$. The sixteen terms in the displacement formula, divided by two for orientation, give $\mu_L(s)\le N$.

To count these products without duplication, take $p\le N^{1/4}$ and $cN/p\le q\le(L-1)^2/p$. Then $q>p$ for all sufficiently large $N$. Uniformly over these $p$, the prime number theorem for the fixed progression $1\bmod4$ gives $\gg N/(p\log N)$ choices for $q$. Indeed, putting $x=N/p\ge N^{3/4}$, the eligible interval contains $[cx,(1+c)x/2]$ once $(L-1)^2/N\ge(1+c)/2$. The prime number theorem applies for all sufficiently large $x$ to this fixed relative interval. Distinct pairs $(p,q)$ give distinct squared distances by unique factorization. Partial summation of the same prime number theorem gives

$$
\sum_{\substack{p\le N^{1/4}\\p\equiv1\bmod4}}\frac1p
\sim\frac12\log\log N.
$$

Summing the lower bounds for $q$ proves the proposition. $\square$ [Prime number theorem for arithmetic progressions](https://personal.science.psu.edu/rcv4/568s20/568chapter11.pdf)

The grid has $\Theta(N/\sqrt{\log N})$ distinct distances altogether. This bounds $R_L(N)$ from above and leaves a logarithmic gap with the proposition. The exponent theorem counts classes at every polynomial multiplicity threshold. The sources cited above give the classical grid count, the underlying displacement formula, frequencies by distance rank, and results for large multiplicities. No claim of priority is made for the consequences derived here. [Guth and Katz, introduction](https://annals.math.princeton.edu/wp-content/uploads/annals-v181-n1-p02-p.pdf) · [Clemen, Dumitrescu and Liu, Theorem 1.7](https://arxiv.org/html/2505.04283v5#S1.SS2)
