# Seven exceptions to the A072633 rounding rule through 10¹⁰⁰⁰

Let $a(n)$ be the least positive $m$ for which $1^n+\cdots+m^n\ge(m+1)^n$. Herbert Kociemba conjectured $a(n)=1+\operatorname{round}(n/\log2)$. Antonio Sanso announced a 330-digit counterexample in July 2026. Elham Mehdi-Nezhad and Amir M. Rahimi subsequently proved that it is the only exception below $0.69\cdot10^{399}$. We extend their exhaustive range to $10^{1000}$. [OEIS](https://oeis.org/A072633) · [Sanso](https://x.com/asanso/status/2079999623507198242) · [Mehdi-Nezhad and Rahimi, equations (2)–(3) and Remark 10](https://arxiv.org/abs/2611.28637)

**Result.** There are exactly seven exceptions for $1\le n\le10^{1000}$. At each one, the actual value exceeds the prediction by one. Write $p_j/q_j$ for the convergents of $2/\log 2$, beginning at index zero. The table specifies each exponent as an exact integer. The attached output gives the decimal expansions of all seven exponents and their actual sequence values.

| Convergent index $j$ | Exponent $n$ | Decimal digits |
|---:|---:|---:|
| 641 | $q_{641}$ | 330 |
| 871 | $q_{871}$ | 451 |
| 1251 | $q_{1251}$ | 638 |
| 1251 | $3q_{1251}$ | 639 |
| 1251 | $5q_{1251}$ | 639 |
| 1697 | $q_{1697}$ | 860 |
| 1769 | $q_{1769}$ | 900 |

## Why the enumeration is exhaustive

Write $L=\log 2$, $M=\lceil n/L+3/2\rceil$, and $\delta=M(M-3/2-n/L)$. Remark 10 of Mehdi-Nezhad and Rahimi gives the counterexample criterion $0<\delta<\gamma_M$. Equation (3) of their paper gives, for $M\ge10^5$,

$$
\gamma_0-87/M<\gamma_M<\gamma_0+116/M,
\qquad \gamma_0=25/12-3L.
$$

We enumerate $10^9\le n\le10^{1000}$. The previously published theorem covers the smaller positive integers. Throughout our range $M>n$ and $\gamma_M<1/250$. Put $h=2M-3$, which is odd. Every exception satisfies

$$
0<n(h-2n/L)=2n\delta/M<1/125.
$$

Write $h=tp$ and $n=tq$ with $\gcd(p,q)=1$. Both $p$ and $t$ are odd. Since $0<p/q-2/L<1/(125t^2q^2)<1/(2q^2)$, Legendre’s continued-fraction theorem makes $p/q$ a convergent of $2/L$. For each such convergent, set $e=q(p-2q/L)$. We only need convergents with $q\le10^{1000}$, $p$ odd and $e>0$. For those we only need odd multipliers satisfying $tq\le10^{1000}$ and $t^2e<1/125$.

The certificate computes rational lower and upper bounds on $L$ from

$$
 L=2\sum_{i\ge0}\frac{1}{(2i+1)3^{2i+1}}.
$$

It rounds each summand down on a grid of width $10^{-2100}$ and allows one unit for each rounding. After $J$ terms the tail is less than $9/(4\cdot3^{2J+1})$, and the program stops when this bound falls below one grid unit. The two rational endpoints for $2/L$ have identical continued-fraction coefficients through the first convergent whose denominator exceeds $10^{1000}$. Thus every needed convergent is determined.

Only eleven candidate pairs $(j,t)$ survive the integer bounds. For each, the code checks $0<\delta<1$ using $M=(tp_j+3)/2$, which verifies the required ceiling defining $M$. It then compares the rational interval for $\delta$ with both bounds for $\gamma_M$. Seven intervals are strictly below the lower bound. Four are strictly above the upper bound. All comparisons use rational arithmetic; none straddles a decision boundary.

Run `python3 census.py` to reproduce the census and every full decimal value in `census.txt`. The separate program `verify.py` checks the 330-digit case directly against the defining power sums on a dyadic grid, independently of the quoted analytic bound.
