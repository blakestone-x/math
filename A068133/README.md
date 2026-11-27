# Triangular numbers with a prescribed triangular digit sum

**Blake Stone** · Proof developed with OpenAI Astra 6.2.

Write $T_m=m(m+1)/2$, and let $s_{10}$ be the sum of the decimal digits. Amarnath Murthy asked in 2002 whether each triangular number occurs infinitely often as the digit sum of triangular numbers. Jon E. Schoenfield recorded the exceptions $0$ and $1$ in 2010. [OEIS A068133](https://oeis.org/A068133)

**Theorem.** For every $m\ge2$ there are infinitely many distinct triangular numbers $T_N$ with $s_{10}(T_N)=T_m$. The only triangular number with digit sum zero is zero, and the only ones with digit sum one are $1$ and $10$.

## Construction

Write $m=2r+e$ with $e\in\{0,1\}$. Since $m\ge2$, we have $r\ge1$. For each integer $k\ge1$ set

$$
S=\sum_{i=0}^{r-1}10^{k3^i},\qquad N=2S+e.
$$

Then $T_N=2S^2+(2e+1)S+e$. Every nonzero summand in this expansion occupies a distinct decimal position after like terms are collected:

| Source | Decimal position | Digit |
| --- | --- | ---: |
| Linear term | $k3^i$ | $2e+1$ |
| Diagonal of the square | $2k3^i$ | $2$ |
| Pair $i<j$ | $k(3^i+3^j)$ | $4$ |
| Constant | $0$ | $e$ |

To see distinctness, divide the positive positions by $k$ and read them in base three. They have one digit equal to one, one digit equal to two, or two digits equal to one, respectively. Their positions identify the indices uniquely. Each coefficient is at most four, so there are no decimal carries. Summing the digits has the effect of replacing each power of ten in $S$ by one. Thus

$$
s_{10}(T_N)=2r^2+(2e+1)r+e=T_{2r+e}=T_m.
$$

Both $N$ and $T_N$ increase strictly with $k$, giving infinitely many witnesses. For example, $m=5$ and $k=1$ give $T_{2021}=2{,}043{,}231$, whose digits sum to $15$.

## Exceptions

Only zero has digit sum zero. A positive integer of digit sum one is $10^j$ for some $j\ge0$. The case $j=0$ gives $T_1=1$. For $j\ge1$, if $T_N=10^j$ then $N(N+1)=2^{j+1}5^j$. Both factors exceed one and are coprime, so they must be $2^{j+1}$ and $5^j$ in some order. At $j=1$ they are $4$ and $5$, giving $T_4=10$. For $j\ge2$ the positive difference $5^j-2^{j+1}$ is at least $25-8=17$ and increases with $j$.

[Proof notes, page 2](../notes/OEIS_Proof_Notes.pdf)
