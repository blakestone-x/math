# How many plus signs does it take to collapse a number?

Blake Stone · Proof developed with OpenAI Codex

Fix a base $b\ge2$. In one round, partition the ordinary base-$b$ expansion of a positive integer into consecutive nonempty blocks and add their values. A cut costs one plus sign. Let $C_b(n)$ be the minimum total cost of reaching a single digit, allowing any number of cuts in each round. For example, $118\to1+1+8=10\to1+0=1$ costs three signs over two rounds.

Butler, Graham and Stong observed that repeatedly cutting in the middle uses $O(\log\log n)$ signs and asked whether this bound reflects the true cost. Simon Demers's OEIS A293929 records the first decimal integer requiring at least $k$ signs and reports that the sequence is believed to be infinite. [Butler–Graham–Stong, §5 (2016)](https://mathweb.ucsd.edu/~ronspubs/16_02_insert_and_add.pdf) · [OEIS A293929](https://oeis.org/A293929)

**Theorem.** For fixed $b$, let $N_L$ be uniformly distributed among all $L$-digit base-$b$ positive integers. Then

$$
\frac{C_b(N_L)}{\log_2 L}\ \longrightarrow\ 1
\quad\text{in probability as }L\to\infty.
$$

The maximum of $C_b(n)$ over $L$-digit inputs is also $(1+o(1))\log_2 L$. In particular, A293929 has a term at every index. The worst-case and typical leading term is $\log_2\log_b n$ when expressed in terms of the number itself.

## Counting the inputs that can finish early

Let $E_b(L,k)$ be the number of $L$-digit inputs that can be collapsed using at most $k$ signs. We will prove the finite bound

$$
E_b(L,k)\le (2L^2)^k b^{\,L-L/2^k+k+1}.
\tag{1}
$$

The counting argument uses one fact about addition. Given the sum and all but one of the addends, the omitted addend is determined. Knowing its block width also recovers any leading zeros.

Consider a successful run with $t$ rounds. Let $\ell_i$ be the width after round $i$, where $\ell_0=L$ and $\ell_t=1$. Round $i$ uses $r_i\ge1$ signs to form $r_i+1$ blocks. Denote the greatest of their widths by $d_i$ and break ties by choosing the leftmost longest block. Let $s=\sum_i r_i\le k$. Every cut strictly decreases the numerical value when made as part of a nontrivial partition, so each $\ell_i\le L$.

For now fix the cut positions and all the widths $\ell_i$. To specify an input following this pattern, it suffices to record the final digit and all digits **outside** the chosen longest block in each round. Starting with the final digit, subtract the recorded block values to recover the omitted addend. Pad it to the prescribed width and concatenate the blocks. Repeating backwards recovers the input uniquely.

The resulting number of recorded digits is

$$
1+\sum_{i=1}^t(\ell_{i-1}-d_i).
$$

We next bound this number for every successful pattern. Each addend is less than $b^{d_i}$, and $r_i+1\le b^{r_i}$. Therefore its sum has width $\ell_i\le d_i+r_i$. Set $u_i=d_i+r_i-\ell_i\ge0$. By the longest-block choice $d_i\ge\ell_{i-1}/(r_i+1)$, giving

$$
\ell_i\ge\frac{\ell_{i-1}}{r_i+1}-u_i.
$$

Upon iteration, each earlier $u_j$ is divided by a product of positive integers. Since each $u_j\ge0$, replacing those denominators by $1$ gives

$$
1=\ell_t\ge\frac{L}{\prod_i(r_i+1)}-\sum_i u_i
 \ge\frac{L}{2^k}-\sum_i u_i,
$$

where $\prod_i(r_i+1)\le2^{\sum_i r_i}\le2^k$. Telescoping the digit count now yields

$$
1+\sum_i(\ell_{i-1}-d_i)
=L+\sum_i r_i-\sum_i u_i
\le L+k+1-L/2^k.
$$

It remains to count patterns. The ordered positive round costs sum to at most $k$, giving at most $2^k$ lists including the empty list (sum the numbers of compositions of $1,\ldots,k$). For each list there are at most $L^k$ choices of cut positions and at most $L^k$ choices of intermediate widths. Invalid choices merely overcount. Multiplying by the number of possible recorded digit strings for each fixed pattern proves (1).

## Upper bound and asymptotics

A middle cut of an $m$-digit number gives a sum with at most $\lceil m/2\rceil+1\le(m+3)/2$ digits. Thus after $j$ middle cuts, unless the process has already finished, the width is at most $3+(L-3)/2^j$. Within $\lceil\log_2 L\rceil$ cuts it reaches at most four digits. There are finitely many such numbers for fixed $b$, and further cuts strictly decrease the value. Consequently,

$$
C_b(n)\le\log_2 L+O_b(1)
$$

for every $L$-digit input.

For the lower bound fix $0<\varepsilon<1$ and take $k=\lfloor(1-\varepsilon)\log_2 L\rfloor$. Then $L/2^k\ge L^\varepsilon$. Divide (1) by the number $(b-1)b^{L-1}$ of $L$-digit inputs. The natural logarithm of this upper bound for the fraction is at most

$$
-(\log b)L^\varepsilon+O_b\!\big((\log L)^2\big),
$$

which tends to $-\infty$. Thus the fraction of inputs finishing within this budget tends to zero. The uniform upper bound proves convergence in probability and gives the same leading term for the maximum. Unbounded cost in base ten ensures a least integer requiring at least $k$ signs for every $k$. $\square$

## How many digits does the first hard number have?

Write $D_k$ for the decimal digit length of A293929$(k)$. There are constants $c,C>0$ such that for all sufficiently large $k$,

$$
c\,2^k\le D_k\le C k^2 2^k.
$$

The middle-cut bound gives $k\le \log_2 D_k+O(1)$, proving the lower estimate. For the other direction, take $L=\lceil k^2 2^k\rceil$. Relative to all $L$-digit decimal inputs, the natural logarithm of the upper bound (1) with budget $k-1$ is at most

$$
-\frac{L}{2^{k-1}}\log 10+2(k-1)\log L+O(k)
=-2(\log 10-\log 2)k^2+O(k\log k).
$$

This is negative for large $k$, so an $L$-digit number requires at least $k$ signs, proving $D_k\le L$. In particular, $\log_2 D_k=k+O(\log k)$.

The proof counts signs spent across all rounds, including rounds with several cuts. The original paper also bounds the number of *rounds* when arbitrarily many signs can be inserted at once. Demers subsequently found the first decimal integer requiring six signs. [Original paper](https://doi.org/10.4169/amer.math.monthly.123.3.274) · [Demers (2019)](https://doi.org/10.1080/00029890.2018.1538435)
