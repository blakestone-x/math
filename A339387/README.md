# Comparing two sums of least residues

**Blake Stone · Proof developed with OpenAI Codex.**

For positive $n,k$, set $h(n,k)=\operatorname{lcm}(n,k)/\gcd(n,k)$. Write $[a]_b$ for the least nonnegative residue of $a$ modulo $b$. The two sequences compared by Sebastian Karlsson in 2020 are

$$
K(n)=\sum_{k=1}^n[h(n,k)]_k,\qquad N(n)=\sum_{k=1}^n[h(n,k)]_n.
$$

**Theorem.** For every $n\ge1$,

$$
N(n)-K(n)\ \ge\ \frac n2\sum_{\substack{d>1\\d^2\mid n}}\varphi(n/d).
$$

In particular, equality of the two sequences implies that $n$ is squarefree, as conjectured in A339387. Here $\varphi$ denotes Euler's totient. [A339387](https://oeis.org/A339387) · [A339384](https://oeis.org/A339384)

## An exact formula for the difference

The summands at $k=n$ coincide. For $1\le k<n$, write $d=\gcd(k,n)$, $u=k/d$, and $v=n/d$, so $1\le u<v$ and $\gcd(u,v)=1$. Then $h(n,k)=uv$, and the contributions to $N(n)$ and $K(n)$ are respectively $v[u]_d$ and $u[v]_d$.

Pair the index $k$ with $n-k$, which replaces $u$ by $v-u$ and leaves $d,v$ unchanged. The two contributions to the difference add up to

$$
v\big([u]_d+[v-u]_d-[v]_d\big)
=
\begin{cases}
n & [u]_d>[v]_d,\\
0 & [u]_d\le[v]_d.
\end{cases}
$$

Indeed, the least residue of $v-u$ is $[v]_d-[u]_d$ if that is nonnegative and otherwise is $[v]_d-[u]_d+d$. Summing this paired identity over all $k<n$ counts each original contribution twice, including the fixed index $k=n/2$ when it exists. We obtain the exact identity

$$
N(n)-K(n)=\frac n2\sum_{\substack{d\mid n\\v=n/d>1}}
\#\{1\le u<v:\gcd(u,v)=1,\ [u]_d>[v]_d\}.
$$

All these terms are nonnegative. Whenever $d>1$ and $d^2\mid n$, we have $d\mid v$, so $[v]_d=0$. Every $u$ coprime to $v$ is also coprime to $d$ and therefore has $[u]_d>0$. These divisor classes contribute the full count $\varphi(v)$, proving the bound. In particular, any prime square dividing $n$ forces strict inequality. $\square$

## The squarefree semiprime case

For $n=pq$ with primes $p<q$, only the divisor $d=p$ can contribute to the exact formula. At $d=1$ both residues are zero, and at $d=q$ one has $u<v=p<q$, so $[u]_q<[v]_q$. At $d=p$, the admissible $u$ run through all $1,\ldots,q-1$. The value $u=p-1$ attains the largest possible residue modulo $p$. Hence the two sums agree precisely when $[q]_p=p-1$, or equivalently $p\mid q+1$. This also recovers the semiprime criterion recorded in A339387. For example, $K(15)=N(15)=30$, whereas $K(35)=93$ and $N(35)=128$.
