# How many modular Ducci tuples enter a cycle at each step?

Let $D$ send a cyclic $n$-tuple over $\mathbb Z/m\mathbb Z$ to its adjacent sums, with $n\ge1$ and $m\ge2$. For a starting tuple $v$, let $\tau(v)$ be the least $h\ge0$ for which $D^h v$ lies on a cycle. This note gives the number
$$
A(h)=\#\{v:\tau(v)\le h\}
$$
for every integer $h\ge0$. Taking $A(-1)=0$, the number entering a cycle **exactly** at step $h$ is $A(h)-A(h-1)$. The formula uses the additive decomposition of the complex $K$-group of a lens space, computed by Mahammed and Yanagida. The indices in that decomposition give a short sum of minima for the Ducci counts. [Yanagida, Theorems 5.3 and 6.1](https://doi.org/10.18910/11698)

## The distribution

For every prime power $p^\ell\parallel m$, put $k=v_p(n)$, $q=p^k$, and $r=\min(k,\ell)$. Define
$$
F_{p,k,\ell}(h)=(\ell-r)\min(h,1)
+\sum_{j=1}^r\min\!\left(h,\ p^{k-j}\bigl(1+(p-1)(\ell-j+1)\bigr)\right).
\tag{1}
$$

**Theorem.** For even $n$,
$$
A(h)=\prod_{p^\ell\parallel m}p^{\ell(n-p^{v_p(n)})+F_{p,v_p(n),\ell}(h)}.
\tag{2}
$$
For odd $n$, put $b=v_2(m)$. Then
$$
A(h)=\frac{m^n}{2^{b-\min(b,h)}}.
\tag{3}
$$
In particular, $A(0)$ counts the periodic tuples. If $p\nmid n$, equation (1) reads $F_{p,0,\ell}(h)=\ell\min(h,1)$. The odd-width formula includes $n=1$, where $D$ is multiplication by two.

For example, if $n=4$ and $m=8$, then $F(h)=\min(h,1)+\min(h,3)+\min(h,8)$ and $A(0)=1$. For $h=0,1,\ldots,8$ the numbers entering a cycle at precisely that step are $1,7,24,96,128,256,512,1024,2048$. Their sum is $8^4$.

## Reduction to a cyclic difference operator

Choose cyclic coordinates so that shifting is multiplication by $x$ in $(\mathbb Z/p^\ell\mathbb Z)[x]/(x^n-1)$. For even $n$ set $x=-y$. The Ducci operator then becomes multiplication by $1-y$. Write $n=qu$, where $q=p^k$ and $p\nmid u$. In $y^n-1=(y^q-1)C(y)$, one has $C=1+y^q+\cdots+y^{(u-1)q}\equiv u\pmod{y^q-1}$. The two factors are comaximal. Since $C(1)=u$ is a unit, $1-y$ is invertible on the $C$ component, whose cardinality is $p^{\ell(n-q)}$. If $u=1$, this factor has one element. On the $y^q-1$ component, $\Delta=y-1$ is nilpotent because $\Delta^q=0$ modulo $p$. A tuple reaches a cycle by step $h$ exactly when its component there belongs to $\ker\Delta^h$. The sign of $\Delta$ does not affect this kernel.

For odd $n$ and odd $p$, the geometric sum gives $(1+x)(1-x+\cdots+x^{n-1})=2$ in the cyclic ring, so all tuples are periodic. For odd $n$ and $p=2$, factor $x^n-1=(x-1)C_1(x)$. Here $C_1(1)=n$ is a unit, and $C_1(-1)=1$. Thus $1+x$ is invertible on the component of rank $n-1$ and acts by multiplication by two on the component of rank one. Its nilpotent component has exactly $2^{\min(\ell,h)}$ states killed by step $h$. Taking products over the coefficient prime powers proves (3), and reduces (2) to computing the local kernel.

The remaining local calculation has two proofs. The elementary argument works directly with the integral group ring. The following argument derives the same counts from the published lens-space decomposition. [Elementary proof](elementary-distribution.md)

## The integral cokernel and the lens space

For $h\ge1$, the integral cokernel of $\Delta^h$ on $\mathbb Z[y]/(y^q-1)$ is
$$
Q_h=\mathbb Z[t]/\bigl(t^h,(1+t)^q-1\bigr),\qquad t=y-1.
$$
Reduction modulo $p^\ell$ gives its cokernel on the finite module $(\mathbb Z/p^\ell\mathbb Z)^q$. An endomorphism of a finite group has equally large kernel and cokernel, so we need $|Q_h/p^\ell Q_h|$. For $h=0$ the kernel of the identity has one element. For $k=0$ and $h\ge1$ the whole component is killed in one step.

Take $k\ge1$. Put $d=h-1$. The complex $K$-ring of the standard lens space $L^d(q)=S^{2d+1}/C_q$ is $Q_h$. To see the presentation, realize it as the unit-circle bundle of the $q$th tensor power of the tautological line bundle on $\mathbb{CP}^d$ (or its dual). Here $K^0(\mathbb{CP}^d)=\mathbb Z[t]/(t^{d+1})$ with $1+t$ the line bundle, and $K^1(\mathbb{CP}^d)=0$. The complex $K$-theory Gysin sequence gives the cokernel of multiplication by the Euler class $1-(1+t)^q$ up to a unit. The rank-one free summand contributes $\ell$ to $\log_p |Q_h/p^\ell Q_h|$. For $d=0$ it is the whole group.

Yanagida's Theorem 6.1 gives the torsion summands for $k\ge2$. For $1\le i\le\min(d,p^k-1)$, find $s$ with $p^s\le i<p^{s+1}$, and put $w_s=p^{s+1}-p^s$. There is one cyclic factor of order $p^{E_i}$ for each such $i$, where
$$
E_i=k-s+\left\lfloor\frac{d-i}{w_s}\right\rfloor .
\tag{4}
$$
This uses the definition of $z_s$ at the beginning of Yanagida's §4. In particular it uses the orders of the generators in the additive decomposition, which can differ from the orders of the monomials $t^i$. [Yanagida, §§4–6, pp. 528–536](https://ir.library.osaka-u.ac.jp/repo/ouka/all/11698/ojm13_03_06.pdf)

For $k=1$ the same orders follow directly from the cyclotomic ring $\mathcal O=\mathbb Z[\zeta_p]$. Write $\pi=\zeta_p-1$. Evaluation at $y=\zeta_p$ identifies the augmentation ideal $(y-1)$ in $\mathbb Z[y]/(y^p-1)$ with $\pi\mathcal O$, since the annihilator of $y-1$ is generated by $1+y+\cdots+y^{p-1}$. It identifies $(y-1)^h$ with $\pi^h\mathcal O$. Thus the torsion summand of $Q_h$ is $\mathcal O/\pi^d\mathcal O$. Its reduction modulo $p^\ell$ has cardinality $p^{\min(d,\ell(p-1))}$, since $p\mathcal O=\pi^{p-1}\mathcal O$ and $\mathcal O/\pi\mathcal O=\mathbb F_p$. Adding the free summand gives (1) for $k=1$.

## Summing the invariant factors

For $k\ge2$ and $h\ge1$, (4) gives $\ell+\sum_i\min(\ell,E_i)$. Write $z_+=\max(z,0)$ and $a_s=\min(\ell,k-s)$ for $0\le s<k$. The indices $p^s\le i<p^{s+1}$ contribute
$$
a_s\min\{w_s,(h-p^s)_+\}
+\min\{(\ell-a_s)w_s,(h-p^{s+1})_+\}.
\tag{5}
$$
Indeed, count one for each integer $b$ with $1\le b\le\ell$ and $E_i\ge b$. For $b\le a_s$, allowable indices are exactly those in the block with $i<h$. If $b=a_s+c$ with $c\ge1$, then $a_s=k-s$ and the condition is $i+cw_s<h$. As $c$ ranges from 1 through $\ell-a_s$, the translated blocks are consecutive and start at $p^{s+1}$. This proves (5).

To evaluate the sum, let $S_s=(h-p^s)_+$ and $T_s=p^{s+1}+(\ell-a_s)w_s$. The expression (5) becomes
$$
a_s S_s+(1-a_s)S_{s+1}-(h-T_s)_+.
$$
At an internal junction $1\le s<k$, the coefficient of $S_s$ from adjacent blocks is $1+a_s-a_{s-1}$. If $a_s=a_{s-1}$, then $a_{s-1}=\ell$ and the term $-(h-T_{s-1})_+=-S_s$ cancels it. In the other case $a_s=a_{s-1}-1$ and the coefficient is zero. The terminal coefficient of $S_k$ is $1-a_{k-1}=0$. What remains after summing (5) is
$$
r(h-1)_+-\sum_{s=k-r}^{k-1}(h-T_s)_+ .
$$
For these last $r$ indices put $j=k-s$. Then $T_s=p^{k-j}(1+(p-1)(\ell-j+1))$. The free summand contributes $\ell$, and for $h\ge1$ the identity $\min(h,T)=h-(h-T)_+$ gives exactly (1). This finishes the proof of (2).

The counts also apply to one specified cycle. If that cycle has length $c$, its basin contains $c\,[A(h)-A(h-1)]/A(0)$ tuples of preperiod exactly $h$. In the above decompositions the invertible components form a permutation on $A(0)$ periodic states, and the nilpotent components have the same count for each such state.

## A uniformly random starting tuple

Let $T$ be the preperiod of a uniformly chosen tuple and let $H$ be the largest possible preperiod. For every width and modulus, at least half of all tuples attain $H$, and the average preperiod is strictly greater than $H-1$.

In fact, for any endomorphism $D$ of a finite group $G$, the images $G_i=D^i(G)$ form a decreasing chain. The eventual image $G_H$ is exactly the set of periodic elements, and $H$ is the first index where two consecutive images agree. The map $D^i:G\to G_i$ has equal-sized fibers. Thus, for integers $0\le s\le H$,
$$
\Pr(H-T\ge s)=\frac{|G_H|}{|G_{H-s}|}\le 2^{-s},
$$
because each of the last $s$ strict inclusions has index at least two. Summing for $1\le s\le H$ gives $\mathbb E(H-T)<1$. This also covers $H=0$.

For even $n$, modulus $p^\ell$ and $k=v_p(n)\ge1$, the exact law is sharper. Let $H_2$ be the second largest length among the terms $\min(h,L)$ in (1), counting multiplicities, and use $H_2=0$ if there is just one term. The largest length $H=p^{k-1}(1+(p-1)\ell)$ occurs once. For $0\le s\le H-H_2$ the single longest term accounts for the entire decrease from $F(H)$ to $F(H-s)$. Hence $\Pr(H-T\ge s)=p^{-s}$ on this range, and the same probability is at most $p^{-s}$ for every larger integer $s\ge0$. In particular, exactly $1-1/p$ of the tuples attain the maximum. For fixed $p,\ell$, as $k\to\infty$, the gap $H-H_2$ tends to infinity, so the shortfall converges to the geometric law with mass $(1-1/p)p^{-s}$ at each $s\ge0$ and mean $1/(p-1)$. The geometric upper bound justifies convergence of the means.

For width $6$ modulo $9$, formula (1) gives lengths $5$ and $1$. Exactly two-thirds of all $9^6$ tuples take the full five steps, and only $1/729$ of them start on a cycle.

## Sources and verification

- Syun-ichi Yanagida, *The additive structure of* $G^*(L^n(p^k))$, Osaka Journal of Mathematics **13** (1976), 523–536. Theorem 6.1 appears on p. 536. Yanagida credits an independent computation by N. Mahammed, *K-théorie des espaces lenticulaires*, C. R. Acad. Sci. Paris Sér. A **272** (1971), 1363–1365. [Yanagida's paper](https://doi.org/10.18910/11698)
- Mark L. Lewis and Shannon M. Tefft, *The maximum length for Ducci sequences on* $\mathbb Z_m^n$ *when* $n$ *is even*, Integers **26** (2026), A17. Their length convention is the one used here. [Journal article](https://math.colgate.edu/~integers/aa17/aa17.pdf)
- Run `python3 verify-distribution.py` from this directory to reproduce the exhaustive comparison across 68 modulus-width pairs (274,138 configurations) and the matrix-kernel checks for 4,452 powers across 119 prime-power parameter triples. [Verifier](verify-distribution.py)
