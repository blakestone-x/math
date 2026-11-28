# A two-digit proof of the split-prime unit-root factor

Let $p=3L+1>3$ be prime and write $B=\binom{2L}{L}$, $c_j=(3j)!/(j!)^3$. In the notation of the Catalan Hankel problem the unweighted triangular-lattice moments satisfy
$$
d_N=\sum_{\lceil N/3\rceil\le j\le\lfloor N/2\rfloor}
 c_j\binom{j}{N-2j}2^{N-2j}.
$$
This follows from the Franel expansion in [Mao–Liu, equation (2.4)](https://arxiv.org/abs/2111.08775) by translation, as detailed in the prime supplement.

**Proposition.** In the ring of integers localized at $p$,
$$
 \frac{d_{p^2-1}}{d_{p-1}}\equiv 2^{pL}\binom{2L}{L}\pmod {p^2}.
$$

**Proof.** Put $h=2^Lc_L$. The terms for $d_{p-1}$ have $L\le j\le(p-1)/2$. The term $j=L$ equals $h$ and each remaining term has $p$-valuation one. In particular $d_{p-1}\equiv h\ne0\bmod p$.

For $N=p^2-1$, write $j=vp+w$, $0\le w<p$. The range begins at $Lp+L$. The valuation of $c_j$ counts the carries in tripling $j$, counted with multiplicity. If $v=L,w>L$, at least one carry leaves the low digit, causing a further carry from the high digit because $3L=p-1$. If $v>L,w>L$, there are again at least two carries. Hence, other than the endpoint $v=w=L$, a summand that survives modulo $p^2$ must have $v>L,w\le L$. Its $c_j$ has valuation one. By Lucas' theorem, when $w<L$ the low digit $p-1-2w$ in $N-2j$ exceeds $w$ and the binomial factor vanishes modulo $p$. Consequently the supplementary terms all have $w=L$ and $L<v\le(p-1)/2$.

At such $v$, $c_{vp+L}/p\equiv c_L c_v/p\bmod p$. Indeed $c_{vp}/c_v\equiv1\bmod p^2$. In $(kp)!/(k!p^k)$ each block of $p-1$ consecutive nonmultiples of $p$ has product $(p-1)!\bmod p^2$, since the reciprocals of $1,\ldots,p-1$ sum to zero in $\mathbb F_p$. Taking the quotient proves the assertion, including $3v\ge p$. Adjoining $L$ at the low digit contributes the unit $c_L\bmod p$, by the rising factorials $(3vp+1)_{3L}/(vp+1)_L^3$. The other factors satisfy
$$
 \binom{vp+L}{p^2-1-2(vp+L)}
 \equiv \binom{v}{p-1-2v},\qquad
 2^{p^2-1-2(vp+L)}\equiv 2^L 2^{p-1-2v}\pmod p.
$$
Thus the supplementary terms contribute $h(d_{p-1}-h)\bmod p^2$. At $v=w=L$ the binomial factor is one, and the contribution is $G=2^{L(p+1)}c_{pL+L}$. Since $G\equiv h^2\bmod p$, division gives
$$
 d_{p^2-1}/d_{p-1}\equiv G/h
 =2^{pL}\,c_{pL+L}/c_L\pmod{p^2}.
$$

Put $H_i=\sum_{j=1}^i1/j$. Expansion of the rising factorials at $v=L$ gives
$$
 c_{pL+L}/c_L \equiv c_L\{1+3pL(H_{3L}-H_L)\}
 \equiv c_L(1+pH_L)\pmod {p^2}.
$$
Here $3L=p-1$ and $H_{p-1}\equiv0\bmod p$. Finally,
$c_L=B\binom{p-1}L\equiv B(1-pH_L)\bmod p^2$, since $L$ is even. The harmonic factors cancel.

**Scope.** The companion unit-root evaluation identifies this factorial quantity with $2x-p/(2x)\bmod p^2$ for $p=x^2+3y^2$, $x\equiv1\bmod3$. For the signed Hankel determinant the Legendre reduction gives $a^p(1-pE)$, $a=54^L B$. Since $3^{3L}=3^{p-1}\equiv1\bmod p$, $a^p\equiv 2^{pL} B^p\bmod p^2$. The remaining determinant assertion is precisely
$$
 E\equiv (B^{p-1}-1)/p\pmod p .
$$
The proposition evaluates the comparison quantity independently of the determinant.
