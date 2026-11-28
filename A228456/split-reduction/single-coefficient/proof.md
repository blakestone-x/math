# A universal coefficient for the split primes of A228456

Let $p=6k+1$ be prime and $n=2k=(p-1)/3$. Put $M=\binom{2n}{n}$ and $q_p(b)=(b^{p-1}-1)/p\bmod p$ for an integer $b$ prime to $p$. Let $H_{p-1}$ be the Catalan Hankel determinant of A228456 and $S_p=(-1)^{(p-1)/2}H_{p-1}$. Define one rational formal power series, independent of the prime,
$$
 F(z)={}_2F_1(1/3,1/3;2/3;z),\qquad
 J(z)=\frac{\log F(z)}{(1-z)F(z)^2}.
$$
All denominators through degree $n$ are prime to $p$.

**Proposition.** Sun's split-prime conjecture is equivalent to each of the two identities
$$
 S_p\stackrel{?}{\equiv}54^{np}\binom{2n}{n}\pmod{p^2},
 \qquad
 [z^n]J(z)\stackrel{?}{\equiv}-M^2 q_p(M)\pmod p .
$$
The proposition is an equivalence. The assertions with question marks remain conjectural for general primes.

### Simplifying the proposed answer

Write $B=\binom{3k}{k}$ and $a=54^n M$. Section 4 of the companion Legendre reduction gives $S_p\equiv a^p(1-pE)\bmod p^2$, with $E$ defined below. The binomial congruence of Yeung as recalled in [Sun's survey, page 2](https://arxiv.org/pdf/1103.4325) gives the proposed value as
$$
 B\left(1+p\big(2q_p(2)/3-3q_p(3)/4\big)\right)\pmod {p^2}.
$$
The product defining $\binom{(p-1)/2}{n}=B$ gives, since $n$ is even,
$$
 M/B\equiv 4^n(1+p(H_{2n}-H_n/2))\pmod{p^2},
 \qquad H_j=\sum_{i=1}^j1/i .
$$
Indeed, the numerator of $2^n n! B$ is the product of the factors $p-(2i-1)$ for $1\le i\le n$. As $2n=p-1-n$, reflection gives $H_{2n}\equiv H_n\pmod p$. Also $a/B\equiv216^n=6^{p-1}\equiv1\pmod p$, so $a^p\equiv B^p\pmod{p^2}$.

For completeness, $H_n\equiv-3q_p(3)/2\pmod p$. To see this, let $\omega$ be a primitive cube root of unity. In the three residue classes $0,1,2$ modulo 3, the sums of $1/i$ over $1\le i<p$ are $H_n/3,-H_n/3,0$ modulo $p$, since $i\mapsto p-i$ exchanges classes 0 and 1. In the binomial expansion,
$$
 (1-\omega)^p\equiv 1-\omega-p\sum_{i=1}^{p-1}\omega^i/i
              \equiv(1-\omega)(1-pH_n/3)\pmod{p^2}.
$$
Squaring after division by $1-\omega$, and using $(1-\omega)^2=-3\omega$, gives the claim. Fermat quotients are additive on products modulo $p$ and $q_p(1+pu)=-u\bmod p$. Consequently
$$
 q_p(M)=q_p(B)+2nq_p(2)-H_n/2
       =q_p(B)-2q_p(2)/3+3q_p(3)/4\pmod p.
$$
Comparing the two expressions for $S_p$, the required equality is exactly $E=q_p(M)\pmod p$. Replacing $1-pq_p(M)$ by $M^{1-p}$ proves the first equivalence.

### Extracting the coefficient

Set $A(s)=P_n(1-2s)$, $C(s)=(P_{2n}(1-2s)-A(s))/(3p)$, and let $D$ be the polynomial part of $C/A$ at infinity over $\mathbb F_p$. The companion reduction gives $E=D(0)+3[s^{-1}]C'/A$. Denote all roots of $A$, with multiplicity, by $r_i$. On writing $C=DA+R$ with $\deg R<n$, the rational function $R'/A$ is $O(s^{-2})$. Hence
$$
 E=D(0)+3\sum_iD(r_i)=3\sum_{j=1}^n D_j\sum_i r_i^j\pmod p ,
$$
as $1+3n=p$.

Let $W=s(1-s)(AC'-A'C)$. The Legendre differential equation gives $W'=-nA^2/3\bmod p$, because $(2n)(2n+1)-n(n+1)=np$. We have $\deg W\le3n+1=p$, with leading coefficient $-n M C_{2n}$, and the degree of $W'$ is at most $2n$. Thus
$$
 W=-n M C_{2n}s^p+O(s^{2n+1}).
$$
Dividing by $s(1-s)A^2$ gives $(C/A)'$. Its polynomial part is $D'$. If $A^*(z)=z^n A(1/z)/M$, this proves for $1\le j\le n$ that
$$
 jD_j=\frac{n C_{2n}}M[z^{n-j}]\frac{1}{(1-z)(A^*(z))^2}.
$$
The Newton identity $\sum_i r_i^j=-j[z^j]\log A^*(z)$ now yields
$$
 E=-\frac{3n C_{2n}}M[z^n]\frac{\log A^*(z)}{(1-z)(A^*(z))^2}.
$$

The leading coefficient $C_{2n}=(4n)!/(3p((2n)!)^2)$. Removing the single factor $p$ from $(4n)!=(p+n-1)!$ and applying Wilson's theorem shows that $3n C_{2n}/M\equiv(n!)^6$. Here $(2n)!(n)!\equiv-1$ since $n$ is even, whence $(n!)^6\equiv M^{-2}$. Finally the reversed Legendre expansion gives
$$
 A^*(z) = \sum_{j=0}^n\frac{(-n)_j^2}{(-2n)_j j!}z^j.
$$
Since $-n\equiv1/3$ and $-2n\equiv2/3\pmod p$, these coefficients agree with $F$ through degree $n$. Substitution gives $E=-M^{-2}[z^n]J(z)\bmod p$, proving the second equivalence.

### A companion coefficient

The same denominator without the logarithm admits the exact evaluation
$$
 [z^n]\frac{1}{(1-z)F(z)^2}\equiv M^2\pmod p.
$$
Write $U=A^*$, and set $V={}_2F_1(n+1,n+1;2n+2;z)$. The two functions $U$ and $z^{2n+1}V$ solve the same hypergeometric differential equation. Abel's Wronskian formula, with leading terms at zero fixing the constant, gives over the rationals
$$
 \frac{1}{(1-z)U^2}=\left(1+\frac{z}{2n+1}\frac{d}{dz}\right)\frac{V}{U}.
$$
The coefficients of $1/U$ through degree $n$ are $p$-integral. Those of $V$ are $p$-integral through degree $n-1$, and the denominator of $[z^n]V$ contains exactly one factor of $p$. Since $1+n/(2n+1)=p/(2n+1)$, the coefficient of degree $n$ in the displayed identity is congruent to
$$
 \frac{p}{2n+1}[z^n]V
 =\frac{((2n)!)^3}{(n!)^3(p-1)!}
 \equiv M^2\pmod p,
$$
where the last step uses $(p-1)!\equiv(2n)!n!\equiv-1\pmod p$. Thus the open identity also asks whether
$$
 [z^n]\frac{\log F(z)+q_p(M)}{(1-z)F(z)^2}\equiv0\pmod p.
$$

### Computation

The accompanying Python program calculates all coefficients with exact integer arithmetic. It uses Newton inversion and packs polynomial coefficients with sufficient separation to multiply them without carry interference. For any positive upper bound $N$ it checks the coefficient identity for every prime $p\equiv1\pmod6$ through $N$. The run `python verify.py 25000` found agreement at all 1,371 split primes through 25,000.
