# An exact maximum preperiod for modular Ducci sequences

**Blake Stone · Proof developed with OpenAI Codex.**

The full manuscript gives the number of starting tuples entering a cycle at each step, for every width and modulus. It includes a finite-ring proof and recovers the conjectured maximum. [Manuscript (PDF)](Ducci-preperiods.pdf) · [LaTeX source](Ducci-preperiods.tex) · [Counting formula and second proof](distribution.md) · [Elementary recursion](elementary-distribution.md) · [Independent computational checks](verify-distribution.py)

Mark L. Lewis and Shannon M. Tefft conjectured that their upper bound in Theorem 1(3) of *The maximum length for Ducci sequences on $\mathbb Z_m^n$ when $n$ is even* is always attained. Their paper appeared in *Integers* 26 (2026), A17. The equality follows by projecting the Ducci operator onto a cyclic group ring whose augmentation ideal has known nilpotency index. We give the short deduction and a direct proof of the group-ring calculation. [Lewis and Tefft, p. 2](https://math.colgate.edu/~integers/aa17/aa17.pdf) · [Clark and Schauz, §4.3, Lemma 4.6 and Theorem 4.7](https://arxiv.org/pdf/2201.02763)

## Statement and proof of the conjecture

For $m\ge2$ and $n\ge1$, the modular Ducci operator replaces each coordinate of a cyclic $n$-tuple over $\mathbb Z/m\mathbb Z$ with the sum of that coordinate and the next. Its **preperiod** is the number of steps before the trajectory first enters a cycle. Let $L_m(n)$ denote the largest preperiod among all starting tuples.

Suppose $n$ is even, $n=p^k n_1$ and $m=p^\ell m_1$, where $p$ is prime, $k,\ell\ge1$, $p\nmid n_1m_1$ and $\gcd(n_1,m_1)=1$. Then

$$
L_m(n)=p^{k-1}\bigl(\ell(p-1)+1\bigr).
$$

**Proof.** Number the coordinates so that the cyclic shift is multiplication by $x$. Then Ducci is multiplication by $1+x$ in $(\mathbb Z/m\mathbb Z)[x]/(x^n-1)$ and the unit polynomial $1$ represents a single nonzero cell. Put $N=p^k$. Reduce coefficients modulo $p^\ell$ and send $x$ to $-y$ in

$$
R=(\mathbb Z/p^\ell\mathbb Z)[y]/(y^N-1).
$$

This defines a surjective homomorphism since $n$ is even and $N\mid n$. It sends the unit seed and its Ducci iterates to $1,(1-y),(1-y)^2,\ldots$. The nilpotency index of $1-y$ is exactly $H=p^{k-1}(\ell(p-1)+1)$ by the cyclic augmentation-ideal theorem. Thus the projected sequence first reaches zero at step $H$. No earlier projected value can be periodic, since every projected value eventually reaches zero. The original trajectory therefore takes at least $H$ steps to enter a cycle. Lewis and Tefft's Theorem 1(3) supplies the matching upper bound. $\square$

The algebraic input predates the conjecture. Clark and Schauz give the exact cyclic group-ring statement in the proof of their Theorem 4.7 and derive it from R. M. Wilson's congruence (2006), or alternatively from C. S. Weisman's binomial congruences (1977). The deduction above identifies the quotient to which that statement applies. [Clark and Schauz, §4.3](https://arxiv.org/pdf/2201.02763)

## A direct proof of the nilpotency index

Let $t=y-1$, $d=p^{k-1}$, $w=N-d$, and $H=N+(\ell-1)w$. The ring is a free module over $\mathbb Z/p^\ell\mathbb Z$ with basis $1,t,\ldots,t^{N-1}$, because its defining polynomial $(1+t)^N-1$ is monic of degree $N$. Reduce powers using

$$
t^N=-\sum_{j=1}^{N-1}\binom Nj t^j .
$$

For $1\le j<N$, $v_p\binom Nj=k-v_p(j)$. Indeed, $\binom Nj=(N/j)\binom{N-1}{j-1}$ and the latter binomial factor is a $p$-unit: modulo $p$ the coefficients of $(1+t)^{N-1}=(1+t^N)/(1+t)$ are all $\pm1$.

Assign weight $v_p(b)w+i$ to an integer monomial $bt^i$ with $b\ne0$. A term on the right side of the reduction has weight at least $N$, with equality exactly at $j=d$. To see this, when $k-v_p(j)=1$, $j$ is a positive multiple of $d$ and $w+j\ge N$, with equality only at $j=d$. When $k-v_p(j)\ge2$, its weight is at least $2w+j>N$ since $2w\ge N$. Thus repeated reduction strictly lowers the exponent of $t$ and never lowers the weight. In a final term with $i<N$ and $p^\ell\nmid b$, the greatest possible weight is $(\ell-1)w+N-1=H-1$. All branches in the reduction of $t^H$ therefore vanish modulo $p^\ell$.

Starting instead from $t^{H-1}$, any branch which increases the weight also vanishes. There is exactly one path preserving weight: choose $j=d$ at each substitution. Each substitution decreases the exponent by $w$ and adds one factor of $p$ to the coefficient. After $\ell-1$ substitutions it ends at $t^{N-1}$ with a coefficient of valuation exactly $\ell-1$. This nonzero basis coefficient proves $t^{H-1}\ne0$. For $\ell=1$ the same assertion is simply the nonvanishing of the basis element $t^{N-1}$. This proves the claimed index.

## The formula for every width and modulus

The same decomposition gives the upper bound directly and covers all $n$ and $m$. For each prime power $p^\ell\parallel m$ and even $n$, set $k=v_p(n)$ and define

$$
B_{p,\ell}(n)=
\begin{cases}
1,& k=0,\\
p^{k-1}\bigl(\ell(p-1)+1\bigr),&k\ge1.
\end{cases}
$$

For all $m\ge2$ one has

$$
L_m(n)=
\begin{cases}
\max_{p^\ell\parallel m}B_{p,\ell}(n),& n\text{ even},\\
v_2(m),& n\text{ odd}.
\end{cases}
$$

To prove this, first fix the modulus $p^\ell$. For even $n$, substitute $x=-y$ in the full ring and write $n=Nr$, $N=p^k$, $p\nmid r$. Factor

$$
y^n-1=(y^N-1)C(y),\qquad C(y)=1+y^N+\cdots+y^{(r-1)N}.
$$

The factors generate the unit ideal since $C(y)\equiv r\pmod{y^N-1}$ and $r$ is a unit. On the component defined by $C$, multiplication by $1-y$ is invertible because $C(1)=r$ is a unit. If $C=1$ this component is absent. On the component defined by $y^N-1$, the calculation above gives nilpotency index $B_{p,\ell}(n)$ for $k\ge1$. For $k=0$ one has $N=1$ and $1-y=0$ on this nonzero component, giving index one. In the product ring the invertible component is periodic from the start, while the unit seed in the nilpotent component first becomes periodic at zero. Consequently $B_{p,\ell}(n)$ is the exact maximum preperiod, attained by the unit seed.

For odd $n$ and odd $p$, the identity $(1+x)(1-x+\cdots+x^{n-1})=1+x^n=2$ in the cyclic ring makes the Ducci operator invertible. For odd $n$ and $p=2$, factor $x^n-1=(x-1)C_1(x)$. Here $C_1(1)=n$ is odd, so the factors are comaximal, and $C_1(-1)=1$, so $1+x$ is a unit on the $C_1$ component whenever that component is present. On the $x-1$ component it acts as multiplication by two, of nilpotency index $\ell$. Finally, the Chinese remainder theorem on the coefficient modulus makes the full preperiod the maximum of its prime-power components. The common unit seed attains all their maxima. $\square$

For example $L_9(6)=5$, $L_{25}(10)=9$, and $L_{72}(12)=8$. The odd-width formula was proved previously by Lewis and Tefft. For even widths, their Theorem 1 already established the coprime case, the single common prime with $\ell=1$, the upper bound in the general single-prime case, and the maximum decomposition for several common primes. The matching lower bound is the missing step in the conjectured equality. Dular asks for the largest preperiod of the modular adjacent-sum map in §7 of *Cycles of Sums of Integers*. His Definition 1.3 uses a positive starting index, so under that convention the answer is $\max(1,L_m(n))$. Lewis and Tefft count from index zero. [Lewis and Tefft, odd widths](https://arxiv.org/abs/2403.05319) · [Dular, §7](https://orbilu.uni.lu/bitstream/10993/57748/1/1905.01765.pdf)

## Which tuples already lie on cycles?

The same decomposition gives a coordinate test. Number the entries $a_0,\ldots,a_{n-1}$ in cyclic order. For even $n$ a tuple is periodic from its first step exactly when, for every $p^\ell\parallel m$, with $N=p^{v_p(n)}$, one has

$$
\sum_{\substack{0\le j<n\\ j\equiv h\pmod N}}(-1)^j a_j\equiv0\pmod{p^\ell}
\qquad(0\le h<N).
$$

Indeed, these sums are the coefficients of its image under $x\mapsto-y$ modulo $y^N-1$. Exactly the zero vector is periodic on that component, and every vector is periodic on the complementary component. The $N$ congruences on disjoint coordinate classes are independent, each with a unit coefficient. Thus the number of periodic tuples at even width is
$\prod_{p^\ell\parallel m}(p^\ell)^{n-p^{v_p(n)}}$.
For odd $n$, the only condition is $\sum_j a_j\equiv0\pmod{2^{v_2(m)}}$, giving $m^n/2^{v_2(m)}$ periodic tuples. Dular treated prime moduli in Theorems 6.4 and 6.6, and Lewis and Tefft proved the odd-width result for arbitrary moduli. [Dular, §6](https://orbilu.uni.lu/bitstream/10993/57748/1/1905.01765.pdf) · [Lewis and Tefft, odd widths](https://arxiv.org/abs/2403.05319)

## Verification

Run `python3 verify.py` to check preperiods against direct orbit enumeration for small modulus-width pairs, enumerate all seeds in a smaller collection, and check the two boundary powers of $1-y$ across larger prime-power cases. The proof applies to every admissible input. These computations supply independent checks on the preperiod convention and off-by-one boundaries.
