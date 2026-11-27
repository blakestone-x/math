# When does the period of a two-tap cellular automaton divide its width?

**Blake Stone · Proof developed with OpenAI Codex.**

Consider a ring of $n$ cells over a finite field $K$ of characteristic $p$. Each time step adds two shifted configurations with nonzero weights $\alpha,\beta\in K$. For distinct integer shifts $u,v$, this is multiplication by $f(x)=\alpha x^u+\beta x^v$ in $K[x,x^{-1}]/(x^n-1)$. Write $P$ for the eventual period starting from one unit cell and zeros elsewhere. Every other seed has period dividing $P$, since multiplying an equality $f^{s+P}=f^s$ by a seed gives the same equality on its orbit. Thus $P$ is also the maximum cycle length.

## Classification

Write $n=p^a m$ with $p\nmid m$. Suppose $m>2$ and $\gcd(v-u,m)=1$. View all finite fields inside a fixed algebraic closure of $\mathbb F_p$. Then

$$
P\mid n \quad\Longleftrightarrow\quad
m+1=q=p^k\text{ for some }k\ge1
\quad\text{and}\quad \alpha,\beta\in\mathbb F_q.
$$

For weights in the prime field the coefficient condition holds automatically. In an extension field $K=\mathbb F_{p^r}$ it requires both weights to lie in $\mathbb F_{p^{\gcd(k,r)}}$.

When these conditions hold, set $B=p^a/\gcd(p^a,u,v)$. For $q\ge5$ the exact period is

$$
P=(q-1)B.
$$

In particular $P=n$ precisely when $a=0$ or at least one of $u,v$ is prime to $p$. For $q=4$, the same answer holds except when both $u+v\equiv0\pmod3$ and $\beta=\alpha^2$, in which case $P=B$. The two smaller values $m=1,2$ are treated below.

## Reduction to an affine image of the roots of unity

Let $H$ be the group of all $m$th roots of unity, and put $S=H\cup\{0\}$. Extending scalars preserves equality of configurations. In a splitting field, $x^n-1$ is the product of the pairwise coprime powers $(x-z)^{p^a}$ for $z\in H$. On a local factor with $f(z)=0$, multiplication by $f$ is nilpotent. On each other factor, $f$ is a unit whose order modulo $x-z$ is the multiplicative order of $f(z)$, prime to $p$. Raising a unit of the form $1+h$ with $(x-z)\mid h$ to $p^a$ gives $1$ on the local factor. By the Chinese remainder theorem, the prime-to-$p$ part of $P$ is therefore the least common multiple $L$ of the orders of the nonzero $f(z)$, and the $p$-part of $P$ divides $p^a$.

It follows that $P\mid n$ if and only if $f(z)\in S$ for every $z\in H$. Multiplication by $z^{-u}\in H$ preserves membership in $S$. Since $z\mapsto z^{v-u}$ permutes $H$, the condition is equivalent to

$$
\alpha+\beta H\subseteq S.
$$

**Affine-image lemma.** If $|H|=m>2$ and $\alpha,\beta\ne0$, this inclusion holds exactly when $S$ is a field containing $\alpha$ and $\beta$.

To see this, first note that $\sum_{h\in H}h=0$. If the affine image omitted zero, it would equal $H$ by cardinality. Summing both sets would give $m\alpha=0$, which is impossible. Thus $-\alpha/\beta\in H$, and $\alpha+\beta H=\alpha(1-H)$. For $s,t\in H$ with $s\ne t$, $s-t=s(1-t/s)\in\alpha^{-1}H$. The difference set $D=H-H$ contains a nonzero element and is invariant under multiplication by $H$. Hence
$D=\alpha^{-1}H\cup\{0\}$ and $|D|=m+1$.

Fix $x=b-c\in D$. Both $b-H$ and $c-H$ are $m$-element subsets of $D$. Their intersection has size at least $m-1$. Each point of this intersection gives different $h,h+x\in H$, since $b-h'=c-h$ implies $h'=h+x$. For any $x,y\in D$, at least $m-1$ possible $h\in H$ satisfy $h+x\in H$ and at least $m-1$ satisfy $h-y\in H$. As $2(m-1)>m$, some $h$ satisfies both. Subtracting gives $x+y\in D$. Therefore $D$ and $S=\alpha D$ are additive groups. The nonzero elements of $S$ already form a multiplicative group containing $1$, so $S$ is a finite field. Now $D=H-H\subseteq S$ and both sets have the same size. Thus $D=S$ and $\alpha D=S$ implies $\alpha\in S$. The relation $-\alpha/\beta\in H$ gives $\beta\in S$. Conversely, a field containing the weights is closed under the required affine map. This proves the lemma and the divisibility classification.

## Generation of the full multiplicative group

Assume the classification conditions, so $H=\mathbb F_q^*$. Choose $c$ with $c(v-u)\equiv u\pmod m$. Set $w=(\beta/\alpha)z^{v-u}$ and $C=\alpha(\beta/\alpha)^{-c}$. As $z$ runs through $H$, the nonzero eigenvalues run through the values

$$
g(w)=Cw^c(1+w),\qquad w\in\mathbb F_q^*\setminus\{-1\}.
$$

Suppose first that $q\ge5$. If these values generated a proper subgroup of $H$, they would all lie in a subgroup $J$ of prime index $\ell\mid q-1$. For every admissible $w$, its inverse is also admissible, and
$g(w)/g(w^{-1})=w^{2c+1}\in J$. A generator of $H$ is admissible since $q-1>2$. It follows that $\ell\mid 2c+1$, so $\ell\ge3$. But

$$
\frac{g(w)^2}{w^{2c+1}}=C^2(w+2+w^{-1})\in J .
$$

Every value on the right has at most two preimages by the quadratic equation for $w$. All $q-2$ admissible elements give nonzero values, forcing $|J|\ge(q-2)/2>(q-1)/3$, a contradiction. Thus the nonzero eigenvalues together generate $H$ and $L=q-1$. The proof concerns their collective orders and does not require any individual eigenvalue to be primitive.

For $q=4$ the two admissible $w$ have order three and satisfy $1+w=w^2$. Their images are $Cw^{c+2}$. If $c+2\not\equiv0\pmod3$, their ratio has order three. Otherwise both images equal $C$, which has order three unless $C=1$. Here $c\equiv1$ is equivalent to $u+v\equiv0\pmod3$, and under this congruence $C=1$ is equivalent to $\beta=\alpha^2$.

## The exact power of the characteristic

This step works for every $m$ if at least one root survives, meaning $f(z)\ne0$ for some $z\in H$. Put $t=\min(v_p(u),v_p(v))$, using $v_p(0)=\infty$. Since the coefficient field is perfect, write $f=G^{p^t}$ where $G=A x^U+D x^V$, $U=u/p^t$, $V=v/p^t$, and at least one of $U,V$ is nonzero modulo $p$. Taking $p^t$-th powers preserves the orders of the residue-field elements. Thus their least common multiple for $G$ is also $L$.

At a surviving root $z$, the order of vanishing of $G-G(z)$ is positive and strictly less than $p$. Indeed,
$G'=x^{U-1}(A U+D V x^{V-U})$. If exactly one of $U,V$ vanishes modulo $p$, this derivative is nonzero on the torus. If $U\equiv V\not\equiv0\pmod p$, then $G'=U G/x$, nonzero at a survivor. In the remaining case $U,V$ are both nonzero and distinct modulo $p$. Here $p$ is odd and any zero of $G'$ is simple, because $p\nmid V-U$. At such a point the nonzero second derivative gives vanishing order exactly two for $G-G(z)$. These arguments apply equally to Laurent monomials because $z\ne0$.

Since $p\nmid L$, the vanishing order of $G^L-1$ at $z$ is the same as that of $G-G(z)$. Raising to $p^j$ multiplies this order by $p^j$. A multiplicity between $1$ and $p-1$ reaches $p^a$ for the first time at $j=a$. Consequently the eventual period for $G$ is $L p^a$. Taking every $p^t$-th step yields the period $L p^{\max(a-t,0)}=LB$ for $f$. If every root is killed the map is nilpotent and $P=1$.

When $m=1$, the only residue is $\alpha+\beta$. When $m=2$, necessarily $p$ is odd and the residues are $\alpha+\beta$ and $(-1)^u\alpha+(-1)^v\beta$. If all these residues vanish, $P=1$. Otherwise $P=LB$ with $L$ the least common multiple of their nonzero multiplicative orders. These formulas include width one.

## Examples and necessity of the stride hypothesis

- Over $\mathbb F_2$, rule 90 has $(u,v)=(-1,1)$. For $n>1$, its maximum eventual period equals $n$ exactly at widths $n=2^a(2^k-1)$ with $k\ge3$. If $m=3$ its period is $2^a$, and if $m=1$ the rule is nilpotent. The binary adjacent-sum rule $1+x$ instead has full period already for $k=2$.
- Over $\mathbb F_5$, opposite weights can kill the constant mode without reducing the maximum period. For $n=20$, $f=1-x$ has $P=20$. For the same width $f=1-x^5$ has $P=4$. Both satisfy the stride hypothesis.
- Over $\mathbb F_4$, write $\omega^2+\omega+1=0$. At width seven, $f=\omega+x$ has period that does not divide seven since $\omega\notin\mathbb F_8$. At width fifteen its maximum period is fifteen since $\mathbb F_4\subset\mathbb F_{16}$.
- A connected graph need not satisfy the stride hypothesis. Over $\mathbb F_2$ take $n=21$ and $f=x+x^4$. The shift by one connects the ring, but $\gcd(4-1,21)=3$. For each $z^{21}=1$, $z^3\in\mathbb F_8^*$, so $1+z^3\in\mathbb F_8$ and $f(z)\in\mu_{21}\cup\{0\}$. Thus $P\mid21$. For a primitive $z$ of order 21 the two surviving eigenvalues $f(z),f(z^{-1})$ have ratio $z^5$, which has order 21. Hence $P=21$ even though $22$ is not a power of two.

## Prior work and verification

Martin, Odlyzko and Wolfram developed the cyclic-polynomial representation for additive automata and analyzed rule 90 explicitly in Section 3 of *Algebraic Properties of Cellular Automata* (1984). For the ordinary binary Ducci rule $1+x$, Ehrlich proved that the unit seed has maximum period, that the width divides the period off the power-of-two widths, and that doubling the width doubles the period there (Theorems 1, 3 and 4). In particular, his results already imply the direct Mersenne-width equality for $1+x$ by Corollary 3 and Theorem 3. Calkin, Stevens and Thomas gave the binary adjacent-sum minimal-polynomial criterion in 2005. Breuer and Shparlinski studied lower bounds for its period at general odd widths. Dular studied modular adjacent sums, including a width-dependent period bound over prime fields in Proposition 2.5. The arbitrary weights, extension-field membership condition, and coprime stride are the scope of the classification here. Priority for the combined theorem has not been established.

- [O. Martin, A. M. Odlyzko and S. Wolfram, *Algebraic Properties of Cellular Automata*](https://content.wolfram.com/sw-publications/2020/07/algebraic-properties-cellular-automata.pdf)
- [A. Ehrlich, *Periods in Ducci's n-Number Game of Differences*](https://www.fq.math.ca/Scanned/28-4/ehrlich.pdf)
- [N. J. Calkin, J. G. Stevens and D. M. Thomas, *A Characterization for the Length of Cycles of the N-Number Ducci Game*](https://doi.org/10.1080/00150517.2005.12428392)
- [B. Dular, *Cycles of Sums of Integers*](https://orbilu.uni.lu/handle/10993/57748)
- [F. Breuer and I. E. Shparlinski, *Lower Bounds for Periods of Ducci Sequences*](https://doi.org/10.1017/S0004972719001187)

Run `python3 verify.py` for an independent check by direct evolution of cell configurations. It compares every pair of nonzero weights over fields of sizes $2,3,4,5,7$, widths $1$ through $32$, and the listed shifts and stride gaps satisfying the hypothesis. It checks both the divisibility decision and the exact period whenever it divides the width, including the width-21 counterexample separately.
