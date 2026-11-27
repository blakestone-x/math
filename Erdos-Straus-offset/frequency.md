# The first negative Jacobi symbol predicts almost every Tier 3 minimum

**Blake Stone · Proof developed with OpenAI Codex.**

Call $p$ a *Tier 3 prime* if $p\equiv1\pmod{12}$ and no prime congruent to $2\pmod3$ divides $(p+3)/4$. In a decomposition $4/p^2=1/x+1/y+1/z$ into positive unit fractions, the offset of $x$ is $4x-p^2$. Let $T(X)$ count all Tier 3 primes $p\le X$, and let $N_r(X)$ count those whose least offset is $r$. A prime without a decomposition contributes to $T(X)$ and to none of the $N_r(X)$.

**Theorem.** For a set of Tier 3 primes of relative density one, a decomposition exists and its least offset is the first positive $a\equiv3\pmod4$ for which $(p/a)=-1$. For a fixed positive $r\equiv3\pmod4$, the ratio $N_r(X)/T(X)$ has positive lower limit precisely in the following two cases:

1. $r\ge7$ is prime.
2. $r=3q$, where $q$ is a prime congruent to $1\pmod4$.

For each other fixed $r$ the ratio tends to zero. In particular, $123$ occurs with positive lower relative frequency, while $119$ occurs and satisfies

$$
N_{119}(X)\ll \frac{X}{(\log X)^{27/16}},
\qquad
\frac{N_{119}(X)}{T(X)}\ll(\log X)^{-3/16}.
$$

These bounds allow infinitely many occurrences of $119$. We prove the density-one assertion by controlling the probability of seeing no negative sign through a cutoff, in addition to estimating each fixed offset. [Explicit minimum of 119](skipped-offsets.md) · [Explicit minimum of 123](composite-offsets.md)

## When a negative Jacobi symbol fails to give a solution

Fix $a\equiv3\pmod4$ and a unit residue $b\pmod a$ with Jacobi symbol $(b/a)=-1$. For $p\equiv b\pmod a$, write $x=(p^2+a)/4$ and $B=p^2x$. A positive divisor $d\mid B^2$ with $d\equiv-B\pmod a$ supplies the two remaining denominators $(B+d)/a$ and $(B+B^2/d)/a$. This is equivalent to the congruence $4d+p^4\equiv0\pmod a$.

Let $q$ be an odd prime in the class $c=-b/4\pmod a$, with division performed in $(\mathbb Z/a\mathbb Z)^\times$. Then

$$
\left(\frac{-a}{q}\right)=\left(\frac{q}{a}\right)
=\left(\frac{-b/4}{a}\right)=1
$$

by quadratic reciprocity. Thus $v^2\equiv-a\pmod q$ has two distinct roots. If $p$ belongs to either root class, $q\mid x$ and $d=qp^3$ supplies a divisor since $4d+p^4=p^3(p+4q)\equiv0\pmod a$. Consequently failure at $a$ forces avoidance of both roots for every such $q$.

More generally, each of the following residue classes gives the same two forbidden roots for an unsuccessful prime. The indicated $d$ works whenever $q\mid x$. All three classes have Jacobi symbol $+1$ modulo $a$.

| Class of $q\pmod a$ | Divisor $d$ | Congruence giving the witness |
|---|---|---|
| $-b/4$ | $qp^3$ | $p+4q\equiv0\pmod a$ |
| $-b^3/4$ | $qp$ | $p^3+4q\equiv0\pmod a$ |
| $-b$ | $qpx$ | $p+q\equiv0\pmod a$ |

Choose $h$ distinct classes from the table. The number of Tier 3 primes $p\le X$ in the fixed class $b$ for which $a$ fails is

$$
\ll_a X(\log X)^{-3/2-2h/\varphi(a)}. \tag{1}
$$

## The upper-bound sieve

Take $z=X^{1/8}$. Omit the finitely many primes $q\le13$ and those dividing $a(a+9)$. For every remaining prime $q\le z$, discard $0\pmod q$ and also $-3\pmod q$ when $q\equiv2\pmod3$. A Tier 3 prime $p>z$ avoids these classes. For $q$ in one of the $h$ specified classes modulo $a$, discard the two roots of $v^2\equiv-a\pmod q$ as well. They coincide with neither $0$ nor $-3$, by the omitted prime factors. Thus the number of discarded residues is precisely

$$
\rho(q)=1+\mathbf1_{q\equiv2\ (3)}+
2\mathbf1_{q\ \mathrm{in\ the\ chosen\ classes}\ (a)}.
$$

It is zero at the omitted primes and at $q>z$. This construction applies to integers in $[1,X]$. Dropping the original condition $p\equiv b\pmod a$ from the sifted set only enlarges the upper bound. Ford's residue-class sieve, Lemma 4.3, bounds the number of surviving integers by a constant times

$$
X\prod_{q\le z}\left(1-\frac{\rho(q)}q\right).
$$

Its constant is uniform for $0\le\rho(q)\le\min(4,q-1)$. The original primes $p\le z$ contribute at most $z$. Mertens' theorem for fixed arithmetic progressions gives $\sum_{q\le z}\rho(q)/q=(3/2+2h/\varphi(a))\log\log z+O_a(1)$. Overlaps between different progression conditions contribute each discarded residue and are included in this sum. The product bound proves (1). With $h=0$ the same proof gives $T(X)\ll X/(\log X)^{3/2}$. [Ford, Lemma 4.3](https://ford126.web.illinois.edu/wwwpapers/divshift.pdf) · [Mertens' theorem for arithmetic progressions, Lemma 3.3](https://doi.org/10.1515/forum-2025-0172)

For a direct Selberg-sieve verification, let $P$ be the product of the retained primes through $z$. For squarefree $d\mid P$, the Chinese remainder theorem gives $\rho(d)=\prod_{q\mid d}\rho(q)$ simultaneous bad classes, with total count $\lfloor X\rfloor\rho(d)/d+O(\rho(d))$. Selberg's upper-bound inequality therefore gives

$$
\frac{X}{G(z)}+
O\!\left(\sum_{d\mid P,\,d\le z^2}3^{\omega(d)}\rho(d)\right),
\quad
G(z)=\sum_{d\mid P,\,d\le z}
\prod_{q\mid d}\frac{\rho(q)}{q-\rho(q)}.
$$

In the divisibility formulation of the cited inequality, associate to each $n\le X$ the product of those $q$ for which $n$ is in a discarded class. Since all retained $q>13$, $3^{\omega(d)}\rho(d)\le d$. The error is $O(z^4)=O(X^{1/2})$. To bound $G(z)$ from below, expand the full product $\prod_{q\mid P,\,q\le y}(1-\rho(q)/q)^{-1}$ with $y=z^{1/16}$. After normalization, its terms are the distribution of a random squarefree divisor in which each $q$ is selected independently with probability $\rho(q)/q$. Its expected logarithm is at most $4\sum_{q\le y}(\log q)/q=(4+o(1))\log y$. For large $X$, Markov's inequality leaves at least half the mass on $d\le z$. Therefore $G(z)\gg_a (\log z)^{3/2+2h/\varphi(a)}$, yielding (1) again. [Elkies, *Selberg's upper-bound sieve*, inequality (1)](https://people.math.harvard.edu/~elkies/M229.20/sieve.pdf)

## The two families

The earlier [prime-offset theorem](README.md) and [composite-offset theorem](composite-offsets.md) give $N_r(X)\gg_r X/(\log X)^{3/2}$ in the two stated families. Those proofs apply Theorem 1.1(2) of Fuchs, Hsu, Rickards, Schindler and Stange to the form $4(u^2+uv+v^2)-3$ in a progression depending on $r$. Taking $r=7$ also proves $T(X)\gg X/(\log X)^{3/2}$. The upper bound for $T(X)$ now gives positive lower relative frequency throughout both families. [Shifted quadratic form theorem](https://doi.org/10.4064/aa250502-24-10)

For the converse we may discard the finitely many primes $p\le r$. The [Jacobi obstruction](README.md) excludes every offset $a$ with $(p/a)=1$. In particular $3$ never works. If $r>3$ is outside the two stated families and $A(p)=r$, the sign $(p/r)$ must be $-1$. Some prime factor $s$ of $r$ thus has $(p/s)=-1$. It cannot be $3$, since $p\equiv1\pmod3$. If $s\equiv3\pmod4$, choose $a=s$. Because $r$ is composite, $a<r$. If $s\equiv1\pmod4$, take $a=3s$. Then $r/s\equiv3\pmod4$ and $r\ne3s$, so again $a<r$. In both cases $a$ has negative Jacobi symbol and must fail. Sum (1) with $h=1$ over the finitely many choices of $s$ and of $b=p\bmod a$. Since $\varphi(a)<r$, this gives

$$
N_r(X)\ll_r X(\log X)^{-3/2-2/r}
$$

for every such fixed $r$. Dividing by the lower bound for $T(X)$ proves the zero relative density.

## The first negative sign determines almost every minimum

Fix any finite set $S$ of $k$ distinct primes $s>13$ congruent to $7\pmod{12}$. Write $M=\prod_{s\in S}s$. Among unit classes $b\pmod M$, exactly $\prod_{s\in S}(s-1)/2^k$ are squares at all $s$. We claim that the upper relative density of Tier 3 primes lying in these classes is at most $C2^{-k}$, with an absolute $C$.

For each such $b$, write $p=Mn+b$ with $1\le b<M$, putting aside $n=0$. The possible $n$ lie in an interval of length at most $X/M+1$. Apply Ford's Lemma 4.3 to this interval, taking $z=(X/M)^{1/8}$ and putting aside primes $p\le z$. For $13<t\le z$, $t\nmid M$, the linear substitution is invertible modulo $t$. Excluding $p\equiv0\pmod t$ and additionally $p\equiv-3\pmod t$ for $t\equiv2\pmod3$ removes $1+\mathbf1_{t\equiv2\ (3)}$ classes of $n$. This uses a sieve constant bounded absolutely. For fixed $M$ and large $X$, removing the primes $s\mid M$ from the baseline product multiplies it by $\prod_{s\in S}(1-1/s)^{-1}$, because every $s$ is $1\pmod3$. The baseline product is $O((\log z)^{-3/2})$ with an absolute constant, and $\log z/\log X\to1/8$ for each fixed $M$.

After summing over the square classes, the factors of $M$ cancel:

$$
\frac{1}{M}\frac{\prod_{s\in S}(s-1)}{2^k}\prod_{s\in S}(1-1/s)^{-1}=2^{-k}.
$$

The discarded small primes, primes dividing $M$, and the cases $n=0$ contribute $o(T(X))$ for each fixed $M$. Dividing by $T(X)\gg X/(\log X)^{3/2}$ and taking the upper limit in $X$ proves the claim. Its constant is independent of $k$ and $S$.

Now set $Y=\max S$. For fixed $Y$, by (1) and a finite sum over $0<a\le Y$ with $a\equiv3\pmod4$ and over classes $b$, outside $o(T(X))$ primes every negative symbol through $Y$ gives a decomposition. For $p>Y$ all the symbols are $\pm1$ and the positive symbols exclude decompositions. Hence if any test prime in $S$ gives a negative sign, the least offset agrees with the first negative sign through $Y$. The proportion for which the density-one assertion can fail therefore has upper limit $\le C2^{-k}$. There are arbitrarily many primes congruent to $7\pmod{12}$. Letting $k\to\infty$ *after* taking this upper limit gives zero. The factor argument above supplies an earlier negative sign whenever a candidate outside the two families has a negative sign. Thus the union over all other minimum shapes has relative density zero.

## Why 119 and 123 differ

For $p>119$ with $A(p)=119$, the earlier [table for offset 7](composite-offsets.md) forces $(p/7)=1$. As $(p/119)=-1$, we get $(p/17)=-1$. Thus $51$ fails despite $(p/51)=-1$. Put $b=p\bmod51$. The three auxiliary classes $-b/4,-b^3/4,-b$ are distinct already modulo $17$. Indeed $b^2\not\equiv1,4\pmod{17}$ since $\pm1,\pm2$ are all quadratic residues there, while $b$ is a nonresidue. The remaining comparison uses $4\not\equiv1\pmod{17}$. All three classes are therefore available in (1). As $\varphi(51)=32$, the exponent is $3/2+6/32=27/16$. Summing over $b$ proves the stated bound for $119$. In contrast, $123=3\cdot41$ belongs to the positive-frequency family. $\square$
