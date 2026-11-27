# Which composite Erdős–Straus offsets can occur first?

**Blake Stone · Proof developed with OpenAI Codex.**

For a prime $p\equiv1\pmod{12}$, put $c=(p+3)/4$. Call $p$ *Tier 3* if no prime factor of $c$ is $2$ modulo $3$. The least offset $A(p)$ is the smallest $a>0$ such that $x=(p^2+a)/4$ is a denominator in a decomposition $4/p^2=1/x+1/y+1/z$ into positive unit fractions, whenever such a decomposition exists. Every candidate $a$ is $3$ modulo $4$. A computational project reported several offsets absent among the Tier 3 primes through $10^8$ and proposed that their absence was structural. Its list includes $123$. [Original claim, pinned revision](https://github.com/CribaGIT/erdos-straus-solver/blob/7dc52eef10c6146b5a3dc6731651fceb396e4f1e/CONJECTURE.md#L162)

**Theorem 1.** For every prime $q\equiv1\pmod4$, the composite offset $r=3q$ is the least offset of infinitely many Tier 3 primes. For each fixed $q$, at least $c_qX/(\log X)^{3/2}$ such primes lie below $X$ for all sufficiently large $X$, for some $c_q>0$. In particular, $123$ occurs infinitely often.

**Theorem 2.** Among offsets whose squarefree part has all its prime factors in $\{3,5,7,11,13\}$, the exact set of possible least offsets for Tier 3 primes is $\{7,11,15,39\}$. In particular, the reported absences of $27,35,55,63,75,91,99,135,143,147$ have proofs.

## The fixed-offset test

For $p\nmid a$ set $B=p^2x$. Here $\gcd(a,B)=1$. The remaining two unit fractions must sum to $a/B$, equivalently $(ay-B)(az-B)=B^2$. A positive divisor $d\mid B^2$ with $d\equiv-B\pmod a$ gives denominators

$$y=(B+d)/a,\qquad z=(B+B^2/d)/a.$$

The complementary divisor has the same residue because $B$ is invertible modulo $a$. Conversely either positive factor in the displayed factorization gives such a divisor. Since $4B\equiv p^4\pmod a$, the residue test is $4d+p^4\equiv0\pmod a$.

A necessary condition for this test is $(p/a)=-1$, with the Jacobi symbol. Indeed if an odd prime $s$ divides $x$, then $-a\equiv p^2\pmod s$ is a nonzero square. Quadratic reciprocity gives $(s/a)=(-a/s)=1$ because $a\equiv3\pmod4$. If $2\mid x$, then $a\equiv7\pmod8$ and $(2/a)=1$ as well. If $(p/a)=1$, all divisors of $B^2$ have Jacobi symbol $+1$ modulo $a$, while $(-B/a)=-1$. This proves the obstruction.

## Proof of Theorem 1

Choose a quadratic nonresidue $b$ modulo $q$ with $4b\not\equiv3\pmod q$. There are $(q-1)/2\ge2$ nonresidues, and the exclusion removes at most one. Dirichlet's theorem gives a prime $t>r$ with $t\equiv2\pmod3$ and $t\equiv b\pmod q$. Then

$$
\left(\frac{-r}{t}\right)=\left(\frac{t}{r}\right)
=\left(\frac{t}{3}\right)\left(\frac{t}{q}\right)=1.
$$

Let $h$ be a root of $h^2\equiv-r\pmod t$ with $h\not\equiv-3\pmod t$. The two roots are nonzero and distinct, so one always meets this condition.

Use the Chinese remainder theorem to impose the following on $p$:

$$
p\equiv-4t\pmod q,\qquad p\equiv h\pmod t,\qquad
p\equiv1\pmod s\quad(3<s<r,\ s\text{ prime},\ s\ne q).
$$

Write $m$ for the product of the displayed prime moduli and $\ell$ for the prescribed class. Apply Theorem 1.1(2) of Fuchs, Hsu, Rickards, Schindler and Stange to $p=4(u^2+uv+v^2)-3$ with $\gcd(u,v)=1$. The form is primitive and positive definite with leading coefficient $1$ and nonsquare discriminant $-3$. The multiplier $4$ and shift $-3$ are coprime and their product is even. The modulus $m$ is coprime to $2\cdot(-3)\cdot4$. Both $\ell$ and $\ell+3$ are units modulo $m$. At $q$ this uses $b\ne0$ and $4b\ne3$, at $t$ it uses $h\ne0,-3$, and at the other primes the residues are $1,4$. The cited theorem therefore supplies the claimed lower bound for these primes. [Fuchs et al., Theorem 1.1(2)](https://www.math.ucdavis.edu/~efuchs/PrimitiveShiftedPrimes.pdf)

These primes are Tier 3 after discarding $p\le3$. Indeed, if a prime $s\equiv2\pmod3$ divided $c=u^2+uv+v^2$, primitivity would give $s\nmid v$ and $u/v$ would be a nontrivial cube root of unity modulo $s$, impossible. Also $c\equiv(u-v)^2\pmod3$ cannot be zero since $p=4c-3>3$ is prime. Hence $c\equiv1\pmod3$ and $p\equiv1\pmod{12}$.

If $0<a<3q$ and $a\equiv3\pmod4$, then $q\nmid a$: the smallest positive multiple of $q\equiv1\pmod4$ that is $3$ modulo $4$ is $3q$. Each prime factor of $a$ therefore has $p\equiv1$ modulo it, including the factor $3$ when present. Thus $(p/a)=1$ and the obstruction rules out $a$.

Finally $p\equiv-4t\pmod{3q}$, using $t\equiv2\pmod3$, and $t\mid x=(p^2+3q)/4$. Thus $d=tp^3$ divides $B^2$. Since $4d+p^4=p^3(p+4t)$ is divisible by $3q$, the fixed-offset test gives a decomposition at $r=3q$. This proves Theorem 1.

### An explicit certificate for 123

Take $p=6\,172\,024\,609$. This is a prime congruent to $1$ modulo $12$, and

$$
c=(p+3)/4=1\,543\,006\,153=13\cdot37\cdot3\,207\,913
$$

has only prime factors congruent to $1$ modulo $3$. The prime $p$ is a quadratic residue at every prime divisor of every $a=3,7,\ldots,119$, so all thirty smaller candidates have $(p/a)=1$.

At $a=123$ we have

$$
x=9\,523\,471\,943\,525\,400\,751
=11^2\cdot31\cdot1493\cdot1\,700\,546\,198\,357.
$$

Take $d=1493px$. Since $1493\mid x$, this divides $B^2=p^4x^2$. Also $p\equiv-1493\pmod{123}$, so $B+d=px(p+1493)$ is divisible by $123$. The fixed-offset test now yields $A(p)=123$. Of the $675$ divisors of $B^2$, six satisfy $d\equiv-B\pmod{123}$, and this $d$ is the smallest. The verifier checks primality, all thirty exclusions, the divisor enumeration, and the exact rational identity. [Certificate verifier](verify_composite.py)

Both certificates also meet the project’s narrower divisor test $d\mid p^2x^2$. In Theorem 1 the complementary divisor $B^2/(tp^3)=px^2/t$ divides $p^2x^2$, and in the example $1493px$ divides $p^2x^2$ directly since $1493\mid x$. [Project’s divisor convention, pinned revision](https://github.com/CribaGIT/erdos-straus-solver/blob/7dc52eef10c6146b5a3dc6731651fceb396e4f1e/CONJECTURE.md#L76-L82)

## Proof of Theorem 2

The following table supplies a divisor for every indicated residue. In each row $x=(p^2+a)/4$, and direct substitution gives $4d+p^4\equiv0\pmod a$. For $a=7,15,39$ we have $2\mid x$. For $a=11$ we have $3\mid x$ since $p\equiv1\pmod3$. The rows for $39$ assume that offset $15$ fails. The rows for $15$ then force $(p/5)=1$, so $p\equiv\pm1\pmod5$. Hence $5\mid(p^2+39)/4$. These divisibilities give $d\mid(p^2x)^2$ in all rows, including $d=50p$.

| Offset $a$ | Residue of $p$ modulo $a$ | Divisor $d$ |
|---|---|---|
| 7 | 3 | $p^3$ |
| 7 | 5 or 6 | $2p$ |
| 11 | 2 | $9p$ |
| 11 | 6 | $p$ |
| 11 | 7 | $p^3$ |
| 11 | 10 | $3p$ |
| 15 | 7 | $2p^3$ |
| 15 | 13 | $2p$ |
| 39 | 7, 34 or 37 | $2p$ |
| 39 | 19 | $5p^3$ |
| 39 | 28 | $50p$ |
| 39 | 31 | $2p^3$ |

The $a=7$ rows cover all nonresidues modulo $7$. The nonresidues modulo $11$ are $2,6,7,8,10$. The missing class $8=-3\pmod{11}$ would make $11\mid c$, impossible for Tier 3 because $11\equiv2\pmod3$. The $a=15$ rows cover all primes $p\equiv1\pmod3$ that are nonresidues modulo $5$. Therefore a negative Legendre symbol at $5$, $7$, or $11$ ensures a working offset of $15$, $7$, or $11$, respectively. For $p\equiv1\pmod3$, the six classes in the rows for $39$ are exactly the quadratic nonresidues modulo $13$. Thus $(p/13)=-1$ ensures a working offset of either $15$ or $39$.

Now suppose $r=A(p)$ satisfies the squarefree-part hypothesis. First $p\nmid r$. Otherwise $p^2\mid r$, since a Tier 3 prime lies outside $\{3,5,7,11,13\}$. Indeed $13$ is the only listed prime congruent to $1$ modulo $12$, and for $p=13$ one has $c=4$. As $r/p^2\equiv3\pmod4$, this yields $r\ge3p^2$. In a decomposition at $r$, the smallest denominator is at most $3p^2/4$ by averaging the three reciprocals. Using this smallest denominator instead would give a positive offset at most $2p^2$, contradicting minimality.

The necessary condition $(p/r)=-1$ and $(p/3)=1$ now force at least one negative symbol at $5,7,11,13$. Hence $r\le39$ by the table. Through $39$, the candidates satisfying the squarefree-part hypothesis are $3,7,11,15,27,35,39$. The symbol $(p/3)=1$ excludes $3$ and $27$. At $35$, a negative Jacobi symbol forces a negative symbol at either $5$ or $7$, giving a smaller working offset. This leaves $7,11,15,39$. Theorem 1 realizes $15$ and $39$ by taking $q=5$ and $13$. For $r=7$ or $11$, impose $p\equiv-4\pmod r$ and $p\equiv1$ modulo every prime strictly between $3$ and $r$. The same shifted-form theorem applies because $-4$ and $-4+3=-1$ are units at $r$ and the other residues are $1,4$. It gives infinitely many Tier 3 primes in each class. All smaller offsets have positive Jacobi symbol, and $d=p^3$ works at $r$. This realizes the two remaining minima. $\square$

## Scope of the Jacobi obstruction

Among $r\equiv3\pmod4$, $r>3$, the prime offsets and the composite offsets $3q$ above exhaust the shapes distinguishable by imposing $(p/a)=1$ for **all** smaller candidates $a$ and $(p/r)=-1$ (with $p$ coprime to all candidates). To see necessity, take any other composite $r$. Each prime divisor $s\equiv3\pmod4$ is itself an earlier candidate. Each prime divisor $s\equiv1\pmod4$ gives the earlier candidate $3s$, because $r/s\equiv3\pmod4$ and $r\ne3s$. The signs at $3$ and $3s$ force $(p/s)=1$ as well. Multiplicativity then gives $(p/r)=1$. Sufficiency follows from the prime-offset construction and Theorem 1. The exact classification in Theorem 2 uses the additional explicit divisors in the table.
