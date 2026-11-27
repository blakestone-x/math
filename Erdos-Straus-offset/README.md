# The least offset in prime-square Erdős–Straus decompositions is unbounded

**Blake Stone · Proof developed with OpenAI Codex.**

For almost every Tier 3 prime, the first offset with negative Jacobi symbol is exactly the least working offset. The proof classifies the fixed offsets of positive lower relative frequency. [Proof](frequency.md) · [Manuscript (PDF)](frequency.pdf)

The 18 offsets reported as skipped in the original project split into 13 that can never occur first and five that can. The proof includes an exact minimum of 119 as well as 123. [Classification (PDF)](skipped-offsets.pdf) · [Proof and table](skipped-offsets.md) · [Verifier](verify_skips.py)

Every integer of the form $3q$ with $q$ prime and $q\equiv1\pmod4$ occurs as the least offset for infinitely many Tier 3 primes. The follow-up proves this and gives a ten-digit prime whose least offset is 123. [Composite offsets](composite-offsets.md) · [PDF](composite-offsets.pdf) · [Certificate verifier](verify_composite.py)

For an odd prime $p$, call $a$ an admissible offset if $x=(p^2+a)/4$ is a positive integer occurring in a decomposition

$$
\frac4{p^2}=\frac1x+\frac1y+\frac1z,\qquad x,y,z\in\mathbb Z_{>0}.
$$

Every denominator exceeds $p^2/4$, so $a>0$ and $a\equiv3\pmod4$. Write $A(p)$ for the least admissible offset whenever a decomposition exists.

A public computational project proposed that $A(p)\le159$ whenever $p\equiv1\pmod{12}$ and $(p+3)/4$ has no divisor congruent to $2$ modulo $3$. The project calls these primes *Tier 3* and reports a computation through $10^8$. Its proof sketch also proposes an unspecified absolute bound. Both bounds fail. The Erdős–Straus conjecture itself concerns the existence of decompositions for every denominator $n\ge2$ and remains open. [Project conjecture, Open Question 5](https://github.com/CribaGIT/erdos-straus-solver/blob/master/CONJECTURE.md) · [Project proof sketch, §5](https://github.com/CribaGIT/erdos-straus-solver/blob/master/PROOF_SKETCH.md)

**Theorem.** For every prime $r\ge7$ with $r\equiv3\pmod4$, there are infinitely many Tier 3 primes $p$ for which $A(p)=r$. For each fixed $r$, their number up to $X$ is at least $c_r X/(\log X)^{3/2}$ for all sufficiently large $X$, where $c_r>0$. An explicit Tier 3 prime with $A(p)=163$ is

$$
p=96\,616\,332\,289.
$$

## An obstruction for one offset

Assume $a\equiv3\pmod4$ is positive and $p\nmid a$. Put $x=(p^2+a)/4$ and $B=p^2x$. Then $\gcd(a,B)=1$. The remaining two fractions must sum to $a/B$. Clearing denominators gives

$$
(ay-B)(az-B)=B^2.
$$

Both factors are positive. Hence a decomposition requires a divisor $d\mid B^2$ satisfying $d\equiv-B\pmod a$. Conversely any such divisor gives a decomposition with

$$
y=(B+d)/a,\qquad z=(B+B^2/d)/a.
$$

Indeed $d$ is invertible modulo $a$, so its complementary divisor is also congruent to $-B$.

**Lemma.** If the Jacobi symbol $(p/a)=1$, then $a$ is inadmissible.

For every odd prime $q\mid x$, the congruence $-a\equiv p^2\pmod q$ yields $(-a/q)=1$, since $q=p$ would force $p\mid a$. Quadratic reciprocity, including its Jacobi form for composite $a\equiv3\pmod4$, gives $(q/a)=(-a/q)=1$. If $2\mid x$, then $a\equiv7\pmod8$, giving $(2/a)=1$ as well. Thus all prime factors of $x$ have symbol $+1$ modulo $a$. The hypothesis supplies the same sign for $p$, so every divisor of $B^2$ has symbol $+1$. But $(-B/a)=-1$ since $(-1/a)=-1$. This excludes the required divisor. $\square$

## Prescribing the exact minimum

Fix $r$ as in the theorem and put $m=r\prod_{3<q<r}q$, with the product over primes. Choose a residue $\ell\pmod m$ by

$$
\ell\equiv1\pmod q\quad(3<q<r),\qquad \ell\equiv-4\pmod r.
$$

Use the theorem of Fuchs, Hsu, Rickards, Schindler and Stange on primes represented primitively by shifted quadratic forms, Theorem 1.1(2), with form $f(u,v)=u^2+uv+v^2$, shift $-3$ and multiplier $4$. It gives at least $c_r X/(\log X)^{3/2}$ primes $p\le X$ in this residue class of the form

$$
p=4f(u,v)-3,\qquad \gcd(u,v)=1.
$$

The form is primitive, positive definite, has leading coefficient $1$ and discriminant $-3$. The shift and multiplier are coprime and their product is even. The modulus $m$ is coprime to $2\cdot(-3)\cdot4$, and both $\ell$ and $\ell+3$ are coprime to $m$. At $r$ their residues are $-4,-1$, and at the remaining primes they are $1,4$. These verify the progression hypotheses of the cited theorem. [Fuchs et al., *Acta Arithmetica* 222 (2026), 371–391](https://doi.org/10.4064/aa250502-24-10) · [Theorem 1.1 in the authors' manuscript](https://www.math.ucdavis.edu/~efuchs/PrimitiveShiftedPrimes.pdf)

Set $c=(p+3)/4=f(u,v)$. No prime $q\equiv2\pmod3$ divides $c$. If such a $q$ divided $v$, the equation modulo $q$ would also force $q\mid u$. Otherwise $u/v$ in $\mathbb F_q$ would solve $t^2+t+1=0$, giving a nontrivial cube root of unity, impossible for $q\equiv2\pmod3$. Also $c\equiv(u-v)^2\pmod3$. For $p>3$ the residue $c\equiv0\pmod3$ would make $p$ divisible by $3$, so $c\equiv1\pmod3$ and $p\equiv1\pmod{12}$. Every divisor of $c$ is $1$ modulo $3$. The primes counted are therefore Tier 3.

For each possible offset $a<r$, all its prime divisors are either $3$ or among the primes $q$ with $3<q<r$. We have $p\equiv1$ modulo each of them. Thus $(p/a)=1$ and the lemma excludes $a$.

At $a=r$, put $x=(p^2+r)/4$ and $B=p^2x$. The divisor $d=p^3$ divides $B^2$. Since $p\equiv-4\pmod r$, we have $4(B+d)\equiv p^3(p+4)\equiv0\pmod r$. The divisor criterion now gives a decomposition, proving $A(p)=r$. $\square$

## Checking the explicit example

For $p=96\,616\,332\,289$, the integer $c=(p+3)/4=79\cdot305\,747\,887$ has two prime factors, both $1$ modulo $3$. For every prime $q$ dividing one of $3,7,\ldots,159$, the residue $p\bmod q$ is a nonzero square modulo $q$. This gives $(p/a)=1$ for every one of the forty possible smaller offsets. At $a=163$, use

$$
x=2\,333\,678\,916\,244\,615\,994\,921,
\qquad d=331\,581\,285\,817\,p.
$$

These give $d\mid(p^2x)^2$ and $d\equiv-p^2x\pmod{163}$. The accompanying script verifies all primalities by trial division, the quadratic residues by Euler's criterion, and the resulting three-fraction identity by direct multiplication. [Standard-library Python verifier](verify.py)

**Related work.** Elsholtz and Tao established a quadratic-reciprocity obstruction to Type I and Type II solutions for odd perfect squares in Proposition 1.6. The fixed-denominator divisor factorization and related Jacobi obstructions also occur in earlier work. The application here excludes *every* decomposition at every smaller offset, within the specific Tier 3 family, while constructing a decomposition at the prescribed offset. [Elsholtz and Tao (2013)](https://arxiv.org/abs/1107.1010) · [R. M. B. Bueno, *The Erdős–Straus equation with a fixed denominator*, §3](https://www.academia.edu/176400926/The_Erd%C5%91s_Straus_equation_with_a_fixed_denominator_Divisor_criteria_and_quadratic_obstructions_with_reproducible_finite_searches)
