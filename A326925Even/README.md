# A326925: the even-degree factorization and its constants

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

For every integer $k\ge1$, the degree-$2k$ polynomial in [A326925](https://oeis.org/A326925) is the product of **exactly two distinct irreducible polynomials over $\mathbb Q$, each of degree $k$**. We construct both factors explicitly and prove that their constant terms are the Fibonacci and Lucas numbers $F_{k-1}$ and $L_{k-1}$.

This proves the even-degree clause recorded by Clark Kimberling in 2019. Combined with the [previous odd-degree proof](../A326925/README.md), it establishes the complete odd/even irreducibility pattern in that conjecture. The previous odd-degree clause is credited and is not counted again.

## The theorem and its exact source meaning

Put
$$
D=1-x-x^2,\qquad A=2x+1,\qquad B=x^2+x-1.
$$
Use degree-indexed normalized polynomials
$$
P_0=-1,\quad P_1=1-x,\quad P_{N+2}=AP_{N+1}-BP_N.
$$
The previously verified derivative identity is
$$
\left(\frac{1-x}{1-x-x^2}\right)^{(n)}
=\frac{n!P_{n+1}(x)}{D^{n+1}}.
$$
Thus degree $2k$ corresponds to derivative order $2k-1$. We also prove that $P_N$ is coprime to $D$ for every $N>0$, so this representation has no polynomial cancellation.

Define two integral polynomial sequences by
$$
\begin{array}{lll}
U_0=1,&U_1=x,&U_{k+2}=AU_{k+1}-BU_k,\\
V_0=-1,&V_1=2-x,&V_{k+2}=AV_{k+1}-BV_k.
\end{array}
$$
For every $k\ge1$,
$$
\boxed{P_{2k}=U_kV_k,\qquad
\deg U_k=\deg V_k=k,\qquad
U_k,V_k\text{ irreducible and coprime over }\mathbb Q.}
$$
Moreover,
$$
\boxed{U_k(0)=F_{k-1},\qquad V_k(0)=L_{k-1},}
$$
where $F_0=0,F_1=1$, $L_0=2,L_1=1$, and both integer sequences satisfy the usual additive recurrence.

The first factors are:

| $k$ | $U_k(x)$ | $V_k(x)$ |
|---:|---|---|
| 1 | $x$ | $2-x$ |
| 2 | $1+x^2$ | $1+4x-x^2$ |
| 3 | $1+3x+x^3$ | $3+3x+6x^2-x^3$ |
| 4 | $2+4x+6x^2+x^4$ | $4+12x+6x^2+8x^3-x^4$ |

These agree with the displayed factorizations in A326925. The first rows of the related arrays A328610/A328611 exchange the two degree-one factors and change both signs. We therefore state the constants with an explicit normalization instead of identifying unspecified factor-list positions. The companion row-sum observations are outside this result.

## Complete proof

### 1. Closed forms and exact factorization

Let
$$
u=\frac{1+\sqrt5}{2},\qquad v=1-u,\qquad K=\mathbb Q(u).
$$
Then $u+v=1$, $uv=-1$, $u^2=u+1$, and $u\ne v$. The characteristic roots of the common polynomial recurrence are $x+u,x+v$. Checking the two initial values and the recurrence proves
$$
\begin{aligned}
(u-v)P_N&=v^2(x+u)^N-u^2(x+v)^N,\\
(u-v)U_k&=u(x+v)^k-v(x+u)^k,\\
V_k&=-v(x+u)^k-u(x+v)^k.
\end{aligned}
$$
Multiplying the last two equations gives the first equation at $N=2k$. Since $u-v\ne0$, this proves $P_{2k}=U_kV_k$.

The two factor formulas can also be written
$$
\begin{aligned}
(u-v)U_k&=-v\big((x+u)^k+u^2(x+v)^k\big),\\
V_k&=-v\big((x+u)^k-u^2(x+v)^k\big).
\end{aligned} \tag{1}
$$
Their leading coefficients are nonzero because $-u^2\ne1$ and $u^2\ne1$. Hence both degrees equal $k$.

### 2. Two elementary irreducibility tools

**Signed binomial criterion.** Let $E$ be a field, $n>0$, and $a\in E$. Suppose that, for every prime $p\mid n$, neither $a$ nor $-a$ is a $p$-th power in $E$. Then $Y^n-a$ is irreducible over $E$.

Here is the induction used in the formal proof. It is convenient to express the hypothesis as
$$
(b^p)^2\ne a^2
\quad\text{for all }b\in E\text{ and primes }p\mid n.
$$
For $n=1$ the conclusion is immediate. Write a larger exponent as $pm$, with $p$ prime. The prime-degree binomial criterion makes $Y^p-a$ irreducible. If $\alpha^p=a$, then
$$
N_{E(\alpha)/E}(\alpha)=(-1)^p(-a),
\qquad N_{E(\alpha)/E}(\alpha)^2=a^2.
$$
For a prime $q\mid m$, a forbidden equality $(b^q)^2=\alpha^2$ in $E(\alpha)$, after taking norms, would give
$$
\big(N_{E(\alpha)/E}(b)^q\big)^2=a^2
$$
in $E$. The induction hypothesis therefore makes $Y^m-\alpha$ irreducible. The composition criterion for adjoining a root then makes $Y^{pm}-a$ irreducible. The full induction is in `SignedKummer.lean`. This is a sufficient criterion; no new general classification of binomial irreducibility is claimed.

**Conjugate-factor descent.** Suppose $F\subseteq E$, $H\in F[X]$, and
$$
H=qr
$$
in $E[X]$, where $q,r$ are coprime irreducibles. If an $F$-automorphism of $E$ carries $q$ to $r$, then $H$ is irreducible over $F$. Indeed, in a factorization $H=ab$ over $F$, the prime polynomial $q$ divides one of $a,b$. Applying the automorphism shows that $r$ divides the same factor. Coprimality makes $qr=H$ divide it, so the other factor is a unit. This exact argument is formalized in `ConjugateDescent.lean`.

We also reuse the previously proved fractional-linear lemma: if $Y^n-c$ is irreducible, $a\ne b$, and $c\ne1$, then
$$
(X-a)^n-c(X-b)^n
$$
is irreducible. A root $x$ of any factor gives $(x-a)/(x-b)$ of degree $n$; the denominator cannot vanish. Thus the factor already has full degree. The implementation is copied unchanged from the preceding package.

### 3. Golden-unit nonpower obstructions

The earlier `GoldenUnit.lean` development, included unchanged, proves:

- Neither $u$ nor $-u$ is a $p$-th power in $K$, for any prime $p$.
- $u^2$ is not a $p$-th power in $K$, for any odd prime $p$.
- For odd $n$, both $Y^n-u^2$ and $Y^n+u^2$ are irreducible over $K$.

For completeness, these arithmetic obstructions have elementary norm-and-trace proofs. The norm of $u$, and also of $-u$, is $-1$; a square root in $K$ would have rational norm whose square is $-1$. For an odd-prime root $b^p=u$, the positive real embedding gives $1<b<u$, the norm is $-1$, and the integral trace is $b-1/b$, strictly between $0$ and $1$. This is impossible. Replacing $b$ by $-b$ handles $-u$.

For $b^p=u^2$ with $p$ odd, one has norm $1$ and $1<b<2$. Its integral trace $b+1/b$ lies strictly between $2$ and $3$, again impossible. In each case $b$ is integral because a positive power is integral, and irrational because the prescribed power is irrational. These facts, the field degree, and the integral trace are all proved in the included Lean dependency.

It follows from the signed criterion that $Y^n-u$ and $Y^n+u$ are irreducible over $K$ for **every** $n>0$.

### 4. The missing even exponents for $Y^n+u^2$

Let $J=K(i)$, with $i^2=-1$. Neither $iu$ nor $-iu$ is a prime power in $J$.

For an odd prime $p$, a hypothetical $b^p=\pm iu$, after taking the norm $J/K$, gives
$$
N_{J/K}(b)^p=u^2,
$$
contradicting the preceding obstruction.

For $p=2$, write $b=a+ci$, with $a,c\in K$. The equation $b^2=\pm iu$ implies
$$
a^2=c^2,\qquad 2ac=\pm u.
$$
Thus $a=\pm c$, so $u=\pm2c^2$. Taking the norm $K/\mathbb Q$ gives
$$
-1=4N_{K/\mathbb Q}(c)^2,
$$
which is impossible. The formal proof constructs the quadratic extension, proves unique coordinates, computes both norms, and handles both signs.

By the signed criterion, $Y^m-iu$ and $Y^m+iu$ are irreducible over $J$ for every $m>0$. They are coprime and are exchanged by complex conjugation, while
$$
Y^{2m}+u^2=(Y^m-iu)(Y^m+iu).
$$
Conjugate-factor descent proves that $Y^{2m}+u^2$ is irreducible over $K$. Together with the odd-exponent result, this proves irreducibility of $Y^k+u^2$ for every $k>0$.

Equation (1), the fractional-linear lemma, and the nonzero scalar factors now show that $U_k$ is irreducible even over $K$, hence over $\mathbb Q$.

### 5. Irreducibility of the second factor

For odd $k$, $Y^k-u^2$ is irreducible over $K$. Equation (1) proves that $V_k$ is irreducible over $K$, hence over $\mathbb Q$.

For even $k=2m$, put
$$
\begin{aligned}
q&=(x+u)^m-u(x+v)^m,\\
r&=-v\big((x+u)^m+u(x+v)^m\big).
\end{aligned}
$$
Then $V_{2m}=qr$. The irreducibility of $Y^m-u$ and $Y^m+u$, followed by the fractional-linear lemma, proves that $q$ and $r$ are irreducible over $K$.

The powers $(X+u)^m,(X+v)^m$ are coprime because $u\ne v$. Their two displayed linear combinations are coprime because $u\ne-u$. The nontrivial automorphism $\sigma$ of $K/\mathbb Q$ sends $u$ to $v$ and $v$ to $u$, and
$$
\sigma(q)=(x+v)^m-v(x+u)^m=r
$$
by $uv=-1$. Since $V_{2m}\in\mathbb Q[X]$, conjugate-factor descent proves its irreducibility over $\mathbb Q$.

### 6. Distinct factors, reduced numerators, and constants

The two transformed expressions in (1) are coprime: their constants $u^2,-u^2$ differ, and their base polynomials $X+u,X+v$ are coprime. Nonzero scalar multiplication does not change coprimality. Coprimality descends to $\mathbb Q$, so $U_k,V_k$ are distinct irreducible factors.

The denominator has roots $-u,-v$, and $D=-(X+u)(X+v)$. At $-u$, the closed form for $P_N$ becomes
$$
(u-v)P_N(-u)=-u^2(v-u)^N\ne0,
$$
and at $-v$ it becomes
$$
(u-v)P_N(-v)=v^2(u-v)^N\ne0.
$$
Therefore $P_N$ is coprime to $D$, for all positive $N$. In particular the odd derivative of order $2k-1$ has canonical reduced numerator
$$
(2k-1)!\,U_kV_k,
$$
because its denominator $D^{2k}$ is monic. The factorial is a nonzero rational unit, so this numerator has the two stated irreducible factors, up to units.

Finally specialize the two recurrences at $x=0$. Since $A(0)=1$ and $B(0)=-1$, each constant sequence obeys the Fibonacci additive recurrence. Their initial values are
$$
U_1(0)=0,\quad U_2(0)=1,\qquad
V_1(0)=2,\quad V_2(0)=1.
$$
Induction gives exactly $U_k(0)=F_{k-1}$ and $V_k(0)=L_{k-1}$. This proves the companion constant-term observation in the specified normalization. $\square$

## Formal package and reproduction

The package is self-contained relative to pinned mathlib. It uses Lean **4.19.0** and mathlib revision **c44e0c8ee63ca166450922a373c7409c5d26b00b**.

```sh
lake exe cache get
lake build
```

The original modules `GoldenUnit.lean`, `MobiusIrreducibility.lean`, `RationalDerivative.lean`, and `DerivativePolynomials.lean` are copied byte for byte from the preceding A326925 package. `OddProof.lean` is the unchanged old `Proof.lean` under a filename that permits the combined project to import it. Their reuse is deliberate and separately recorded in the build audit.

The new modules are:

| Module | Responsibility |
|---|---|
| `SignedKummer.lean` | Sufficient signed nonpower criterion, including the norm induction |
| `ConjugateDescent.lean` | Irreducibility from exchanged coprime factors; coprimality of two linear combinations |
| `GoldenConjugation.lean` | The nontrivial automorphism of the real quadratic field |
| `QuadraticUnits.lean` | Construction of $K(i)$, coordinates, conjugation, and nonpower obstructions |
| `BinomialUnits.lean` | Irreducibility of $Y^n\pm u$ and $Y^n+u^2$ at all positive exponents |
| `EvenFactors.lean` | Explicit factors, closed forms, product identity, and Fibonacci/Lucas constants |
| `EvenProof.lean` | Irreducibility of both factors over $\mathbb Q$, degrees, and exact factorization |
| `EvenDerivative.lean` | Coprimality, no cancellation, and exact canonical reduced numerator |

The main algebra endpoint is `A326925Even.even_degree_factorization`. The constant endpoints are `EvenFactors.fib_constant` and `EvenFactors.lucas_constant`. The exact reduced-numerator endpoint is `A326925Even.odd_derivative_numerator_factorization`, and `A326925Even.factors_coprime` proves distinctness of the normalized factors. Both are in `EvenDerivative.lean`. The accompanying author and independent build records identify the exact source hashes and theorem dependencies.

No admissions, added axioms, unsafe declarations, or native-evaluation proof shortcuts occur in these files. Main theorem dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

The classical prime and odd binomial ingredients are in mathlib's [KummerPolynomial.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/FieldTheory/KummerPolynomial.lean) and [KummerExtension.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/FieldTheory/KummerExtension.lean). In particular `Polynomial.X_pow_sub_C_irreducible_of_odd` is in **KummerExtension.lean**; this corrects the filename citation in the previous package without changing its proof.

## Sources, novelty, and count

The official source exports for A326925, A328610, and A328611 are preserved in [sources](sources). Exact revisions, Git blob hashes, degree/index reconciliation, factor-order issues, both-engine searches, and primary literature comparisons are documented in [source_checks.md](source_checks.md).

No earlier proof of this exact even-degree clause was located in the checked sources. This is a bounded prior-publication search, not a certification of historical priority or OEIS editorial acceptance. The techniques of norms, binomial irreducibility, and conjugation descent are standard algebra.

This package resolves **one new factorization clause**, together with its explicit Fibonacci/Lucas constant-term observation. It does not recount the earlier odd-degree clause, count the two companion arrays as independent factorization problems, or claim the separate row-sum observations.

