# A326925: irreducibility of every odd-degree derivative numerator

**The odd-degree clause is proved.** Let

$$
f(x)=\frac{1-x}{1-x-x^2}.
$$

For every even integer $n\geq0$, the reduced numerator of $f^{(n)}(x)$ is irreducible over $\mathbb Q$. Its degree is $n+1$. Equivalently, every odd-degree polynomial in the family recorded in [OEIS A326925](https://oeis.org/A326925) is irreducible. The proof establishes the stronger irreducibility of the normalized polynomial over $\mathbb Q(\sqrt5)$.

Blake Stone, developed with OpenAI Astra 6.2, November 27, 2026.

This is **one** recorded conjectural clause. The separate claim that every degree-$2k$ polynomial has exactly two irreducible degree-$k$ factors, and the related Fibonacci/Lucas constant-term observations, are not claimed here.

## Exact source and indexing

The source's displayed polynomials start

$$
\begin{aligned}
P_1&=1-x,\\
P_2&=2x-x^2,\\
P_3&=1+3x^2-x^3,\\
P_4&=1+4x+4x^3-x^4.
\end{aligned}
$$

Here the subscript is the **degree**. The source title's derivative index is shifted by one relative to its degree, whereas the displayed polynomials and Mathematica program start with derivative order zero and degree one. We make the intended indexing explicit and prove the identity

$$
\boxed{f^{(n)}(x)=\frac{n!P_{n+1}(x)}{(1-x-x^2)^{n+1}}.} \tag{1}
$$

The program also chooses a numerator sign and divides out $n!$. Such nonzero rational scalar factors do not affect irreducibility. The formal package proves both irreducibility of $P_N$ for odd $N$ and irreducibility of the **canonical reduced numerator** of the even-order derivative, including the no-cancellation step.

## Complete proof

### 1. Recurrence and derivative correspondence

Set $D=1-x-x^2$, and introduce the auxiliary constant $P_0=-1$. Define

$$
P_{N+2}=(2x+1)P_{N+1}-(x^2+x-1)P_N. \tag{2}
$$

An induction using (2) gives

$$
D P_N'+N(2x+1)P_N=N P_{N+1}. \tag{3}
$$

Equation (1) follows from (3) and the quotient rule, starting with $P_1=1-x$. The formal derivative on rational functions is defined using canonical numerator and denominator. A separate theorem proves the quotient rule for **every** representation $p/q$ with $q\ne0$, so equation (1) is an identity of actual rational functions, independent of an arbitrary representation.

### 2. A closed form over the golden-ratio field

Write

$$
u=\frac{1+\sqrt5}{2},\qquad v=1-u,\qquad K=\mathbb Q(u).
$$

Then $u+v=1$, $uv=-1$, and $u^2=u+1$. The recurrence (2), including its two initial values, gives

$$
(u-v)P_N(x)=v^2(x+u)^N-u^2(x+v)^N. \tag{4}
$$

Since $v^2u^4=u^2$, this is

$$
(u-v)P_N(x)=v^2\big((x+u)^N-u^4(x+v)^N\big). \tag{5}
$$

Both scalar factors are nonzero. Also $u^4\ne1$, so (5) has degree exactly $N$.

### 3. The arithmetic obstruction: $u^4$ is no odd-prime power in $K$

Let $p$ be an odd prime. Suppose $b\in K$ satisfies $b^p=u^4$. Since $u$ is an algebraic integer and a power of $b$ is integral, $b$ is an algebraic integer. The norm from $K$ to $\mathbb Q$ satisfies

$$
\operatorname{N}(u)=-1,\qquad
\operatorname{N}(b)^p=\operatorname{N}(u^4)=1.
$$

Because $p$ is odd, $\operatorname{N}(b)=1$. In the real embedding with $u>1$, the equation $b^p=u^4$ implies $b>1$. Moreover,

$$
u^4=3u+2<8,
$$

while $p\geq3$. Thus $b<2$: otherwise $b^p\geq2^p\geq8$.

The number $b$ is irrational, since $u^4=3u+2$ is irrational. Its other conjugate is $1/b$, because its norm is one. As an algebraic integer, its trace is an integer. But

$$
2<b+\frac1b<3 \qquad(1<b<2),
$$

which is impossible for an integer. Therefore $u^4$ is not a $p$-th power in $K$ for any odd prime $p$.

The Lean development proves the quadratic degree, norm, integrality, minimal-polynomial coefficient identities, and integer trace needed in this argument. It does not assume a classification of the units of $\mathbb Q(\sqrt5)$.

### 4. Binomial and linear-fractional irreducibility

The classical binomial criterion for odd $N$ states that $Y^N-a$ over a characteristic-zero field is irreducible if $a$ is not a $p$-th power for each prime $p\mid N$. Applying the preceding obstruction gives

$$
Y^N-u^4\quad\text{irreducible over }K
\qquad(N\text{ odd}). \tag{6}
$$

For completeness, consider the general linear-fractional transformation

$$
Q(X)=(X-a)^N-c(X-b)^N,
\qquad a\ne b,\quad c\ne1.
$$

If $Y^N-c$ is irreducible, then so is $Q$. Indeed, take a root $x$ of any irreducible factor of $Q$, in its root field. The value $x=b$ is impossible because $a\ne b$. Therefore

$$
y=\frac{x-a}{x-b}
$$

satisfies $y^N=c$. Its minimal polynomial has degree $N$, so the field containing $x$ has degree at least $N$. Thus the chosen factor already has degree at least $N$, while $Q$ has degree $N$ because $c\ne1$. The factor is associated to all of $Q$, proving irreducibility. This degree argument is fully formalized, including the exceptional-denominator check.

Apply it with $a=-u$, $b=-v$, and $c=u^4$. Equation (5) and (6) prove that $P_N$ is irreducible over $K$ for every odd $N$. Irreducibility then descends to $\mathbb Q$.

### 5. Reduction of the derivative numerator

For odd $N\geq3$, the irreducible polynomial $P_N$ has degree $N>\deg D=2$, so it cannot divide $D$. For $N=1$, $P_1=1-x$ does not divide $D$, since $D(1)=-1$. Thus no factor of $P_N$ cancels against any power of $D$ when $N$ is odd.

In equation (1), $n!$ is a nonzero rational scalar. For even $n$, $N=n+1$ is odd, so the reduced numerator is associated to $P_{n+1}$ and is irreducible. This proves the exact source clause. $\square$

## Formal verification

| Module | Main responsibility |
|---|---|
| `GoldenUnit.lean` | Quadratic field, norm and integral trace, odd-prime-power obstruction, odd binomial irreducibility |
| `MobiusIrreducibility.lean` | Irreducibility preserved by the displayed linear-fractional transformation |
| `RationalDerivative.lean` | Rational derivative, quotient-rule independence, iterated numerator recurrence |
| `DerivativePolynomials.lean` | Polynomial recurrence, closed form, degree, derivative bridge, cancellation criterion |
| `Proof.lean` | Exact A326925 instantiation and final statements over $\mathbb Q$ |

The principal declarations are:

- `A326925.odd_irreducible_over_quadratic`: the stronger assertion over $\mathbb Q(\sqrt5)$.
- `A326925.odd_degree_irreducible`: irreducibility of every odd-indexed $P_N$ over $\mathbb Q$.
- `A326925.degree_eq`: $\deg P_N=N$.
- `A326925.source_derivative`: the exact identity (1).
- `A326925.even_derivative_numerator_irreducible`: irreducibility of the reduced numerator of every even-order derivative of the original rational function.

The package pins Lean **4.19.0** and mathlib **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. To reproduce:

```sh
lake exe cache get
lake build
lake env lean Proof.lean
```

The classical binomial result is mathlib's `Polynomial.X_pow_sub_C_irreducible_of_odd`, in [KummerPolynomial.lean at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/FieldTheory/KummerPolynomial.lean). No new general binomial criterion is claimed. The package contains no admissions, added axioms, unsafe declarations, or native-evaluation proof shortcuts. Main theorem dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

Some auxiliary golden-ratio nonpower lemmas are included, but they are not counted as additional conjecture resolutions and do not establish the even-degree clause.

## Sources and historical scope

The conjecture is attributed in A326925 to Clark Kimberling in 2019. The exact primary export and three related entries are preserved in `sources/`. Both search engines, the current trureturing index, and nearby Fibonacci-polynomial literature were checked. No earlier proof of this exact odd-degree assertion was located. This is a bounded prior-publication search, not a certification of historical priority; details and exact source hashes are in [source_checks.md](source_checks.md).

The complete independent audit and build logs are included with the package. The source-index discrepancy is documented rather than counted as another resolution, and no result for A327315 or the separate even-degree family is claimed.
