# A326926: the complete irreducibility classification

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

The nonconstant row of degree $n$ in [A326926](https://oeis.org/A326926) is irreducible over $\mathbb Q$ **if and only if $n+1$ is a prime other than $3$**. This proves the full irreducibility assertion recorded by Clark Kimberling in 2019 and repeated in [A326933](https://oeis.org/A326933).

The prime cases have an elementary explanation: the reciprocal polynomial is Eisenstein at the prime $n+1$. The composite cases follow from the classical divisibility property of Lucas polynomials. We formalize both arguments, the differential identities that make Eisenstein apply, and the exact correspondence with the reduced numerators in the source definition.

The assertion repeated in the two entries is counted once. The recurrence and divisibility facts are existing mathematics and are credited below.

## Exact theorem and indexing

Set
$$
D=1-X+X^2,\qquad A=1-2X,
$$
and define integer polynomials
$$
P_0=1,\quad P_1=A,\quad
P_{n+2}=AP_{n+1}-DP_n.
$$
The source row has degree $n$ and is $P_n$. Peter Bala's November 2026 source addendum uses one-based row indexing: its $R(N,X)$ is $P_{N-1}(X)$.

For every $n\ge0$ we prove
$$
\left(\frac1D\right)^{(n)}
=\frac{n!P_n}{D^{n+1}},\qquad
\gcd(P_n,D)=1,\qquad \deg P_n=n.
$$
Since $D$ is monic, the canonical reduced numerator over $\mathbb Q[X]$ is **exactly** $n!P_n$. Dividing by $n!$ therefore gives precisely the source row, with no unproved assumption about cancellation or normalization.

For $n>0$, the classification is
$$
\boxed{P_n\text{ is irreducible over }\mathbb Q
\quad\Longleftrightarrow\quad
n+1\text{ is prime and }n+1\ne3.}
$$
The degree-zero row $P_0=1$ is a unit. The exceptional prime gives
$$
P_2=3X(X-1).
$$
The first prime cases are
$$
\begin{aligned}
P_1&=1-2X,\\
P_4&=-1+5X-10X^3+5X^4,\\
P_6&=1-21X^2+35X^3-21X^5+7X^6.
\end{aligned}
$$

## Complete proof

### 1. Differential identities and the source numerator

The recurrence and the identities $A'=-2$, $D'=-A$ give
$$
P_{n+1}'=-(n+2)P_n, \tag{1}
$$
and
$$
DP_n'+(n+1)AP_n=(n+1)P_{n+1}. \tag{2}
$$
Here is a simultaneous induction. Both formulas hold at $n=0$. If they hold at $n$, differentiation of the recurrence gives
$$
\begin{aligned}
P_{n+2}'
&=-2P_{n+1}+AP_{n+1}'+AP_n-DP_n'\\
&=-2P_{n+1}-(n+1)AP_n-DP_n'\\
&=-(n+3)P_{n+1},
\end{aligned}
$$
using (2). Also (1) and the recurrence give
$$
DP_{n+1}'+(n+2)AP_{n+1}
=(n+2)(AP_{n+1}-DP_n)
=(n+2)P_{n+2}.
$$
This proves the induction.

The derivative formula now follows by induction as well. Its base is $P_0=1$. If it holds at order $n$, the quotient rule and $D'=-A$ give
$$
\left(\frac{n!P_n}{D^{n+1}}\right)'
=\frac{n!\big(DP_n'+(n+1)AP_n\big)}{D^{n+2}}
=\frac{(n+1)!P_{n+1}}{D^{n+2}}.
$$

There is no cancellation. The identity
$$
A^2=4D-3
$$
shows that $A$ and $D$ are coprime over $\mathbb Q$: explicitly
$$
-\frac A3 A+\frac43D=1.
$$
Starting with $P_0=1$, reduction of the recurrence modulo $D$ gives
$$
P_{n+2}\equiv AP_{n+1}\pmod D.
$$
Thus induction proves $P_n$ coprime to $D$ for every $n$. The factorial is a nonzero rational scalar, so $n!P_n$ is coprime to $D^{n+1}$. Since this denominator is monic, the displayed numerator is the canonical reduced numerator.

### 2. Degree, leading coefficient, and constant coefficient

Induction on the recurrence gives
$$
\deg P_n\le n,\qquad [X^n]P_n=(-1)^n(n+1).
$$
For the leading-coefficient calculation, the recurrence reduces to
$$
(-2)(-1)^{n+1}(n+2)-(-1)^n(n+1)
=(-1)^{n+2}(n+3).
$$
This coefficient is nonzero in characteristic zero, so
$$
\deg P_n=n,\qquad \operatorname{lc}(P_n)=(-1)^n(n+1). \tag{3}
$$

Define integers $s_0=0$, $s_1=1$, $s_{j+2}=s_{j+1}-s_j$. Specializing the polynomial recurrence at zero gives
$$
P_n(0)=s_{n+1}.
$$
The integer sequence is periodic with period six:
$$
(s_0,s_1,s_2,s_3,s_4,s_5)=(0,1,1,0,-1,-1).
$$
For a prime $p\ne3$, either $p=2$ or $p\equiv1,5\pmod6$. Consequently
$$
P_{p-1}(0)=s_p\in\{1,-1\}. \tag{4}
$$

### 3. Prime indices: reciprocal Eisenstein

Let $p$ be a prime other than $3$ and write
$$
P_{p-1}(X)=\sum_{j=0}^{p-1}c_jX^j.
$$
Equation (1) gives
$$
P_{p-1}'=-pP_{p-2}.
$$
Comparing coefficients shows that $p$ divides $jc_j$ for each $1\le j\le p-1$. Since $p$ does not divide such a $j$, it divides every positive-degree coefficient $c_j$.

By (3), $c_{p-1}=(-1)^{p-1}p$, which is not divisible by $p^2$. By (4), $c_0=\pm1$. Therefore the reciprocal
$$
Q(X)=X^{p-1}P_{p-1}(X^{-1})
=c_0X^{p-1}+c_1X^{p-2}+\cdots+c_{p-1}
$$
has leading coefficient prime to $p$, every other coefficient divisible by $p$, and constant coefficient not divisible by $p^2$. Eisenstein's criterion proves $Q$ irreducible over $\mathbb Q$.

Reversal preserves irreducibility here: a factorization of $P_{p-1}$ would have two factors with nonzero constant coefficients, whose reciprocals would give a factorization of $Q$ of the same respective degrees. Thus $P_{p-1}$ is irreducible.

This is the classical Eisenstein criterion applied after reversal, not a new general irreducibility criterion.

### 4. Composite indices and the exceptional prime

Let $U_0=0$, $U_1=1$, and $U_{j+2}=AU_{j+1}-DU_j$. Then
$$
U_N=P_{N-1}\qquad(N\ge1).
$$
The classical Lucas addition identity is
$$
U_{m+n+1}=U_{m+1}U_{n+1}-DU_mU_n.
$$
It follows by induction that $U_d$ divides $U_{kd}$ for every positive $k$: the induction step uses
$$
U_{kd+d}=U_{kd}U_{d+1}-DU_{kd-1}U_d.
$$
This proves
$$
d\mid N\quad\Longrightarrow\quad P_{d-1}\mid P_{N-1}
\qquad(d,N>0). \tag{5}
$$
The addition and divisibility identities are established results, including Norfleet's Theorem 1 and Corollary 1; they are re-proved in the formal package as dependencies.

If $N=n+1$ is composite, choose a proper prime divisor $d$ of $N$. Then
$$
1\le\deg P_{d-1}=d-1<N-1=\deg P_{N-1}.
$$
Equation (5) gives a nonconstant proper divisor, so $P_n$ is reducible. Finally $P_2=3X(X-1)$ handles $N=3$. Together with the prime argument, this proves the asserted equivalence. $\square$

## Formal verification

The project pins Lean **4.19.0** and mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. Reproduce with:

```sh
lake exe cache get
lake build
```

| Module | Responsibility |
|---|---|
| `SixthDerivative.lean` | Integer recurrence, differential identities, exact degrees and leading coefficients, six-periodic constants |
| `LucasDivisibility.lean` | Classical addition formula and index divisibility for a generic second-order recurrence |
| `ReverseTransfer.lean` | Transfer of irreducibility from a reciprocal when the constant coefficient is nonzero |
| `ReverseEisenstein.lean` | Standard integer Eisenstein criterion, reversal, and Gauss's lemma |
| `Irreducibility.lean` | Prime irreducibility, composite obstruction, exceptional index, and the full equivalence |
| `RationalDerivative.lean` | Formal derivation on rational functions and the iterated quotient rule; reused unchanged from the previous package |
| `SourceBridge.lean` | Literal rational function, iterated derivative, coprimality, and canonical reduced numerator |
| `Proof.lean` | Complete irreducibility equivalences for the canonical numerator and the exact normalized source row |

The algebra endpoint is `SixthDerivative.irreducible_iff`. The exact source endpoints are `SixthDerivative.source_numerator_irreducible_iff` and `SixthDerivative.source_irreducible_iff`. Theorems `derivative_numerator` and `normalized_source_numerator` identify the unnormalized and normalized source expressions exactly. Formal proofs contain no admissions, added axioms, unsafe declarations, or native-evaluation proof shortcuts. Endpoint axiom dependencies are the standard `propext`, `Classical.choice`, and `Quot.sound`.

The accompanying author build, independent review, and checksums identify the exact verified files. Shared mathlib dependencies are pinned; the independent project build does not reuse local proof objects.

## Sources, prior work, and scope

The official OEIS exports, including source programs and current comments, are preserved in [sources](sources). Exact revisions and hashes, row-index reconciliation, primary-paper comparisons, and bounded prior-publication searches are in [source_checks.md](source_checks.md).

Peter Bala's November 2026 source addendum already supplies the recurrence, closed form, roots, and strong divisibility. Mark Norfleet's [2005 paper](https://www.fq.math.ca/Papers1/43-2/paper43-2-12.pdf) supplies the classical recurrence identities and divisibility theorem. These facts are credited as prior work. The related generalized Fibonacci and tangent-polynomial irreducibility literature was checked for an earlier instance of this exact classification.

No earlier proof of the exact A326926 classification was located in the checked sources. This is a bounded search, not certification of historical priority or OEIS editorial acceptance. The contribution is a complete proof, including its formal correspondence with the source's reduced numerator.

We count **one irreducibility classification**, shared by A326926 and A326933. We do not claim a formula for the number of factors in every reducible row of A326933.
