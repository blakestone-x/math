# A327315: the complete irreducibility classification

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

For every derivative order n≥0, the factorial-normalized numerator of

\[
\frac{d^n}{dx^n}\left(\frac{x-2}{x^2-x+1}\right)
\]

is irreducible over the rationals **exactly when n+1=2^a3^b for some nonnegative integers a,b**. These are precisely the indices in [A069353](https://oeis.org/A069353), as conjectured in [A327315](https://oeis.org/A327315).

The result covers every source row, including the initial polynomial X−2 at derivative order zero. The degree is n+1. The source title's reference to degree n is an indexing mistake: its displayed rows and executable definition consistently give degree n+1. That descriptive correction is documented in [source_checks.md](source_checks.md) and is not counted as a separate resolution.

This package proves one complete classification. It also proves irreducibility over the quadratic field containing a primitive sixth root of unity in the allowed degrees, produces a proper factor in every excluded degree, and establishes the exact correspondence with the canonical reduced derivative numerator. These are parts of the same proof.

## Exact polynomial and source definition

Write

\[
A=1-2X,\qquad D=1-X+X^2,
\]

and define degree-indexed polynomials by

\[
S_0=-1,\quad S_1=X-2,\quad
S_{N+2}=A S_{N+1}-D S_N.
\]

The Lean definition is `TwistedDerivative.poly R N`, over a general commutative coefficient ring R. Over the rationals, S_N has degree N and leading coefficient (−1)^(N+1). The OEIS row at derivative order n is S_(n+1).

The exact source bridge is

\[
f^{(n)}(X)=\frac{n!\,S_{n+1}(X)}{D(X)^{n+1}},
\qquad f(X)=\frac{X-2}{D(X)}.
\]

There is no cancellation between S_N and D. Since D is monic, the canonical rational-function numerator is exactly n!S_(n+1), and multiplying it by 1/n! gives S_(n+1). Thus the theorem concerns the reduced numerator in the original definition, not a loosely related polynomial sequence.

The formal derivative is the usual quotient-rule operation on rational functions. `RationalDerivative.derivative_div` proves that it is independent of the fraction used to represent the rational function, and `iterate_div` proves the repeated quotient-rule formula.

## Why the classification holds

### 1. Recovering the derivative rows

The recurrence gives the differential identities

\[
S_N'=-N S_{N-1}\quad(N\ge1),\qquad
D S_N'+N A S_N=N S_{N+1}.
\]

Since D′=−A, repeated differentiation yields the displayed rational-function formula. The identities

\[
4D-A^2=3,\qquad D-(X+1)(X-2)=3
\]

give rational Bezout certificates for A and D, and for S_1 and D. Reducing the recurrence modulo D then shows that every S_N is coprime to D. This establishes the exact numerator normalization for every n≥0.

### 2. A sixth-root closed form

Let K=ℚ(u), where u²−u+1=0, and set v=1−u. Then [K:ℚ]=2, u+v=uv=1, u³=v³=−1, and u⁶=v⁶=1. The recurrence has the closed form

\[
S_N=-v(u-X)^N-u(v-X)^N
 =(-1)^{N+1}v\big((X-u)^N-v(X-v)^N\big).
\]

The last expression is a fractional-linear transform of Y^N−v. Because u≠v and v≠1, this transform preserves irreducibility and degree.

### 3. Every allowed degree is irreducible

For N=2^a3^b, the classical cyclotomic expansion identity gives

\[
Y^{2N}-Y^N+1=\Phi_{6N}(Y).
\]

The proof starts with Φ_6=Y²−Y+1 and repeatedly substitutes Y² or Y³. Both 2 and 3 divide the cyclotomic index at every step.

To show Y^N−v irreducible over K, take any irreducible factor q of degree d and a root y in K[Y]/(q). Then y^N=v, so y is a root of Φ_(6N), irreducible over ℚ of degree 2N. Therefore

\[
2N\le [K(y):\mathbb Q]=2d,
\]

while d≤N. Hence d=N, and the binomial is irreducible. The fractional-linear formula gives irreducibility of S_N over K and therefore over ℚ.

### 4. Every excluded degree has a proper factor

If N is positive and is not of the form 2^a3^b, it has a prime divisor p>3. Write N=pm, so 1≤m<N. Every such prime is congruent to 1 or 5 modulo 6.

- If p≡1 mod 6, v^p=v. The difference-of-powers identity shows S_m divides S_N.
- If p≡5 mod 6, u^p=v. The same identity gives the reflected factor S_m(1−X), using
  \[
  S_m(1-X)=-u\big((X-u)^m-u(X-v)^m\big).
  \]

These factors have rational coefficients and degree m. Their divisibility is first checked in K[X] and then descended to ℚ[X]. Their positive degrees strictly below N prove reducibility.

For example, N=5 gives the reflected degree-one factor S_1(1−X)=−X−1, matching the factor X+1 in the printed source row n=4. N=7 gives the ordinary degree-one factor X−2 in row n=6.

## Formal organization

| Module | Role |
| --- | --- |
| `TwistedDerivative.lean` | Recurrence, derivative identities, coefficient maps, exact degrees and leading coefficients. |
| `CyclotomicSmooth.lean` | Cyclotomic identity for 2,3-smooth exponents; generic quadratic-field irreducibility argument. |
| `SixthField.lean` | Concrete quadratic field and exact sixth-root identities. |
| `MobiusIrreducibility.lean` | Fractional-linear preservation of binomial irreducibility; reused unchanged from the earlier polynomial project. |
| `ClosedForm.lean` | Closed form, smooth-degree irreducibility, ordinary and reflected divisors. |
| `Classification.lean` | Every positive integer has only the prime factors 2 and 3 exactly when it is 2^a3^b; complete irreducibility criterion. |
| `RationalDerivative.lean` | Representation-independent rational-function derivative; reused unchanged. |
| `SourceBridge.lean` | Exact derivative formula, coprimality and canonical numerator. |
| `Proof.lean` | Final equivalences for the literal reduced numerator and factorial-normalized source row. |

The final endpoints are `TwistedDerivative.source_irreducible_iff` for the factorial-normalized row and `TwistedDerivative.source_numerator_irreducible_iff` for the canonical reduced numerator. Both apply to every natural number n without an extra positivity assumption. The core polynomial theorem is `irreducible_iff_smooth`; the exact source identities are `source_derivative`, `derivative_numerator`, and `normalized_source_numerator`.

The package targets Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The local proof modules use no `sorry`, `admit`, custom axioms, `unsafe`, or `native_decide`. The printed theorem dependencies are the standard `propext`, `Classical.choice`, and `Quot.sound`.

## Sources and attribution

The polynomial family and the algebraic methods are connected to earlier work. In particular, Remete's 2021 [generalized simplest polynomials](https://arxiv.org/abs/2111.08341) include this exact family under

\[
S_N(X)=(-1)^{N+1}f_1^{(N)}(X-1).
\]

This identification is derived by comparing the definitions. Remete's Corollary 10 gives a sufficient irreducibility criterion requiring a prime p≠3 with v_p(m²+m+1)=1. It does not apply at m=1, because m²+m+1=3. The inspected irreducibility section does not give the complete degree classification at this parameter.

The fractional-linear and cyclotomic approach also has antecedents in Cass–Cullinan–Rasmussen–Trifunovski's [generalized Rikuna specializations](https://homepages.math.uic.edu/~dtrifu2/pdf/rikuna_spec.pdf) and Calcut's [tangent analogues of Chebyshev polynomials](https://www2.oberlin.edu/faculty/jcalcut/arctan.pdf). These connections are credited; the underlying all-degree polynomial construction and the standard cyclotomic theorems are not presented as new.

The checked OEIS source still contains the explicit conjecture. Exact-identifier searches, semantic literature checks, the trureturing catalog, and targeted global/ProveIt GitHub code searches did not locate an earlier proof of this exact classification. This is a bounded prior-publication review, not a guarantee of historical priority. The preserved source exports, hashes, search scope and closest primary references are recorded in [source_checks.md](source_checks.md).
