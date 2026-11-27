# A118207: the Liouville–cyclotomic product identity

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

This package proves Peter Bala's conjectural formula in [OEIS A118207](https://oeis.org/A118207), including the full passage from finite products to formal power series.

Let λ(n) = (−1)^Ω(n), where Ω counts prime factors with multiplicity, and define

\[
A(X)=\prod_{n\ge1}(1+X^n)^{\lambda(n)}.
\]

Then, for the usual cyclotomic polynomials Φₙ,

\[
\boxed{A(X^2)=\prod_{n\ge1}\Phi_n(X^n)\Phi_n((-X)^n).}
\]

The equality holds as an identity of formal power series, so it proves equality of every coefficient. The theorem concerns the complete infinite product; a finite coefficient check is not used as a substitute for that assertion.

## Mathematical proof

Put

\[
F(X)=\prod_{n\ge1}(1-X^n)^{\lambda(n)}.
\]

Proposition 1 of Peter Bala's [April 9, 2023 note](https://oeis.org/A118205/a118205.pdf) already proves

\[
F(X)=-\prod_{n\ge1}\Phi_n(X^n).
\]

We credit that identity and its Möbius regrouping to Bala. The four-page note also proves a formula for the reciprocal, but it does not state the functional identity conjectured in A118207. Our package formalizes the helper as part of a complete proof of the latter assertion.

### The arithmetic behind the cyclotomic product

Normalize the sign by setting Ψ₁(X) = 1−X and Ψₙ(X) = Φₙ(X) for n > 1. Cyclotomic factorization and multiplicative Möbius inversion give

\[
\Psi_n(X)=\prod_{d\mid n}(1-X^d)^{\mu(n/d)}.
\]

Consequently,

\[
\prod_{n\ge1}\Psi_n(X^n)
=\prod_{a,d\ge1}(1-X^{ad^2})^{\mu(a)}.
\]

The exponent of 1−X^m is

\[
\sum_{d^2\mid m}\mu(m/d^2)=\lambda(m).
\]

To prove the last equality, write m uniquely as ab² with a squarefree. All summands except d = b vanish. The remaining summand is μ(a) = λ(m), because removing square factors does not change the parity of the number of prime factors. This proves Bala's normalized product and accounts for its single overall minus sign.

### Splitting the even and odd indices

Complete multiplicativity gives λ(2n) = −λ(n). Pairing factors at X and −X gives

\[
F(X)F(-X)=
\prod_{\substack{m\ge1\\m\text{ odd}}}(1-X^{2m})^{\lambda(m)}
\prod_{m\ge1}(1-X^{2m})^{-2\lambda(m)}.
\]

Meanwhile,

\[
\begin{aligned}
A(X^2)
&=\prod_{n\ge1}\left(\frac{1-X^{4n}}{1-X^{2n}}\right)^{\lambda(n)}\\
&=\prod_{\substack{m\ge1\\m\text{ even}}}(1-X^{2m})^{-\lambda(m)}
  \prod_{m\ge1}(1-X^{2m})^{-\lambda(m)}.
\end{aligned}
\]

In both expressions the exponent on 1−X^(2m) is −λ(m) for odd m and −2λ(m) for even m. Thus A(X²) = F(X)F(−X). Substituting Bala's identity at X and −X cancels its two signs and proves the conjecture.

All regroupings are finite modulo X^(N+1) for each N: a factor with exponent greater than N is already 1 in that quotient. There is no analytic convergence assumption.

## Complete formalization

The proof first works with an arbitrary nilpotent element in a commutative ring. Its products have finite multiplicative support and its factors are units, so negative integer exponents are legitimate. It then applies the theorem to the class of X in ℚ[[X]]/(X^(N+1)) for every N.

| Module | Role |
| --- | --- |
| [FiniteProducts.lean](FiniteProducts.lean) | Quotients by X^(N+1), coefficient separation, nilpotent units, and finite-support product regrouping. |
| [CyclotomicUnits.lean](CyclotomicUnits.lean) | Sign-normalized cyclotomic polynomials, their unit evaluations, and multiplicative Möbius inversion. |
| [Arithmetic.lean](Arithmetic.lean) | Complete multiplicativity of λ, λ(2n) = −λ(n), unique squarefree-times-square decomposition, and the square-divisor formula. |
| [EulerRegroup.lean](EulerRegroup.lean) | Both explicit fiber regroupings, Bala's helper, and the complete nilpotent product identity. |
| [FormalProduct.lean](FormalProduct.lean) | A coefficientwise product construction with a proved stabilization theorem. |
| [SourceSeries.lean](SourceSeries.lean) | The literal two factor families in the source, all quotient-tail bounds, and equality of the complete formal products. |
| [Proof.lean](Proof.lean) | The combined endpoint and axiom audits. |

The factor `liouvilleSquareFactor n` is the unit power (1+X^(2n))^λ(n). The factor `cyclotomicPairFactor n` uses the actual mathlib cyclotomic polynomials evaluated at X^n and (−X)^n. Index zero is set to the neutral factor, so both products begin at the source's index one.

`formalProduct` takes its degree-N coefficient from the finite prefix through index N. `cutMap_formalProduct` proves that later factors cannot change that coefficient. The source factors satisfy the required tail hypothesis, and their images are identified exactly with the nilpotent units used in the algebraic proof. Equality in every quotient implies equality of every coefficient.

The principal endpoints are:

- `A118207.product_scaledCycloUnit_eq_euler`: Bala's normalized helper in an arbitrary nilpotent ring.
- `A118207.nilpotent_cyclotomic_pair`: the complete product identity for nilpotent elements.
- `A118207.source_conjecture`: the exact source equality in ℚ[[X]].
- `A118207.source_coefficient_identity`: equality in every natural-number degree.
- `A118207.full_resolution`: the source equality and all coefficient identities together.

## Reproduction and review

The project pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Every proof module is an explicit default build root.

```sh
lake exe cache get
lake build
```

The author build is recorded in [verification.txt](verification.txt). The independent build and mathematical/source review are recorded in [independent_build.log](independent_build.log) and [independent_review.md](independent_review.md). The proof files use no `sorry`, `admit`, custom axioms, or `native_decide`. Printed axiom dependencies are restricted to Lean's standard logical axioms.

## Attribution and scope

Clary supplied the sequence in 2006. Bala stated the target conjecture on April 5, 2023 and supplied the separate helper proof in the April 9 note. Cyclotomic factorization, Möbius inversion, the Liouville square-divisor formula, and the even/odd split are classical. The result counted here is one resolution of the precise A118207 formula, together with a full formal proof.

[source_checks.md](source_checks.md) records the immutable source snapshot, the closest primary work, exact and semantic prior-work checks, and their limits. No earlier settlement was located in the inspected sources. Those bounded checks do not establish worldwide priority.

The complete human proof is included in the [Batch 12 manuscript](../notes/Math_Proofs_Batch12.pdf).
