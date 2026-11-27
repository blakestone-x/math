# A184534: the reciprocal cube-root floor and its exact generating function

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

This package proves the empirical generating function in [OEIS A184534](https://oeis.org/A184534) from the literal real-root definition, and corrects the indexing of the separate empirical closed form.

For positive integers n, define

\[
a(n)=\left\lfloor\frac1{\{(n^3+4)^{1/3}\}}\right\rfloor,
\]

where braces denote fractional part. Then

\[
\boxed{a(1)=1,\qquad a(2)=3,\qquad a(3)=7,\qquad
a(n)=\left\lfloor\frac{3n^2}{4}\right\rfloor\quad(n\ge4).}
\]

Consequently Colin Barker's empirical generating function is correct:

\[
\boxed{\sum_{n\ge1}a(n)x^n=
\frac{x(x^6-2x^5+x^4-x^2-x-1)}{(x-1)^3(x+1)}.}
\]

The equality is proved coefficientwise as an identity of formal power series in Lean. The denominator has constant coefficient −1 and is a unit, so the proved numerator–denominator identity determines the quotient uniquely.

## A general cube-root estimate

The main inequality is proved for an entire array. For integers 0 < h ≤ n,

\[
\left\lfloor\frac1{\{(n^3+h)^{1/3}\}}\right\rfloor
=\left\lfloor\frac{3n^2}{h}\right\rfloor.
\]

Put q = floor(3n²/h). The hypotheses imply q ≥ 3n > 0, hq ≤ 3n², and h(q+1) ≥ 3n²+1. Two exact cubic comparisons give

\[
(n^3+h)q^3<(nq+1)^3,
\qquad
(n(q+1)+1)^3<(n^3+h)(q+1)^3.
\]

Indeed, the first difference is

\[
q^2(3n^2-hq)+3nq+1>0.
\]

For the second comparison, the right side minus the left side equals

\[
(q+1)^2\bigl(h(q+1)-3n^2\bigr)-3n(q+1)-1
\ge(q-3n)(q+1)+q>0.
\]

Since real cubing is strictly increasing, these inequalities place the root strictly between n+1/(q+1) and n+1/q. Its integer part is n, and taking the reciprocal of its positive fractional part places the result strictly between q and q+1. This proves the floor formula. Substitution h=4 covers every n≥4. Separate exact integer cubic comparisons prove the three smaller values; no floating-point root evaluation is used.

## The corrected indexing and recurrence

The source prints the empirical formula

\[
\frac{3(1-(-1)^n+4n+2n^2)}8
\]

as a(n) for n>2. At n=3 it equals 12, while the actual source value is 7. The expression is a(n+1) for n≥3. Equivalently, for n≥4 the correct same-index expression is

\[
a(n)=\frac{3(2n^2-1+(-1)^n)}8.
\]

The exact source recurrence holds from newest index 8:

\[
a(n)=2a(n-1)-2a(n-3)+a(n-4)\qquad(n\ge8).
\]

Its cutoff is necessary: the same recurrence fails at n=7. The formal proof retains the exceptional initial values, proves the recurrence at all required later indices, and derives every coefficient of the displayed generating function. It also proves the closed-form discrepancy at n=3.

## Formalization

| Module | Role |
| --- | --- |
| [CubeRoot.lean](CubeRoot.lean) | The literal real power, fractional part and floor; the general h-parameter theorem; exact initial-value certificates. |
| [Sequence.lean](Sequence.lean) | The corrected all-index sequence, parity formulas, the unbounded recurrence, and the printed-formula counterexample. |
| [GeneratingFunction.lean](GeneratingFunction.lean) | The exact one-based source coefficients and the formal numerator–denominator identity. |
| [Proof.lean](Proof.lean) | The combined endpoint and axiom reports. |

The principal endpoints are `A184534.general_formula`, `source_eq_term`, `source_recurrence`, `source_generating_function`, and `full_resolution`. `sourceSeries` has coefficient zero equal to zero, and coefficient n equal to the literal source expression for every positive n. This follows the entry's offset 1; no claim is made that the source expression at n=0 should be the constant coefficient.

The project pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All four local proof modules are explicit default build roots. To reproduce:

```sh
lake exe cache get
lake build
```

The [author build](verification.txt) and [independent build](independent_build.log) compile from copied source/configuration files in fresh isolated directories, sharing only pinned external dependency caches. The [independent review](independent_review.md) checks the mathematics, literal source, offsets, and final theorem scope. Principal axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The proof sources contain no `sorry`, `admit`, custom axiom, or `native_decide`.

[verify.py](verify.py) independently checks the floor values by exact integer cubic comparisons and replays the recurrence and generating-function coefficients. Its finite replay is supplementary; the unbounded conclusion is proved in Lean.

## Attribution and prior-work scope

Clark Kimberling supplied the sequence in 2011. Barker supplied the empirical closed form and generating function in 2012. The eventual formula and recurrence already appear in numerical generators; this package does not claim to have first discovered those expressions. It supplies the complete real-root proof, corrects the printed index, and proves the exact recorded generating-function assertion.

The [source dossier](source_checks.md) records the immutable OEIS export, both web engines, exact and semantic global/scoped GitHub checks, and inspected related implementations. No earlier proof of the exact source-to-generating-function assertion was located in that bounded search. Global historical priority is unverified.

This package counts as one source-assertion resolution. The general array estimate, parity formulas, recurrence, and indexing correction are components and consequences of the same proof.
