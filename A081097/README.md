# A081097: an exact Pell classification and the empirical generating function

This package proves Colin Barker's empirical generating function for [OEIS A081097](https://oeis.org/A081097), starting from Benoit Cloitre's literal nested-floor definition. It also gives an exhaustive, ordered classification of the positive solutions.

The assertion addressed is the **empirical generating function for the case m = 5**. The source's broader conjecture for arbitrary nonsquare m, with its wording about a recurrence of order m, is outside this result.

## Result

Let a(1), a(2), ... be the increasing positive integers n satisfying

\[
n^2=\frac15\left(n+\left\lfloor\sqrt5\,n\left\lfloor\sqrt5\,n\right\rfloor\right\rfloor\right).
\]

The restriction to positive n follows the source's listed sequence and offset. Zero also satisfies the displayed equation but is not listed in the entry.

Then

\[
\sum_{j\ge1}a(j)X^j
=\frac{X(X^7+X^6+13X^5+89X^4-17X^3-17X^2-5X-1)}
{(X-1)(X^2-4X-1)(X^2+4X-1)(X^4+18X^2+1)}.
\]

Equivalently, the sequence starts

\[
1,6,23,40,273,1870,7343,12816,87841,\ldots
\]

and satisfies the simpler inhomogeneous recurrence

\[
\boxed{a(j+8)=322a(j+4)-a(j)-64\qquad(j\ge1).}
\]

Subtracting two consecutive instances gives the order-nine homogeneous relation

\[
a(j+9)=a(j+8)+322a(j+5)-322a(j+4)-a(j+1)+a(j).
\]

## Why the classification is complete

Put y = floor(sqrt(5)n). Squaring the inequalities defining the outer floor, with all factors nonnegative, shows that its value is 5n²−n exactly when

\[
y^2=5n^2-2n+1\quad\text{or}\quad y^2=5n^2-2n+2.
\]

The converse is also proved: either integral quadratic relation forces both required floors. The n = 1 endpoint is checked within the argument.

Writing x = 5n−1 therefore gives

\[
x^2-5y^2\in\{-4,-9\},\qquad x\equiv4\pmod5,\qquad x,y\ge0.
\]

Every such pair belongs to exactly one of four ordered families. Start at one of

| Family | x | y | Initial n = (x+1)/5 |
|---|---:|---:|---:|
| 1 | 4 | 2 | 1 |
| 2 | 29 | 13 | 6 |
| 3 | 114 | 51 | 23 |
| 4 | 199 | 89 | 40 |

and repeatedly apply

\[
U(x,y)=(161x+360y,\;72x+161y).
\]

This map preserves the two norms and the residue class. For x ≥ 483 its inverse

\[
U^{-1}(x,y)=(161x-360y,\;161y-72x)
\]

has nonnegative coordinates and strictly decreases x. Infinite descent reduces every admissible pair to x < 483. The norm then forces y < 217, and an exact finite certificate gives precisely the four seeds above. Lean's kernel checks that certificate; it is not a search-based assumption about arbitrarily large solutions.

Both coordinates strictly increase between consecutive seeds, and the last seed lies below U applied to the first. The positive matrix U preserves those inequalities. Consequently the increasing sequence cycles through the four families in the displayed order, with no omitted or duplicate positive solution.

The matrix identity U²−322U+I = 0 supplies the recurrence. The formal generating-function proof compares every coefficient in the ring of integer formal power series; the displayed denominator has constant coefficient −1, so the identity uniquely determines the quotient.

## Complete formalization

The zero-based Lean function `term j` equals the source's a(j+1).

| Module | What it proves |
|---|---|
| [FloorBridge.lean](FloorBridge.lean) | Both directions between the literal real floors and the two Pell equations. |
| [PellFinite.lean](PellFinite.lean) | The bounded seed certificate, checked by the kernel. |
| [PellOrbits.lean](PellOrbits.lean) | Norm and congruence preservation, strict descent, and exhaustive orbit classification. |
| [Sequence.lean](Sequence.lean) | Strict ordering, unique enumeration of all positive literal solutions, and the recurrences. |
| [GeneratingFunction.lean](GeneratingFunction.lean) | The exact source numerator and denominator identity in integer formal power series. |
| [Proof.lean](Proof.lean) | `A081097.full_resolution`, combining enumeration, coefficients, and the source identity, with axiom checks. |

The principal endpoints are `source_iff_pell`, `pell_classification`, `source_iff_unique_term`, `term_recurrence`, `source_generating_function`, and `full_resolution`.

## Reproduction and review

The project pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All six proof modules are explicit default build roots.

```sh
lake exe cache get
lake build
python verify_integer_replay.py
```

The author and independent build logs are [verification.txt](verification.txt) and [independent_build.log](independent_build.log). The separate mathematical and source-definition review is [independent_review.md](independent_review.md). The Lean proofs use no `sorry`, custom axioms, or `native_decide`; the theorem audits permit only Lean's standard logical axioms. The integer replay is supplementary and is not the proof of the unbounded classification.

## Attribution and scope

Cloitre supplied the sequence in 2003; Barker recorded the empirical generating function in 2013. Pell descent, norm-one units, positive matrix iteration, and rational generating functions are classical tools. The contribution here is their complete application to this literal source assertion, together with a full Lean proof.

[source_checks.md](source_checks.md) records the source snapshot, exact and semantic prior-work checks, exclusions, and their limits. Searches located no earlier proof of this exact assertion; bounded searches cannot establish global priority. This is counted as one conjectural-formula resolution, with the orbit classification and recurrences as parts of the same result.

The complete human proof is also included in the [Batch 12 manuscript](../notes/Math_Proofs_Batch12.pdf).
