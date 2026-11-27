# Independent audit of A389524

Reviewer: root agent, separate from the agents that developed the proof.
Date: November 26, 2026 (America/Chicago).

## Result

**PASS.** Conjectures 1 and 3 are proved from the source's recursive
triangle for every positive integer index. Both final modules were
compiled independently, in dependency order, in a fresh directory with
Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

| Source | Audited SHA-256 |
|---|---|
| `Uchimura.lean` | `878257266d1ebc4e4f1791dc18a3a2d9b7c6e0d323d4ecaecc8ecfe74423305a` |
| `Proof.lean` | `54ebf0871d58e0f529d110dd2b641dab5f3f9d6370cb0455a3323616385d70ab` |

The second module used the freshly generated first module, not a prior
local compiled copy. Both compiler exits were zero. The printed theorem
dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`.
See `audit-verification.txt` for the complete verification record.

## Exact statement review

The primary A389524 snapshot records three numbered conjectures. This
package proves the first (row sums equal the divisor count) and the third
(`T(2n,n)=n-d(n)`). The weighted orphan-count identity numbered 2 is
explicitly excluded in the source comments, README, and source checks.

The formal `triangle` retains the exceptional first-column initialization
in the source's Mathematica program. For later columns it uses the same
integer-valued recurrence and zero region. Its second sum runs through
`j=1,...,n-1`, which is the source's sum through `n-i` in reverse order.
The auxiliary column zero is outside the displayed domain. Recursive
calls decrease the first argument, so the termination proof is valid.

`triangle_eq_column` covers every row and every positive column. It proves
the connection to the polynomial construction by strong induction,
including entries above the diagonal and the first column. No polynomial
sequence is assumed to agree with the recursively defined triangle.

The row-sum theorem includes exactly the nonzero region `1≤k≤n`; columns
beyond it vanish by the source definition. The divisor target is the
cardinality of the standard `Nat.divisors` finset. Its coefficient bridge
uses a checked bijection of positive factor pairs, rather than treating a
Lambert coefficient as a new definition of the divisor function.

The diagonal theorem uses integer subtraction, consistent with A049820's
definition. The boundary case `n=1` is included and gives zero on both
sides.

## Algebra review

The finite Uchimura proof works in a commutative ring with an element
`q` satisfying `q^(N+1)=0`. Invertibility of `1-q^i` for positive `i` is
proved from nilpotence. The polynomial factor `1-qz` is likewise a unit.
Consequently all cancellations in the scaling identity and derivative
step have explicit justified invertibility hypotheses.

The scaling equations for `H` and `G` include their finite boundary
terms; the nilpotence hypothesis makes those boundary terms vanish.
Comparing coefficients in `K(qz)=K(z)` forces all positive-degree
coefficients of `K` to be zero. Evaluating and differentiating the product
identity then yields the finite weighted-tail/Lambert identity.

Specialization to `AdjoinRoot (X^(N+1))` proves equality modulo that
polynomial. `X_pow_dvd_iff` supplies equality of coefficients at every
degree at most `N`. The later application takes `N=n`, so it is within
the proven range. Every geometric sum is finite and has the correct
truncation. No analytic convergence theorem is being implicitly used.

The polynomial recurrence linking row sums to weighted tails starts from
zero and includes the new constant term in A389524. It does not reuse the
different A380385 recurrence as an assumption. The final diagonal
calculation follows from the same verified weighted-tail coefficients.

## Human proof, attribution, and scope

The complete README argument agrees with the formal steps, including the
quotient-ring argument and the positive-divisor bijection. Uchimura's
1981 identity and Bressoud–Subbarao's 1984 treatment are explicitly credited
as classical prior work. The claimed contribution is the connection to
the two exact 2025 triangle conjectures and its full formal verification.

There are no proof placeholders, custom axioms, `native_decide` calls,
unsafe proof replacements, or finite-index substitutes for the universal
statements. The package counts two assertions in one sequence entry and
makes no global priority or OEIS acceptance claim.
