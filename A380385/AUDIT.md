# Independent mathematical and formal audit of A380385

The complete final `Proof.lean` was read, matched against the official OEIS export, and recompiled in a new isolated directory with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Compilation returned exit code 0. The exact command output and source hash are in `audit-verification.txt`.

## Definition and source correspondence

The official `oeis/oeisdata` source, `seq/A380/A380385.seq`, revision 20 (January 25, 2025), was independently retrieved. Its blob SHA is `d56997e8a4b51da96ea087378580fcfb4265d9f5`. The source explicitly directs the reader to the Mathematica program for the exact recurrence. That program sets T(n,1) to 1 at n=1 and to 0 otherwise, then applies the displayed two-sum recurrence to subsequent columns. The source title alone omits this exception. The formal `triangle` matches the program and the displayed triangle, and the README identifies the ambiguity.

For k>=2 and k<=n, the second sum in the formal definition runs over j=1,...,n-1 rather than using n-i; reversal of the source summation index gives precisely this expression. Every recursive call has a smaller row index. Terms above the triangle and the auxiliary zeroth column are zero. No generating-function identity is assumed in the definition.

## Column formula

The polynomial `column k` is X^(k+1) times the finite Euler product through k. Its first term is X, and the proved multiplication rule is exactly the one required by the recurrence. `column_prefix` derives the prefix-sum equation by a polynomial geometric-sum identity. The treatment of natural-number subtraction is valid because all column polynomials have zero constant coefficient; coefficients below the shift therefore vanish even when the natural difference truncates to zero.

Strong induction on the row proves `triangle_eq_column` from the recursively defined triangle for every row and column. The source-indexed `column_formula` then follows by the coefficient shift for 1<=k<=n. It includes the diagonal and exceptional first column.

## Row sum and the infinite-product interpretation

The finite identity sum(column k)=1-eulerProduct m is proved by induction and telescoping, not assumed. Coefficient extraction gives the row sum for every n>0. `eulerCoefficient_stable` proves that factors with exponent greater than n do not change the degree-n coefficient. This is the exact formal-series interpretation of the infinite Euler product; no analytic convergence assumption is needed.

The separate official A010815 export was checked. Its definition is the coefficient of degree n in the infinite product of (1-q^m), and its finite-product programs use the same truncation through n. Thus identifying the stable finite coefficient with A010815 is justified. Euler's pentagonal-number theorem itself is not asserted as a newly proved result or required as a premise.

## Verification result

No missing hypotheses, definition substitutions, unfinished proofs, custom axioms, unsafe declarations, or `native_decide` calls were found. The three reported final declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Checked source SHA-256:

`6eeee2111267ae5b08c4df6a8791b9fcf1872bad230449fe7c35a7021677806a  Proof.lean`

This establishes the two stated identifications for the exact source-program recurrence. Historical-priority claims remain limited to the source searches recorded separately.
