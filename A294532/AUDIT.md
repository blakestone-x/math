# Independent audit of the complementary Fibonacci family

Reviewed November 26, 2026.

## Formal verification

The complete final `Analytic.lean` and `Proof.lean` were read. Byte-identical copies were then compiled in a fresh isolated directory, with the newly built `Analytic.olean` first on the module search path. Both compilations returned exit status 0. The final ratio-limit and quantitative-bound theorems report only `propext`, `Classical.choice`, and `Quot.sound`.

Exact source hashes, commands, compiler output, and successful exit codes are recorded in `audit-verification.txt`. No `sorry`, additional axiom, finite-data assumption, circular definition, or unproved convergence premise was found.

## Match to the 34 source definitions

Each of the 34 coefficient rows was independently compared against the title in the downloaded official OEIS export for A294532 through A294565. The Lean recurrence uses `a(n+2)`, so a source term `r*n+c` becomes `r*n+(2*r+c)` in the Lean parameter table. All rows have the correct shift, signs, and coefficients.

The shared defining conditions are exactly the positive-integer partition into increasing complementary sequences, initial values `a(0)=1`, `a(1)=2`, `b(0)=3`, and the selected recurrence. The source title for A294565 has constant -2; its family guide instead gives -3. The code proves both variants with distinct parameter names. The additional guide variant is not an additional OEIS sequence and should not be counted as one.

The Mathematica snippet in A294532 itself uses different initial values, `a(1)=3` and `b(0)=2`. The formal specification follows the title, the family guide's stated seeds, and the displayed sequence data, which agree on `a(1)=2` and `b(0)=3`; it does not adopt the conflicting snippet.

## Mathematical checks

Strict monotonicity and the initial values imply `a(n)≥n+1` and `b(n)≥n+3`. Every supported forcing term is at least 2. The proof of the gap bound correctly excludes the initial consecutive terms 1 and 2: any hypothesized gap of at least three between successive `b` values would force two consecutive integers greater than 3 into `a`, contradicting its proved later gap of at least two. Hence `b(n)≤2*n+3` for every index.

The verified coefficient table then gives a nonnegative forcing term bounded by `32*(n+1)`. Converting this integer forcing term to a natural number uses a proved nonnegativity fact, so no truncation changes the recurrence.

For the real recurrence, the exponential lower bound `(3/2)^n≤a(n)` follows by two-step induction. With `phi=(1+sqrt(5))/2`, the step error satisfies

$$
d_{n+1}=(1-\phi)d_n+e_n,\qquad d_n=a_{n+1}-\phi a_n.
$$

The coefficient has absolute value at most 2/3. The linear bound for `d_n` and exponential lower bound for `a(n)` therefore imply convergence of the successive-term ratio to `phi`, without assuming that this limit exists. The final uniform estimate

$$
\left|\frac{a_{n+1}}{a_n}-\phi\right|
\le97(n+1)(2/3)^n
$$

has the correct constant and index shift. The finite case split over 35 parameter records is only a verification of explicit linear inequalities; each resulting sequence theorem holds at all indices.

## Scope and prior work

`Solution` contains the OEIS sequence-defining conditions. The formal result applies to every pair satisfying those conditions. Construction, existence, and uniqueness of such complementary pairs are not separately formalized in this package; they are not replaced by a convergence assumption.

The relevant prior source is Clark Kimberling and Peter J. C. Moses, [*Linear Complementary Equations and Systems*, Fibonacci Quarterly 57(5), 2019, pp. 96–110](https://www.mathstat.dal.ca/FQ/Papers1/57-5/kimberling-moses.pdf). Its Theorem 2.1 explicitly assumes that the ratio limit exists before identifying it. The present analytic argument proves convergence from the defining sequence conditions. The audit confirms this distinction; it does not assert global publication priority beyond the source-status search documented with the package.
