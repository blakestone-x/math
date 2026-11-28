# A202253 and A202254: bounded zero-sum arrays

This package proves the recorded counting formulas, recurrences, and generating functions for ordered arrays of three or four integers. Every entry and every adjacent difference must lie in `[-n,n]`, and the entries must sum to zero. Adjacency is linear, without a wraparound edge.

For every natural number `n`, the literal counts satisfy

\[
A_3(n)=1+2\left\lfloor\frac{2n^2+2n}{3}\right\rfloor,
\]

and

\[
A_4(n)=\begin{cases}
(22n^3+33n^2+26n+12)/12,&n\text{ even},\\
(22n^3+33n^2+26n+3)/12,&n\text{ odd}.
\end{cases}
\]

These are Kimberling's A202253 floor conjecture and Barker's A202254 parity conjecture. The formal sequences are cardinalities of the actual finite sets of source arrays, not definitions by these formulas.

## Proof

For three entries, fix the middle entry `y≥0` and eliminate the third entry. Every source condition reduces to `y−n≤x≤n−2y`, which is nonempty exactly when `3y≤2n`. Count this interval and use negation to pair the positive and negative slices.

For four entries, fix the sum `s=b+c≥0` of the middle two entries and put `m=n−s`, `h=floor(m/2)`, `epsilon=m mod2`, and `v=a+c`. The arrays biject with the integer points

\[
-h\le b\le n-h-\epsilon,\quad -m\le v\le m,\quad -m\le b+v\le n.
\]

This is a rectangle with two equal triangular corners removed. Its size is `(n+1−epsilon)(2m+1)−h(h+1)`. Sum the slices and pair their signs to obtain the cubic parity formula. The manuscript gives all bijections and polynomial sums explicitly.

## Exact source generating functions

The source entries start at index one. Their generating functions therefore have constant coefficient zero, even though the natural array counts have `A_3(0)=A_4(0)=1`:

\[
\sum_{n\ge1}A_3(n)x^n=\frac{x(3+3x+2x^2-x^3+x^4)}{(1-x)^3(1+x+x^2)},
\]

\[
\sum_{n\ge1}A_4(n)x^n=\frac{x(7+10x+2x^2+4x^3-x^4)}{(1-x)^4(1+x)}.
\]

The associated fifth-order recurrences hold for every source index `n≥6`; they also hold at `n=5` with the natural index-zero extensions. The formal generating functions retain these indexing conventions explicitly.

## Modules and reproduction

| Module | Content |
|---|---|
| [Arithmetic.lean](Arithmetic.lean) | Floor arithmetic and finite sums |
| [TripleCount.lean](TripleCount.lean) | Literal triples, explicit signed-slice bijection, exact count |
| [CornerCount.lean](CornerCount.lean) | Rectangles, triangular corner bijections, disjoint partition |
| [QuadrupleCount.lean](QuadrupleCount.lean) | Literal quadruples and exact slice decomposition |
| [QuadrupleFormula.lean](QuadrupleFormula.lean) | Parity formula and recurrence |
| [GeneratingFunction.lean](GeneratingFunction.lean) | Exact source power-series identities and coefficient conventions |
| [Proof.lean](Proof.lean) | Public formula endpoints and principal axiom audits |

Run `lake build` with Lean4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All seven proof modules are explicit default roots. Fresh source-only author and independent build records accompany the final package. The supplementary [verify.py](verify.py) uses exact integer arithmetic to replay literal finite counts, frozen terms, individual slices, recurrences and generating-function products. The unbounded proofs are in Lean.

## Attribution and scope

Hardin authored both source arrays. Kimberling conjectured the triple formula; Barker conjectured the quadruple formulas and both generating functions. The underlying floor sequence A143978 is known prior background. An existing admitted A202253 statement and a synthetic formula implementation are acknowledged in [source_checks.md](source_checks.md).

This is **one mathematical family with two source entries**. Recurrences and generating functions are consequences within that family. A202253's separate proposed interpretation by bounded triples satisfying `w+2x+3y=0` is outside the selected scope.

Exact and semantic searches found no earlier complete proof of these selected source-count assertions in the inspected material. Those bounded checks do not establish worldwide priority. The complete human proof is in [manuscript-section.tex](manuscript-section.tex), with immutable [source snapshots and hashes](sources/manifest.json).
