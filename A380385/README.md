# A380385: Euler-product columns and row sums

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Results

Mats Granvik's [OEIS A380385](https://oeis.org/A380385) defines a signed triangle by a recurrence and records two tentative identifications. We prove both for every index:

\[
T(n,k)=[x^{n-k}]\prod_{i=1}^{k-1}(1-x^i)
\qquad(1\le k\le n),
\]

and

\[
\sum_{k=1}^{n}T(n,k)=-\operatorname{A010815}(n)
\qquad(n\ge1).
\]

Here A010815 is defined by the coefficients of Euler's product

\[
\prod_{i\ge1}(1-x^i).
\]

These are two assertions about one OEIS entry. The proof derives the column formula from the original recurrence. The Euler product, its coefficients, and the elementary telescoping identity used below are established mathematics and are not claimed as new.

## The exact source recurrence

The source explicitly directs readers to its Mathematica program for the precise recurrence. That program separately specifies the first column:

\[
T(n,1)=\begin{cases}1,&n=1,\\0,&n\ne1.\end{cases}
\]

For k >= 2, it sets T(n,k)=0 when n<k, and otherwise

\[
T(n,k)=\sum_{i=1}^{k-1}T(n-i,k-1)
       -\sum_{i=1}^{n-1}T(n-i,k).
\]

The first-column exception matters: applying the displayed title recurrence to every column would give T(2,1)=-1, contrary to the source program and data. We follow the source's stated exact formulation and displayed triangle. The Lean definition also sets the auxiliary zeroth column to zero.

The recurrence is well founded because every term on the right has a smaller first index. In the second sum we use the equivalent indexing j=1,...,n-1, obtained by reversing i to n-i. Thus the formal source defines the actual triangle recursively; the conjectured coefficient formula is a theorem rather than an assumption.

## Proof of the column formula

For coefficient manipulations, extend T(n,k)=0 when n<0. All generating series in this argument are formal. Write

\[
C_k(x)=\sum_{n\ge0}T(n,k)x^n.
\]

The first-column rule gives C_1(x)=x. For k >= 2, move the second sum to the left in the defining recurrence. This gives

\[
\sum_{j=1}^{n}T(j,k)=\sum_{i=1}^{k-1}T(n-i,k-1).
\]

The same identity holds for n<k because all relevant terms vanish. Taking generating series yields

\[
\frac{C_k(x)}{1-x}
=(x+x^2+\cdots+x^{k-1})C_{k-1}(x),
\]

so

\[
C_k(x)=x(1-x^{k-1})C_{k-1}(x).
\]

Induction now gives

\[
C_k(x)=x^k\prod_{i=1}^{k-1}(1-x^i).
\]

Taking the coefficient of x^n proves the first assertion, including the diagonal T(k,k)=1.

## Proof of the row-sum identity

Put

\[
P_m(x)=\prod_{i=1}^{m}(1-x^i),\qquad P_0(x)=1.
\]

Since P_k=P_{k-1}(1-x^k), the column formula gives

\[
C_k(x)=x^kP_{k-1}(x)=P_{k-1}(x)-P_k(x).
\]

Therefore, for every N,

\[
\sum_{k=1}^{N}C_k(x)=1-P_N(x).
\]

Fix n>=1 and take N=n. Taking coefficients of x^n gives

\[
\sum_{k=1}^{n}T(n,k)=-[x^n]P_n(x).
\]

Every factor 1-x^i with i>n leaves the coefficient of x^n unchanged. Consequently [x^n]P_n(x) is exactly the n-th coefficient of the infinite Euler product, which is A010815(n). This proves the second assertion.

## Formal statements and verification

[Proof.lean](Proof.lean) includes:

- `A380385.triangle`: the direct recursive definition above.
- `A380385.triangle_eq_column`: the column-polynomial identity, proved by strong induction from the recurrence.
- `A380385.column_formula`: the first source conjecture with its original n,k indexing.
- `A380385.eulerCoefficient_stable`: every finite Euler product extending through index n has the same coefficient at degree n. This supplies the precise connection to the infinite-product definition of A010815.
- `A380385.row_sum`: the full row-sum conjecture for all positive n.

The proof uses finite polynomial arithmetic and finite sums. Its theorems have no additional hypotheses on the recurrence or its solutions. The final declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; there are no unfinished proofs, additional axioms, or `native_decide` calls.

The package pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. [verification.txt](verification.txt) records the fresh build of the packaged source and its SHA-256 hash. [AUDIT.md](AUDIT.md) and [audit-verification.txt](audit-verification.txt) record the completed independent mathematical review and fresh compilation of the exact final source. The [collected proof notes](../notes/Math_Proofs_Batch5.pdf) include both arguments.

## Sources and prior-work scope

- [A380385](https://oeis.org/A380385), Mats Granvik, January 23, 2025; coefficient program dated January 25, 2025. The official export records revision 20, January 25, 2025.
- [A010815](https://oeis.org/A010815), Euler-product coefficients.
- [A231599](https://oeis.org/A231599), cited by Granvik as the related finite-product triangle.

The retrieved A380385 entry still presents the row identity tentatively and labels the coefficient program conjectural. Exact-identifier, mathematical-description, GitHub, and trureturing searches did not locate an earlier proof of these two identifications. This is a bounded source check, not an assertion of exhaustive historical priority or OEIS review. [source_checks.md](source_checks.md) records the checks and source ambiguity explicitly.

## Reproduce

From this directory with the pinned toolchain selected:

```sh
lake exe cache get Mathlib.Algebra.Polynomial.Coeff Mathlib.Algebra.GeomSum Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
lake build
```

The manifest also fixes the transitive dependencies.
