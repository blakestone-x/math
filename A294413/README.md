# A294413: a complementary recurrence with a negative correction

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Result

For the complementary sequences in [OEIS A294413](https://oeis.org/A294413),

\[
a_{n+2}=a_{n+1}+a_n-b_{n+1}+6,
\qquad a_0=1,\quad a_1=3,\quad b_0=2,\quad b_1=4,
\]

we prove the conjectured limit

\[
\lim_{n\to\infty}\frac{a_{n+1}}{a_n}
=\phi=\frac{1+\sqrt5}{2}.
\]

We also prove the explicit estimate

\[
\left|\frac{a_{n+2}}{a_{n+1}}-\phi\right|
\le20(n+1)\left(\frac23\right)^n\qquad(n\ge0).
\]

The main additional work is a growth argument that remains valid despite the negative complementary term. A general assertion that positivity and a summable normalized disturbance suffice for a dominant-root ratio limit is false; the proof here derives an exponential lower bound directly.

## Exact specification and scope

The formal `Solution` requires two strictly increasing natural-number sequences whose ranges are disjoint and cover every positive integer, the four seeds above, and the displayed recurrence. The recurrence is an equality over the integers, so subtraction is not truncated at zero.

The theorem applies to every pair satisfying those defining conditions. It assumes neither convergence nor a growth bound. It does not separately formalize the mex construction or prove existence and uniqueness of a complementary pair.

The source's title, seeds, displayed a-data, and Mathematica program agree with this specification. Its example line for the complement contains a typo: it includes 6, although a(2)=6. The actual complement starts 2,4,5,7,8,9,11,... . We use the defining equation and seeds, not that inconsistent example.

## Proof

### 1. A counting bound

If t<a(i) and t<b(j), every integer from 1 through t occurs among the first i terms of a or the first j terms of b. Hence

\[
t\le i+j.\tag{1}
\]

In particular, if a(i)>i+j+1, then b(j)≤a(i). Otherwise (1), applied with threshold t=a(i) and indices i+1,j, would give a(i)≤i+j+1.

### 2. Linear bounds from the original recurrence

We first prove a(n)≥3n by strong induction. The initial terms are a(0)=1, a(1)=3, a(2)=6. For n≥3 the inductive bound gives

\[
a(n-1)\ge3(n-1)>2(n-1)+1.
\]

The consequence of (1) with i=j=n−1 yields b(n−1)≤a(n−1). Therefore

\[
a(n)=a(n-1)+a(n-2)-b(n-1)+6
\ge a(n-2)+6\ge3n.
\]

Now suppose b(n)>2n+2. Since a(n+1)≥3n+3>2n+2, applying (1) with threshold 2n+2 and indices n+1,n gives 2n+2≤2n+1, a contradiction. Thus

\[
b(n)\le2n+2.\tag{2}
\]

### 3. An exponential lower bound

Define

\[
u_n=a(n+1)-2(n+1).
\]

The initial values are u(0)=1 and u(1)=2. Substituting the original recurrence gives

\[
u_{n+2}=u_{n+1}+u_n+2n+6-b(n+2).
\]

The last term is nonnegative by (2). Since (3/2)²≤3/2+1, two-step induction gives

\[
u_n\ge(3/2)^n,\qquad a(n+1)\ge(3/2)^n.\tag{3}
\]

This is the crucial point: positivity alone would not give the growth needed to control the ratio.

### 4. A contracting step error

Put A(n)=a(n+1) and e(n)=6−b(n+2). Then

\[
A_{n+2}=A_{n+1}+A_n+e_n,
\qquad |e_n|\le6(n+1).
\]

Define d(n)=A(n+1)−φA(n). The identity φ²=φ+1 yields

\[
d_{n+1}=(1-\phi)d_n+e_n.
\]

Because |1−φ|≤2/3, induction gives

\[
|d_n|\le\bigl(18+|6-3\phi|\bigr)(n+1)\le20(n+1).
\]

Divide by the proved bound (3). This gives the stated quantitative estimate, whose right side tends to zero. Deleting or adding one initial term does not change the limit, so the original ratio a(n+1)/a(n) tends to φ.

## Prior work and source status

Clark Kimberling's entry, introduced October 31, 2017, still labels the ratio limit conjectural in the retrieved source. The included official snapshot is revision 9, November 1, 2017.

Kimberling and Moses, [*Linear Complementary Equations and Systems*, Fibonacci Quarterly 57(5) (2019), 96–110](https://www.fq.math.ca/Papers1/57-5/kimberling-moses.pdf), study these equations. Their Theorem 2.1 assumes that the ratio limit exists and that its disturbance is positive. It therefore does not establish the convergence needed here.

An earlier publicly available [*Kimberling Note*](https://www.scribd.com/document/1067832042/kimberling-note), uploaded by `bambasene564` (publication date not established), also claims A294413 using a general signed-disturbance theorem. That theorem, as stated, has a counterexample: choose c=d=1, a(n)=1, and D(n)=−1. The sequence is positive and the weighted absolute disturbances sum to a finite value, but every successive ratio is 1 rather than φ. The missing positive-growth conclusion cannot follow from those hypotheses. The direct bounds (1)–(3) above supply the needed condition for A294413.

The recurrence-normalization method and positive-disturbance arguments are prior mathematics, including the related sketch in that note. We claim a complete formal proof of the precise A294413 assertion with its derived growth bound, not invention of the general recurrence method or exhaustive historical priority. The bounded search found the earlier attempt but did not locate an earlier complete valid proof for this negative-correction case. See [source_checks.md](source_checks.md).

## Formal verification

- [Proof.lean](Proof.lean) states the original conditions, proves the counting and growth bounds, and concludes `A294413.conjecture` and `A294413.ratio_error_bound`.
- [Analytic.lean](Analytic.lean) is reused byte-for-byte from the repository's A294532 package. Its signed-disturbance theorem requires an exponential lower bound; the present proof establishes that premise.
- [AUDIT.md](AUDIT.md) and [audit-verification.txt](audit-verification.txt) record a separate mathematical review and fresh isolated compilation of both exact source files.
- [verification.txt](verification.txt) records a fresh build of the complete pinned package.
- [Collected proof notes](../notes/Math_Proofs_Batch5.pdf) present the proof alongside the other results in this batch.

Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` check all declarations. The final theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. There are no unfinished proofs, additional axioms, `native_decide` calls, or unsafe replacements.

## Reproduce

With the pinned toolchain selected, run from this directory:

```sh
lake exe cache get
lake build
```

The manifest also pins the transitive dependencies.
