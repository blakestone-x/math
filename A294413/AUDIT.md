# Independent mathematical and formal audit of A294413

Both complete source files were read and independently recompiled with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. A fresh `Analytic.olean` was built in an isolated directory, which was then placed first on `LEAN_PATH` when compiling `Proof.lean`. Both compilations returned exit code 0. The commands, output, and hashes are recorded in `audit-verification.txt`.

## Source fidelity

The [official OEIS entry](https://oeis.org/A294413) and the [official export file](https://github.com/oeis/oeisdata/blob/main/seq/A294/A294413.seq) give the seeds a(0)=1, a(1)=3, b(0)=2, b(1)=4 and recurrence

\[
a(n)=a(n-1)+a(n-2)-b(n-1)+6.
\]

The checked `Solution` uses those seeds, strict increase of both sequences, disjoint positive cover, and the correctly shifted recurrence over the integers. The negative term is genuine integer subtraction. The final theorem quantifies over every pair satisfying those defining conditions; it does not add a growth or convergence hypothesis or claim a separate construction or uniqueness theorem.

The source's example line listing the complement is inconsistent: it includes 6 even though the recurrence and displayed a-data give a(2)=6. The title, seeds, recurrence, Mathematica mex program, and displayed a-data agree with the formal specification. The actual complement begins 2,4,5,7,8,9,11,... . The inaccurate example line should not be used as a defining condition. This issue was reported to the package author for its source documentation.

## Growth proof

The threshold-count lemma is valid: if a(i) and b(j) both exceed t, every positive integer through t must appear among the first i terms of a or the first j terms of b, giving t<=i+j.

The three base values a(0)=1, a(1)=3, a(2)=6 are correct. Strong induction then proves a(n)>=3n. For the induction step, the threshold bound and a(i)>=3i show b(i)<=a(i) for i>=2. The signed recurrence consequently gives a(i+1)>=a(i-1)+6, which closes the lower-bound induction.

Applying the same threshold count at t=2n+2 gives b(n)<=2n+2. There is no use of an unproved density or asymptotic assertion in either bound.

The shifted sequence

\[
u_n=a(n+1)-2(n+1)
\]

has u_0=1, u_1=2 and recurrence

\[
u_{n+2}=u_{n+1}+u_n+2n+6-b(n+2).
\]

Its disturbance is nonnegative by the complement bound. The analytic two-step induction therefore proves u_n>=(3/2)^n, hence a(n+1)>=(3/2)^n. This establishes the exponential growth needed for the signed-error ratio theorem, rather than assuming it.

## Analytic conclusion and quantitative estimate

For v_n=a(n+1), the original disturbance is 6-b(n+2). The proof derives its absolute bound by 6(n+1). The general analytic theorem controls the golden-ratio step error and divides by the proved exponential lower bound. This establishes the ratio limit itself.

The constant in the quantitative bound is also justified: the general coefficient is

\[
18+|6-3\phi|\le20.
\]

Thus, for all n>=0, the proved bound is exactly

\[
\left|\frac{a(n+2)}{a(n+1)}-\phi\right|
\le20(n+1)(2/3)^n.
\]

The final unshifted ratio theorem follows from invariance of a limit under deletion of one initial term. No denominator is zero, no asymptotic assumption is substituted for growth, and no conclusion from an unproved signed-disturbance principle is used.

## Formal result

No defect, placeholder, custom axiom, `native_decide` use, finite-range restriction, or sequence-definition mismatch was found. The final declarations `A294413.conjecture` and `A294413.ratio_error_bound` depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Checked SHA-256 hashes:

- `Analytic.lean`: `35ee9e50e139b60137e69f0269513a85a65b8c538be46fa77dabed0739b0e3ad`
- `Proof.lean`: `1cb2fe23435602b2433a7feb440cf04d70875fa419b1c14ab8644bb7521a18d6`

This audit verifies mathematical and formal correctness and the source specification. Broader publication-priority claims depend on the separately recorded literature search.
