# A052392: the empirical subdiagonal generating function and recurrence

This package proves the two formulas recorded as empirical by Robert Israel on November 26, 2018, for [OEIS A052392](https://oeis.org/A052392). They are treated as **one source family**, with one all-index Lean endpoint. The sequence is defined independently of the claimed formulas by the source's triangle algorithm, including its exceptional entry `T(2,1) = 3`.

## Exact result

Let `T(r,0) = T(r,r) = 1`, let `T(r,k) = 0` for `k > r`, and set `T(2,1) = 3`. For `r >= 3` and `0 < k < r`, put

\[
T(r,k)=T(r-1,k-1)+2T(r-2,k-1)+T(r-1,k).
\]

With the original offset `n = 0`, define `a(n) = T(2n+1,n)`. Then

\[
\sum_{n\ge0}a(n)x^n
=\frac{2x^2-3x+1}{2x\sqrt{1-8x+4x^2}}+\frac{x-1}{2x},
\]

where the formal square root has constant term 1. For every integer `n >= 0`,

\[
8na(n)-(32+28n)a(n+1)+(78+30n)a(n+2)
 -(45+11n)a(n+3)+(5+n)a(n+4)=0.
\]

The apparent pole at zero cancels: the identity is an identity of formal power series. The Lean theorem uses its equivalent form after multiplication by `2X`; it also proves that the reciprocal square root with constant term 1 exists and is unique. There is no assumed coefficient formula, assumed recurrence, or finite verification in the proof.

## Proof idea

Write the triangle in square coordinates `S(m,n) = T(m+n,n)`. Let `D(m,n)` be the weighted Delannoy array with boundary entries 1 and interior rule `D(m+1,n+1) = D(m,n+1) + D(m+1,n) + 2D(m,n)`. An induction proves

\[
S(m+1,n+1)=D(m+1,n+1)-D(m,n).
\]

A second double induction proves a balance identity for `D`. It yields a three-term recurrence for `d(n) = D(n,n)` and the exact relation

\[
2a(n+1)=d(n+2)-3d(n+1)+2d(n).
\]

The diagonal recurrence gives the formal differential equation `(1-8X+4X²)D' = (4-4X)D`. Differentiating `(1-8X+4X²)D²` shows it is the constant 1. Substituting the exact relation gives the generating function. A displayed linear combination of five diagonal recurrences gives the source's order-four recurrence, with index zero checked separately.

The complete argument, including the boundary conditions and the induction identity, is in [manuscript-section.tex](manuscript-section.tex).

## Source interpretation and prior work

The frozen source [sources/A052392.seq](sources/A052392.seq) contains Israel's two empirical formulas and the exact Maple algorithm used here. Its associated triangle is [A054120](https://oeis.org/A054120). Russell Jay Hendel's June 2, 2015 comment in that entry already proves the local triangle recurrence from the original strip-sum definition. That recurrence is credited prior work. This package begins from the algorithm actually attached to A052392 and proves its empirical subdiagonal formulas.

Weighted Delannoy generating functions are classical. Paul Barry's 2006 paper, *On Integer-Sequence-Based Constructions of Generalized Pascal Triangles*, develops the surrounding generalized-triangle framework. The present proof does not claim that framework or Hendel's recurrence as new. The bounded exact and semantic search, including global GitHub search and the current ProveIt and trureturing repositories, found source mirrors and sequence-generation code, but no proof of the exact A052392 assertions. See [source_checks.md](source_checks.md). This is a source-status resolution; worldwide priority is not asserted.

## Formal proof

The package pins Lean **4.19.0** and mathlib commit **c44e0c8ee63ca166450922a373c7409c5d26b00b**. Run:

```sh
lake exe cache get
lake build
```

Every local module is an explicit default root:

| File | Content |
| --- | --- |
| `Array.lean` | Independent source triangle, Delannoy difference, balance identity, diagonal recurrence |
| `Recurrence.lean` | The exact empirical recurrence for every `n >= 0` |
| `GeneratingFunction.lean` | Formal differential equation, unique normalized reciprocal root, exact generating function |
| `Proof.lean` | `A052392.full_resolution`, joining the source assertions and printing axiom audits |

All principal theorems use only Lean's standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), with some requiring fewer. No `sorry`, custom axioms, admitted identities, or `native_decide` occur.

The author clean build starts from proof source and pinned configuration only; local compiled proof objects are excluded. Its log is `verification.txt`, produced by the batch build harness. An independent reviewer supplies a separate clean build and review record.

## Supplemental finite check

`python3 verify.py` recomputes the literal triangle, compares all 23 terms displayed in the frozen source, checks 100 instances of the recurrence, and verifies 101 coefficients of the squared-root identity and cleared generating function with exact integer arithmetic. These checks help detect transcription errors. The unbounded proof is the Lean development and manuscript, not this computation.

## Completed independent review

The [independent review](independent_review.md) passed, with a separate [fresh source-only build](independent_build.log). Both build logs identify the exact proof and configuration hashes.
