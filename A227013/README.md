# A227013: the harmonic mean between consecutive fourth powers

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

This package proves the conjectured generating function in [OEIS A227013](https://oeis.org/A227013) from the literal harmonic mean. It also gives the corrected same-index floor formula and valid recurrence cutoff.

For n ≥ 1, let

\[
d_n=n^4-(n-1)^4,\qquad
H_n=\sum_{k=(n-1)^4+1}^{n^4}\frac1k,\qquad
a(n)=\left\lfloor\frac{d_n}{H_n}\right\rfloor.
\]

Then

\[
\boxed{a(1)=1,\quad a(2)=6,\quad
a(n)=\left\lfloor n^4-2n^3+\frac53n^2-\frac23n\right\rfloor\quad(n\ge3).}
\]

With the first source term placed at degree zero, the exact source generating function is

\[
\boxed{\sum_{j\ge0}a(j+1)x^j=
\frac{-1-2x-22x^2-23x^3-20x^4-4x^5+2x^6-3x^7+x^8}
{(x-1)^5(1+x+x^2)}.}
\]

The formal proof establishes this identity in ℤ[[X]], with no assumed formula or recurrence for the harmonic mean. The denominator has constant coefficient −1, so the quotient is uniquely determined.

## Main argument

Pair each reciprocal in a consecutive block with its reflected partner about the block's midpoint c. For centered positions t with |t|≤r<c, two exact rational identities bound

\[
B(c,t)=\frac12\left(\frac1{c+t}+\frac1{c-t}\right)
\]

between

\[
\frac1c+\frac{t^2}{c^3}+\frac{t^4}{c^5}+\frac{t^6}{c^7}
\quad\text{and}\quad
\frac1c+\frac{t^2}{c^3}+\frac{t^4}{c^3(c^2-r^2)}.
\]

Exact central moments through degree six give lower and upper bounds on H_n/d_n. For the quartic block, c=(n²−n+1)². Clearing denominators and shifting n=t+5 gives two explicit positive-coefficient polynomials. Their identities are proved by Lean's polynomial normalization, and their coefficients are in [polynomial_certificates.json](polynomial_certificates.json) and the complete [manuscript](manuscript-section.tex).

Writing Q(n)=n⁴−2n³+5n²/3−2n/3, these bounds prove the strict sandwich

\[
Q(n)<\frac{d_n}{H_n}<Q(n)+\frac23\qquad(n\ge5).
\]

The fractional part of Q(n) is either 0 or 1/3, so the sandwich fixes the floor. Exact rational kernel computations handle n=1,2,3,4. The resulting quartic polynomial plus a period-three correction satisfies the order-seven recurrence. Preserving the two exceptional initial values gives the exact numerator of the source generating function.

## Indexing corrections

The source prints a cosine-polynomial expression as a(n). That expression is actually a(n+2) for n≥1: at n=1 it equals 40, while the literal first term is 1. Our same-index formula above is proved from the harmonic mean.

The recurrence is

\[
a(n)=4a(n-1)-6a(n-2)+5a(n-3)-5a(n-4)+6a(n-5)-4a(n-6)+a(n-7),
\]

valid for every n≥10. The source's printed cutoff n>2 cannot be used literally; even at n=9 the right side is 5233 rather than a(9)=5232. The formal proof includes this counterexample. The generating function's constant coefficient 1 corresponds to a(1), so the formal source series explicitly uses coefficient j equal to a(j+1).

The exact generating-function assertion is counted as one resolution. The floor estimate, corrected indices, recurrence, and helper inequalities are parts of the same family.

## Complete formal development

| Module | Role |
| --- | --- |
| [Moments.lean](Moments.lean) | Ordinary power sums by induction; exact central moments through degree six. |
| [Bounds.lean](Bounds.lean) | Reflection of the literal reciprocal sum; paired rational identities; uniform sum bounds. |
| [Certificates.lean](Certificates.lean) | Both positive-coefficient polynomial identities for every shifted index. |
| [SourceBounds.lean](SourceBounds.lean) | Literal quartic block and harmonic mean; strict sandwich; exact initial values. |
| [Sequence.lean](Sequence.lean) | Residue-class floor formulas and the unbounded order-seven recurrence. |
| [GeneratingFunction.lean](GeneratingFunction.lean) | Exact source numerator and denominator for the independently specified closed sequence. |
| [Source.lean](Source.lean) | Proof identifying every positive literal harmonic-mean floor with that sequence. |
| [Proof.lean](Proof.lean) | Literal source power series, full generating-function endpoint, recurrence, and cutoff counterexample. |

The main endpoint is `QuarticHarmonic.full_resolution`. All eight local modules are explicit default build roots. The package pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```sh
lake exe cache get
lake build
python3 verify.py
```

The [author build](verification.txt) and [independent build](independent_build.log) start in separate fresh directories from proof source and pinned configuration, with no local compiled proof objects copied. Their logs preserve exact source hashes. The [independent review](independent_review.md) checks the source, all proof layers, the polynomial certificates, and the indexing conventions. The principal audits use only `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, admitted lemma, custom axiom, or `native_decide`.

`verify.py` supplements the unbounded proof with exact rational literal values, source terms, recurrence and formal-series coefficients. Finite numerical agreement is not used as a substitute for the universal theorem.

## Prior work and scope

The cubic case A227012 and the general cubic recurrence theorem already have a complete proof in [rajdeepbaror/kimberling-a227012-lean](https://github.com/rajdeepbaror/kimberling-a227012-lean). We inspected that work and excluded those cubic results. Its theorem does not cover fourth-power blocks. This package proves the quartic source assertion, not a general theorem for arbitrary polynomial block functions.

Moment identities, rational inequalities, and polynomial-periodic recurrences are classical. The proposed formula and recurrence already occur in OEIS and numerical generators. Our selected contribution is the complete proof and formal source bridge for the recorded conjectural generating function. The [source dossier](source_checks.md) describes the bounded exact and semantic prior-work search; it does not claim worldwide historical priority.
