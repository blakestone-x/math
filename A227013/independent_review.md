# Independent review: A227013

**Decision: PASS.** Reviewed November 27, 2026 by the number13 agent, which did not contribute to this package's proof or configuration. No mathematical or source-scope blocker was found. The reviewer made no proof/configuration changes.

## Literal source and exact target

I independently fetched the current official OEIS-data record and the frozen [immutable revision](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A227/A227013.seq). They agree with the package's 1,180-byte source file and SHA256 `46325556aa29c1c490c7b3fbd35295840230765aede9205bdb98b77986e890bc`. Revision 21 is dated November 3, 2024; the repository export date is a separate date. The literal block runs from (n−1)^4+1 through n^4, inclusive, for positive n.

`blockLen`, `reciprocalSum`, and `harmonic` reproduce this block exactly: the finite sum has j=0,...,d−1 and denominator (n−1)^4+1+j. Positivity and the natural-subtraction cast are proved under n≥1. Rational arithmetic represents these harmonic means exactly. The selected conjectural endpoint is the displayed generating function, not an assumption that the printed closed formula or recurrence is correct.

The power series has coefficient j equal to the literal a(j+1), matching the printed rational function's constant coefficient 1 and the source's positive offset. Both the numerator and the factored denominator are the exact printed expressions. The denominator constant is −1, so the proved multiplication identity determines its quotient uniquely in the formal power-series ring.

## Mathematical proof audit

I read all eight Lean modules and the complete human manuscript.

1. **Exact centered sums.** The ordinary power sums through degree six are established by induction, and the centered second, fourth and sixth moments follow by polynomial expansion. Their formulas agree with the moments used in the manuscript and later rational bounds.
2. **Paired reciprocal inequalities.** Reflection j↦d−1−j correctly pairs the consecutive reciprocals. The two remainder identities are exact rational identities. The proof establishes the positive denominators and the centered-position bound before using nonnegativity, including the one-element block.
3. **Quartic specialization.** The midpoint is c=(n²−n+1)², the radius is (d−1)/2, and c²−r²=n⁴((n−1)⁴+1). These agree with the literal endpoints. The lower and upper bounds estimate H/d, so their directions are correctly reversed when bounding d/H.
4. **Uniform strict separation.** The positive-coefficient certificates yield Q(n)H<d and (Q(n)+2/3)H>d for every n≥5. Positivity of Q, H and d is established. The resulting strict sandwich Q(n)<d/H<Q(n)+2/3 is therefore valid for every required large index, without an asymptotic assumption.
5. **Floor and exceptions.** The three residue classes show that Q(n) has fractional part either 0 or 1/3. Thus its upper sandwich bound lies at or below the next integer, while the harmonic mean is strictly below that bound. Exact rational kernel calculations handle n=1,2,3,4; the exceptional terms 1 and 6 are retained explicitly.
6. **Recurrence and generating function.** The residue-class quartic polynomials prove the order-seven recurrence for arbitrary indices of the closed sequence. Transport to the literal source is valid when every involved index is at least three, i.e. newest index at least ten. Exact initial coefficient calculations retain all corrections through generating-function degree eight. The final theorem identifies the source sequence before applying the formal series identity.

The manuscript supplies the full algebraic proof and all 25 rows of the two certificate polynomials. I checked every displayed coefficient against the machine-readable coefficient lists and the Lean expressions. Independently, SymPy normalization verified both complete rational certificate identities, positivity of all their coefficients, the midpoint-radius factorization, and the source denominator factorization. The two certificate degrees are 24 and 14.

## Index conventions and scope

The manuscript and README accurately disclose that the source's printed cosine-polynomial expression is a(n+2) for positive n, rather than a same-index expression. The source recurrence's condition n>2 is also corrected: the literal recurrence fails at n=9, where its right side is 5233 while a(9)=5232, and it holds for every n≥10. The formal endpoint includes the recurrence failure. These are clarifications and consequences within the single generating-function source family, not separate problem counts.

The formal scope is precise. `full_resolution` contains the all-positive-index source identification, the corrected floor formula, the literal power-series coefficient bridge, and the exact source numerator-denominator identity. It does not assert a general theorem for arbitrary polynomial block functions.

## Independent fresh build and axiom audit

The [independent build](independent_build.log) copied only the eight proof modules and pinned configuration into a new isolated directory, sharing external dependency caches but no local compiled proof objects. `lake build` exited with code 0. Every local module is an explicit default root. Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` match the package configuration.

The principal endpoints report only `propext`, `Classical.choice`, and `Quot.sound`. No proof source contains `sorry`, `admit`, a custom axiom, or `native_decide`. The exact initial computations use kernel reduction. The build emits a few tactic-style lint warnings; these do not indicate admitted goals or failed checks.

## Prior-work and supplementary checks

I read the source dossier and query receipts, independently fetched the complete jOEIS and LODA generators, and independently fetched the cited cubic repository's README at the pinned commit. The generators encode the proposed recurrence but do not identify it with the harmonic mean. The prior repository's stated theorem scope covers cubic block functions, including A227012 and A227015; it does not cover the quartic block in this package. Attribution and the refusal to claim worldwide priority are appropriate.

As an independent follow-up, I ran exact and semantic queries in current ProveIt and trureturing. The exact identifier returned no hits. Semantic hits concerned digamma powers, Fourier harmonics, harmonic-number bounds, matrix means, Ramsey arguments and other unrelated material. The compact [reviewer receipts](sources/independent_semantic_receipts.json) record the observed current revisions and bounded results. These queries strengthen the recorded screen but do not establish exhaustive global priority.

Before running the supplied verifier, I independently computed the literal means with exact fractions at n=1,...,6, checked both sandwich bounds at n=5,6, all 37 displayed source terms, and the nine nonzero generating-function product coefficients. I then inspected and reran [verify.py](verify.py), which passed its exact literal checks through n=10, moment and certificate replays, formal-series coefficients through degree 200, recurrence through newest index 300, and the n=9 failure. Finite checks are supplementary; the universal claims are proved in Lean.

**Final result:** source correspondence, human mathematics, formal proof, build reproducibility, index corrections, and bounded provenance documentation all pass independent review.
