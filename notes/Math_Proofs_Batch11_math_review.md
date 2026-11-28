# Batch 11: independent mathematical and manuscript review

**PASS: no mathematical or source-interpretation correction required.** Reviewed November 27, 2026.

This review was performed by a contributor who authored none of the Batch 11 proof modules or conventional proof sections. It compared the complete combined manuscript and guide with the exact archived OEIS statements, the package mathematical descriptions, and the relevant formal definitions and endpoints. The reviewer independently recomputed the finite scanner discrepancy described below. No proof source or manuscript text was edited during this review, and no additional Lean build was run.

## Exact reviewed artifacts

| Artifact | SHA-256 |
|---|---|
| `Math_Proofs_Batch11.tex` | `ef3a25ae01370a647212e48dd5a6910869e384f35c501b5939b094ff20873379` |
| `Math_Proofs_Batch11.pdf` | `e0a029afb16c693c74fc637be660b4c35deea505881e5578a41987bf1d116b23` |

The PDF is the final nine-page rendering supplied for this review. The publisher's separate rendering record covers the page-by-page visual inspection and final TeX compilation log. This report assesses mathematical completeness, statement alignment, counting, and attribution; it does not replace the rendering record or either project's independent fresh-build report.

## Scope and counting

The manuscript addresses **four recorded source assertions in two mathematical families**:

- One complete irreducibility classification in A327315. A069353 specifies its set of indices; its separate infinitude-of-primes question is not claimed solved.
- One length assertion repeated in A289001 and A289004.
- One length assertion for the distinct scanner in A289035.
- One length assertion for the distinct scanner in A289239.

The three scanner assertions are refuted by one common length theorem. The manuscript explicitly explains this shared proof, counts the repeated A289001/A289004 assertion once, and does not count the growth limit, recurrence obstruction, source typo corrections, quadratic-field strengthening, or supporting factors as additional conjecture resolutions. Nine algebra modules plus seven scanner modules give the stated sixteen local proof modules.

## A327315: exact statement and source bridge

The archived source program starts with derivative order zero and row `X−2`. Its displayed rows have degree `n+1`, despite the descriptive title's degree-`n` wording. The manuscript follows the program and rows consistently: the source polynomial is `P_n=S_(n+1)`, and irreducibility is equivalent to `n+1=2^a3^b`. The initial linear row is included. The normalization by `n!` and the statement for the unnormalized canonical numerator agree with the formal endpoints `source_irreducible_iff` and `source_numerator_irreducible_iff`.

The conventional recurrence argument is complete. Its top coefficients are nonzero and alternate between −1 and 1, giving degree exactly `N`. Differentiation and the recurrence yield `S_N′=−N S_(N−1)` and `D S_N′+N A S_N=N S_(N+1)`, including the stated zero boundary of the second identity. The quotient-rule induction consequently has numerator `n!S_(n+1)` and denominator `D^(n+1)`.

The two displayed Bezout identities are correct. They establish coprimality of `A` and `D` and of the first row and `D`; the recurrence modulo `D` propagates it to every row. Since the denominator is monic and `n!` is a nonzero rational unit, the formula identifies the exact canonical reduced numerator. No cancellation or source-normalization step is assumed without justification.

## A327315: both classification directions

The sixth-root relations are consistent: `u+v=uv=1`, `u²=−v`, `v²=−u`, and both sixth powers are one. The closed form has the correct phase and sign. In particular, its transformed binomial is `Y^N−v`, as used in the subsequent argument.

For `N=2^a3^b`, repeated cyclotomic expansion is applicable because each expanding prime already divides the current cyclotomic index. It gives the monic irreducible polynomial `Y^(2N)−Y^N+1=Φ_(6N)` of degree `2N`. If an irreducible factor of `Y^N−v` over the quadratic field has degree `d`, its root lies in an extension of rational degree `2d` and has rational minimal polynomial of degree `2N`. Thus `d≥N`, while divisibility gives `d≤N`. This proves irreducibility of the binomial, including `N=1`.

The fractional-linear step correctly uses `u≠v` and `v≠1`. A root cannot equal the denominator pole; the transformed root generates a field containing a root of the irreducible degree-`N` binomial. The factor-degree argument therefore proves irreducibility of the transformed degree-`N` polynomial. Descent from irreducibility over the quadratic field to irreducibility over the rationals is valid because degrees of nonzero polynomials are preserved by the coefficient embedding.

For every excluded positive degree, a prime divisor other than 2 or 3 supplies `N=pm` with `1≤m<N`. The two residue classes modulo six are both covered. The ordinary factor for `p≡1` is `S_m`; the reflected factor for `p≡5` is `S_m(1−X)`. The latter's displayed identity has the correct scalar `−u`, since `u²=−v`. Difference of powers proves the required divisibilities over the quadratic field, and polynomial division descends them to the rational coefficient field. Both factors have strictly intermediate positive degree, so they are proper factors. The final prime-factor argument excludes every positive integer outside the specified smooth set.

The Remete family identification is algebraically consistent with the displayed six-periodic coefficients and closed form. The text credits that existing polynomial family and its structural methods. It restricts the prior-literature finding to the inspected statements and records that Remete's stated sufficient criterion does not apply at parameter one. This review does not independently certify an exhaustive historical-priority search.

## The three scanners: literal rules and count equations

The source rules, seed, pair consumption, retained singleton, and unmatched-leading-letter behavior agree with the archived programs and `Scanner.rewrite`. The finite-word invariant means every 1 is followed immediately by a zero; it excludes both adjacent ones and a terminal one. The conventional preservation proof addresses the potentially delicate `01→001` boundary: its terminal output 1 is followed by the rewritten suffix's initial zero. The other variants' output boundaries also preserve the invariant.

Consequently the scanner processes exactly `floor(L_n/2)` pairs and retains a final zero if the length is odd. Each pair produces one 1, and every input 1 lies in a mixed pair. This proves the stated equations

$$
O_{n+1}=\left\lfloor L_n/2\right\rfloor,
\qquad L_{n+1}=2L_n-O_n-(L_n\bmod2).
$$

They are derived from the literal words and are independent of the variant. The manuscript does not assume the conjectured scalar recurrence. Eliminating the one-count gives exactly the displayed corrected recurrence, including its initial values.

The independent A289004 definition has the exact eight nonzero recurrence coefficients and starts at index ten. The initial-value typo is resolved correctly by the official program and term list: 151 belongs at index eight and 257 at index nine.

As an independent diagnostic, the reviewer implemented direct string scanning for each of the three rules through iteration 23, without using the arithmetic state to generate the words. All three first disagreed with the separately computed A289004 recurrence at iteration 22. The actual values at indices 19 through 23 were `53908, 92027, 157099, 268184, 457819`; the reference values were `53908, 92027, 157099, 268182, 457812`. The good-word invariant and both count equations held in every scanned case. This supports the finite comparison; the universal claims rest on the proof, not this diagnostic.

## Growth and the eventual-recurrence obstruction

The discrepancy recurrence has the correct coefficient and sign:

$$
S_{n+1}=\mu S_n+(1-\mu)e_n,
\qquad S_0=2,
\quad\mu=1-\sqrt2/2,
\quad e_n\in\{0,1\}.
$$

The interval `[0,2]` is invariant under this update. The good-word count bound also proves the length lower bound, so `L_n` is positive and tends to infinity. The displayed ratio identity then proves convergence to `λ=1+√2/2`, rather than presuming it from a characteristic equation. Multiplication of finitely many shifted consecutive ratios correctly yields `L_(n+j)/L_n→λ^j` for every fixed shift.

Dividing a hypothetical eventual relation by the positive `L_n` is valid, and its finite coefficient sum may be passed to the limit. A monic integer relation would therefore make `λ` an algebraic integer. Closure of algebraic integers under subtraction and multiplication would make `(λ−1)²=1/2` integral over the integers, contradicting the rational algebraic-integer criterion. This proves failure beyond every cutoff for every monic integer polynomial, exactly as stated by `literal_no_eventual_monic_relation`.

The source's degree-ten polynomial is transcribed correctly, including its constant term and signs. It is monic, so the general obstruction applies to it. The manuscript appropriately limits the coefficient scope to monic integer recurrences; it does not claim the same conclusion for arbitrary rational or real coefficients.

The known Pell-word identification, related density observations, and final-letter-removed recurrence are credited and kept separate from the literal retained-singleton length claims. Their different iteration convention is not used as a substitute for the new scanner bridge.

## Attribution correction and verification boundaries

The Batch 10 correction is accurate. The September 19, 2026 predecessor explicitly proves the full A211417 positive-shift assertion and stronger classification. The manuscript labels the retained Lean work as an independent formalization of prior mathematics, preserves the original audit history, and excludes this correction from the current four-assertion count. The cited historical commit and proposition labels agree with the accompanying correction report.

The manuscript names the correct source-facing Lean endpoints and pinned dependency revision. The conventional arguments match their coefficient domains, index ranges, positivity conditions, and quantifiers. Package-level author and nonauthor fresh-build records are a separate verification gate; this manuscript review did not rerun Lean or certify a build still in progress. The publisher should use the completed package reports for the final compilation claims.

**Disposition:** the frozen combined manuscript passes independent mathematical and statement-consistency review. No change to a proof, theorem, source interpretation, result count, or attribution was required.
