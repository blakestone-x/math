# Combined manuscript: mathematical and text consistency review

**PASS — no correction required.** Reviewed November 27, 2026. This was a read-only review; the manuscript and proof sources were not edited.

Reviewed file: `output/batch10/notes/Math_Proofs_Batch10.tex`.

SHA-256 at this review: `71b8eebd50ee5eaf26b5481840a06452c9fdc90f3e505e22da56a1da496b3ede`.

## Scope and counting

- The total is exactly **five assertions: three proofs and two refutations**. The polynomial classification repeated in A326926/A326933 is one; the entire positive-shift family for all three specified values of $k$ is one; the length conjecture repeated in A289128/A289131 is one; the two position-limit assertions are two refutations.
- Eight polynomial modules plus one factorial-ratio module plus six word modules gives the stated fifteen local proof modules. Two polynomial exports plus one factorial-ratio export plus four word exports gives seven preserved OEIS exports.
- The manuscript excludes known original integrality, the older fixed-factor/negative-shift statements, and the already recorded scalar formulas from the new-result count. Historical priority and editorial acceptance are not overstated.

## Polynomial section

The derivative order, zero-based degree index, Bala's one-based row index, factorial normalization, and nonconstant restriction agree with the frozen Lean source and independently retrieved official exports. The simultaneous differential induction is correct. The Bezout identity and monic denominator justify the exact canonical numerator; cancellation is not assumed. The prime proof includes $p=2$, handles $p=3$ separately, and excludes composite indices by a proper divisor of strictly smaller positive degree. Both implications and the exact source endpoints are represented accurately.

## Factorial-ratio section

The explicit multiplier is exactly `coefficient r = ((30*r).factorial)^r`. The shift set agrees with the literal filtered interval in Lean, and the assertion is uniform in all $n\ge0$ and all $r\ge0$ for the three prescribed values of $k$. The empty-product case is stated correctly.

I independently recalculated all thirty displayed floor-function values. The manuscript's three rows are exact. I also recalculated the forced residues: for $k=2$, `14`; for $k=3$, `9,19`; for $k=5$, `5,11,17,23`. Every listed residue has value one. The nested-floor identity, the inequality $0<di<m$, the uniqueness of a large-divisor shift, the small-divisor bound, and the valuation sum for the full product are correct. Multiplicities are included. The prose justifies the original integrality before using the valuation of the integer quotient and agrees with `sourceRatio_eq_a` and the rational-integrality endpoint.

## Word section

The scanner cases, initial words, arbitrary-suffix block identity, growing block sizes, odd/even iterates, and all six count formulas agree with the frozen formalization. The recurrence begins at index six and retains the exceptional initial word. The proof explicitly constructs the nested infinite limit and uses actual one-based occurrence positions with unbounded ranks. All four displayed rational expressions and their limits are correct. The conclusion is precisely nonexistence of a real limit for each ratio; no unproved liminf, limsup, or complete cluster-set classification is asserted.

## Mathematical typography and verification claims

I found no incorrect sign, missing factorial, shifted exponent, mistaken residue, or mathematical LaTeX delimiter/tag in the reviewed source. The theorem names and source-index domains agree with the formal endpoints. The stated axiom and fresh-build boundaries are accurate now that the independent builds of all three packages have completed successfully. PDF layout and final rendering remain with the parent reviewer.
