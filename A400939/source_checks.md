# Source identity and bounded prior-resolution review

Checked on November 27, 2026 UTC. This note documents the material actually inspected. It is not a certificate that all literature or unpublished work has been searched.

## Primary source

- Entry: [OEIS A400939](https://oeis.org/A400939), the halving Recamán walk.
- Entry author and date: Zlatko Damijanic, October 10, 2026.
- Retrieved source header: `%I A400939 #58 Nov 05 2026 19:25:01`.
- Repository: [`oeis/oeisdata`](https://github.com/oeis/oeisdata).
- File: `seq/A400/A400939.seq`.
- Git blob identifier: `c9db5ad44bbf95b2a7d4c0f054c51901cbdaf231`.
- Latest file-changing export commit returned by the GitHub commits endpoint: `df38d77b83a78d8ab5aaa501dec6e3a3db977f01`, November 20, 2026.
- [Immutable file link](https://github.com/oeis/oeisdata/blob/df38d77b83a78d8ab5aaa501dec6e3a3db977f01/seq/A400/A400939.seq).
- Exact retrieved UTF-8 source retained in `sources/A400939.seq`; its Git blob hash was checked against the connector response.

The `%N` definition starts at index 1 with value 1 and divides by 2 only when the quotient is an unvisited integer. The generalized-divisor `%C` comment replaces 2 by an arbitrary divisor that is not a power of 2, and conjectures eventual permanent addition. That comment has no separate author/date attribution in the retrieved entry. It reports checks for divisors through 10^10. No independent repetition of those source computations is claimed or needed here.

The same entry also conjectures that every positive integer appears in the divisor-2 walk. That is a distinct assertion, outside this package's theorem. The source's statement relating positive-integer occurrence to repeated visits to dyadic chains is also outside the proved result.

MathWorld's [Halving Recamán Sequence](https://mathworld.wolfram.com/HalvingRecamanSequence.html) was inspected as a second published statement of the original rule. It explicitly notes that only the division branch requires a new value. The formal definition preserves this asymmetry.

## Exact target proved

For every odd prime p for which 5 is a quadratic nonresidue, the literal generalized walk divides exactly once, at index p or p+1. Before that index its values are triangular. Afterwards it satisfies the applicable exact identity

    2*a_p(n) + p^2 + 1 = n*(n+1),

or

    2*a_p(n) + (p+1)^2 = n*(n+1),

and none of those later values is divisible by p. A finite triangular-prefix test distinguishes the two possible indices. Quadratic reciprocity specializes this to every odd prime congruent to 2 or 3 modulo 5. A kernel-checked application of Dirichlet's theorem proves arbitrarily large primes in the class 3 subfamily.

This is an infinite-family partial resolution of the source's generalized-divisor conjecture. It is not a complete resolution of either conjecture in the A400939 entry.

## Search-engine checks

Both available search engines were used. Exact identifier queries were supplemented by semantic queries because an existing proof need not mention the OEIS number. The following are the substantive query groups; quoted phrases were queried literally where shown.

| Engine | Queries | Observed result |
|---|---|---|
| Search 1 | `"A400939" proof division k`; `"A400939" "5" "prime"`; `"A400939" site:trureturing.org` | The primary entry, MathWorld, OEIS contest announcement, and unrelated identifier collisions. No proof of the prime-family classification identified. |
| Search 1 | `"Recaman" "5" "quadratic nonresidue"`; `"halving Recaman" "stops dividing"`; `"A400939" proof theorem -site:oeis.org -site:mathworld.wolfram.com`; `site:trureturing.org "Recamán" OR "Recaman"` | The source conjecture and unrelated Recamán material. No equivalent classification identified. |
| Search 2 | `"halving Recaman" "quadratic"`; `"A400939" "nonresidue"`; `"Recamán" "division" "prime" "5"`; `"A400939" "generalized"` | OEIS announcements and distinct Recamán sequences. A December 2025 note on a recurrence dividing or multiplying by the changing index concerns a different process, not the fixed-divisor visited-value rule. |
| Search 2 | `"halving Recaman" "prime" "quadratic"`; `"division Recaman" "five"`; `"A400939" proof "stops"` | Source entry and unrelated results; no equivalent theorem identified. |

Search results are a bounded discovery aid. Failure to locate a proof is not proof of its absence. No claim of historical priority beyond this documented check is made.

## trureturing catalog and issue checks

The live [trureturing conjecture catalog](https://www.trureturing.org/conjectures) was opened. It displayed 2,235 resolved results. Text searches for `A400939` and `Recam` found no matches. Searching `halving` found a result about halving partitions, which concerns a different object. Earlier attempts to open the home URL and `/research/` failed; the later successful catalog read is the actual catalog evidence.

The GitHub connector searched the current issues of `the-omega-institute/trureturing`:

1. `repo:the-omega-institute/trureturing A400939` returned [issue 20145](https://github.com/the-omega-institute/trureturing/issues/20145), about prime digit sums in different bases, and [issue 20169](https://github.com/the-omega-institute/trureturing/issues/20169), about generalized Eulerian numbers. Their A400939 occurrences are incidental source-exposure records. Neither asserts a proof of this walk classification.
2. `repo:the-omega-institute/trureturing "Recaman"` returned the [A386969 closed-form issue 18645](https://github.com/the-omega-institute/trureturing/issues/18645) and [generating-function issue 18646](https://github.com/the-omega-institute/trureturing/issues/18646), plus incidental mentions in other topics. A386969 subtracts the current index when possible and otherwise adds the index plus 3. Its rule is different from division by a fixed prime, so those resolutions do not settle the target here.
3. `repo:the-omega-institute/trureturing "nonresidue" "division"` returned topics involving safe-prime products and Erdős problems 203 and 699. No A400939 or Recamán classification was identified in those results.

No issue, comment, pull request, or message was created in any external project during this review.

## Reused mathematics and credit

The modular identity `(2n+1)^2 = 4n(n+1)+1`, elementary primality, and triangular-number arithmetic are standard. The package's contribution is how the exact visited-value dynamics force the first division and the resulting offset, making that modular identity a permanent obstruction for the stated prime family.

Quadratic reciprocity is reused from mathlib's `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, at the pinned source [QuadraticReciprocity.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean).

Infinitude is reused from mathlib's `Nat.forall_exists_prime_gt_and_eq_mod`, at the pinned source [PrimesInAP.lean](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/LSeries/PrimesInAP.lean). The formal theorem does not introduce Dirichlet's theorem as a new axiom or treat it as a new result.

The bounded check found no prior proof of the exact prime-family theorem. The proof's correctness is supported separately by its Lean compilation and independent audit; correctness and novelty are distinct questions.
