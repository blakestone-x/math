# Independent review of A143132

Reviewed November 26, 2026. The full main source was read and independently recompiled with Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The compilation returned exit status 0 and printed only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Source fidelity and proof

Reviewed final source: `Proof.lean`. Its exact SHA256 and independent compiler output are recorded in `audit-verification.txt`.

The sequence is the binomial transform of the finite list `[1,5,15,35,70]`, indexed from 1 by OEIS. The source defines its term at index `n+1` as `b n = 1 + 5*n + 15*choose(n,2) + 35*choose(n,3) + 70*choose(n,4)`, then defines `a n = b (n-1)`. This correctly represents the stated binomial transform and its offset. The four-step difference identity has a factor of 10. It proves period four modulo 10 for every index, and strong induction plus the four initial terms gives `a n % 10 = 1` for `n % 4 = 1`, and 6 otherwise, whenever `n ≥ 1`.

The arithmetic function at zero is irrelevant to the theorem's positive-index domain. The initial cases are finite proof obligations within an unbounded induction, not a substitute for proving all indices. No defect was found. The known binomial/polynomial formula must retain its prior attribution; the selected last-digit conjecture is its elementary congruence consequence.


## Prior-work check

The selected formula was checked against the [official OEIS entry](https://oeis.org/A143132) and its [internal format](https://oeis.org/A143132/internal). Exact-identifier and semantic searches, together with the trureturing, Fabian Arevalo, and Eppie proof indexes, did not locate an earlier proof of the selected claim. The README records the relevant known formulas and their attributions. This search supports the source-status statement; it does not establish global publication priority.
