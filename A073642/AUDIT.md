# Independent review of A073642

Reviewed November 26, 2026. The final arithmetic and asymptotic sources were read and independently recompiled with Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The compilation returned exit status 0 and printed only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Source fidelity and proof

Reviewed final source: `Proof.lean`. Its exact SHA256 and independent compiler output are recorded in `audit-verification.txt`.

The recursion for `ones` is proved equal to the sum of standard binary digits. The recursion for `a` is proved equal to the sum of the zero-based positions of those digits, using `Nat.digits 2 n`. The valuation recursion is proved equal to the standard `padicValNat 2 n`. The finite valuation-square sum includes precisely the positive integers from 1 through `n`.

The increment identities encode the carry when adding 1 to a binary integer: the popcount increases by one minus the length of the carry, and the positional sum changes by that length minus the sum of the cleared positions. Induction gives the nonnegative additive identity `2*a n + valuationSquareSum n + 3*ones n = 3*n`. This identity proves the conjectured division/subtraction formula exactly; natural-number truncation introduces no additional restriction. The final theorem uses `Nat.digits` and `padicValNat` explicitly, so no informal identification of custom helper functions is needed.

The result includes `n=0` and has no assumptions replacing the conjecture. No defect, placeholder, additional axiom, bounded-range restriction, or sequence-definition mismatch was found.


## Prior-work check

The selected formula was checked against the [official OEIS entry](https://oeis.org/A073642) and its [internal format](https://oeis.org/A073642/internal). Exact-identifier and semantic searches, together with the trureturing, Fabian Arevalo, and Eppie proof indexes, did not locate an earlier proof of the selected claim. The README records the relevant known formulas and their attributions. This search supports the source-status statement; it does not establish global publication priority.


## Independent audit of the asymptotic correction

The final `Asymptotic.lean` was reviewed after its author header and
`summatory_block` theorem were added. Both final packaged modules were
copied to a separate audit directory. `Proof.lean` was compiled to a fresh
`Proof.olean`, that directory was placed first on `LEAN_PATH`, and
`Asymptotic.lean` was then compiled against it. Both returned exit code 0.
The exact commands, output, and final source hashes are recorded in
`audit-asymptotic-verification.txt`.

The primary [OEIS entry](https://oeis.org/A073642) and
[internal entry](https://oeis.org/A073642/internal), revision 121, July 5,
2026, contain the suggested summatory asymptotic with a constant strictly
between 0.47 and 1/2. The formal correction explicitly uses the natural
logarithm, `Real.log`; its conclusion should retain that convention.

`weightSum n` sums the indices 0 through n-1. `summatory n` therefore
sums 0 through n, which equals the source's sum over 1 through n because
`a 0 = 0`. The two doubling identities separately track the sum of bit
counts and the sum of bit positions. Their simultaneous induction proves

$$
4\,\operatorname{weightSum}(2^m)+m2^m=m^2 2^m.
$$

The endpoint identity `a(2^m)=m` then gives the exact summatory formula

$$
4S(2^m)+m2^m=m^2 2^m+4m.
$$

For positive m the division and logarithm normalization are justified by
nonzero denominators. The finitely many excluded initial indices do not
affect the proved limit. The remaining error terms are 1/m and
2^(-m)/m, both tending to zero, so `power_two_limit` proves precisely

$$
\lim_{m\to\infty}\frac{S(2^m)}{2^m(\ln(2^m))^2}
=\frac{1}{4(\ln 2)^2}.
$$

The proof that this constant exceeds 1/2 is exact: a finite Taylor lower
bound proves exp(7/10)>2, giving 0<ln(2)<7/10, and rational arithmetic
completes the comparison. No numerical approximation is used as evidence
for the strict inequality.

`only_possible_limit` is a conditional uniqueness statement: any limit
of the full normalized sequence must equal the established subsequence
limit. `no_limit_below_half` consequently rules out every proposed
constant below 1/2, including the interval in the source. The module does
not prove or assume that the full all-index limit exists. This scope
matches the revised README and is sufficient to refute the stated
natural-log constant range.

No semantic mismatch, unsupported growth assumption, placeholder,
nonstandard axiom, or `native_decide` use was found in the final module.
The two audited asymptotic theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.
