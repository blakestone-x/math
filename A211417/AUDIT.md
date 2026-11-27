# Independent audit: A211417 positive-shift integrality

**Date:** 27 November 2026 UTC.  
**Result:** PASS for the complete stated positive-shift family.  
**Frozen proof SHA-256:** `4d276b1eb1e954f8d8ceaaf007ef63bfa6a3c9fc7179745d791875877996b964`.

A reviewer separate from the proof author read the entire frozen
`Proof.lean`, the README, the manuscript section, the source-check report,
and the archived source. An isolated fresh Lake build passed. No
mathematical or Lean-source correction was required. The full build record
is [audit-verification.txt](audit-verification.txt).

## Statement and source semantics

The reviewer independently retrieved both the current official OEIS export
and the [immutable export](https://github.com/oeis/oeisdata/blob/dff800c40a409482c9b734eecd1958986302e385/seq/A211/A211417.seq).
Both match the package's archived source byte for byte. The SHA-256 is
`a75083c938bfac328fa90aeabb3e0fd0d50313e1e2e948fa837e2dfdf409cb93`, and the
recomputed Git blob is `d0f348463c143fc227c5e0cbafaa2b49732312bb`.

The selected source assertion asks for a positive constant, depending on
`k` and `r` but independent of `n`, that makes the factorial ratio divided
by the product of eligible positive shifts integral. The permitted slopes
are exactly two, three, and five. The source requires `r≥1`; this package
also proves the empty-product case `r=0`.

In Lean, `shifts k r` is exactly the inclusive interval from one through
`r`, filtered by `Nat.Coprime i k`. Its factors are `k*n+i`. Each factor is
strictly positive, including when `n=0`. There is no omitted endpoint,
zero factor, extra coprimality condition on `n`, or finite restriction on
the indices.

The witness `coefficient r = ((30*r)!)^r` is explicitly defined before the
theorems. `coefficient_pos` proves it positive for every `r`. In
`bala_positive_shift_conjecture`, the existential witness precedes the
universal quantifier over `n`, so the constant is genuinely uniform. It
even works independently of which of the three slopes is selected. The
proof cannot be satisfied by the vacuous choice zero.

## The factorial ratio is exact

The definitions `numerator` and `denominator` contain exactly the five
factorials in the source ratio. Although `a` uses natural-number division,
the proof does not assume that this truncated operation is the source
sequence.

First, `cross_divisibility` is proved entirely for products of factorials,
before any division by the factorial denominator. Its specialization at
`r=0` yields `factorial_ratio_integral`. Consequently,
`factorial_ratio_identity` proves

```
a n * denominator n = numerator n.
```

The separately defined `sourceRatio` is the literal rational expression.
`sourceRatio_eq_a` identifies it with the rational cast of `a`. Finally,
`positive_shift_rational_integrality` constructs an integer equal to the
source's requested quotient. Thus the final theorem covers ordinary
rational integrality, with no truncation convention left unresolved.

## Review of the arithmetic argument

Let

\[
F(n,m)=\left\lfloor\frac{30n}{m}\right\rfloor+
\left\lfloor\frac n m\right\rfloor-
\left\lfloor\frac{15n}{m}\right\rfloor-
\left\lfloor\frac{10n}{m}\right\rfloor-
\left\lfloor\frac{6n}{m}\right\rfloor.
\]

The nested-division identities in `divide_scale` correctly reduce this to
the integer function

\[
f(t)=t+\lfloor t/30\rfloor-\lfloor t/2\rfloor-
\lfloor t/3\rfloor-\lfloor t/5\rfloor,
\qquad t=\lfloor30n/m\rfloor.
\]

The floor inequality is proved universally by Lean's arithmetic tactic.
The manuscript's period-30 table agrees with this function. It establishes
the nonnegative contribution for every positive `m`, including all small
prime powers.

For a selected shift, assume `m>30i` and `m∣kn+i`. Writing `kn+i=mj` and
`d=30/k` gives `30n+di=mdj`. The inequalities `0<di<m` are established
before the quotient identity is used. The conclusion is exactly
`floor(30n/m)+1=dj`, with no off-by-one ambiguity. If `k∣j`, the original
divisibility equation would force `k∣i`, contradicting the selected shift's
coprimality.

The resulting residue cases were independently checked:

| Slope `k` | Possible `t mod 30` | Value of `f(t)` |
|---|---|---|
| 2 | 14 | 1 |
| 3 | 9, 19 | 1 |
| 5 | 5, 11, 17, 23 | 1 |

Therefore `landau_at_shift` supplies exactly one extra factorial
contribution whenever a sufficiently large modulus divides a selected
shift. This argument applies to any such positive modulus; it does not
silently exclude primes dividing two, three, or five.

## The whole product and all prime-power multiplicities

For `m>30r`, two different selected shifts cannot both be divisible by
`m`: their difference has absolute value less than `m`. The Lean proof
handles both natural-subtraction directions, so it does not lose the case
where the indices are ordered oppositely. When one shift is divisible,
the previous lemma gives the required extra contribution. When none is
divisible, nonnegativity suffices.

For `m≤30r`, the number of divisible shifts is at most `r`, and
`r*floor(30r/m)≥r`. Thus `contribution_bound` covers every positive modulus
with the exact correction supplied by the explicit constant.

The proof then counts divisibility at **every prime-power level** for
**every factor**. `valuation_as_sum` and `valuation_shiftProduct` formally
justify interchanging these finite sums. This establishes the valuation
of the entire product, including shared primes and repeated powers; the
argument does not infer product divisibility merely from individual
factor divisibility.

The common cutoff

```
b = 30*n + 30*r + k*n + r + 1
```

exceeds each factorial argument and every selected shift. Its adequacy for
both the factorial formula and the shift valuations is proved, so finite
summation does not discard a possible contribution. The reviewer also
inspected the pinned mathlib declarations for Legendre's factorial
valuation formula, the prime-power divisibility criterion, product
factorization, and the equivalence between valuation comparison and
natural-number divisibility. Their nonzero and primality hypotheses are
discharged in this proof.

After obtaining cross divisibility, cancellation of the strictly positive
factorial denominator is valid. This completes the uniform theorem for all
`n,r`, including their zero boundaries.

## Prior work and scope

The reviewer independently inspected the A211417 item in Adamczewski's
[*OEIS Open*](https://arxiv.org/pdf/2608.11941), Appendix A, printed page 21.
That item proves the `30n−1` divisor assertion, a different clause. The
reviewer also read Kenta Kitamura's
[repository README](https://github.com/KitaKen1/oeis-a211417) and the
[merged pull-request record](https://github.com/google-deepmind/formal-conjectures/pull/5010)
for the four fixed-factor assertions. Those statements are correctly
excluded from this package's new claim.

The [negative-shift issue](https://github.com/google-deepmind/formal-conjectures/issues/4923)
was read directly. It reports a paper-complete argument with a positive
explicit constant for the separate negative-shift family. The reviewer
checked that report's scope, rather than independently verifying that
other proof. Excluding the negative-shift family is appropriate.

The README and manuscript claim the generalized positive-shift family with
arbitrary `r`, not optimal constants, a mixed product over different
slopes, supercongruences, or resolution of every assertion in A211417. The
author's broader search record was reviewed, but its entire search was not
repeated. Neither this audit nor Lean verification establishes exhaustive
historical novelty or first-publication priority.

## Fresh isolated verification

Only `Proof.lean`, `lakefile.lean`, `lean-toolchain`, and
`lake-manifest.json` were copied into a new audit directory. No local proof
object, author-generated project cache, or project build directory was
copied. The installed external dependency caches were reused; each
dependency's Git revision matched the pinned manifest, and all tracked
worktrees and indexes were clean. Inherited `LEAN_PATH` and
`LEAN_SRC_PATH` were cleared.

The package built with Lean **4.19.0**, release commit **6caaee842e94**, and
mathlib **c44e0c8ee63ca166450922a373c7409c5d26b00b**. Lake freshly compiled
`Proof`, exited **0**, and emitted no warnings or errors. All four input
files remained byte-identical in both the package and audit directory.
All five printed endpoint axiom reports contain only

```
[propext, Classical.choice, Quot.sound]
```

Full source inspection and a separate textual scan found no admissions,
custom axioms, unsafe declarations, native-evaluation proof shortcuts, or
trust-level changes. Dependency caches were reused rather than rebuilt;
the audit claims a fresh proof-module build, not an independent rebuild of
all of mathlib or a separate kernel-replay audit.

**Disposition:** the frozen proof, exact source interpretation, complete
product valuation argument, zero boundaries, and uniform positive witness
all passed. The package is ready for integration within its stated scope.
