# Independent review of A291897

**Disposition: pass for the stated formal scope.** The final two-module package
was compiled twice from fresh source-only copies under Lean 4.19.0 and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Both explicit default roots,
`EulerSource` and `EulerProof`, compiled. The three printed theorem audits report
only `propext`, `Classical.choice`, and `Quot.sound`.

This review was prepared by the separate runtime/review agent, which did not
write the proof bodies. During runtime recovery the reviewer replaced the broad
`Mathlib.Tactic` import with explicit imports and supplied its formerly implicit
finite-type and finite-sum dependencies. No definition or proof body changed.
The final proof-module SHA256 matches the pre-recovery proof-module digest.

## Statement and source fidelity

The frozen OEIS A291897 record defines the sequence as the reduced numerator of
the Euler polynomial value `E(2*n-1,n)` and records the conjecture that this
numerator is divisible by `(2*n-1)^2`. Its offset is positive, matching the formal
theorem's hypothesis `0 < n`. The archived source is pinned to OEIS data commit
`091a90f51479669655f4e46343867ea2abd5d4ff`; receipt hashes are in
`sources/manifest.json`.

The formal source is not a quotient constructed to make divisibility immediate.
It first defines the signed Euler numbers by the usual parity/finite recurrence,
then the integral centered polynomial

\[
 C_m(x)=\sum_{j=0}^{m}\binom mj E_{m-j}x^j.
\]

It forms the rational value `Rat.divInt (centered m (2*n-1)) (2^m)` and takes its
actual reduced numerator using `Rat.num`. In particular, the statement concerns
the numerator after rational cancellation, not merely the integral numerator of
an unreduced display fraction.

The analytic identification of this finite formula with classical Euler
polynomials, including their exponential generating function, remains the
documented mathematical source bridge. This Lean package does not formalize
analytic generating functions or prove equality with an independently defined
analytic Euler-polynomial object. Its kernel-checked theorem is the unbounded
divisibility assertion for the explicit centered finite formula. The Python
checks below provide finite corroboration of the source bridge and do not remove
that formal-scope qualification.

## Review of the unbounded argument

The central integer theorem is stronger than the selected sequence assertion:
for every odd natural degree `m` and integer `x` divisible by `m`, the integer
`centered m x` is divisible by `m^2`.

The finite sum is partitioned termwise by exponent. At exponent zero, the term
vanishes because `E_m=0` for odd `m`, proved directly from the source recurrence.
At exponent one, `choose m 1 = m`, and the assumed divisibility `m | x` supplies
the second factor of `m`. At exponent at least two, `m^2 | x^2 | x^j`; multiplying
by the remaining integer coefficient preserves divisibility. These cases cover
every summand. The proof does not assume any finite test bound, sign condition on
`x`, or the target divisibility assertion.

The rational-reduction lemma is also general. If `d | a`, `b != 0`, and `d` is
coprime to `b`, then `d` divides the reduced numerator of `a/b`.
`Rat.num_den_mk` gives a common factor `c` with `a = num*c` and `b = den*c`.
Since `c | b`, it is coprime to `d`. Cancellation by coprimality then gives
`d | num`. This explicitly handles the potential loss of a numerator divisor
during fraction reduction.

For the application, oddness gives the integer Bezout identity
`m - 2*(m/2) = 1`, so `m` is coprime to `2`. The proof lifts this to coprimality
of `m^2` and `2^m`; the denominator is nonzero. Consequently the square divisor
of the centered integer survives reduction.

Finally, `m = 2*n-1` and `x = 2*n-1`. The hypothesis `0 < n` justifies the cast
from truncated natural subtraction to integer subtraction. The degree is odd,
and it divides the chosen `x`. The concluding theorem therefore applies to every
positive natural source index. This specialization contains no unchecked
conversion between natural and integer subtraction.

## Build and axiom evidence

The successful author build ran at `2026-11-28T07:09:52.750924+00:00`; the separate
build ran at `2026-11-28T07:10:06.223751+00:00`. Their complete outputs appear in
`verification.txt` and `independent_build.log` respectively. Each fresh directory
received only the local Lean sources, pinned toolchain, lakefile, and complete
dependency manifest. It shared only the exact external dependency caches, with
no local proof `.olean` copied from another build. Thus "independent build"
means a separate source-only compilation, not a different compiler or a
different mathematical foundation.

Both logs contain successful kernel checks and standard-axiom audits for
`square_dvd_centered`, `odd_square_dvd_num`, and `source_conjecture`. A source scan
rejects local `sorry`, `admit`, custom `axiom` declarations, and `native_decide`.
The failed intermediate attempts during import minimization remain in the
runtime's separate build directories; they are not reported as successful
verification and their objects are not inputs to the successful builds.

The reviewed inputs have these SHA256 values:

| File | SHA256 |
|---|---|
| `EulerSource.lean` | `1b46dd9bdb2b593f903b2a7dd59e3e0d4c4a2155bdb667e733320bdfbef45833` |
| `EulerProof.lean` | `c36364428c3bf1095c6fb0be6cfb359a29253a9d0a2ef4983b347eb7e970d1f4` |
| `lakefile.lean` | `a295ea6a27206c28db942eb2b0b09ab5da576261cc54b634e5fed4c503a8af94` |
| `lake-manifest.json` | `db53dcf19b380f988038e0f5953e08e49f97f0be70c8973b5d2ea4daffa154f8` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |

## Supplementary executable checks and exclusions

Running `python verify.py` passed all 15 frozen OEIS terms, compared the centered
definition with independently computed SymPy Euler polynomials through degree
12, replayed the conjecture for indices 1 through 100 using exact reduced
rationals, and checked the generalized multiple-of-degree assertion for odd
degrees through 25 and multipliers from -5 through 5. These checks are useful for
detecting indexing, sign, normalization, and transcription mistakes; they do not
replace the unbounded Lean theorem.

The neighboring A292911 record concerns additional cubic divisibility and a
prime-pattern conjecture. Neither is proved or counted by this package. This
review also makes no global novelty claim and does not infer present open status
solely from the frozen OEIS comment. It approves the exact formal divisibility
result and its explicitly qualified classical source connection.

## Fresh review of the restored human proof

The reviewer subsequently read the restored `README.md`,
`manuscript-section.tex`, and `source_checks.md`. Their mathematical statements
and formal-scope qualifications agree with the compiled package and this review.
No further Lean change was required.

In particular, the manuscript's generating-function calculation correctly
recovers the centered identity: multiplying `sech(t)` by `exp(x*t)` gives
`2*exp((x+1)*t)/(exp(2*t)+1)`, and substituting `2*t` into the Euler-polynomial
generating function gives the coefficient `2^m E_m((x+1)/2)`. The signed-number
recurrence follows from `cosh(t)*sech(t)=1`, using the vanishing odd Euler
numbers; it agrees with the formal parity-based integer recurrence. This proves
the classical source bridge in the human argument while the prose accurately
states that the analytic identification is not a separate Lean theorem here.

The manuscript's three-way division of summands matches
`square_dvd_centered`. Its positive common cancellation factor is legitimate
because the original denominator is the positive number `2^m`; its coprimality
argument therefore preserves the complete square divisor even for negative or
zero centered values. The substitution `m=x=2*n-1` is valid for every integer
`n>=1` and corresponds to the formal positive-natural-index specialization.
The README gives the same argument with the same reduced-numerator convention.
Both documents count the general lemma and its specialization as one family and
exclude the cubic assertion. The bounded prior-work and attribution paragraphs
do not claim a worldwide-priority determination.

The prose versions reviewed have SHA256 values:

- `README.md`: `3334e59ca5aed5557a7951d3777cda350e320b16d9ca0528f0bd56872c9b43a6`.
- `manuscript-section.tex`: `a75cc80396e752305e3ed930bcfe0b5c6a7d88ae098a9ba487fb3cd04fd1e83c`.
