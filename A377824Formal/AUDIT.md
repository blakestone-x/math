# Independent audit: A377824Formal

**Verdict: PASS.** The exact final Lean source proves the recorded
asymptotic for the literal composition statistic, including the complete
enumeration and position-counting bridge. The written proof agrees with
the formal statements and preserves their domain restrictions.

Reviewed November 26, 2026 (America/Chicago), by a separate agent from
the proof author. This is an internal independent check, not an external
journal review or a certification of historical priority.

## Final-publication addendum — November 26, 2026 (America/Chicago)

The final repository check found the independently developed concurrent
[A377824 manuscript](../A377824/README.md) already present at commit
`c92ab48c98acba51cb42ceb73536a7bad251ec2d`. The preserved
[README](sources/prior_repo_README.md) and
[LaTeX source](sources/prior_repo_minimum-positions.tex) were checked:
they prove the same exact main term, source asymptotic, and a stronger
$O(n^2\varphi^n)$ error bound. Their exact Git blob identifiers and
SHA-256 hashes are recorded in `source_checks.md`.

This package was therefore renamed **A377824Formal** and is a formal
companion. It contributes **no additional conjecture resolution to
Batch 7**. This publication-status correction does not affect the
mathematical audit: the Lean proof independently establishes the literal
statistic, the exact main term, and its stated $(7/4)^n$ error bound.
It does not claim to formalize the stronger $\varphi^n$ estimate.

All frozen Lean and build files, the OEIS export, and both original
verification logs are unchanged. Their hashes were checked after the
directory rename; recompilation was unnecessary. The audit verdict
remains **PASS** for the exact proof source identified below.

## Exact artifact and independent compilation

Reviewed all 545 lines of `Proof.lean` at SHA-256:

```text
49a3695e54eb9acab9bcc6f50a4927c9b64168883fc6ccf8ea7032d1a2748571
```

The exact file was copied to a fresh isolated directory and compiled
directly with Lean 4.19.0, using the pinned mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Only dependency caches were
reused; no preexisting compiled artifact for this proof was available
to the independent invocation. Compilation exited successfully.

`audit-verification.txt` records the invocation conditions, source hash,
exit status, and all nine axiom reports. They contain only `propext`,
`Classical.choice`, and `Quot.sound`, as applicable. The file contains no
`sorry`, `admit`, custom axiom declarations, `native_decide`, or unsafe
proof implementation.

## Target correspondence

The preserved official export, revision 28 of April 19, 2025, defines
A377824 as the sum of the positions of minimum parts over all
compositions of n. Its example `(1,2,1,1,2)` contributes `1+3+4=8`.
This fixes both one-based indexing and inclusion of every minimum
occurrence. The conjecture is `a(n) ~ n^2 * 2^(n-5)`.

The function `a` is defined as `total minWeights`. `minWeights` applies the predicate
that a part is at most every part of the list. It therefore marks all
minimum occurrences, rather than only the first minimum, their values,
or distinct minimum values. `weights_positions` and `a_positions`
identify the recursion exactly with the sum of the one-based indices.
The empty composition contributes zero, so the boundary value a(0)=0
matches the source.

## Exhaustive enumeration without duplication

`mem_compositions` proves an equivalence for every natural n and every
list: membership in the generated list holds exactly when all parts
are positive and the sum is n. Thus the development does not merely
enumerate a selected family of compositions.

`compositions_nodup` independently proves uniqueness. The two recursive
branches are disjoint because one has first part 1 and the other has
first part at least 2. Both transformations are injective on their
domains. These results justify summing each actual ordered composition
once. The total count `2^n` for compositions of n+1 is also proved.

## Exact main term and complete error bound

The recurrences for the total number of ones and the sum of their
positions are derived from the same enumeration. The loss when the
first part is increased is exactly the indicator that it was one;
inserting a first one increases every old marked position by one.

The result is the exact identity

```text
32 * total oneWeights n = (n+1)*(n+6)*2^n, for n >= 2.
```

The restriction n>=2 is necessary for this particular formula and is
retained in the closed-form error theorem and the README.

Every composition containing a one has its minimum-position statistic
equal to its ones-position statistic. The remaining compositions are
all accounted for by `clean`. Their count satisfies the Fibonacci
recurrence with initial values 1 and 0, giving the proved upper bound
`(7/4)^n`. Positivity of the parts bounds the composition length by n,
and its position sum by n^2. Consequently, the error estimate applies
to the entire target sequence:

```text
0 <= a(n) - (n+1)*(n+6)*2^n/32 <= n^2*(7/4)^n, for n >= 2.
```

No restriction on the number of minima or the length of the composition
has been introduced. The universal error bound is not inferred from
finite computations or a generating-function assumption.

## Asymptotic domain

`normalized_bounds` divides only on the range n>=2, where the real
denominator is strictly positive. Its lower and upper bounds converge
to one, and the proof uses an eventual squeeze to obtain
`normalized_limit`. The value of the normalized expression at n=0
therefore does not affect the conclusion.

`conjecture` gives equivalence to `n^2*2^n/32`. The final
`original_conjecture` then proves eventual equality with the exact
source expression using n>=5. This correctly handles natural-number
subtraction in the formal exponent n-5 without treating the finitely
many smaller indices as an asymptotic obstacle.

## Prose, prior work, and scope

Reviewed the completed `README.md` and `source_checks.md` against the
source and formal declarations. The displayed recurrences, initial
conditions, polynomial correction terms, and geometric error all agree.
The package formally verifies one recorded conjecture and its explicit
error estimate. Following the final-publication addendum above, it is
counted as a formal companion and contributes no additional conjecture
resolution in Batch 7; correction terms are not counted separately.

The documentation credits Knopfmacher and Munagi's *Smallest Parts in
Compositions* and its minimum-one dominance argument. The related
primary chapter's descriptions of minimum-count, minimum-sum, and
first-minimum-position statistics were independently checked. The
present statistic includes all minimum positions, and the source notes
acknowledge that related positional formulas can be derived by symmetry.

The initial additional exact/semantic search still returned the source conjecture.
The retrieved trureturing catalogue contained no occurrence of A377824.
These checks support the bounded search record; they do not establish
absolute publication priority. No OEIS editorial acceptance is claimed.

No mathematical or formalization correction was required by this audit.
