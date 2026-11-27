# Independent audit: the A400939 prime-family partial result

**Date:** November 27, 2026 UTC  
**Result:** PASS for the stated infinite prime family.  
**Reviewed proof SHA-256:** `eada9af1cbabf1dd50de12c4a34d3a655130582e201abcdd3585c9090a76e57c`.

A separate reviewer read the complete frozen `Proof.lean`, the README, the manuscript section, the source-status note, and the preserved primary entry. No change to the proof was required. An isolated Lake build of the exact frozen source and package configuration completed successfully. The full transcript is [audit-verification.txt](audit-verification.txt).

## Exact source and walk semantics

The reviewer independently retrieved the [immutable official OEIS export](https://github.com/oeis/oeisdata/blob/df38d77b83a78d8ab5aaa501dec6e3a3db977f01/seq/A400/A400939.seq) and checked that it equals the preserved source byte for byte. Its recomputed Git blob hash is `c9db5ad44bbf95b2a7d4c0f054c51901cbdaf231`, matching the recorded source identifier. The current official export also matched those same bytes on the review date.

The entry contains two distinct conjectures: positive-integer occurrence for the original divisor-two walk, and eventual permanent addition for a generalized divisor that is not a power of two. This package proves a restricted infinite family within the second conjecture.

The definition `walk` starts the mathematical sequence at index one with value one. Its index-zero value is auxiliary. In the recursive branch test, `Fin (n+1)` bounds the potential seen indices by `n`, and the condition `0 < i.val` excludes index zero. Thus the seen values are exactly those at indices one through `n`. The theorem `walk_followsRule` formally translates this finite-index test to the quantified source rule. There is no assumption that a separately defined recurrence happens to model the walk.

The only branch requiring a new value is division. The addition branch adds `n+1` without testing whether the result was previously visited, matching the source's explicit program. `DivisionAt` records the branch conditions for a division **arriving** at index `d`, with `d>1`; `division_value` proves that this condition actually makes the source rule take that division.

## Initial division and index review

The formal triangular prefix is proved from primality and the literal walk rule. For a positive index `n` with `n+1<p`, neither positive factor of `n(n+1)` can be divisible by the prime `p`. Consequently the values at indices `1≤n<p` are precisely `T_n`.

For every odd prime, the value before index `p` is `p(p−1)/2`. Its quotient is `q=(p−1)/2`. If `q` has not appeared, the division arrives at index `p`. Otherwise the addition branch reaches `T_p`, and the next candidate quotient is `q+1`. The proof that two positive triangular numbers cannot be consecutive rules out an earlier occurrence of this second quotient. Therefore the first division arrives at `p+1` in this second case.

The theorem `division_at_prime_iff` uses the exact finite witness range `0<i<p`. The prose's equivalent description by any positive triangular number is valid because `T_i≥i` and `q<p`, forcing every possible witness into that range. The examples and the distinction between the preceding index and the arrival index agree with the formal definitions.

## Permanent tail and uniqueness

The two doubled offsets are exactly

| Division arrival index | Doubled offset `D` | Valid tail identity |
|---|---|---|
| `p` | `p²+1` | `2*a(n)+D=n*(n+1)` for every `n≥p` |
| `p+1` | `(p+1)²` | `2*a(n)+D=n*(n+1)` for every `n≥p+1` |

Both offsets are congruent to one modulo `p`. If a tail value were divisible by `p`, the tail identity would give `n(n+1)=1` modulo `p`, hence `(2n+1)²=5`. This contradicts the nonsquare hypothesis. The proof uses this contradiction inductively to establish nondivisibility, the exact tail identity, and the addition transition at **every** later index. It does not extrapolate from a finite trajectory.

`unique_division_from_tail` excludes earlier divisions using the strictly increasing triangular prefix and the fact that division cannot increase a natural number. It excludes later divisions using tail nondivisibility. Together with the exhibited division, this proves the biconditional `DivisionAt ... e ↔ e=d` for every index `e`; it proves uniqueness as well as eventual stopping.

## Residue classes and infinitude

The main specialization covers every prime `p≠2` with `p % 5 = 2` or `p % 5 = 3`. The exclusion of the even prime is explicit. The proof obtains the nonsquare hypothesis from the actual pinned mathlib quadratic-reciprocity theorem and the finite square table modulo five.

The reviewer inspected the declarations of both reused mathlib results. `Nat.forall_exists_prime_gt_and_eq_mod` supplies a prime above an arbitrary bound in the unit residue class three modulo five. Applying the all-index classification to that prime proves `arbitrarily_large_single_division`. Thus infinitude is formally established, not asserted from a few example primes. Quadratic reciprocity and Dirichlet's theorem are imported proved theorems and are accurately credited as existing mathematics.

## Fresh isolated verification

Only `Proof.lean`, `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json` were copied into a new audit project. No local proof object, author-produced proof cache, or project build directory was copied. The audit reused the installed dependency caches, checking every dependency checkout's Git HEAD against the pinned manifest. Inherited `LEAN_PATH` and `LEAN_SRC_PATH` values were cleared.

The exact package configuration was built using `lake build`, Lean **4.19.0** release commit `6caaee842e94`, and mathlib **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. The package's `Proof` module was freshly compiled, the build exited **0**, and all four frozen input files remained byte-identical afterward.

Both principal end theorems report only:

```text
[propext, Classical.choice, Quot.sound]
```

Full source inspection and a textual scan found no admissions, added axioms, unsafe declarations, native-evaluation proof shortcuts, or changes to the trust level. The literal walk has no empirical trajectory, recurrence, or future-branch assumption built into the main result.

## Scope and disposition

The README and manuscript accurately present an **infinite-family partial result**. They make no stopping claim for every non-power-of-two divisor, no claim about arbitrary composite divisors or the remaining odd-prime classes, and no occurrence claim for the original halving walk.

The reviewer checked the exact source identity and read the author's bounded prior-publication search record. That broader search was not repeated as part of this formal audit, and neither the audit nor the build certifies exhaustive historical novelty.

**Disposition:** the frozen proof, its exact source-rule interpretation, the prime-family classification, and its infinitude consequence passed. No correction was required.
