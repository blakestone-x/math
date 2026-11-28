# Independent formal and statement review: A288523

**Review date:** November 27, 2026  
**Result:** PASS for the exact replacement-length conjecture stated below.  
**Reviewer:** separate proof-review agent, after the author froze the source.  
**Frozen `Proof.lean` SHA-256:** `de2cc1889b658ac2b0ca496e2186686238190c0772221d47529000101c4e8b33`.

The reviewer read all of `Proof.lean`, `README.md`, `source_checks.md`, and both preserved OEIS entries. The proof was not edited during this review. A separate isolated Lake project rebuilt the exact frozen proof successfully; its full transcript is [independent_build.log](independent_build.log).

## 1. Exact primary-source correspondence

The current official exports were independently retrieved from the `oeis/oeisdata` repository and compared byte for byte with the preserved files. Both matched on the review date. The reviewer also recomputed the Git blob hashes, using SHA-1 of `blob <byte length>\0<contents>`:

| Entry | Current official source | Verified Git blob SHA-1 |
|---|---|---|
| A288523 | [Official export](https://github.com/oeis/oeisdata/blob/main/seq/A288/A288523.seq) | `b7eb9058918bc0c3420f45e3a0949ca056178fd1` |
| A288520 | [Official export](https://github.com/oeis/oeisdata/blob/main/seq/A288/A288520.seq) | `b05de0c91d728128265de06fa29c1ff6296a5979` |

The precise target is the conjectured equality between the lengths of the finite iterates in A288520 and the independently defined recurrence A288523. The same length assertion appears in both entries and constitutes one claim.

The formal `rewrite` scans a list from left to right. It replaces `00` by `0101`, replaces `10` by `010`, consumes both input letters when either rule matches, and recurses only on the unprocessed input. If the next letter is `1`, it copies the current letter and advances by one. Empty and single-letter suffixes are preserved. Thus it implements the nonoverlapping replacement operation in the source program; generated output is not scanned again in the same pass. `word 0` is exactly `00`.

The source recurrence applies at indices **N ≥ 5**, with five values `(2, 4, 5, 8, 11)` at indices zero through four. The theorem `length_recurrence n` uses N = n + 5 and therefore has the exact stated domain. The proof does not extend the order-four recurrence incorrectly to N = 4. `reference` is an independent integer-valued definition, and `original_conjecture` proves equality with it at every natural index. No convention concerning truncated natural-number subtraction is involved.

## 2. Mathematical proof review

The proof establishes an exact finite-word coding before using any length recurrence:

- `rewrite_tail` proves the boundary identity for **every** finite token word, by induction on that word and checking each of the three tokens. This is sufficient to control interactions across replacement boundaries.
- `rewrite_encode` derives both alternating prefix transitions. `word_coding` then proves by induction that every actual source iterate after `00` has the stated encoded form.
- `morph_length_cubic` proves the length identity for every token word using additivity and the three token cases. It is not inferred from a finite numerical sample.
- `encode_length_three` includes the boundary contributions in both phases. `length_affine` applies this identity to the proven coding of the source iterates.
- `length_recurrence` combines consecutive affine identities to obtain the exact source relation. `original_conjecture` uses the five initial cases and strong induction to identify the lengths with the source recurrence.

The reviewer checked the token-length table, both boundary-length rows, recurrence indices, and generating-function numerator in the prose against the proof. These agree. The generating-function display is correctly described as an ordinary algebraic consequence, not a separately formalized theorem.

## 3. Isolated kernel verification and dependency audit

A newly created audit directory received only the exact four text files `Proof.lean`, `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`. No author-produced proof object, proof cache, or package-local build directory was copied. The audit reused the installed dependency caches through symlinks.

Every dependency checkout's Git HEAD was checked against the corresponding revision in the copied manifest. The mathlib checkout was also clean. The build used Lean **4.19.0**, release commit `6caaee842e94`, and mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. The audit process cleared inherited `LEAN_PATH` and `LEAN_SRC_PATH` values before invoking `lake build`. The isolated build exited with code **0** and freshly built the package's `Proof` module. All four copied input files were confirmed unchanged afterward.

The printed axiom dependencies for `rewrite_tail`, `word_coding`, `length_affine`, `length_recurrence`, and `original_conjecture` are exactly:

```text
[propext, Quot.sound]
```

Full source inspection and a textual check found no admissions, added axioms, unsafe declarations, native-evaluation proof shortcuts, or trust-level changes. The main theorem has no unproved recurrence, coding, or source-agreement assumption.

## 4. Scope and provenance limits

This audit supports the all-index finite-iterate length equality and the stronger affine recurrence presented in the package. It does not establish the neighboring position or frequency conjectures, nor the existence of an infinite limiting word. The package states these limits clearly.

The reviewer independently verified the exact current primary-source bytes and read the author's prior-publication search record. The broader search described in `source_checks.md` was not repeated as part of this formal audit. Neither a successful build nor that bounded literature search certifies exhaustive historical priority. No claim of a new general substitution method or of OEIS editorial acceptance is made.

**Disposition:** no correction was required. The frozen proof and its exact source interpretation passed this review.
