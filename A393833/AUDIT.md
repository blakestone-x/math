# Independent audit of A393833

**Reviewer:** `scout_sequences`, separate from the proof-authoring agent.  
**Date:** November 26, 2026 (America/Chicago).  
**Result:** Passed mathematical review, source-definition review, and fresh Lean compilation.

## Files reviewed

The reviewed `Proof.lean` has SHA-256
`0a2b108259cfe2f5fb95aa986c45f580d2c0fdbb1322411eb47ed240fdaeac76`.
The preserved official OEIS record `source.seq` has SHA-256
`b7bdfce372b42c539af3cf69ed9099891a260237d6400b2fde1ae14ad391ea39`.
The source and final README were read in full. The proof source was copied unchanged into a separate audit directory and recompiled there. The source hash was identical before and after compilation. Exact compiler output is in `audit-verification.txt`.

## Fidelity to the original problem

The definition `residues m k` sorts the finite set of every positive proper divisor of `k` in increasing order and maps each divisor to its natural-number remainder modulo `m`. This is the ordered list required by the original entry. It is not an unordered set of residues and retains repeated residues.

The predicate `Good n k` requires exactly `2*n+2` positive divisors, exactly `2*n+1` entries in the proper-divisor residue list, and palindromicity of that list. It therefore includes the divisor-count restriction in the sequence name, in addition to the existence conjecture in the comment. Both the text and the executable predicates in the source permit constant palindromes.

The original minimum is a positive integer. Although `Good` does not separately repeat `0 < k`, its divisor-count condition excludes zero for every positive `n`: mathlib's divisor set of zero is empty, whereas `2*n+2` is positive. Thus `exists_least` over natural-number witnesses gives the intended positive minimum. It does not claim that the constructed prime power itself is minimal.

## Mathematical review

For a prime `p`, the divisors of `p^r` are exactly the powers `p^j` with `0 <= j <= r`, and the proper divisors are those with `0 <= j < r`. The formal proof invokes mathlib's exact prime-power divisor descriptions to derive both the divisor count and the proper-list length.

If `p` is congruent to one modulo `m`, every proper divisor has residue `1 % m`. The proof establishes equality of the actual sorted residue list with `List.replicate r (1 % m)`, using its length and its individual elements. Consequently, no separate ordering assumption is being imported into the argument.

The general construction uses the existing theorem `Nat.exists_prime_gt_modEq_one` to choose a prime `p > B`, then takes `k = p^r`. Its assumptions `0 < m` and `0 < r` are sufficient; the latter ensures `p^r >= p > B`. Substituting `m = n` and `r = 2*n+1` proves the required property for every positive index and every bound. This supplies arbitrarily large witnesses, and well-ordering supplies a least witness.

The boundary `n = 1` is included: all residues are zero, since `1 % 1 = 0`. The construction may choose `p = 2` and `k = 8`; the fact that the actual minimum is six does not affect the existence argument. No assumption of a nonconstant palindrome is needed or present. The old inconsistent example at index nine in the source is not used.

## Formal verification

A fresh standalone Lean 4.19.0 invocation compiled an exact copy of the final source, using compiled libraries from the pinned mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. It exited with code zero. All five printed theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The source contains no `sorry`, `admit`, `native_decide`, custom axiom, finite-index cutoff, or unproved definition bridge. The prime-congruence theorem is an ordinary imported, kernel-checked mathlib theorem, expressly credited in the README. The audit does not certify historical priority; the bounded prior-work search and its limits are documented separately in `source_checks.md`.
