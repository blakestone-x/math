# Independent audit of A289629

Auditor: root, separately from the proof-author agent. Checked November 26,
2026 (America/Chicago).

## Result

**PASS.** The exact final source was read in full and independently compiled
in a fresh directory. Its statements match all nine branches of the
preserved OEIS conjectural comment. Eight branches are proved and the fifth
is refuted. Four of the true branches are already established in A349989
and are correctly excluded from the batch's count of additional resolutions.

The reviewed source is `Proof.lean`, SHA-256:

```text
e4eebf49e447b7fe49b11f28a6cd28db46070104ed8023c7e1edf522ef3e616a
```

## Statement and proof checks

The definition is the literal integer expression `(k+1)^n+(-k)^n`.
The exponent families are natural numbers with the original hypothesis
`1 ≤ m`; the proofs explicitly eliminate truncated-subtraction ambiguity
by writing `m` as a successor. The geometric factorization applies to
arbitrary integer bases and odd multipliers, so it covers both odd and
even seed exponents without a sign assumption.

Every infinite branch supplies a specific square divisor greater than
one. The seed values, square divisors, and odd-multiplier decompositions
were checked against both the Lean source and the README. The generic
squarefreeness obstruction correctly uses the fact that an integer with
absolute value greater than one is not a unit.

For the false fifth branch, `m=2` lies in the stated domain. The value
`F_7(30)` is factored into five distinct primes, and the proof establishes
squarefreeness using those prime and coprimality certificates. The two
explicit Lucas certificates exhaust all prime divisors of the relevant
predecessors. The README's displayed modular residues were separately
recalculated and agree with the certified calculations. No unchecked
factorization or primality assumption occurs in the proof.

The corrected odd-parameter restriction follows from the same universal
factorization. It does not purport to classify every even parameter.

## Source and contribution checks

The primary A289629 snapshot records the nine families with `m ≥ 1` and
expressly distinguishes square divisibility from the least eligible base.
The formal theorems make no claim about minimality or new sequence terms.
The live primary OEIS search result retained the same conjectural comment.

The full A349989 snapshot, including formulas omitted by some search
snippets, already covers both `k=3` branches and the `k=19` and `k=113`
branches. The README and `source_checks.md` credit all four. The batch
therefore counts four other true families and one refutation, not nine
new results. The odd-power factorization and Lucas criterion are classical.
The documented literature searches are bounded and do not certify priority.

## Independent compilation

The source was copied into the fresh directory recorded in
`audit-verification.txt` and compiled with Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The author's compiled output
was not reused. Compilation exited with status zero.

All five public axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The source contains no `sorry`, `admit`, new axioms,
`native_decide`, or unsafe replacement for a proof. The final source hash
matches the author's fresh package-build record and the independent log.
