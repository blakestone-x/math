# Independent audit of A324017

**Reviewer:** `scout_sequences`, separate from the proof-authoring agent.  
**Date:** November 26, 2026 (America/Chicago).  
**Result:** Passed mathematical review, original-statement review, and fresh Lean compilation.

## Exact files and compiler result

The reviewed `Proof.lean` has SHA-256
`a3716c9e0da21b2a3604ed97c8021b20ffafa0cac079745c2afa42d8dcdaa240`.
The preserved official source `source.seq` has SHA-256
`ad3d97f7f70cc9e8d7e7253aeaebba52ed26af960f3d942ac6cbc367aa0b14ef`.
The final `README.md` and `source_checks.md` were also read in full. Their formulas, domains, counterexample, source caveats, classical-credit discussion, and stated verification scope agree with the checked proof. An exact copy of the final proof was compiled in a fresh, separate audit directory with Lean 4.19.0 and the pinned mathlib libraries. Compilation exited with code zero. The four public theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Exact output and before/after source hashes are preserved in `audit-verification.txt`.

No `sorry`, `admit`, `native_decide`, custom axiom, unproved imported conjecture, or finite-domain restriction appears in the proof.

## Definition and quantifier fidelity

The source defines a right-associated tower by height zero equal to one and height `m+1` equal to the base raised to the height-`m` tower. The formal `tower` definition is exactly this recurrence. The formal `array m n` is precisely the height-`m` tower with base `2*n-1`, reduced modulo `(2*n)^m`. It uses the defining formula from the entry rather than assuming that repeatedly reducing intermediate exponents is valid.

The first original claim asks for positive integers `m,n,k`, each greater than one. `fixed_point` proves a stronger statement for all positive `m,n` and every natural `k` satisfying the stated congruence. Thus the original range is fully covered; no upper bound or least-residue assumption is imposed on `k`.

The quotient claim retains the original range `n > 1`, `m >= 2`. For nonnegative integers and a positive denominator, natural-number division is the floor in the source statement. Here `2*n` is strictly positive. The theorem proves congruence of this literal quotient modulo `2*n`.

The third claim is refuted even when its unspecified representative `j` is required to be the canonical remainder `0 <= j < (2*n)^(m+1)`. This eliminates any dependence on choosing an artificially large congruent representative. The counterexample has `m=n=2`, `j=27`, so all original index restrictions hold. The theorem `third_claim_false` states the negation of that canonical-residue reading explicitly.

## Mathematical verification

Write `b=2*n` and `a=b-1`. The period lemma proves

`a^(b^r) = 1 (mod b^(r+1))` for every `r >= 1`.

The initial case follows by expanding `(b-1)^b` modulo `b^2`, using that `b` is even. The induction step is the ordinary lifting fact: if `b^r` divides `x-1` with `r>=1`, then `b^(r+1)` divides `x^b-1`. The geometric sum has `b` summands, each congruent to one modulo `b`. This argument needs no primality or squarefreeness assumption on `b`.

The exponent-congruence lemma correctly uses a known multiplicative period; it does not mistake congruence of exponents modulo the output modulus for a universally valid rule. All towers are odd, so every positive-height tower is `-1` modulo `b`. Induction with the period lemma gives consecutive-height stabilization modulo `b^m` starting exactly at height `m`. Applying it after replacing the height-`m` tower by any congruent `k` proves the first claim.

For the second claim, write a tower of height at least two as `(b-1)^E`, where `E` is odd and `E=-1 (mod b)`. The first two binomial terms give `-1+b*E (mod b^2)`, hence the canonical remainder `b^2-b-1`. The formal proof establishes both this congruence and the strict bound putting the proposed remainder between zero and `b^2-1`. Its displayed natural-number formula, `b*(b-2)+(b-1)`, avoids truncated-subtraction ambiguity. Dividing the remainder by `b` gives `b-2`, which is `2*(n-1)` in the original range.

For the refutation, the exact tower of height two at base three is 27, so its remainder modulo 64 is 27. The array entry at height three is `3^27 mod 64 = 59`, not 27. Lean checks these exact finite calculations with `norm_num`, and the general negation is then obtained by substituting this witness. The reported counterexample is not based on a sample-based inference.

The valid replacement `corrected_compatibility` keeps the modulus at `b^m` while increasing the height. It follows directly from stabilization and the fact that `b^m` divides `b^(m+1)`. It makes no claim that the additional next digit is already determined one height earlier.

## Source issues and prior-work scope

The current official export is revision 91, dated February 16, 2025, and still records all three claims as conjectures. The third comment's examples also transpose the array indices: the displayed table places 563 at `A(3,6)` and 16115 at `A(4,6)`, whereas the comment names `A(6,3)` and `A(6,4)`. The counterexample addresses the literal asserted formula; it does not purport to refute every possible intended correction of that comment.

The general theory of modular tower stabilization and exponential fixed points is established prior work. In addition to the Shapiro references documented by the author, Jiménez Urroz and Yebra's [2009 JIS paper](https://cs.uwaterloo.ca/journals/JIS/VOL12/Yebra/yebra4.pdf), especially its Section 3, explicitly describes the period condition that permits lifting fixed-point residues. The present package applies elementary period and binomial arguments to these particular recorded statements; it does not establish a new general theory of tetration.

Independent exact-identifier and semantic searches using two web search engines did not locate an earlier resolution of these particular comments. A separate agent checked the current trureturing, Fabian Arevalo, and Eppie proof-index pages for the exact identifier, with no matches. The enumerated targets in Low-Hanging Fruit volumes I–V do not include it. These are bounded searches, not a certificate of historical priority.
