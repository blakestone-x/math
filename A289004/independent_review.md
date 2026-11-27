# Independent review of A289004 and its three source scanners

**Result: PASS.** Reviewed November 27, 2026 by a different agent from the author of all seven local Lean proof modules. The reviewer read the complete frozen Lean sources, the README, the manuscript fragment, the source-check report, all six official source exports, and the complete four-page Dekking–Keane primary paper. No mathematical or source-alignment correction was required. The frozen proof sources were not edited.

## Frozen source and fresh verification

The frozen `Proof.lean` SHA256 is
`d39b2c116a0c8fd1bc49bda7e22c832e44509b63dd7f0591b836d8a5515dd499`.
Every source and configuration hash matched `source_freeze.json` before and after the independent build. All nine dependency checkouts matched the exact revisions in `lake-manifest.json`, with no tracked modifications. In particular, Lean is 4.19.0 and mathlib is `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

A fresh isolated Lake project was created at
`research/batch11/sequences/A289004_independent_io_ponh3`.
Only the seven proof sources, `lakefile.lean`, the manifest, and the toolchain file were copied. No local `.olean` or other proof build object was reused; the pinned stock dependency caches were linked, and inherited `LEAN_PATH` was removed. `lake build` rebuilt all seven proof modules successfully with exit code 0. The full transcript and source hashes are in [independent_build.log](independent_build.log).

The main endpoints report only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms; two elementary endpoints omit Classical.choice. No `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` occurs in the local Lean sources. The build emits one informational `ring_nf` suggestion in Growth, with no proof error.

## Literal-source alignment

The current official `oeis/oeisdata` exports were fetched independently and byte-compared with all six preserved source files. Every comparison passed. [independent_source_comparison.json](independent_source_comparison.json) records byte counts, SHA256 hashes, Git blob hashes, and retrieval URLs. In particular, the current records still contain the three length assertions being refuted.

The scanner correctly distinguishes the three `01` replacements, while sharing `00 → 0010`, `10 → 010`, and seed `00`. It consumes matched input pairs once, copies an unmatched leading letter, and retains a final singleton. The `11` case advances by one character, allowing a later match, which agrees with the source's left-to-right replacement semantics. That branch is subsequently proved unreachable along all three actual orbits; it is not removed by an assumed invariant.

The source program calls the seed iteration 0. The independently defined `reference` exactly matches the order-ten signature `(2,-1,0,2,-1,0,1,-1,0,-1)` and initial values in A289004's Mathematica program. The source prose repeats index 9; the program and term list consistently place 151 at index 8 and 257 at index 9. The formal counterexample does not exploit that typo.

An independent diagnostic used Python's nonoverlapping regular-expression replacement, separately from the author's scanner implementation, and parsed the comparison recurrence's signature and initial values from the preserved source. It replayed iterations 0 through 23 for all three rules and matched all 7, 7, and 6 printed initial iterates, respectively. Every variant first disagreed at iteration 22: actual length 268184 versus source value 268182. At iteration 23 the values are 457819 and 457812. All three length and ones-count lists agreed. The full diagnostic record is [independent_replay.json](independent_replay.json). These computations support the source-semantics check; the universal claims are proved in Lean.

## Mathematical proof review

### Good-word invariant and count bridge

`Good` means every 1 is followed by a 0. This entails no adjacent ones and a final zero in every nonempty word. The seed satisfies it, and `rewrite_good` establishes preservation for every good finite input. The delicate boundary is the left variant's image `001` of `01`: the source invariant forces a following input zero, and `rewrite_left_zero` proves that the remaining output begins with zero. This is checked explicitly rather than presumed from a list of examples.

Every consumed pair therefore contributes one output 1, while an odd final zero contributes none. A `00` pair has length four and each mixed pair length three, giving

\[
O_{n+1}=\lfloor L_n/2\rfloor,\qquad
L_{n+1}+O_n+(L_n\bmod2)=2L_n.
\]

`word_counts` derives the arithmetic state from the literal list functions by induction. It does not assume the conjectured recurrence, and it accounts for natural-number subtraction without an unproved no-underflow hypothesis. The shared state proves equality of all three length sequences at every index. The corrected rounded recurrence is then a direct elimination of O_n.

### First failure and growth

`first_failure` proves every earlier equality for n<22 and the exact unequal values at n=22, through `word_counts`. Its finite arithmetic proof uses ordinary kernel-checked decision and normalization, with no native-decision shortcut.

For S_n=L_n−(2+√2)O_n and μ=1−√2/2, the exact count equations give
S_(n+1)=μS_n+(1−μ)(L_n mod 2). The nonnegative bound 0≤S_n≤2 follows by induction. Independently, the good-word ones bound gives L_(n+1)≥L_n+⌊L_n/2⌋ and L_n≥n+2. Thus the proof establishes divergence of L_n and existence of the ratio limit, rather than using a guessed asymptotic recurrence. The ratio formula then yields λ=1+√2/2, and finite telescoping proves the fixed-shift limits L_(n+j)/L_n→λ^j.

### No eventual monic integer recurrence

The coefficient convention in `relation` is explicit: the coefficient of X^i multiplies L_(n+i). If a monic integer polynomial gave a relation eventually, dividing by L_n and applying the finite-sum limit would force that polynomial to vanish at λ. Thus λ would be integral over ℤ. Closure of integral elements under subtraction and powers would make (λ−1)²=1/2 integral; injectivity of ℚ→ℝ reduces this to a rational algebraic integer, contradicting 2z=1 for an integer z.

`literal_no_eventual_monic_relation` puts the original list lengths in this universal statement. The exact source polynomial
X¹⁰−2X⁹+X⁸−2X⁶+X⁵−X³+X²+1
has the correct signs and shifts; its specialization proves failures of the original recurrence beyond every cutoff. The scope is precisely monic integer recurrences. The package does not claim the corresponding result for arbitrary rational or real coefficients.

## Prior-work and counting scope

The complete primary [Dekking–Keane paper](https://arxiv.org/pdf/2202.13548), version 2 dated February 20, 2023, was read independently. Its Theorem 4 identifies A289001's infinite fixed word as the Pell word. It does not establish the retained-singleton finite-iterate length recurrence refuted here. The current A293077 export gives a known floor recurrence for the convention that discards an odd final output letter; its second iterate has length 6, whereas the retained convention has length 7. A289037 records the related earlier density argument. These known facts are correctly attributed and are not counted as newly resolved assertions.

The repetition in A289004 and A289001 is one assertion. A289035 and A289239 state two further instances for different replacement rules, all handled by the same structural theorem. The source report describes its prior-publication search as bounded, without promising exhaustive novelty or editorial acceptance. This audit confirms the mathematical and source scope; it does not convert the bounded search into an unconditional priority claim.
