# Independent review: A052392

**Verdict: PASS.** Reviewed November 27, 2026 by the separate `number13` agent. The reviewer did not author or modify the mathematical proof or its Lean sources.

## Source-to-theorem correspondence

I independently fetched the two immutable OEIS-data files linked in the source dossier and read their full relevant contents. A052392 revision 12 has offset 0, defines `T(2n+1,n)`, prints Israel's exact empirical generating function and order-four recurrence, and attaches the triangle algorithm with `T(2,1)=3`. A054120 revision 27 contains Hendel's 2015 proof of the local triangle recurrence. The package correctly credits that existing proof rather than counting it as a new resolution.

`sourceArray` independently implements the recurrence in square coordinates. `triangle (m+n) n = sourceArray m n` is proved; the boundary, outside-triangle value, exceptional entry, and all internal recurrence cases are accounted for. `source n` is literally `triangle (2*n+1) n`. Thus the formal sequence is not defined by the generating function or recurrence being proved. The formal scope begins at the exact source algorithm; its historical equivalence with the original strip-sum description is explicitly credited to Hendel.

## Mathematical review

I checked the weighted Delannoy difference identity, its exceptional base value `4-1=3`, and the diagonal/adjacent relations. The balance identity holds on both axes and propagates by the stated recurrence. An independent symbolic expansion confirms the manuscript's displayed balance discrepancy is precisely `2(m-n)` times the Delannoy recurrence residual.

The diagonal recurrence is equivalent to the stated formal differential equation, including its constant coefficient. In characteristic zero, the derivative of `Q*D^2` vanishes, and its constant coefficient is 1. The branch uniqueness proof is valid: the ring is a domain, `Q` is nonzero, and the sum of two normalized candidates has constant coefficient 2. Existence is supplied by the independently defined diagonal series itself.

The exact source-to-diagonal relation gives the cleared identity

`2X*A = (1-X)*((1-2X)*D-1)`.

Substitution of the unique normalized reciprocal root reproduces the source numerator `2X^2-3X+1` and the correction `(X-1)/(2X)`. The numerator vanishes at zero, and multiplication by `2X` is injective, so this formal version faithfully represents the recorded generating function.

I independently checked the manuscript's explicit five-recurrence linear combination as a symbolic polynomial identity. It proves the source recurrence for every positive index; the separate index-zero check is correct. No finite cutoff is used in the Lean conclusion.

## Fresh build and axiom audit

I ran `python research/batch10/build_package.py output/batch13/A052392 independent`. The harness created a fresh isolated directory, copied only local source/configuration files, and reused only the pinned external dependency caches. All four local modules are explicit default roots and were newly compiled. The build completed with exit code 0. The full receipt, exact source/configuration hashes, and axiom reports are in [independent_build.log](independent_build.log).

The audited principal endpoints, including `A052392.full_resolution`, use at most `propext`, `Classical.choice`, and `Quot.sound`. I inspected the full four-module source and found no admitted proof, custom axiom, or `native_decide`. The endpoint contains the unique normalized reciprocal root, the exact source generating-function identity, and the recurrence for every natural index.

The supplementary verifier was rerun successfully: all 23 displayed source terms, recurrence indices 0 through 99, and coefficients 0 through 100 of both formal identities passed. This replay checks transcription; the all-index proof is the Lean development.

## Attribution and counting

The dossier discloses prior sequence generators, classical weighted Delannoy methods, Barry's generalized-triangle framework, and Hendel's local recurrence. Its search conclusion is appropriately bounded and does not assert worldwide priority. The generating function and recurrence are one source family, not two independent problem counts. No mathematical, formal-scope, indexing, or attribution blocker was found.

No changes to the frozen proof sources or configurations were requested or made during this review.
