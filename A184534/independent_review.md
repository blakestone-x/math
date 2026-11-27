# Independent review: A184534

**Result: PASS.** Reviewed November 27, 2026 by the algebra lane, which did not author the proof modules. No mathematical or formal-proof correction was needed. Two minor provenance clarifications were requested and completed before this review was finalized.

## Literal source and theorem scope

Read the frozen OEIS export, the primary current OEIS entry, all four Lean modules, the README, the human manuscript, and the source dossier. Independently fetched the official export at commit `571197984aeda7b8b680fe3a1f6a43f9898cd441`. After removal of an extra final blank line from the saved export, the package file is byte-identical to the retrieved body: 1228 bytes, SHA-256 `aa7000bc8f5800ce327cd2b5c00ce8138b16d5cf471d49f03bb2b01f205e996e`.

The formal `root` is the nonnegative real cube root of `n^3+h`, `rootFloor` is the integer floor of the reciprocal of its fractional part, and `source n` specializes h to 4. This is the literal source definition. The theorem does not substitute a guessed sequence for the root expression.

The source has offset 1. The formal generating series has constant coefficient zero and coefficient n equal to the literal source for every n>0. Its numerator and factored denominator match the empirical source expression, including the sign of `(X-1)^3`. The denominator has constant coefficient −1, so the proved product identity determines the intended formal quotient.

The package correctly distinguishes the true generating-function assertion from the source's shifted empirical closed form. The printed closed form gives 12 at n=3, while the source is 7; the Lean counterexample certifies this discrepancy. The corrected formula holds for every n≥4, and the recurrence begins at newest source index 8. The recurrence is not asserted at index 7, where it fails.

## Mathematical review

Checked the general inequality for all natural 0<h≤n. With q=floor(3n²/h), the proof establishes q≥3n>0, hq≤3n², and h(q+1)≥3n²+1. The two cubic comparisons are strict and imply

\[
n+\frac1{q+1}<(n^3+h)^{1/3}<n+\frac1q.
\]

These inequalities identify the integer part of the root and place the reciprocal fractional part strictly between q and q+1. The proof checks positivity before taking reciprocals. The three exceptional h=4 cases are established by exact integer cubic inequalities, not approximations.

Reviewed the parity formulas, the all-index term definition, and the recurrence proof. For the generating function, the proof checks the finitely many initial coefficient equations and then uses the proved recurrence for every later coefficient. This is an equality of complete formal power series. The final `full_resolution` theorem includes the literal source bridge, eventual formula, recurrence, source coefficients, and exact numerator–denominator identity.

The human derivation agrees with the formal proof. The formula for the uncorrected quadratic floor has the two additional units at source indices 1 and 3, which produce precisely the exceptional numerator terms.

## Fresh independent build and source hashes

Ran `python research/batch10/build_package.py output/batch13/A184534 independent`. The harness copied only the four proof sources and three configuration files to a fresh isolated directory, without local proof objects, and reused the pinned external dependency cache. `lake build` compiled every explicit default root and exited with code 0.

[independent_build.log](independent_build.log) records the build and SHA-256 hashes. Every proof/configuration hash was compared with the final package and remains identical. Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned. Printed dependencies for all principal endpoints are only `propext`, `Classical.choice`, and `Quot.sound`. The four proof modules contain no `sorry`, `admit`, custom axiom, or `native_decide`.

## Supplementary finite replay

Independently ran the exact-integer verifier. It passed for every source index 1 through 10000, all 88 frozen source terms, the recurrence over its claimed range, and every generating-function coefficient through degree 10000. It also checked 4040 instances of the general h-parameter estimate. The author reran the same verifier after normalizing the source export; the final recorded source hash matches the byte-compared export. These finite checks support interpretation and indexing. The unbounded claims are proved by the Lean modules.

## Provenance review and limits

Read the exact and semantic search receipts and their stated result limits. Independent primary-source checks confirmed that A184534 still records the generating function as empirical, while the parent array A184532 supplies the root-based definition without the general inequality proved here. An independent exact web query found the primary entry and numerical sequence-fitting material, without an earlier source-to-generating-function proof.

The existing jOEIS/LODA recurrence or formula programs and Sequencelib synthetic code are properly disclosed as prior computational descriptions. I separately fetched the complete ATP benchmark: it asks whether two synthesized integer programs agree for all nonnegative inputs; neither definition uses a cube root or fractional part. The dossier initially described that artifact as a finite-prefix benchmark. Its wording and search-summary assessment have now been corrected to distinguish unbounded program equivalence from the missing literal source bridge.

The package credits the source authors, disclaims first discovery of the existing expressions, and counts the generating-function resolution, indexing correction, recurrence, and general estimate as one coherent result. The bounded searches and this review do not establish worldwide historical priority.
