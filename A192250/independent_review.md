# Independent review: A192250/A192251

**Result: PASS.** Reviewed November 27, 2026 by the algebra lane, which did not author any of this package's three proof modules. No mathematical, indexing, or formal-proof correction was needed. The result is one polynomial-reduction family with two component assertions.

## Literal source and indexing

Read all three proof modules, both target source entries, the defining A192232 entry, the complete human manuscript, README, source dossier, and search receipts. Independently fetched each official OEIS-data file at the immutable commit recorded in `sources/manifest.json`. All three saved files are byte-for-byte equal to the freshly retrieved UTF-8 bodies; the manifest byte counts and SHA-256 hashes agree.

The defining source procedure divides a polynomial by X², writes it as X²t+r with degree r<2, and replaces it by (X+1)t+r until the degree is at most one. `sourceStep` implements precisely that operation using monic polynomial division. `sourceStep_natDegree_lt` proves strict decrease of the natural degree for every nonterminal input. `sourceReduction` uses this decrease as its well-founded termination argument. Its definition does not assume the conjectured recurrence or a closed form for either component.

`sourceStep_remainder` proves that each actual step preserves remainder modulo M=X²−X−1. `sourceReduction_eq_remainder` then identifies the terminating algorithm with the unique monic remainder, including the already-terminal and zero-polynomial cases. The final recurrence theorems concern coefficients of this literal terminating algorithm; the remainder is a proved intermediate interpretation.

Both target entries have offset 1. The source program starts its polynomial list at degree 0 and extracts its first element at sequence index 1. Thus the input at index n is

\[
P_n(X)=\sum_{k=0}^{n-1}\binom{2k}{k}X^k.
\]

The formal `prefixPoly n` has exactly these n terms. Its first coefficient pair is (1,0), followed by (1,2), (7,8), (27,48), and (167,258). The constant and linear components therefore match the literal A192250 and A192251 conventions. The recurrence uses n−3, so n≥4 is the complete range involving only the published source indices. No value at index zero is needed for either selected assertion.

## Mathematical proof and exact endpoints

Checked the human polynomial identity and its formal counterpart. For n≥4, put

\[
A=(n-1)(n-2),\quad B=(5n-7)(n-2),\quad
C=2(2n-3)(3n-8),\quad D=4(2n-3)(2n-5).
\]

The central-binomial ratio (k+1)c(k+1)=2(2k+1)c(k) yields

\[
AP_n-BP_{n-1}-CP_{n-2}+DP_{n-3}
=D c(n-3)X^{n-3}(X^2-X-1).
\]

The coefficients of the shared prefix cancel because A−B−C+D=0. The three remaining monomials have coefficients −Dc(n−3), −Dc(n−3), and Dc(n−3), respectively. Reducing this exact identity modulo M and taking either coefficient proves Mathar's displayed recurrence.

The proof first establishes the polynomial identity at the shifted nonnegative parameter n+4 and then explicitly translates it to the original source index n≥4. All recurrence arithmetic is over the integers. The natural-number subtractions in sequence indices are justified by that range; they do not conceal a truncated arithmetic identity. `a192250_conjecture` and `a192251_conjecture` state the exact recorded coefficients and signs, and `full_resolution` combines both without extra assumptions.

The manuscript agrees with the formal derivation. The general monic-remainder bridge and the adjacent-binomial ratio are supporting lemmas, not additional counted results.

## Fresh independent build and frozen artifacts

Ran `python research/batch10/build_package.py output/batch14/A192250 independent`. The build copied only the three proof sources and three configuration files into a new isolated directory, with no precompiled local proof objects. It reused the pinned external dependency cache. Every local module is an explicit default root, and `lake build` compiled all three and exited with code 0.

The complete build and six proof/configuration hashes are in [independent_build.log](independent_build.log). Each hash was compared against the final frozen package and remains unchanged. The package pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All eight printed axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. No proof module contains `sorry`, `admit`, `native_decide`, an unsafe declaration, or a custom axiom.

All 19 author-file checks in `SHA256SUMS` passed after the author declared the documentation frozen. This review and the independent artifacts are additional reviewer files, so they are not included in that author-only manifest.

## Supplementary independent replay

Wrote and ran a separate integer-coefficient-array implementation of the literal source procedure. It repeatedly splits the polynomial at X² and forms (X+1)t+r, without a polynomial-remainder library or a Fibonacci-sum shortcut. It checks strict degree decrease on each step.

The replay reduced the source polynomials for every index 1 through 120, performed 7021 successful strict-degree checks, matched all 23 frozen terms of each component, and verified both recurrences at every index 4 through 120. [independent_reduction_check.json](independent_reduction_check.json) records the method, ranges, first pairs, and source hashes. These finite checks support source fidelity and indexing; the complete unbounded claims are proved by the Lean modules.

## Provenance assessment and limits

Independent primary-source checks confirmed that both target entries record the recurrence as Mathar's May 4, 2014 conjecture. The frozen A192251 entry also credits Campbell's 2016 Fibonacci-weighted sum formula. The package properly credits that formula and makes no claim to have discovered the sequence or its weighted-sum representation.

Inspected the research-only extraction of Wiktorowicz's [2026 note](https://oeis.org/A192232/a192232.pdf): Lemmas 1–2, the closure fact, the full statement and proof of Theorem A, and the Section 6 inventory. My attempts to refetch the PDF returned HTTP 403; the inspected extraction records the author's earlier successful full-paper web response and is not presented as a new download. Lemma 1 supplies the same general source-to-remainder observation used here, and Lemma 2 supplies the general Fibonacci-weighted component sums. These are correctly credited as prior supporting material. Theorem A explicitly assumes that the input b(k) is a polynomial in k and gives denominator dividing (1−x)(1−x−x²)^(d+1). Its inventory does not include either selected target. This polynomial-input theorem does not establish the particular central-binomial polynomial-coefficient recurrence proved in this package. The review does not turn this bounded comparison into a claim of worldwide priority.

Read the exact and semantic search receipts, including their result limits and the distinction between current repository heads and older indexed search results. An independent exact/semantic web search returned the primary conjectural entries and related reduction material without an earlier proof of the selected endpoints. The dossier explicitly discloses the related general holonomic literature and the limits of those comparisons.

Separately fetched the full immutable jOEIS A192251 generator and both ATP benchmark files. The jOEIS file implements the known Fibonacci-weighted sum. The SMT problems ask whether two synthesized integer programs agree for every nonnegative input; they are unbounded program-equivalence problems, not finite-prefix tests. Neither inspected problem states Mathar's order-three recurrence or the source polynomial-reduction semantics. The dossier describes this distinction accurately. Existing generators and broad recurrence collections are disclosed, and their existence is not hidden to inflate a novelty claim.

The package is suitable for publication as a complete formally checked proof of the two selected recorded assertions, counted together as one family. Historical first-discovery priority remains outside the scope of the bounded search and this review.
