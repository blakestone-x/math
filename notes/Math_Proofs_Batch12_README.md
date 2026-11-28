# Batch 12: three complete conjecture proofs

**Blake Stone · Proofs developed with ChatGPT · November 27, 2026**

The [nine-page manuscript](Math_Proofs_Batch12.pdf), *Floor sequences, replacement words, and cyclotomic products*, gives complete mathematical proofs of three precise assertions recorded as conjectural or empirical in the OEIS. Each assertion also has a complete Lean proof connected to its literal source definition.

| Package | Assertion proved | Principal formal endpoint |
| --- | --- | --- |
| [A081097](../A081097/README.md) | The increasing enumeration of all positive solutions of the fixed-5 nested-floor equation, and Barker's exact empirical generating function. | `A081097.full_resolution` |
| [A288511](../A288511/README.md) | Every literal replacement-word length equals the independently defined thirteen-term source recurrence. | `Kimberling288511.all_lengths` |
| [A118207](../A118207/README.md) | Bala's identity between the Liouville-weighted product at X² and the paired cyclotomic product at X and −X, as complete formal power series. | `A118207.full_resolution` |

## 1. A081097: a floor equation becomes four exhaustive Pell orbits

The source asks for positive integers n satisfying

\[
n^2=\frac15\left(n+\left\lfloor\sqrt5\,n\lfloor\sqrt5\,n\rfloor\right\rfloor\right).
\]

Both directions of the floor reduction are proved. With x = 5n−1, the equation is equivalent to a nonnegative integer solution of x²−5y² in {−4,−9}, with x congruent to 4 modulo 5. Every such pair lies in exactly one ordered orbit of the matrix

\[
U=\begin{pmatrix}161&360\\72&161\end{pmatrix}
\]

starting at (4,2), (29,13), (114,51), or (199,89). An inverse-unit descent proves exhaustiveness; a kernel-checked finite certificate supplies only its terminal case. Ordering the four orbits proves an increasing enumeration of all source members and the exact rational generating function printed in the source.

The first eight terms are 1, 6, 23, 40, 273, 1870, 7343, 12816, and the enumeration satisfies

\[
a(j+8)=322a(j+4)-a(j)-64\qquad(j\ge1).
\]

This is the fixed-parameter assertion with parameter 5. The separate OEIS conjecture concerning arbitrary nonsquare parameters remains outside this result. Zero satisfies the displayed equation trivially, but is excluded in accordance with the positive source list and its offset.

Proof and provenance: [Lean endpoint](../A081097/Proof.lean), [source checks](../A081097/source_checks.md), [independent review](../A081097/independent_review.md), [OEIS source](https://oeis.org/A081097).

## 2. A288511: the exact lengths of a literal replacement process

Start at the finite word 00. At each step, scan once from left to right, applying the nonoverlapping rules 00 → 0101 and 10 → 001 and copying unmatched letters. The theorem proves that every resulting word length equals A288511, including all sixteen initial values and the specified recurrence beginning at index 16.

The proof uses three code blocks, 10, 100, and 1000, whose interior evolution is governed by A → B, B → C, C → AAB. A ten-phase boundary description proves an identity of actual finite words at every later step. The block counts obey an affine state update. A universal symbolic certificate then yields the thirteen-term recurrence, and strong induction proves equality with the independently specified source sequence at every natural index.

The same length conjecture appears in A288508, A288511, and A288512 and is counted once. Adjacent position, frequency, and limiting-word conjectures are not included. The source's printed generating function has an extra leading x relative to its offset zero; the manuscript documents the corrected generating function as an algebraic corollary, without counting it as an additional resolution or claiming a separate formal-series theorem.

Proof and provenance: [Lean endpoint](../A288511/Proof.lean), [source checks](../A288511/source_checks.md), [independent review](../A288511/independent_review.md), [OEIS source](https://oeis.org/A288511).

## 3. A118207: the complete Liouville–cyclotomic identity

Let λ(n) = (−1)^Ω(n), with Ω counting prime factors with multiplicity, and put

\[
A(X)=\prod_{n\ge1}(1+X^n)^{\lambda(n)}.
\]

The result proves Bala's exact conjecture:

\[
\boxed{A(X^2)=\prod_{n\ge1}\Phi_n(X^n)\Phi_n((-X)^n).}
\]

Bala's April 9, 2023 note already proves a related helper identity for the product of (1−Xⁿ)^λ(n). That helper is explicitly credited and re-proved in Lean. The additional even/odd product argument uses λ(2n) = −λ(n) and cancels the two cyclotomic signs.

The formal proof establishes the algebraic identity for nilpotent elements in arbitrary commutative rings, then applies it in every quotient ℚ[[X]]/(X^(N+1)). A separately proved stabilization theorem connects those finite products to the literal source factor families. The final statement is equality of complete formal series and every coefficient, with no fixed degree bound and no analytic convergence hypothesis.

Proof and provenance: [Lean endpoint](../A118207/Proof.lean), [source checks](../A118207/source_checks.md), [independent review](../A118207/independent_review.md), [OEIS source](https://oeis.org/A118207), [Bala's credited helper note](https://oeis.org/A118205/a118205.pdf).

## Reproduction and evidence

The packages contain seventeen local proof modules: six for A081097, four for A288511, and seven for A118207. Every local module is an explicit default Lake root. All three projects pin Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

Run the following separately inside each package:

```sh
lake exe cache get
lake build
```

Each package includes an author build, a fresh build performed during independent review, exact source/configuration hashes, and a review of its mathematical argument and source binding. Only source and configuration files were copied into those isolated build directories; the pinned external dependency cache was shared. The principal axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. The bounded Pell certificate uses only `propext`. There are no admitted proofs, custom axioms, or calls to `native_decide` in the proof sources.

The independent reviews were performed by separate collaborating agents who had not contributed to the respective package's proof sources. They are internal reviews, not external journal peer review. Exact-integer and finite-series replays are supplementary checks; the unbounded results are supplied by the mathematical and Lean proofs.

Each source dossier records immutable OEIS exports and bounded exact/semantic searches of the web, global GitHub, ProveIt, and trureturing. No earlier settlement of these exact assertions was located in the inspected material. Search coverage and indexing limits prevent that conclusion from establishing worldwide priority. Known methods and previously proved helper identities retain their attribution and are not counted as additional problems.

## Files

- [Manuscript PDF](Math_Proofs_Batch12.pdf)
- [Self-contained LaTeX source](Math_Proofs_Batch12.tex)
- [PDF build and visual inspection record](Math_Proofs_Batch12_build.log)
- [Collection review record](Math_Proofs_Batch12_review.md)
- [Collection SHA-256 inventory](Math_Proofs_Batch12_SHA256SUMS.txt)

Each proof package has its own complete SHA-256 inventory. The publication contains three distinct conjectural-assertion resolutions; the shared word conjecture, four Pell orbits, and classical product lemmas are counted at their proper scope.
