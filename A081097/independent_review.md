# Independent review: A081097

Reviewer: sequences12, a separate review agent with no contribution to this package's proof sources. Reviewed November 27, 2026.

## Verdict and scope

**PASS for the fixed-5 empirical generating-function assertion.** All six Lean modules, the exact OEIS export, source_checks.md, README, and the complete manuscript section were inspected. No mathematical or source-binding defect was found. The result proves an increasing, unique enumeration of the positive solutions of the literal nested-floor equation and the exact source numerator–denominator identity. It does not prove the separate source conjecture for arbitrary nonsquare parameters.

The review is independent within this collaborative run. It is not a claim of external journal review or exhaustive historical priority.

## Primary source comparison

I separately fetched the immutable official export at `oeis/oeisdata` commit `72c53dd50967ac7166f7d31bf79be95174ec5bc6` and compared its bytes with `sources/A081097.seq`; they match. Its SHA-256 is `ac65edf8f88112594d9f04f03f1cf9f5a958b6e54fc7d3f21f93661809f0ef20`.

`Source` preserves both real floors, their multiplication order, the factor 1/5, and the parameter 5. The source lists positive integers beginning at 1; the package states this positive restriction explicitly. Although zero also satisfies the displayed equation, it is omitted from the OEIS list and from the proved enumeration. The generated power series is one-based: coefficient zero is 0 and coefficient j+1 is the zero-based formal term j.

The source's factored denominator and complete signed numerator were compared term by term with `sourceDenominator` and `sourceNumerator`. They agree exactly.

## Mathematical audit

1. **Both directions of the floor bridge.** The necessary square alternatives follow from the two outer-floor inequalities and nonnegativity. Conversely, the two integer square alternatives force the inner floor as well as the outer floor. The potentially delicate case c=2, n=1, where the upper squared inequality would be an equality, is excluded explicitly because it would require an integer square equal to 5. No implication is silently reversed when squaring.

2. **Pell normalization.** Substitution x=5n−1 gives precisely the norms −4 and −9. Positive n gives nonnegative x, and the residue condition x≡4 mod 5 recovers n integrally. The forward orbit step preserves the norm and residue without assuming the desired floor identity.

3. **Exhaustive descent.** The inverse matrix gives a strictly smaller nonnegative first coordinate whenever x≥483. The threshold has a strict margin: 483²−25920·9=9. Descent uses a natural-number measure with its nonnegativity hypotheses, so termination is proved rather than inferred from examples. Every smaller admissible pair lies in the finite rectangle x<483, y<217. The kernel certificate classifies exactly four pairs there. It is only the base case of the unbounded argument.

4. **Actual ordered enumeration.** The four seeds increase in both coordinates and the fourth is smaller than U applied to the first. The positive matrix preserves the required strict inequalities. `term_strictMono`, source membership, and the converse classification together establish unique increasing enumeration, not merely generation of some solutions. Division by five is justified by a separate exact identity rather than by truncating integer division.

5. **Recurrence and generating function.** U has determinant 1 and trace 322. The offset x=5n−1 gives the inhomogeneous constant −64. The four-orbit interleaving correctly produces a gap-four recurrence, and subtracting adjacent instances gives the order-nine homogeneous recurrence. `zeroBased_generating_function` proves every coefficient, splitting only the nine initial coefficients from the general recurrence. The final factorization and sign normalization recover the literal source expression. The denominator has constant coefficient −1, so the product identity specifies the formal quotient uniquely.

6. **Formal endpoint.** `full_resolution` combines positivity, strict order, literal membership with a unique index, every power-series coefficient, and the source identity. There is no assumed source-to-orbit bridge, restricted finite cutoff, or arbitrary comparison sequence in the final statement.

## Supplementary independent replay

`independent_replay.json` records an independently written integer-only scan of every positive n≤1,000,000. The inner floor was computed as `isqrt(5*n*n)` and the outer floor as `isqrt(5*n*n*inner*inner)`, avoiding floating-point square roots. Its ten members agree exactly with the interleaved Pell orbits. I also independently enumerated all bounded Pell pairs and recovered exactly the four seeds. These checks supplement the proof; they are not the basis of the unbounded conclusion.

## Fresh build and axiom audit

`independent_build.log` records the fresh isolated build on the final manifest. Only source/configuration files were copied into the isolated directory; no local proof objects were reused. All six local proof modules are explicit Lake roots. Lean 4.19.0 and the pinned mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` were used. The first isolated run passed but predated a root-name-only manifest correction; it was deliberately rerun on the final manifest.

The final build shows exit code 0 and the ordinary axiom set `[propext, Classical.choice, Quot.sound]` for the principal endpoints. The finite Pell certificate uses only `propext`. Source inspection found no admitted proof, custom axiom, or `native_decide`. Ordinary `decide +kernel` performs kernel reduction and is appropriate for the bounded certificate.

## Bounded prior-work record

The source dossier distinguishes this precise empirical fixed-5 formula from the broader arbitrary-parameter conjecture and credits classical Pell and matrix methods. Its exact-ID, semantic, global GitHub, ProveIt, and trureturing searches are clearly described as bounded evidence rather than a priority guarantee. The existing jOEIS implementation marked Conjectural and the nearby Cloitre–Shallit paper are explicitly distinguished from a proof of this literal assertion.

## Reviewed source/configuration hashes

- `FloorBridge.lean`: `b2182c92df773616bb6f57a9b8e6d0a3ac55b9de84b9d98a9e5373399e7d38d0`
- `GeneratingFunction.lean`: `e9ce93338076e47f2ca880872e37c81594baee14c3f7a7cc0fac67e3da273baa`
- `PellFinite.lean`: `e722177acf721a327c77ddc01e4bfa2f147c42f4c057cdaa7b899e9e0d2894a1`
- `PellOrbits.lean`: `de9194f13c9532716d3f9303492709282a4dba12033a141575a6e6dac1ee5293`
- `Proof.lean`: `c8664b72dee0ecb3e85e08510ef7002d0906dbb94699b17646b719599fb5c117`
- `Sequence.lean`: `55c4387fdcc0e1141298327402244e3954ce4987bdd6ea0961265f5b774d372d`
- `lakefile.lean`: `60d04509076d1ee656da28cb273d79be6749a0902ed1910d077df2835e1b1280`
- `lean-toolchain`: `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea`
- `lake-manifest.json`: `d0e812b743b93ae5732ea31048ff40dcbcf45a989543a9accb77240f98f5b217`
- `sources/A081097.seq`: `ac65edf8f88112594d9f04f03f1cf9f5a958b6e54fc7d3f21f93661809f0ef20`
