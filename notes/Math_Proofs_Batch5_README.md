# Four sequence proofs: congruences, growth, and Euler products

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

[Read the six-page manuscript](Math_Proofs_Batch5.pdf) · [LaTeX source](Math_Proofs_Batch5.tex)

This collection proves five selected assertions across four OEIS entries. Each package includes a complete written proof, exact Lean source, pinned dependencies, an official source snapshot, a fresh package build log, an independent audit and compilation log, and SHA-256 checksums.

| Package | Proved result | Main formal theorem |
|---|---|---|
| [A087412](../A087412/README.md) | Exactly `2*3^e` ordered solutions of `x^3+y^3 ≡ 1 (mod 3^e)` for every `e≥2`. | `A087412.original_conjecture` |
| [A217280](../A217280/README.md) | The weighted binomial sum has remainder 1 modulo 5 exactly at indices whose base-five digits are all 0 or 2; all other remainders are 0. | `A217280.conjecture` |
| [A294413](../A294413/README.md) | The complementary recurrence with negative correction has successive-ratio limit `(1+√5)/2`, with an explicit `20(n+1)(2/3)^n` error bound for the shifted ratio. | `A294413.conjecture`, `A294413.ratio_error_bound` |
| [A380385](../A380385/README.md) | Both the finite Euler-product column formula and the negative Euler-product row-sum identity. | `A380385.column_formula`, `A380385.row_sum` |

The four packages contain five Lean modules in total. They use Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All exact final sources have passed a fresh package build and a separate isolated compilation. The final theorem reports contain only `propext`, `Classical.choice`, and `Quot.sound`; there are no proof placeholders, extra axioms, or `native_decide` calls.

## Precise scope

The formal sources begin with the actual finite sum, ordered residue set, complementary-sequence conditions, or source-program recurrence. They do not assume the conjectured formulas.

A294413 applies to every pair satisfying its original conditions and derives growth and convergence; existence and uniqueness of the complementary pair are not separately formalized. A380385 follows the program explicitly designated by the entry as its exact recurrence, including the exceptional first column. The source discrepancies are explained in their package READMEs.

An earlier public attempt concerning A294413 is acknowledged and its general signed-disturbance claim is shown false by an explicit counterexample. The new growth argument supplies the missing condition. The [prior-work addendum for A294532–A294565](../A294532/PRIOR_WORK_ADDENDUM.md) records the related positive-correction notes found during this follow-up search. The earlier family's Lean sources and proved results remain unchanged.

The selected source assertions remained conjectural or tentative in the retrieved entries. The searches and their limits are recorded in the package documentation. This is not a claim of exhaustive historical priority or OEIS editorial acceptance. Lucas congruences, permutation-polynomial algebra, recurrence contraction, and Euler-product identities are credited as established mathematics.

## Reproduce

Enter any of the four package directories with Elan selecting its pinned toolchain:

```sh
lake exe cache get
lake build
```

The included `lake-manifest.json` files pin the transitive dependencies. Each `verification.txt` records the package build; `AUDIT.md` and `audit-verification.txt` record the independent checks. The package `SHA256SUMS.txt` files identify the exact deliverables.
