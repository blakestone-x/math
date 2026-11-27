# Five formally verified proof packages

**Blake Stone** · Developed with OpenAI Astra 6.2 · November 26, 2026

[Read the collected proofs (PDF)](Math_Proofs_Batch4.pdf) · [LaTeX source](Math_Proofs_Batch4.tex)

This collection contains five Lean packages addressing 38 distinct OEIS entries: a 34-entry family handled by one uniform convergence theorem, plus four separate entries. A second assertion within A073642 is refuted as well. The 34 related cases are counted as one family, and the extra refutation is not counted as another sequence.

| Package | Result | Formal scope |
|---|---|---|
| [A063956](../A063956/README.md) | Unitary-prime-divisor product identity | All positive pairs of integers |
| [A073642](../A073642/README.md) | Squared-valuation identity for the weighted binary digit sum | All natural indices, using standard binary digits and 2-adic valuations |
| [A073642 asymptotic addendum](../A073642/Asymptotic.lean) | The proposed natural-log constant range below 1/2 is impossible | A power-of-two subsequence limit and exclusion of every full limit below 1/2 |
| [A129453](../A129453/README.md) | Generalized binomial quotient is an integer square | The original double gcd product; all 0 ≤ k ≤ n, with exact division proved |
| [A143132](../A143132/README.md) | Last decimal digits repeat 1,6,6,6 | All positive OEIS indices |
| [A294532–A294565](../A294532/README.md) | Successive-term ratios tend to the golden ratio, with an explicit error bound | Every pair satisfying the exact complementary-sequence specification; existence and uniqueness are not separately formalized |

All five packages have successful fresh Lean 4.19.0 builds, pinned mathlib dependencies, source hashes, and separate mathematical and compiler audits. The final axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The proofs contain no unfinished placeholders or additional axioms.

The source notes credit earlier formulas and results, especially Kimberling–Moses (2019) on complementary equations and Ma (2025) on ordinary integrality. The official OEIS exports still mark the selected assertions as conjectural or tentative. Targeted prior-work searches found no earlier proofs of the exact selected assertions; that bounded finding is not an exhaustive priority claim or a claim of OEIS acceptance.

The PDF contains the complete written arguments and was compiled twice and visually checked on all eight pages. With a standard TeX Live installation, reproduce it from this directory using:

```sh
pdflatex Math_Proofs_Batch4.tex
pdflatex Math_Proofs_Batch4.tex
```

Each proof package gives its own `lake` verification commands and records the exact checked sources. [Math_Proofs_Batch4_sources.json](Math_Proofs_Batch4_sources.json) records the retrieved revisions and SHA-256 hashes for the four separate OEIS entries and two related prior-work entries. The [family source manifest](../A294532/source_manifest.json) covers all 34 family members.
