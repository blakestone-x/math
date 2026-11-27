# Thirty-five ratio bands in two Gray-code Fibonacci recurrences

Research note for Blake Stone, developed with OpenAI Codex.

Stanislav Sykora asked about the mean growth and persistent consecutive-ratio fluctuations of two sequences built from the binary-reflected Gray transform $G(m)=m\mathbin{\mathrm{XOR}}\lfloor m/2\rfloor$. From initial terms $1,1$, A265385 uses $a_{n+2}=G(a_n+a_{n+1})$ and A265387 uses $b_{n+2}=G(b_n)+G(b_{n+1})$. The two sequences satisfy $a_n=G(b_n)$ at every positive index. [OEIS A265385](https://oeis.org/A265385) · [OEIS A265387](https://oeis.org/A265387)

**Theorems.** For both sequences $x$, the mean growth $(x_{2n}/x_n)^{1/n}$ tends to $2$. From numerator index $n=97$ onward, the adjacent ratios $x_n/x_{n-1}$ lie in 35 pairwise disjoint closed intervals indexed by $n\bmod35$. In particular each ratio sequence has at least 35 distinct accumulation points. Every positive shift indivisible by 35 keeps the two ratios uniformly separated. Convergence along individual residue classes remains a further question. [Manuscript (PDF)](manuscript.pdf) · [Editable LaTeX](manuscript.tex) · [35 exact intervals for each sequence](intervals.csv)

A 13-row prefix induction isolates five coarse bands by hand from $n=20$ onward. A refinement enumerates 316,710 prefix pairs and 474,991 directed transitions. Replaying the calculation in both sets of coordinates verifies every phase label and integral interval endpoint. The smallest gaps between the refined enclosures are $15\cdot10^{-12}$ for A265385 and $69\cdot10^{-12}$ for A265387.

The [earlier paper](../A265385/README.md) already proves the mean growth for A265385 and explicitly leaves its adjacent-ratio fluctuations open. The findings added here are the ratio bands for both sequences and the mean-growth theorem for A265387. Sykora’s original conjectural comments are preserved in the [A265385 source record](https://github.com/oeis/oeisdata/blob/main/seq/A265/A265385.seq) and [A265387 source record](https://github.com/oeis/oeisdata/blob/main/seq/A265/A265387.seq).

## Verification

| Claim | Verification |
| --- | --- |
| Recurrence, universal 13-row invariant, five ratio bands at every subsequent index | [Lean 4 source](GrayPhases.lean), standard library only |
| The two real-valued mean-growth limits | [Lean 4 and Mathlib source](GrayLimits.lean) |
| 35 disjoint intervals for each sequence and gap sizes for every other lag | [Exact Python verifier](verify.py) and the [endpoint table](intervals.csv) |
| Recorded runs and axiom reports | [Verification transcript](verification.txt) |

Run the exact integer verifier from this directory. It needs only the Python standard library.

```sh
python3 verify.py
```

With Lean 4.19.0 and Lake, the full project can be built with the pinned Mathlib revision. The first command retrieves prebuilt dependencies.

```sh
lake exe cache get Mathlib.Analysis.SpecialFunctions.Pow.Continuity Mathlib.Analysis.SpecificLimits.Basic Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity
lake build
```

The discrete induction can also be checked by itself with `lean GrayPhases.lean`. The Lean theorems cover the five bands and both growth limits. The 35-band refinement is a computer-assisted integer proof with its own exhaustive verifier.
