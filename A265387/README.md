# Seventy ratio bands in two Gray-code Fibonacci recurrences

The [arbitrary-seed continuation](universal.md) proves mean growth 2 for every positive pair of seeds, classifies the eventual five-step sign patterns, and proves at least 141 accumulation points of each original ratio sequence. The [all-residue proof](phase_paths.pdf) raises the bound to **280** and shows oscillation on every residue class modulo 140. [Manuscript](universal.pdf) · [Lean growth theorem](UniversalGrowth.lean) · [Lean limits](UniversalLimits.lean)

Research note for Blake Stone, developed with OpenAI Codex.

Stanislav Sykora asked about the mean growth and persistent consecutive-ratio fluctuations of two sequences built from the binary-reflected Gray transform $G(m)=m\mathbin{\mathrm{XOR}}\lfloor m/2\rfloor$. From initial terms $1,1$, A265385 uses $a_{n+2}=G(a_n+a_{n+1})$ and A265387 uses $b_{n+2}=G(b_n)+G(b_{n+1})$. The two sequences satisfy $a_n=G(b_n)$ at every positive index. [OEIS A265385](https://oeis.org/A265385) · [OEIS A265387](https://oeis.org/A265387)

**Theorems.** For both sequences $x$, the mean growth $(x_{2n}/x_n)^{1/n}$ tends to $2$. From numerator index $n=97$, the adjacent ratios $x_n/x_{n-1}$ lie in 35 disjoint closed intervals indexed by $n\bmod35$. From $n=1401$, they lie in 70 disjoint closed intervals indexed by $n\bmod70$. Consequently **all 35 subsequences modulo 35 fail to converge**, and each full ratio sequence has at least **70 distinct accumulation points**. The subsequent all-residue paper settles convergence on individual classes modulo 70 and 140. [Manuscript (PDF)](manuscript.pdf) · [Editable LaTeX](manuscript.tex)

A 13-row prefix induction isolates five coarse bands by hand from $n=20$. Two more inductions track progressively finer binary prefixes. The verifier replays both sequences in separate coordinates and checks every state, label and integer endpoint.

| Residues | First numerator index | Reachable pairs per graph | Directed transitions | Exact enclosure table |
| ---: | ---: | ---: | ---: | --- |
| 35 | 97 | 316,710 | 474,991 | [Endpoints in units of $10^{-12}$](intervals.csv) |
| 70 | 1401 | 67,410 | 101,108 | [Endpoints in units of $10^{-26}$](intervals70.csv) |

For a positive lag indivisible by 35, the ratios stay separated by at least $15\cdot10^{-12}$ in A265385 and $69\cdot10^{-12}$ in A265387 from $n=97$. For a positive lag indivisible by 70, the corresponding bounds are $36\cdot10^{-26}$ and $25\cdot10^{-26}$ from $n=1401$.

The [earlier paper](../A265385/README.md) already proves the mean growth for A265385 and explicitly leaves its adjacent-ratio fluctuations open. The findings added here are the ratio bands for both sequences and the mean-growth theorem for A265387. Sykora’s original conjectural comments are preserved in the [A265385 source record](https://github.com/oeis/oeisdata/blob/main/seq/A265/A265385.seq) and [A265387 source record](https://github.com/oeis/oeisdata/blob/main/seq/A265/A265387.seq).

## Verification

| Claim | Verification |
| --- | --- |
| Recurrence, universal 13-row invariant, five ratio bands at every subsequent index | [Lean 4 source](GrayPhases.lean), standard library only |
| The two real-valued mean-growth limits | [Lean 4 and Mathlib source](GrayLimits.lean) |
| 35 and 70 disjoint intervals per sequence, nonconvergence modulo 35, and lag bounds | [Exact Python verifier](verify.py) and both published endpoint tables |
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

The discrete induction can also be checked by itself with `lean GrayPhases.lean`. The Lean theorems cover the five bands and both growth limits. The 35- and 70-band refinements are computer-assisted integer proofs with an exhaustive verifier.
