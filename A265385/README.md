# The growth rate of OEIS A265385

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

A complete written and machine-checked proof of the mean-growth conjecture stated in [OEIS A265385](https://oeis.org/A265385), contributed by Stanislav Sykora in 2015.

## Result

Let `G(m) = m XOR floor(m/2)` be the binary-reflected Gray transform, and define

$$
a(1)=a(2)=1,\qquad a(n)=G(a(n-1)+a(n-2))\quad(n\ge3).
$$

Then

$$
\boxed{\lim_{n\to\infty}\left(\frac{a(2n)}{a(n)}\right)^{1/n}=2.}
$$

The key invariant is stronger than the limit:

$$
52\,2^n\le128\,a(n)<53\,2^n\qquad(n\ge5).
$$

Equivalently, for every `n ≥ 7`, the binary representation of `a(n)` begins with the same six digits, `110100`:

$$
\left\lfloor\frac{a(n)}{2^{n-7}}\right\rfloor=52.
$$

Gray code commutes with deleting low-order bits. The bounds on the two previous terms force their sum into the prefix interval for `39`, and `G(39)=52` reproduces the invariant. Consequently

$$
\frac{52}{53}\,2^n<\frac{a(2n)}{a(n)}<\frac{53}{52}\,2^n\qquad(n\ge5),
$$

so taking positive real nth roots and applying the squeeze theorem proves the result.

## Files

| File | Purpose |
| --- | --- |
| [A265385_proof.pdf](A265385_proof.pdf) | Complete mathematical proof, quantitative error bound, verification overview, and source attribution. |
| [A265385_proof.tex](A265385_proof.tex) | Editable LaTeX source of the paper. |
| [Proof.lean](Proof.lean) | The exact recurrence, prefix invariant, universal exponential bounds, positivity, and integer ratio inequalities; imports only `Std`. |
| [Limit.lean](Limit.lean) | Real ratio inequalities, nth-root squeeze, and the unconditional real limit theorem. |
| [lean-toolchain](lean-toolchain) | Pins Lean 4.19.0. |
| [lakefile.lean](lakefile.lean), [lake-manifest.json](lake-manifest.json) | Project configuration and pinned dependency revisions. |
| [verification.txt](verification.txt) | Successful compiler/build output and axiom reports for the actual packaged sources. |
| [AUDIT.md](AUDIT.md) | Independent mathematical and formal review, source hashes, and scope/novelty qualifications. |

## Reproduce the verification

Run these commands from this directory, with Lean managed by Elan so that the supplied `lean-toolchain` is honored.

The integer proof needs only Lean's standard library:

```sh
lean Proof.lean
```

For the complete real-limit theorem:

```sh
lake exe cache get Mathlib.Analysis.SpecialFunctions.Pow.Continuity Mathlib.Analysis.SpecificLimits.Basic Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity
lake build
```

The project pins Mathlib to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, the `v4.19.0` revision. The dependency lockfile is included. Downloading the Mathlib cache avoids rebuilding the library from source.

The final checked statement is:

```lean
noncomputable def meanGrowth (n : ℕ) : ℝ :=
  ((a (2*n) : ℝ) / (a n : ℝ)) ^ (1 / (n : ℝ))

theorem growth_rate_limit :
    Tendsto meanGrowth atTop (𝓝 2)
```

Both declarations are in namespace `A265385`. The sequence is defined with the original OEIS indexing. Its auxiliary value at zero is unused in generating the positive-index terms and does not affect the limit.

`lake build` completed successfully on the packaged source files. The final theorem's `#print axioms` output is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean logical dependencies. There are no unfinished proofs, added axioms, or external numerical certificates. The induction covers every natural-number index; finite checking is used only for the explicitly stated initial cases.

To rebuild the PDF with an ordinary TeX installation containing the packages listed in the source:

```sh
pdflatex -interaction=nonstopmode -halt-on-error A265385_proof.tex
pdflatex -interaction=nonstopmode -halt-on-error A265385_proof.tex
```

## Source status and precise scope

The live [OEIS entry](https://oeis.org/A265385) and its [internal representation](https://oeis.org/A265385/internal) were inspected on November 26, 2026. The entry still stated the mean-growth assertion conjecturally, and its internal revision was `#18 Jan 16 2016 18:01:31`. Searches by exact sequence identifier and equivalent recurrence descriptions did not locate an earlier proof. This establishes the source status checked during this work; it does not certify exhaustive publication priority or imply acceptance by OEIS.

The theorem proves the mean growth limit of 2. The separate observation in the OEIS comment about persistent fluctuations of adjacent-term ratios is outside its scope. The PDF also derives the ordinary root-growth limit and an explicit logarithmic error bound; these are elementary written corollaries, while the Lean files formally verify the bounds and the stated OEIS mean-growth limit.

## Adjacent-term fluctuations

The companion manuscript now proves the persistent fluctuations from Sykora’s original comment. The ratios for A265385 have at least 35 distinct accumulation points. The same analysis treats the related recurrence A265387. [Proof and exact certificates](../A265387/README.md)
