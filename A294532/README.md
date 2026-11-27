# A294532–A294565: complementary Fibonacci ratios

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Result

For all 34 complementary-sequence equations in OEIS A294532 through A294565, the ratio of successive `a` terms converges to the golden ratio:

$$
\lim_{n\to\infty}\frac{a_{n+1}}{a_n}=\phi=\frac{1+\sqrt5}{2}.
$$

The proof also gives the uniform quantitative estimate

$$
\left|\frac{a_{n+1}}{a_n}-\phi\right|\le97(n+1)\left(\frac23\right)^n
\qquad(n\ge0).
$$

These are 34 related instances of one general argument. They are not 34 independent proof methods. The additional alternative equation appearing in the family guide is covered separately and is not counted as another OEIS entry.

**Formal scope:** the theorems quantify over every pair of sequences satisfying the exact defining conditions below. No convergence or growth assumption is added. This package does not separately construct the sequences by a mex algorithm or prove existence and uniqueness of the complementary pairs.

## Exact defining conditions

Let `a,b : ℕ → ℕ` be strictly increasing, with disjoint ranges that together cover all positive integers, and let

$$
a_0=1,\qquad a_1=2,\qquad b_0=3.
$$

For one coefficient row in the table, require

$$
a_{n+2}=a_{n+1}+a_n+e_n,
\qquad e_n=p b_{n+1}+q b_n+r n+s.
$$

The coefficients are integers. The recurrence is an equality over the integers, so negative coefficients are not interpreted as truncated natural-number subtraction. The table uses the shifted index `n+2`: an original term `r*n+c` in the OEIS title becomes `r*n+(2*r+c)` here.

| Entry | p | q | r | s |
|---|---:|---:|---:|---:|
| [A294532](https://oeis.org/A294532) | 0 | 1 | 0 | 0 |
| [A294533](https://oeis.org/A294533) | 0 | 1 | 0 | 1 |
| [A294534](https://oeis.org/A294534) | 0 | 1 | 0 | 2 |
| [A294535](https://oeis.org/A294535) | 0 | 1 | 0 | 3 |
| [A294536](https://oeis.org/A294536) | 0 | 1 | 0 | -1 |
| [A294537](https://oeis.org/A294537) | 0 | 1 | 1 | 2 |
| [A294538](https://oeis.org/A294538) | 0 | 1 | 2 | 4 |
| [A294539](https://oeis.org/A294539) | 0 | 1 | 1 | 1 |
| [A294540](https://oeis.org/A294540) | 0 | 1 | 2 | 3 |
| [A294541](https://oeis.org/A294541) | 1 | 0 | 0 | 0 |
| [A294542](https://oeis.org/A294542) | 1 | 0 | 0 | 1 |
| [A294543](https://oeis.org/A294543) | 1 | 0 | 0 | 2 |
| [A294544](https://oeis.org/A294544) | 1 | 0 | 0 | 3 |
| [A294545](https://oeis.org/A294545) | 1 | 0 | 0 | -1 |
| [A294546](https://oeis.org/A294546) | 1 | 0 | 1 | 2 |
| [A294547](https://oeis.org/A294547) | 1 | 0 | 2 | 4 |
| [A294548](https://oeis.org/A294548) | 1 | 0 | 1 | 1 |
| [A294549](https://oeis.org/A294549) | 1 | 0 | 1 | 3 |
| [A294550](https://oeis.org/A294550) | 1 | 1 | 0 | 0 |
| [A294551](https://oeis.org/A294551) | 1 | 1 | 0 | 1 |
| [A294552](https://oeis.org/A294552) | 1 | 1 | 1 | 2 |
| [A294553](https://oeis.org/A294553) | 1 | 1 | -1 | -2 |
| [A294554](https://oeis.org/A294554) | 1 | 1 | 0 | 2 |
| [A294555](https://oeis.org/A294555) | 1 | 1 | 0 | 3 |
| [A294556](https://oeis.org/A294556) | 1 | 1 | 1 | 3 |
| [A294557](https://oeis.org/A294557) | 1 | 1 | 1 | 1 |
| [A294558](https://oeis.org/A294558) | 1 | 1 | 2 | 4 |
| [A294559](https://oeis.org/A294559) | 1 | 2 | 0 | 0 |
| [A294560](https://oeis.org/A294560) | 2 | 2 | 0 | 0 |
| [A294561](https://oeis.org/A294561) | 2 | 1 | 0 | 0 |
| [A294562](https://oeis.org/A294562) | 1 | -1 | 0 | 1 |
| [A294563](https://oeis.org/A294563) | 1 | -1 | 1 | 2 |
| [A294564](https://oeis.org/A294564) | 2 | -1 | 0 | -1 |
| [A294565](https://oeis.org/A294565) | 2 | -1 | 0 | -2 |

The A294532 guide gives the final A294565 equation with constant `-3`, while [A294565's own title](https://oeis.org/A294565) gives `-2`. The table follows the individual title. The additional parameter `A294565Guide = (2,-1,0,-3)` and theorem `A294565Guide_ratio_limit` cover the guide's variant as well. All 34 individual titles were checked against the [official OEIS export](https://github.com/oeis/oeisdata), snapshot `2026-11-26T03:00:21-05:00`; the source manifest records the exact revisions and file hashes.

The A294532 Mathematica snippet has different seeds (`a_0=1,a_1=3,b_0=2`) from its title and displayed data. This package follows the title and data (`a_0=1,a_1=2,b_0=3`), which are the specification stated above. It does not use that inconsistent program snippet as a definition.

## Proof

### 1. The complementary sequence grows at most linearly

Strict increase and the initial values give

$$
a_n\ge n+1,\qquad b_n\ge n+3,\qquad b_{n+1}\ge b_n+1.
$$

Substituting these inequalities into the finite coefficient table proves `e_n ≥ 2` for every row, including the guide variant. For example,

$$
b_{n+1}-b_n+1\ge2,
\qquad 2b_{n+1}-b_n-3\ge b_n-1\ge n+2.
$$

The recurrence therefore implies `a_(n+2) ≥ a_(n+1)+2`. Beyond the initial pair `1,2`, two consecutive integers cannot both occur in the `a` sequence.

Suppose `b_(n+1) > b_n+2`. The integers `b_n+1` and `b_n+2` lie strictly between consecutive `b` terms, so neither is a `b` term. Complementarity forces both to be `a` terms. Both are at least 4, contradicting the preceding gap property. Consequently

$$
b_{n+1}\le b_n+2,
\qquad n+3\le b_n\le2n+3.
$$

The lower and upper bounds, substituted into each signed linear expression in the table, yield

$$
0\le e_n\le32(n+1).
$$

The formal proof checks all coefficient cases and derives both bounds from the defining conditions.

### 2. A contracting error controls the ratio

More generally, consider a real recurrence

$$
a_{n+2}=a_{n+1}+a_n+e_n,
\quad a_0\ge1,\quad a_1\ge\frac32,
\quad 0\le e_n\le C(n+1),\quad C\ge0.
$$

Two-step induction gives `a_n ≥ (3/2)^n`, because `(3/2)^2 ≤ 3/2+1` and the error is nonnegative. In particular, all denominators are positive.

Define `d_n = a_(n+1) - φ a_n`. The identity `φ²=φ+1` gives

$$
d_{n+1}=(1-\phi)d_n+e_n.
$$

Since `3/2 < φ < 5/3`, we have `|1-φ| ≤ 2/3`. Set `K=3C+|d_0|`. Induction proves

$$
|d_n|\le K(n+1).
$$

Indeed, the induction step is bounded by

$$
\frac23K(n+1)+C(n+1)\le K(n+1)\le K(n+2).
$$

Combining this with the exponential lower bound,

$$
\left|\frac{a_{n+1}}{a_n}-\phi\right|
=\frac{|d_n|}{a_n}
\le\frac{K(n+1)}{(3/2)^n}\longrightarrow0.
$$

This proves existence of the ratio limit as well as its value. For the 34 equations, `C=32`, `d_0=2-φ`, and `K=98-φ<97`, yielding the stated error estimate.

## Prior work and source status

The [family guide A294532](https://oeis.org/A294532) and its individual entries conjecture the golden-ratio limit. Clark Kimberling and Peter J. C. Moses discuss this subject in [*Linear Complementary Equations and Systems*, Fibonacci Quarterly 57(5) (2019), 96–110](https://www.fq.math.ca/Papers1/57-5/kimberling-moses.pdf). Their Theorem 2.1 identifies a dominant-root limit under hypotheses that explicitly include existence of the ratio limit, in condition (ii). The present argument proves convergence from the defining complementary equations for this family and supplies a uniform error bound. The prior conditional identification is not claimed as new.

Targeted searches checked the family identifiers, the complementary Fibonacci formulation, the 2019 paper, and public OEIS proof collections. No earlier proof of convergence for these exact assertions was located in those checks. This is a bounded source-status finding, not an exhaustive historical priority claim or a claim of OEIS acceptance. See [source_checks.md](source_checks.md).

## Formal verification

- [Analytic.lean](Analytic.lean) proves the general real and natural recurrence limits and the quantitative estimate.
- [Proof.lean](Proof.lean) defines the exact `Parameters` and `Solution` specifications, derives the complementary bounds, checks all coefficient rows, and instantiates the general argument.
- `ComplementaryFibonacci.solution_ratio_limit` is the family convergence theorem.
- `ComplementaryFibonacci.solution_ratio_error_bound` is the uniform estimate.
- `A294532_ratio_limit` through `A294565_ratio_limit` are the 34 named corollaries; all are in the `ComplementaryFibonacci` namespace.
- [AUDIT.md](AUDIT.md) and [audit-verification.txt](audit-verification.txt) record a separate review and compilation of the exact final sources.
- [Collected proof notes](../notes/Math_Proofs_Batch4.pdf) contain the human-readable argument with the other results in this batch.

The final sources compile with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The final theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no unfinished proofs, added axioms, `native_decide` calls, or unsafe replacements.

## Reproduce

From this directory, with Elan selecting the pinned toolchain:

```sh
lake exe cache get Mathlib.Analysis.SpecificLimits.Normed Mathlib.Data.Real.Sqrt Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity
lake build
```

The manifest locks transitive dependencies. [verification.txt](verification.txt) contains the successful fresh package build and the checked source hashes. The finite coefficient case split verifies linear inequalities; the resulting theorems cover every natural index.
