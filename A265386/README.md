# The growth rate and alternating ratios of OEIS A265386

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

A complete written and Lean-checked proof of the mean-growth conjecture in [OEIS A265386](https://oeis.org/A265386), together with a quantitative theorem about its persistent alternating ratios.

## Results

Let `G(m) = m XOR floor(m/2)` be the binary-reflected Gray transform. The sequence is

$$
a(1)=a(2)=1,\qquad
a(n)=G\bigl(G(a(n-1))+G(a(n-2))\bigr)\quad(n\ge3).
$$

The conjectured mean growth rate is correct:

$$
\boxed{\lim_{n\to\infty}\left(\frac{a(2n)}{a(n)}\right)^{1/n}=\sqrt2.}
$$

The adjacent ratios also satisfy, for every integer $k\ge8$,

$$
\boxed{\frac{a(2k+1)}{a(2k)}>3,\qquad
\frac{a(2k+2)}{a(2k+1)}<\frac23.}
$$

Thus the alternating large and small steps persist forever, and adjacent ratios cannot converge to one value. The mean growth statement remains valid despite those fluctuations.

## The proof's invariant

For every integer $j\ge0$, the normalized leading-bit pair

$$
\left(\left\lfloor\frac{a(2j+16)}{2^j}\right\rfloor,
\left\lfloor\frac{a(2j+17)}{2^j}\right\rfloor\right)
$$

belongs to an explicit set of **48 states**, starting from $(158,510)$.

Gray code commutes with deleting low binary digits. Each addition introduces one carry in $\{0,1\}$. Consequently each state has four possible two-step transitions. The set is closed under all **192 transitions**, which Lean verifies by ordinary kernel evaluation. An induction then proves membership for every index.

The resulting bounds are

$$
136\,2^j\le a(2j+16)<160\,2^j,
\qquad489\,2^j\le a(2j+17)<512\,2^j.
$$

They imply the uniform squared bounds

$$
2^n\le4a(n)^2,\qquad a(n)^2<2^{n+1}\qquad(n\ge16).
$$

Applying these at $n$ and $2n$ and taking positive real $2n$th roots proves the mean-growth limit by squeezing. The sharper parity bounds give both adjacent-ratio inequalities directly.

## Files

| File | Purpose |
| --- | --- |
| [A265386_proof.pdf](A265386_proof.pdf) | Complete mathematical proof, including the explicit 48-state table. |
| [A265386_proof.tex](A265386_proof.tex) | Editable LaTeX source. |
| [Proof.lean](Proof.lean) | Exact recurrence, explicit certificate, kernel-checked closure, unbounded induction, parity bounds, positivity, and adjacent-ratio inequalities. Imports only `Std`. |
| [Limit.lean](Limit.lean) | Squared bounds, ratio estimates, and the unconditional real limit theorem. |
| [certificate.json](certificate.json) | Human-readable data for the same 48-state set embedded in the Lean proof. |
| [lean-toolchain](lean-toolchain) | Lean 4.19.0. |
| [lakefile.lean](lakefile.lean), [lake-manifest.json](lake-manifest.json) | Project configuration and locked dependencies. |
| [verification.txt](verification.txt) | Successful fresh build output and axiom reports for the packaged sources. |
| [AUDIT.md](AUDIT.md) | Independent mathematical and formal review, source hashes, and novelty limits. |
| [audit-verification.txt](audit-verification.txt) | Output from the independent rebuild of both source files. |
| [SHA256SUMS.txt](SHA256SUMS.txt) | Checksums of the package files. |

## Reproduce the verification

Run these commands from this directory, with Lean managed by Elan so the supplied toolchain file is honored.

The complete discrete invariant and oscillation proof needs only Lean's standard library:

```sh
lean Proof.lean
```

For the full real-valued limit:

```sh
lake exe cache get \
  Mathlib.Analysis.SpecialFunctions.Pow.Continuity \
  Mathlib.Analysis.SpecificLimits.Basic \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.Positivity
lake build
```

Mathlib is pinned to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, its `v4.19.0` revision. The supplied manifest locks all transitive dependencies; `lake update` is unnecessary.

The final theorem, in namespace `A265386`, is:

```lean
noncomputable def meanGrowth (n : ℕ) : ℝ :=
  ((a (2*n) : ℝ) / (a n : ℝ)) ^ (1 / (n : ℝ))

theorem growth_rate_limit :
    Tendsto meanGrowth atTop (𝓝 (Real.sqrt 2))
```

The persistent-oscillation theorem is expressed without division:

```lean
theorem adjacent_oscillation (k : Nat) :
    3 * a (2*k+16) < a (2*k+17) ∧
    3 * a (2*k+18) < 2 * a (2*k+17)
```

The positivity theorem justifies translating these into the displayed ratio inequalities. Nonconvergence of the adjacent ratios is an immediate written consequence of the separation of the two subsequences; the formal source proves the stronger uniform separation inequalities themselves.

Both packaged modules passed a fresh `lake build`. Their audited theorems have only these standard Lean logical dependencies:

```text
[propext, Classical.choice, Quot.sound]
```

There are no unfinished proofs, custom axioms, or `native_decide` calls. The finite certificate is checked inside Lean and connected to every natural-number index by induction. No finite prefix of computed terms is assumed to establish the universal statements.

To rebuild the paper with a standard TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error A265386_proof.tex
pdflatex -interaction=nonstopmode -halt-on-error A265386_proof.tex
```

## Source status and attribution

Stanislav Sykora contributed the sequence on December 7, 2015. The [live OEIS entry](https://oeis.org/A265386) and its [internal representation](https://oeis.org/A265386/internal) were inspected on November 26, 2026. The entry still stated the mean growth limit conjecturally; its revision was `#16 Jan 16 2016 18:08:45`.

Searches by exact identifier and equivalent recurrence descriptions, including available formal-proof collections, did not locate an earlier proof. This records the source status checked during this work; it does not establish exhaustive publication priority or imply that OEIS has reviewed or accepted this proof.
