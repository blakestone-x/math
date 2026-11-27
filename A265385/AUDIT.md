# Verification and scope review: OEIS A265385

Review date: November 26, 2026.

## Result

The supplied Lean sources prove the mean growth conjecture recorded in [OEIS A265385](https://oeis.org/A265385):

$$
\lim_{n\to\infty}\left(\frac{a(2n)}{a(n)}\right)^{1/n}=2,
$$

where $a(1)=a(2)=1$, $a(n)=G(a(n-1)+a(n-2))$ for $n\ge3$, and $G(m)=m\mathbin{\mathrm{XOR}}\lfloor m/2\rfloor$.

No mathematical defect was found in the invariant argument or its passage to the real limit. Both source files were independently compiled successfully, including a fresh rebuild of `Proof.olean` before compiling `Limit.lean`.

## Statement fidelity

- `a 1 = 1` and `a 2 = 1` agree with the OEIS initial conditions.
- The recursive clause `a (n + 3) = gray (a (n + 2) + a (n + 1))` gives exactly the stated recurrence for every index at least three.
- The auxiliary value `a 0 = 0` is never used to generate the positive-index sequence.
- `gray n` is natural-number XOR with `n / 2`, so the division is integer division as required.
- `meanGrowth n` uses real division and real exponentiation: `((a (2*n) : ℝ) / (a n : ℝ)) ^ (1 / (n : ℝ))`.
- The final theorem is `Tendsto meanGrowth atTop (𝓝 2)`, with no additional hypotheses. The arbitrary totalization at index zero has no effect on this limit.

## Mathematical audit

The key invariant is

$$
\left\lfloor\frac{a(k+7)}{2^k}\right\rfloor=52
\qquad(k\ge0).
$$

Its two initial values are checked exactly. For the induction step, if the preceding terms lie in their asserted intervals, their sum has quotient 39 on division by the next power of two. The Gray transform commutes with deleting low binary digits, and $G(39)=52$. Thus the argument establishes the invariant for every natural-number index, rather than only for a computed prefix of the sequence.

The proof then obtains

$$
52\,2^n\le128\,a(n)<53\,2^n\qquad(n\ge5).
$$

The cases $n=5,6$ are exact finite evaluations; all larger indices follow from the unbounded induction. These bounds also establish the positivity needed for division. The cross-multiplied ratio inequalities in `Proof.lean` are converted to real inequalities in `Limit.lean`, giving

$$
2\left(\frac{52}{53}\right)^{1/n}
\le\left(\frac{a(2n)}{a(n)}\right)^{1/n}
\le2\left(\frac{53}{52}\right)^{1/n}
\qquad(n\ge5).
$$

Both outside expressions converge to 2. The formal limit theorem applies the squeeze theorem with these eventually valid bounds.

## Formal verification

Toolchain: `leanprover/lean4:v4.19.0`.

Mathlib commit: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

Reproduction commands, run in this package directory after installing the pinned Lean toolchain:

```sh
lake exe cache get Mathlib.Analysis.SpecialFunctions.Pow.Continuity Mathlib.Analysis.SpecificLimits.Basic Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity
lake build
```

The packaged project built successfully. Before packaging, independent verification also freshly compiled `Proof.lean` to `Proof.olean` and then compiled `Limit.lean`; both of those commands exited with status 0. The final theorem's reported dependencies were exactly:

```text
'A265385.growth_rate_limit' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

These are standard Lean axioms. There was no `sorryAx` dependency. Source inspection also found no `sorry`, `admit`, custom axiom, `native_decide`, `unsafe` declaration, or `implemented_by` override in either proof file. The proof does not assume its growth estimate or a logically equivalent convergence claim.

The packaged sources add explanatory and author headers to the independently reviewed sources; their semantic proof content is unchanged. The complete packaged project was then checked with `lake build`, which exited with status 0. The exact compiler version and output are recorded in `verification.txt`.

Packaged source SHA-256 hashes:

| File | SHA-256 |
| --- | --- |
| `Proof.lean` | `183ad5a3b3f711654c27f9c9bc9cc586f616c8cac59a2d69f9dd1d16546febe5` |
| `Limit.lean` | `f7f07a562d9b1b81aa009e1398eee1d54400f1f6335f125fde05d4403177a63f` |

## Source status and novelty limits

The [live OEIS internal entry](https://oeis.org/A265385/internal), retrieved during this work, still described the mean growth limit as a conjecture. Its entry revision was `#18 Jan 16 2016 18:01:31`. The entry linked a table of 1,000 terms and background pages on Fibonacci numbers and Gray code; it did not link a proof.

Searches for the exact sequence identifier with “proof” and “theorem”, and for the author and Gray-transformed Fibonacci recurrence, did not locate an earlier proof. This supports describing the result as a proof of a conjecture still listed as such by OEIS. It does not establish exhaustive publication priority or independent acceptance by OEIS.

## Explicit scope

The proved assertion is the mean growth limit above. The OEIS comment also describes persistent fluctuations in the ratios of consecutive terms. This package does not prove that those fluctuations persist or characterize their limiting behavior. Neither that observation nor the behavior of other Gray-code recurrences is used in the theorem.
