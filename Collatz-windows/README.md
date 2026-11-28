# Collatz windows and logarithmic stopping time

**Status.** This is a conditional reduction of the Collatz conjecture. Proving that the window hypothesis holds for an absolute constant remains open.

Use the shortcut map `T(n) = n/2` on even inputs and `T(n) = (3n+1)/2` on odd inputs. The hypothesis `WindowBound C` says that, for every starting integer `n ≥ 2` and every offset along its orbit, a window of length `N ≥ max(4, C log₂ n)` has at most `5N/8` odd steps. The logarithm uses the original start at every offset.

The W4 statement and split-map valuation formula come from the supplied research notes. This package gives the formal proofs and an audit of the counting argument.

## What Lean proves

* **W4.** If such a constant exists, every positive integer reaches 1. In fact, one good prefix of length `8k` with at most `5k` odd steps forces a strict descent for any start at least 32. The finite smaller starts are checked by the kernel.
* **Quantitative equivalence.** The window hypothesis holds for some constant exactly when every start reaches 1 in at most a constant times its binary logarithm. The file proves both directions.
* **Counting and exceptional starts.** The displayed count estimate and the assumed mass-decay bound imply an infinitely-often lower bound on survival time. A separate binary residue model satisfies the count estimate while arbitrarily large starts survive forever. Using that estimate to deduce a pointwise upper bound would require additional structure specific to the dynamics.
* **2-adic results.** The distance criterion characterizes survival of the multiplicative coefficient. Transferring its converse to numerical stopping uses the coefficient stopping time conjecture. The file also constructs the 2-adic logarithm that gives the exact valuation formula for the split-map family.

## What happens at the first coefficient drop?

Let `t` be the first depth at which `3^a < 2^t`, with `a` odd steps so far. Write `R` for the number of runs of consecutive odd steps. If the numerical endpoint still satisfies `T^t(n) ≥ n`, Lean proves both inequalities

```text
T^t(n) < n + R
n (2^t − 3^a) ≤ 3^a R.
```

During an odd run, the identity `2(T(x)+1) = 3(x+1)` carries one additive unit through the entire run. In particular, with one odd run a numerical miss must be an exact return to the starting value. The file also gives an exact test for which larger starts with the same first `t` parities miss descent. Existence of a suitable prefix for every positive start remains open. The coefficient stopping time conjecture is discussed in [Lagarias's survey](https://web.williams.edu/Mathematics/sjmiller/public_html/355Sp24/addcomments/Lagarias_3x%2B1AndItsGeneralizations.pdf).

The same file checks the classical rising blocks starting at `2^k w − 1`. For any proposed step limit and any lower bound on the start, there is a larger integer whose entire initial segment stays strictly above its starting value after time zero. This explains the need for a start-dependent search horizon. [Roosendaal’s account of the rising family](https://www.ericr.nl/wondrous/)

## A necessary bound on the window constant

Starting at `4,861,718,551,722,727`, exactly 632 of the first 1,011 shortcut steps are odd. Hence `8 × 632 = 5,056 > 5 × 1,011 = 5,055`. This start forces every admissible W4 constant to satisfy

```text
C > 1011 / log₂(4861718551722727) ≈ 19.401122169.
```

Lean checks the parity count and the strict rational lower bound `C > 97/5`. The start is entry 1916 of a published table. [OEIS A033491 data](https://oeis.org/A033491/b033491.txt)

[Descent criteria and numerical certificate](Descent.lean)

## An exact criterion for escape

Let `a(m,t)` count odd inputs in the first `t` shortcut steps from `m`. A positive orbit tends to infinity if and only if **some** positive integer `m` satisfies

```text
3^a(m,t) ≥ 2^t  for every t ≥ 0.
```

Every escaping orbit supplies such an `m` among its own iterates. Conversely, the orbit of any such `m` escapes. Equivalently, escape occurs precisely when the 2-adic set `Slope.omegaSet` contains a positive ordinary integer.

The proof counts visits of a nonrepeating orbit to each interval from `32^j` up to `32^(j+1)`. There are at most `65 · 29^j` visits, giving a convergent geometric bound for the sum of the reciprocals of all iterates. This bounds the accumulated affine corrections. Consequently the coefficient `3^a(n,t)/2^t` tends to infinity and attains a minimum at a finite time. Starting at that minimum gives the required integer. In the reverse direction, the coefficient around every positive cycle is strictly below one. Repeated periods eventually violate the displayed inequality.

Full convergence is equivalent to two further claims. Every positive integer has a prefix with `3^a(m,t) < 2^t`, and every positive cycle visits 1. Both claims remain open. [Lean proof](Escape.lean)

Garcia and Tal studied the sparsity of divergent orbits. Pulowski spelled out the implication from reciprocal summability to growth of the coefficient. This file proves its own explicit counting estimate in Lean. [Garcia and Tal, Acta Arithmetica 90 (1999)](https://doi.org/10.4064/aa-90-3-245-250) · [Pulowski’s derivation](https://mathoverflow.net/q/513539)

## Reproduce

The package pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From this directory with the pinned Lean toolchain installed, run

```sh
lake exe cache get
lake build
```

The source ends with axiom audits for the main theorems. [Lean source](CollatzWindows.lean)
