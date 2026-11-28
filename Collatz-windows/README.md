# Collatz windows and logarithmic stopping time

**Status.** This is a conditional reduction of the Collatz conjecture. Proving that the window hypothesis holds for an absolute constant remains open.

Use the shortcut map `T(n) = n/2` on even inputs and `T(n) = (3n+1)/2` on odd inputs. The hypothesis `WindowBound C` says that, for every starting integer `n ≥ 2` and every offset along its orbit, a window of length `N ≥ max(4, C log₂ n)` has at most `5N/8` odd steps. The logarithm uses the original start at every offset.

The W4 statement and split-map valuation formula come from the supplied research notes. This package gives the formal proofs and an audit of the counting argument.

## What Lean proves

* **W4.** If such a constant exists, every positive integer reaches 1. In fact, one good prefix of length `8k` with at most `5k` odd steps forces a strict descent for any start at least 32. The finite smaller starts are checked by the kernel.
* **Quantitative equivalence.** The window hypothesis holds for some constant exactly when every start reaches 1 in at most a constant times its binary logarithm. The file proves both directions.
* **Counting and exceptional starts.** The displayed count estimate and the assumed mass-decay bound imply an infinitely-often lower bound on survival time. A separate binary residue model satisfies the count estimate while arbitrarily large starts survive forever. Using that estimate to deduce a pointwise upper bound would require additional structure specific to the dynamics.
* **2-adic results.** The distance criterion characterizes survival of the multiplicative coefficient. Transferring its converse to numerical stopping uses the coefficient stopping time conjecture. The file also constructs the 2-adic logarithm that gives the exact valuation formula for the split-map family.

## Reproduce

The package pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From this directory with the pinned Lean toolchain installed, run

```sh
lake exe cache get
lake build
```

The source ends with axiom audits for the main theorems. [Lean source](CollatzWindows.lean)
