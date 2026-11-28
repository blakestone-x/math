# A045994: the Motzkin-convolution recurrence

This package proves R. J. Mathar's September 27, 2013 recurrence conjecture for the literal recursive definition of [OEIS A045994](https://oeis.org/A045994), for every `n ≥ 5`.

Let `M(n)` be the Motzkin numbers, with `M(0) = M(1) = 1` and

\[
M(n+2)=M(n+1)+\sum_{k=0}^{n}M(k)M(n-k).
\]

Define `a(0) = 1` and, for `n ≥ 1`,

\[
a(n)=M(n)+\sum_{k=1}^{n-1}M(k)a(n-k-1).
\]

Then

\[
\begin{aligned}
0={}&(n+1)a(n)+2(-2n-1)a(n-1)+2(-n+3)a(n-2)\\
&+(11n-19)a(n-3)+(11n-27)a(n-4)+3(n-3)a(n-5).
\end{aligned}
\]

The proof starts from the source convolution, derives its algebraic generating-function equation, and proves an explicit differential identity whose coefficients are the conjectured recurrence. It covers all indices in the stated range.

## Source correction and scope

The same OEIS snapshot prints a different generating function, `1/(1-x(1+x)M(x))`. That expression has coefficient `8` at `x³`, whereas the defining recurrence gives `a(3) = 7`. We formally prove this disagreement and use the defining recurrence throughout. Its correct transform is

\[
A(x)=\frac{M(x)}{1+x-xM(x)}.
\]

The recurrence proof and this correction belong to **one target family**. No claim is made here about the separate grand-Motzkin-path interpretation in the source comments. Classical Motzkin identities and algebraic-to-differential methods are background, not new discoveries. The bounded prior-work search is documented in `source_checks.md`; it does not establish worldwide priority.

## Formal proof

| Module | Role |
|---|---|
| `Source.lean` | Literal natural-number definitions and both generating-function identities |
| `Algebra.lean` | Quadratic elimination and exact differential certificate |
| `Proof.lean` | The recurrence for every `n ≥ 5` and the printed-transform counterexample |

The public theorem is `A045994.source_recurrence`. The correction is `A045994.printed_generating_function_false`.

The package pins Lean `4.19.0` and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All three modules are explicit default build roots. From this directory, use:

```sh
lake exe cache get
lake build
```

`verification.txt` records a fresh author build from copied source and pinned configuration, including SHA256 inputs and axiom audits. The permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, admitted theorem, additional axiom, or `native_decide` is used.

`verify.py` provides independent exact-integer and symbolic checks; run it with Python and SymPy installed. Those finite checks are supplementary to the universal Lean proof. `manuscript-section.tex` contains the full human proof, and immutable source snapshots and their hashes are under `sources/`.
