# A104722: recurrence for repeated-Catalan self-convolution

This package proves R. J. Mathar's November 9, 2012 recurrence conjecture for the literal definition of [OEIS A104722](https://oeis.org/A104722), with its necessary starting index.

Let `C(r)` be the Catalan numbers and define

\[
b(n)=C\!\left(\left\lfloor n/2\right\rfloor\right),\qquad
a(n)=\sum_{k=0}^{n}b(k)b(n-k).
\]

For every **`n ≥ 4`**,

\[
(n+4)a(n)+(n+1)a(n-1)-4(n+1)a(n-2)+4(2-n)a(n-3)=0.
\]

The source does not print a starting index. At `n = 3` the displayed left side equals **4**, so extending the theorem to that index would be false. The package proves both the full valid range and this exception.

## Proof and attribution

Splitting the literal convolution into even and odd indices proves

\[
a(2r+1)=2C(r+1),\qquad
a(2r+2)=C(r+2)+C(r+1)\qquad(r\ge0).
\]

The recurrence then follows from two explicit linear combinations of the standard identity

\[
(r+2)C(r+1)=2(2r+1)C(r).
\]

Catalan closed forms and the relation to A059348 were already known. The source credits James Sellers's 2008 generating-function argument; Zhao, Li and Sun's 2025 paper also discusses the related Catalan enumeration. These ingredients are credited and are not claimed as new. The result contributed here is an explicit proof and Lean formalization of the recorded recurrence, including its corrected cutoff. The bounded search in `source_checks.md` supports no claim of worldwide priority.

This is **one target family**. The two parity cases, endpoint calculation, and exception are not counted as additional resolutions.

## Formal proof

| Module | Role |
|---|---|
| `Source.lean` | Literal repeated-Catalan convolution, parity identities and Catalan ratio |
| `Proof.lean` | Exact recurrence for every `n ≥ 4` and the `n = 3` exception |

The public results are `A104722.source_recurrence` and `A104722.index_three_exception`.

Lean is pinned to `4.19.0` and mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Both modules are explicit default build roots. From this directory:

```sh
lake exe cache get
lake build
```

The fresh author log `verification.txt` records source/configuration SHA256 hashes, compilation of all roots, and axiom audits. Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` occur. There is no `sorry`, admitted theorem, additional axiom, or `native_decide`.

`verify.py` independently recomputes the literal sequence with exact binomial coefficients, matches all source terms, checks the endpoint and range through `n = 200`, and verifies both symbolic linear-combination certificates. These checks supplement the unbounded Lean proof. The full human proof is in `manuscript-section.tex`. Immutable official source snapshots and their hashes are in `sources/`.
