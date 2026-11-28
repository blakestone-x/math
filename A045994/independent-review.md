# Independent review: A045994

Review date: **2026-11-28**. Reviewer: a separate proof-review agent that did not author or restore this package's Lean development. Outcome: **PASS for the stated recurrence and generating-function discrepancy**.

This is a source and mathematical review plus a separate clean compilation. It is not an external peer review or a claim of worldwide priority. The author and reviewer builds use the same pinned compiler and external libraries, with separate local build directories and objects.

## Source binding and scope

I compared the three Lean modules with the frozen A045994 definition and the standard Motzkin recurrence in the supporting A001006 snapshot. `A045994.source` starts with `a(0)=1`; its successor clause has precisely `M(n+1) + sum_{k=1}^n M(k)a(n-k)`. Replacing `n+1` by the source index gives the literal defining convolution. In particular the `M(0)` term is excluded, as required by the source.

The Motzkin sequence uses the standard first-return recurrence with `M(0)=M(1)=1`; the package does not claim a new proof of the classical Motzkin identities or a formal path bijection. The separate grand-Motzkin-path interpretation appearing in source comments is explicitly outside its theorem scope.

## Mathematical review

1. **Power-series translation.** `motzkin_equation` proves `M=1+xM+x²M²`, and `source_equation` proves `A=M+x(M−1)A` directly by coefficient extraction. The second identity has the correct shift and removes the constant term of `M`. It gives the valid transform `A=M/(1+x−xM)`, with denominator constant coefficient one.
2. **Elimination certificate.** The displayed polynomial certificate eliminates `M` to obtain `pA²+qA+1=0`, where `p=x⁴+3x³+2x²−x` and `q=x²+2x−1`. It is checked by Lean's algebra tactics and by the exact symbolic replay. The proof does not assume the source's inconsistent printed transform.
3. **Differentiation and cancellation.** Differentiating the quadratic and taking the stated polynomial combination yields `(2pA+q)(uA′+vA−w)=0`. The factor `2pA+q` has constant coefficient `−1`, so its cancellation is valid. The Lean proof establishes nonzeroness and uses the integral-domain property of rational formal power series; the manuscript's unit argument is also valid.
4. **Coefficient extraction and endpoint.** The coefficient of degree `n` in `uA′+vA` is the exact six-term expression in Mathar's conjecture. The proof covers `n≥6` by coefficient extraction and verifies the remaining endpoint `n=5` from the literal definitions. The final public theorem assumes `5≤n`, so truncated natural subtraction does not change any source index.
5. **Source discrepancy.** The printed reciprocal `1/(1−x(1+x)M)` has degree-three coefficient `8`, while the literal source gives `a(3)=7`. The formal counterexample proves that multiplication by its proposed denominator cannot yield one. The manuscript correctly states the discrepancy as a correction within this target family.

I also checked that the manuscript's initial values, both polynomial certificates, the differential identity, the coefficient formula and the explicit `n=5` arithmetic agree with the formal proof. No blocking mathematical or statement mismatch was found.

## Fresh compilation and audit

The independent build started from copied Lean sources and pinned package configuration in a new directory. It copied no local `.olean` files from the source or author build. All three modules (`Source`, `Algebra`, `Proof`) were explicit roots and compiled successfully with Lean **4.19.0** and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The helper checked every local Lean source for `sorry`, `admit`, custom `axiom` declarations and `native_decide`. The printed principal theorem audits use only `propext`, `Classical.choice` and `Quot.sound`. The full real compiler output and SHA256 inputs are in [independent_build.log](independent_build.log).

Reviewed Lean SHA256 values:

| File | SHA256 |
|---|---|
| `Source.lean` | `132eee8e5a1f2baf4acdf94c0207c09c047ff09cb78c1e656ec0f97e74d91e6d` |
| `Algebra.lean` | `f6762f164aa69b17ac3c31f198d7717f4225d1651160113aa2489c781a2d6b54` |
| `Proof.lean` | `b6d2fedffbdb6f96e809e99bd6e580c10a155833b7c38f6635165dac0c075ba0` |

## Supplementary replay

I reran the supplied exact Python/SymPy checker after the independent compilation. It verified source byte counts and hashes, all **28** frozen terms, the recurrence for every `5≤n≤200`, both polynomial certificates, and the degree-three discrepancy. The real output is appended to [independent-verification.txt](independent-verification.txt). This is a separate execution of the supplied checker, not a separately authored verification algorithm; the unbounded result rests on the Lean proof.

The review does not establish novelty of the algebraic method or worldwide priority of the particular recurrence. Those are distinct from correctness and source fidelity and remain subject to the bounded checks and qualifications in `source_checks.md`.
