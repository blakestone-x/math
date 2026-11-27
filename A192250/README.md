# A192250 and A192251: Mathar's polynomial-reduction recurrences

This package proves the two conjectural recurrences recorded by R. J. Mathar on May 4, 2014, for the constant and linear components of one polynomial-reduction family. The recurrence holds at every source index **n ≥ 4**. Both entries have offset 1, so this is the full range in which all four displayed terms belong to the source sequences.

## Exact source and result

Put `c(k) = binomial(2k,k)` and

\[
P_n(X)=\sum_{k=0}^{n-1}c(k)X^k.
\]

The source reduction repeatedly divides a polynomial by `X²`, writes it as `X² t + r` with `degree r < 2`, and replaces it by `(X+1)t+r`, until its degree is at most one. Write the result of reducing `P_n` as `a(n)+b(n)X`. Then `a` is A192250 and `b` is A192251. The first five pairs are `(1,0), (1,2), (7,8), (27,48), (167,258)`.

For either `y=a` or `y=b`, and every integer `n ≥ 4`, we prove

\[
\begin{aligned}
 &(n-1)(n-2)y(n)-(5n-7)(n-2)y(n-1)\\
 &\qquad-2(2n-3)(3n-8)y(n-2)
 +4(2n-3)(2n-5)y(n-3)=0.
\end{aligned}
\]

The source Mathematica program builds the polynomial list starting with degree 0, then reads its first element as sequence index 1. Consequently `P_n` has **n terms**, with highest input exponent `n-1`. This indexing is preserved in the formal definitions.

## Proof

Let `M=X²-X-1` and `D=4(2n-3)(2n-5)`. The elementary adjacent-binomial identity

\[
(k+1)c(k+1)=2(2k+1)c(k)
\]

gives the exact polynomial certificate

\[
\begin{aligned}
 &(n-1)(n-2)P_n-(5n-7)(n-2)P_{n-1}\\
 &\quad-2(2n-3)(3n-8)P_{n-2}+D P_{n-3}
   =M\,D c(n-3)X^{n-3}.
\end{aligned}
\]

Each source substitution preserves remainder modulo `M`, and the degree decreases at every nonterminal step. The terminal polynomial is therefore exactly the unique remainder modulo the monic polynomial `M`. Reducing the certificate modulo `M` and taking its constant or linear coefficient proves the two recorded assertions together.

The complete human proof is in `manuscript-section.tex`.

## Formalization

| File | Content |
|---|---|
| `Reduction.lean` | Literal prefix polynomial, central-binomial identity, polynomial divisibility certificate, and recurrence for every coefficient of the remainder |
| `SourceReduction.lean` | Actual division-and-substitution algorithm, strict degree decrease, termination, and equivalence with monic remainder |
| `Proof.lean` | Original-index recurrence and the two literal source endpoints, with axiom audits |

Principal declarations:

- `A192250.a192250_conjecture`
- `A192250.a192251_conjecture`
- `A192250.full_resolution`

The endpoint sequences use the terminating source algorithm. They are not defined by the conjectured recurrence. The source-to-remainder bridge is proved in Lean rather than supplied as a hypothesis.

## Reproduce

The package pins Lean **4.19.0** and mathlib commit **c44e0c8ee63ca166450922a373c7409c5d26b00b**. In this directory:

```sh
lake exe cache get
lake build
python verify.py
```

All three local modules are explicit default roots. `verification.txt` records a successful fresh source-only author build: no previously compiled local proof objects were copied, while the pinned external mathlib cache was reused. Every audited declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.

`verify.py` independently implements the source substitution with integer coefficient lists, checks all 23 published values of each component, and checks 100 recurrence instances for each component. Those finite computations are supplementary; the Lean statements quantify over the complete source range.

## Source and prior work

- [A192250](https://oeis.org/A192250), [A192251](https://oeis.org/A192251), and the defining [A192232](https://oeis.org/A192232) are saved at immutable OEIS-data revisions under `sources/`.
- The general equivalence of reduction and monic remainder is standard and is explicitly proved in Lemma 1 of Rafał Wiktorowicz's [2026 note](https://oeis.org/A192232/a192232.pdf). We credit it as supporting prior work. The note's explicit theorem and table concern polynomial input sequences and constant-coefficient recurrences, rather than this central-binomial input and Mathar's polynomial-coefficient recurrence.
- A192251 already records John M. Campbell's Fibonacci-weighted sum formula from February 1, 2016. That known formula is not claimed as a new result and is not needed by our direct certificate.
- Existing LODA and jOEIS generators, and unbounded synthesized-program equivalence problems in the OEIS ATP benchmark, are disclosed in `source_checks.md`. They do not supply the selected source recurrence proof in the inspected files.

The bounded exact and semantic checks used both web search engines, global GitHub search, current ProveIt/trureturing searches, and the existing publication catalogue. The selected exact recurrence proofs were not found in the material inspected. This is not a claim of worldwide priority. The two component assertions are counted as **one mathematical family**.
