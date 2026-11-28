# Independent agent audit

**Result: PASS for the mathematical proof, original-source correspondence, documentation, and fresh formal compilation.**

Reviewed November 27, 2026 by a separate assistant agent from the proof's author. This is an independent agent review within the same work session, not external peer review or a certification of historical priority.

## Frozen proof and reproducibility

The audited first-party source is `Proof.lean`, 276 lines, SHA-256:

```text
ca0cf4a84c6d34e10670d6fe7349590e7c77eb519bea1f7a80e14a996e2ebdb1
```

The source and its pinned Lake configuration were copied to a fresh isolated directory. Only stock dependency caches were reused. `lake build` freshly compiled the first-party proof and succeeded under Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The frozen source hash was checked again after the build.

The source-definition equality, full polynomial congruence, and all three source endpoints report exactly these standard axioms:

```text
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, custom axiom declaration, `unsafe` declaration, or `native_decide` occurs in the proof. The complete independent build log is `audit-verification.txt`.

## Exact source correspondence

All four official `oeis/oeisdata` files were retrieved again during the audit. The saved bytes were checked independently against the current connector-reported Git blob hashes:

| Entry | Verified Git blob SHA-1 |
|---|---|
| A000033 | `dd7b47b9c48399a10e808ebacc9cdeb9dcbcbfc1` |
| A000159 | `08dab7ac2feb8f60467e08c74fcdc11e4b83d3e1` |
| A000181 | `9059953cca1624299eb341610a259cf019d8e3da` |
| A058087 | `394c485c5f0669e021381ef00569986efae90a90` |

The following details were checked directly against those sources:

- `sourceMenage` is the literal rational rook sum, with the same range, factorial, binomial coefficient, denominator, and power of `X - 1`. Its special zero row agrees with the source's Maple definition.
- `menage_eq_sourceMenage` proves the integral rewriting, including the reindexing and nonzero-denominator argument. This connection is a theorem, not a hypothesis.
- `hit_eq_sourceMenage` proves the coefficient connection. The source's descending-degree convention means that A058087(n,n-d) is the coefficient of degree d.
- The A000033 endpoint covers every n ≥ 1 and every prime. Its n = 1 term is correctly obtained from the explicit degree-two coefficient formula and equals zero.
- The A000159 endpoint covers every n ≥ 3 and every prime except 3.
- The A000181 endpoint covers every n ≥ 4 and every prime greater than 3.
- The combination is exactly a(n) + 2a(n+p) + a(n+2p), with positive middle coefficient and the original shifts.

An independent exact-rational calculation from the original coefficient formula matched every displayed source term: 22 terms of A000033, 21 of A000159, 20 of A000181, and all 55 listed triangular entries of A058087. This is an indexing and definition sanity check; the universal proof is the Lean development.

## Mathematical review

The proof is valid by an elementary polynomial argument. The coefficient identity for the second difference of `(1+X)^a` follows from Frobenius and is applied only below degree 2p. It yields the required second difference of the integral rook coefficient for j < p. Summands with j ≥ p vanish because p divides j!, and terms with j > n vanish because the rook coefficient is zero.

The common finite summation range therefore remains correct when n < p. The proofs of truncation and scaled sums explicitly handle this boundary. The full polynomial congruence assumes n > 0, as required to control the shifted upper binomial argument; it is not incorrectly extended to the exceptional zero row.

For degrees d < p, extracting coefficients gives the desired positive-coefficient relation. The characteristic-two argument separately proves the additional range d < 4, which is necessary to include p = 2 for both A000033 and A000159. The final prime case splits cover precisely the source domains.

No recurrence conjecture, finite numerical cutoff, seating-arrangement counting theorem, or unproved integrality assertion is used as an assumption. The formal target is the source-defined coefficient sequence, and its bridge is complete.

## Scope and attribution

The README and source review distinguish the three recorded source assertions from the one shared polynomial theorem and one proof module. They credit Mark van Hoeij's 2019 conjectures and the classical defining formula. They also identify the separate earlier A000159 recurrence resolution, which this package does not claim.

The literature review explicitly discloses that the mathematical contents of the relevant Carlitz and Stevens papers were unavailable. The package therefore makes no claim that the congruence is historically new or that these consequences were absent from older literature. The formal proof and source correspondence pass this audit; historical priority remains outside its certified scope.

No mathematical or formal-source change was required by this audit. A presentation-only correction to mathematical delimiters was requested during prose review; the corrected README and source review were then reread and passed. The proof remained byte-identical throughout.
