# A327315 contributor cross-review

Reviewed November 27, 2026. **The mathematical and literal-source checks below passed.** This report is a contributor cross-review, not a claim that every local module was independently reviewed by a nonauthor: this reviewer authored `CyclotomicSmooth.lean`, `SixthField.lean`, and `SourceBridge.lean`. The parent author separately checked the first two modules and is reviewing the source bridge. A separate whole-package independent review is planned. No source was modified during this review.

## Parent-authored modules reviewed

The complete current `TwistedDerivative.lean`, `ClosedForm.lean`, `Classification.lean`, and `Proof.lean` were read. The recorded direct compilation transcripts for their public endpoints report successful completion and only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. This report does not substitute those transcripts for a fresh isolated package build.

1. **Recurrence and degree.** The recurrence starts at S₀=−1 and S₁=X−2. Its top coefficient is (−1)^(N+1), which is nonzero over ℚ, so every degree statement has the required noncancellation argument. The differential identities use degree index N, not derivative index n.
2. **Exact phase and scalar.** The closed form is S_N=−v(u−X)^N−u(v−X)^N. Its transformed form has the scalar (−1)^(N+1)v multiplying (X−u)^N−v(X−v)^N. The scalar is proved nonzero. The identities u+v=uv=1 and v²=−u fix the sixth-root phase correctly.
3. **Allowed degrees.** Irreducibility of Y^N−v over the quadratic field is transferred through an invertible fractional-linear change with u≠v and v≠1. Descent to ℚ uses an injective coefficient map and a primitive nonzero polynomial. No unjustified claim that arbitrary scalar extension preserves irreducibility is made.
4. **Excluded degrees.** For N=pm with a prime p outside {2,3}, m is strictly positive and strictly below N. The proof covers both possible residues modulo 6. If p≡1, v^p=v and S_m divides S_N. If p≡5, u^p=v and the correct factor is S_m(1−X)=−u((X−u)^m−u(X−v)^m). Both candidate factors belong to ℚ[X]; divisibility descends using the coefficient embedding, and their degree m proves that they are proper nonunit factors.
5. **Arithmetic completeness.** Prime-factor induction proves that a positive integer with no prime factor outside {2,3} is 2^a3^b. The classification therefore has no uncovered composite or boundary case.
6. **Final endpoints.** `source_numerator_irreducible_iff` and `source_irreducible_iff` quantify over every natural n. They substitute degree N=n+1, which is automatically positive, and handle the n=0 linear row. The nonzero factorial is a polynomial unit over ℚ, so the raw and factorial-normalized numerators have the same criterion.

## Contributor-authored modules checked for consistency

The generic cyclotomic argument chooses an irreducible factor q of degree d over K and its adjoint-root field E. Its root y satisfies the irreducible degree-2N rational polynomial Φ_(6N). Thus 2N≤[E:ℚ]=2d, and the degree bound d≤N forces full degree. The two facts used here—finite-dimensionality and the tower degree—are established in Lean, not supplied as unproved annotations. The Φ_(6N) identity is derived from the prime expansion formula at 2 and 3.

The concrete sixth-root field is the quotient by the irreducible polynomial Φ₆, with finrank exactly two. Its root identities, distinctness, and nonzero conditions are explicit lemmas.

The source bridge proves that every S_N is coprime to D using rational Bezout certificates for A,D and X−2,D and the recurrence. The quotient-rule numerator is exactly n!S_(n+1); D is monic, so the canonical numerator has that exact scalar. The final normalization multiplies by the inverse factorial, whose nonzeroness includes n=0.

## Literal source and prior-art scope

The saved A327315 program, displayed rows and zero-based offset agree with the degree shift N=n+1. Its title's degree-n wording does not. The conjectured index set is the membership set defined by A069353; A069353's array enumeration offset and separate question about primes are irrelevant to this classification.

The README and manuscript credit the exact Remete polynomial-family connection and the earlier cyclotomic/fractional-linear literature. The bounded prior-proof report does not claim an exhaustive novelty search. The supporting field lemmas, the stronger extension-field irreducibility, the source-title correction, and neighboring observations are not counted as separate conjectures.
