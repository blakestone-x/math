# Independent audit: A326925 odd-degree irreducibility

**Result: PASS.** The frozen package proves the odd-degree irreducibility clause recorded in OEIS A326925, with a complete bridge from the original rational function to its canonical reduced derivative numerators. The proof, source interpretation, package README, and stated scope agree.

Reviewed independently on November 27, 2026 by the sequence-audit agent, which did not author these five proof modules. No proof source was changed during the audit.

## What was checked

The audit covered every declaration in `GoldenUnit.lean`, `MobiusIrreducibility.lean`, `RationalDerivative.lean`, `DerivativePolynomials.lean`, and `Proof.lean`; the exact preserved OEIS records; the complete README; and the source and prior-publication notes. The helper modules had already been independently read and compiled under their development names. Their final packaged versions were checked to be identical after the documented import and namespace renaming. The final instantiation was then read separately, and all five exact packaged modules were compiled together in a new isolated Lake project.

The result concerns one recorded clause: every odd-degree polynomial in this family is irreducible. It also proves irreducibility over the larger quadratic field, the exact degree, and the correspondence with reduced derivative numerators. These stronger statements and supporting lemmas are consequences and proof components, not additional conjecture resolutions. The even-degree factorization clause and A327315 are explicitly outside the claimed result.

## Source interpretation and indexing

The official A326925 export is revision 13, October 31, 2019, Git blob `e8036d79dbacfa38c832486936d3d80b5472cde1`. Its displayed polynomial list and Mathematica program begin with derivative order zero and polynomial degree one. Thus the source title's derivative index is shifted by one relative to the polynomial degree. The package correctly records

$$
f(x)=\frac{1-x}{1-x-x^2},\qquad
f^{(n)}(x)=\frac{n!P_{n+1}(x)}{(1-x-x^2)^{n+1}}.
$$

Odd polynomial degree therefore corresponds to even derivative order. The program's scalar and sign normalization has no effect on irreducibility over the rationals. The package does not count this indexing discrepancy as another resolution.

The related A328610 and A328611 exports describe the separate even-degree factors, while A327315 uses a different rational function. None is silently substituted for the family proved here. The four preserved source files were checked against their recorded Git blob hashes.

## Mathematical audit

### Quadratic-field obstruction

`GoldenUnit.lean` constructs the golden-ratio field as a subfield of the reals and establishes its degree two, the minimal polynomial of the golden ratio, and its norm $-1$. It derives the required norm and trace coefficient identities for irrational elements of this field and proves that the trace of an algebraic integer in the field is an integer.

For an odd prime $p$, a putative equation $b^p=\phi^4$ makes $b$ an algebraic integer with norm one. The real embedding gives $1<b<2$, since $p\geq3$ and $\phi^4=3\phi+2<8$. Irrationality is proved from the same equation. The quadratic relation then implies that the integral trace lies strictly between two and three, a contradiction. No classification of the field's units or unproved algebraic-number claim is assumed.

The existing mathlib odd-binomial irreducibility theorem is applied with the required nonpower obstruction for every prime divisor of the odd exponent. Its use is appropriately credited as classical mathematics in the README. The additional nonpower and nonsquare lemmas in this module are not needed to claim an even-degree result, and the README does not make that claim.

### Linear-fractional change of variable

`MobiusIrreducibility.lean` proves the needed transformation theorem rather than assuming it. For

$$
Q(X)=(X-a)^N-c(X-b)^N,
$$

it checks the hypotheses $a\ne b$ and $c\ne1$, establishes degree $N$, and takes a root of an irreducible factor. The exceptional value $x=b$ is excluded before forming $(x-a)/(x-b)$. The latter is a root of the irreducible binomial, so its degree gives a lower bound $N$ for the factor's root field. This forces the chosen factor to have the full degree and to be associated with $Q$. The zero, constant, and nonunit conditions used in this argument are supplied in the formal proof.

### Derivative and polynomial bridges

`RationalDerivative.lean` defines differentiation using the canonical numerator and denominator of a rational function. Its quotient rule for an arbitrary nonzero-denominator representation is derived by differentiating the cross-multiplied canonical identity. It therefore justifies the use of successive unreduced quotient representations rather than making the desired derivative formula true by definition.

`DerivativePolynomials.lean` proves the recurrence and the differential identity for the family beginning $P_0=-1$, $P_1=1-X$. It proves the closed form over a field with $u+v=1$, $uv=-1$, as well as its compatibility with coefficient maps and its exact degree. The formal iterated derivative theorem includes the factorial factor and the denominator exponent. The final package specializes these results to $u=\phi$, $v=1-\phi$, proves irreducibility in the quadratic field, and descends it to $\mathbb Q$.

### Canonical numerator and cancellation

The final assertion is not restricted to an unreduced expression. `Proof.lean` proves that an odd-indexed $P_N$ cannot divide $D=1-X-X^2$. Degree handles all odd $N\geq3$; the remaining case $N=1$ is checked at $X=1$, where $P_1(1)=0$ and $D(1)=-1$. Irreducibility then excludes cancellation with every power of $D$. The nonzero rational factorial is a unit, so the actual canonical numerator of each even-order derivative is irreducible. This establishes the literal function and intended degree clause in the source.

## Independent kernel verification

The final check used Lean 4.19.0 and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`, as pinned by the package. A new temporary Lake project received copies of the five source modules and the package configuration. Existing mathlib dependency objects were reused, but no compiled object for any of the five package modules was copied. A full `lake build` returned exit code zero. The detailed output is in [audit-verification.txt](audit-verification.txt).

All printed main theorem dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`. A source scan found no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide` declaration or use. The exact audited proof-source hashes are:

| File | SHA-256 |
|---|---|
| `GoldenUnit.lean` | `e362553050405c282b468c631ea3d080025389fda12901165a2bfa2bf2fddeff` |
| `MobiusIrreducibility.lean` | `f39a3dac59fa2b21614dd3e22286e0f79a97de40425c172cb209fccb1c92b3a8` |
| `RationalDerivative.lean` | `54913422f586a5d2dacd6ab40d1f79faa1f2aeecddbe14a08811f1453c1ce5c2` |
| `DerivativePolynomials.lean` | `dfd9673f3f8d2be0514d8a75b55896dbf392eb661045fc768a3b276d68c8556a` |
| `Proof.lean` | `1c4b98449d5c9e04a8b3e2d8e2ff1132a5b6195b26828c10156c42782b097659` |

## Historical and prose review

The README faithfully explains the proof, its assumptions, the exact source indexing, the canonical-numerator conclusion, and the one-clause scope. Its claimed degree and stronger quadratic-field irreducibility agree with the formal theorems.

The independently performed source check used both available search engines, the live trureturing index, the related complete OEIS entries, and nearby primary Fibonacci-polynomial literature. No earlier proof of this exact odd-degree assertion was located. The package correctly states this as a bounded search rather than a guarantee of historical priority. Classical binomial irreducibility and related older polynomial results are distinguished from the exact source assertion.

No mathematical, formalization, source-bridge, or scope issue remains from this audit.
