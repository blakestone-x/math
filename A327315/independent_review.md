# A327315 independent mathematical and formal review

**Review date:** November 27, 2026  
**Result:** PASS — no mathematical, source-alignment, or build correction required.

The reviewer authored none of the nine local proof modules in this package.
This review read every local Lean module, the README, the source-alignment
report, the preserved OEIS entries, and the conventional proof. It also rebuilt
all nine local modules in a new isolated Lake project.

## Statement and literal-source alignment

The final theorem is the complete equivalence, for every natural number n,

\[
\operatorname{Irreducible}_{\mathbb Q}\left(
\frac1{n!}\operatorname{num}
\left[\left(\frac{X-2}{X^2-X+1}\right)^{(n)}\right]\right)
\quad\Longleftrightarrow\quad
\exists a,b\in\mathbb N,\ n+1=2^a3^b.
\]

Here the numerator is the canonical numerator of a rational function with
monic denominator. The endpoint is
`TwistedDerivative.source_irreducible_iff`; the corresponding unnormalized
numerator endpoint is `source_numerator_irreducible_iff`.

The official A327315 program, offset, displayed coefficient rows, and displayed
polynomials all begin at derivative order zero with X−2. They therefore agree
with the formal degree index N=n+1. The entry's descriptive degree-n phrase
conflicts with its executable definition; the package correctly follows the
latter and explicitly records the discrepancy. A069353 defines precisely
the integers 2^a3^b−1. Its separate prime question is not part of this theorem.

The reviewer independently fetched the current official `oeis/oeisdata`
exports through the GitHub connector and compared the complete bytes against
the preserved sources. Both match. Git-blob SHA1 and content SHA256 were
recomputed, not merely copied from the package:

| File | Bytes | Git blob SHA1 | SHA256 |
| --- | ---: | --- | --- |
| A327315.seq | 1753 | `47efe5bcf666241a43536ea4f106e7342c741f96` | `4cf24334a3be2295bb091e05b507ac500c163688bfacb3bfd8372103fc79c463` |
| A069353.seq | 1770 | `aeb2a0ed4dcbaff009e9044abd2c52659409c9bf` | `6926741f40247aef89e3d5f02ba30681f28738dcc0555ba516e418a167f105ef` |

The machine-readable comparison is in
[independent_source_comparison.json](independent_source_comparison.json).
Direct OEIS-page requests were blocked by HTTP 403 during this independent
check; the complete official GitHub exports were obtained successfully.

## Mathematical review

**Recurrence and degree.** `TwistedDerivative.lean` defines S₀=−1, S₁=X−2
and S_(N+2)=(1−2X)S_(N+1)−(1−X+X²)S_N. Its derivative identities and top
coefficient induction establish the exact degree N, rather than only an
upper bound. Mapping coefficients to the quadratic field preserves the
same recurrence.

**The derivative and cancellation bridge.** `RationalDerivative.lean`
defines the ordinary quotient-rule derivative on rational functions and
proves the formula for any fraction with nonzero denominator. Consequently
the iteration used in the endpoint is independent of a chosen fraction.
`SourceBridge.lean` proves the derivative formula
n!S_(n+1)/D^(n+1), where D=1−X+X². The explicit Bezout identities
4D−(1−2X)²=3 and D−(X+1)(X−2)=3 establish the initial coprimality.
Recurrence reduction modulo D propagates it to every S_N. The factorial is
a rational unit and D is monic, so the canonical numerator is exactly
n!S_(n+1). No unproved reduction, cancellation, or scalar-normalization
assumption remains.

**Allowed degrees.** `SixthField.lean` constructs a genuine quadratic
field from the irreducible sixth cyclotomic polynomial, with u+v=uv=1
and u⁶=v⁶=1. `CyclotomicSmooth.lean` proves
Y^(2N)−Y^N+1=Φ_(6N) when N=2^a3^b. For an irreducible factor q of
Y^N−v over this field, its root is a root of that rational cyclotomic
polynomial. The tower-degree comparison 2N≤2 deg(q), together with
deg(q)≤N, forces full degree. The proof does not assume the desired
binomial irreducibility.

**Fractional-linear step.** The generic helper proves that the transformation
of Y^N−c to (X−a)^N−c(X−b)^N preserves irreducibility under a≠b and c≠1.
It checks the pole exclusion and uses the root-field degree argument.
`ClosedForm.lean` proves the exact identity

\[
S_N=(-1)^{N+1}v\big((X-u)^N-v(X-v)^N\big),
\]

with a nonzero scalar. All required hypotheses are established in
`SixthField.lean`. Irreducibility over that field then descends to ℚ.

**Excluded degrees.** Every positive N outside 2^a3^b has a prime divisor
p other than 2 and 3. The proof treats both residues modulo 6. For N=pm,
p≡1 gives S_m as a divisor; p≡5 gives the reflected divisor S_m(1−X).
The reflection identity, sixth-root phase, and difference-of-powers
divisibility have the correct signs. Divisibility is descended from the
quadratic coefficient field to ℚ, and both proposed factors have exact
degree m with 0<m<N. Thus neither branch relies on a constant or
full-degree factor. `Classification.lean` combines these results into
the all-positive-degree equivalence, and `Proof.lean` transfers it to
every derivative order, including n=0.

## Prior-literature and scope check

The reviewer independently inspected the defining family and irreducibility
subsection of [Remete's primary paper](https://arxiv.org/pdf/2111.08341).
The package's specialization
S_N(X)=(-1)^(N+1)f₁^(N)(X−1) follows from the six-periodic coefficients.
Corollary 10 requires a prime p≠3 dividing m²+m+1 to valuation one.
At m=1 the expression is 3, so that sufficient criterion is inapplicable.
The inspected subsection does not supply the complete degree criterion
at this parameter. The package correctly credits the existing family and
methods, and qualifies its prior-publication screen.

This review confirms that attribution comparison; it does not certify
historical priority or independently repeat every recorded search.
The classification is one source assertion. Its field-strengthening,
degree correction, exact source bridge, and two factor branches are
components of that assertion, not extra resolution counts.

## Independent isolated build

The independent build used Lean 4.19.0 and the exact pinned mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

A new project was created at:

`research/batch11/sequences/A327315_independent_tff8jbl8`.

Only the nine Lean sources, Lake configuration, toolchain file, and dependency
manifest were copied. No local proof objects were copied. Only the pinned
external mathlib and dependency caches were reused. The default target
explicitly contains all nine local modules.

**Fresh Lake build: exit 0.** All nine local modules were rebuilt. The log
reports successful completion and only the standard theorem axioms
`propext`, `Classical.choice`, and `Quot.sound`.
A token search found no `sorry`, `admit`, custom `axiom`, `unsafe`,
or `native_decide` declaration in the local Lean sources.

The complete log and all twelve source/configuration SHA256 values are in
[independent_build.log](independent_build.log). Each digest was also compared
with the author build, the current frozen package, and the copied isolated
source. All match. In particular:

- `Proof.lean`: `b095327806306b64c9daf39a8042690481c85e528503328e6a430aa15b2703a3`
- `SourceBridge.lean`: `a8cbd56e27157c51f8c6288c80685c65518981739c7f7b941652ae6ea0a548a3`
- `Classification.lean`: `1a89ad057e4d0dbeec44f62d30b31fdcabc5d212df2f8332780f0a02c7b2face`

No proof source or configuration was changed during this review.
