# Independent review: A326926 irreducibility classification

**Result: PASS.** Reviewed November 27, 2026 by a separate agent from the package author and the source-bridge author. No mathematical or source-alignment correction was required. The frozen Lean sources were not edited during this review.

## Reviewed claim

The exact claim is the shared nonconstant-row assertion in A326926 and A326933:

\[
P_n\text{ is irreducible in }\mathbb Q[X]
\quad\Longleftrightarrow\quad
n+1\text{ is prime and }n+1\ne3,
\qquad n>0,
\]

where $P_n$ is the factorial-normalized reduced numerator of the $n$-th derivative of $1/(1-X+X^2)$. This is one classification repeated in two entries. The package does not claim a formula for the number of irreducible factors in every reducible row.

I read all eight local proof modules in full, the complete README, the source-review report, both preserved OEIS exports, and the Lake configuration. I also independently retrieved the current official exports and rebuilt the complete frozen package in a fresh isolated project.

## Independent source verification

The current official exports were fetched independently from `oeis/oeisdata` and byte-compared with `sources/A326926.seq` and `sources/A326933.seq`. Both comparisons passed. The official blob hashes and saved-file SHA-256 hashes are:

| Entry | Official Git blob SHA-1 | Saved SHA-256 |
| --- | --- | --- |
| A326926 | `173825bb478501279712e959dc33951402a5ccd2` | `4336b193f72c83da94dea67f1ab47902593bdd875499508f6ac871bda534aa3a` |
| A326933 | `44e3707566d6c02df0b4f9dfef3b21325cf98030` | `4a22e57a1a89fceb807ecd8e5b3de97dc5b9ced9add64f4aac6e8961f4645b12` |

A326926 revision 29 retains the tentative irreducibility comment. Its title and Mathematica program define the degree-indexed row by `Numerator[Factor[D[1/(X^2-X+1),{X,n}]]]/n!`, starting at $n=0$. The first rows are $1$, $1-2X$, and $3X(X-1)$. The formal source function, derivative order, factorial normalization, and exceptional prime therefore agree with both the literal program and the worked polynomials.

Peter Bala's November 2026 addendum explicitly shifts to one-based row indexing. Its $R(N,X)$ is the package's $P_{N-1}(X)$. The package reconciles this shift correctly. A326933's current offset is zero and its program uses the same numerator. The classification is restricted to $n>0$, exactly as required by the source's word “nonconstant”; the degree-zero polynomial $1$ is a unit.

## Mathematical chain

### Polynomial identities and exact degree

`SixthDerivative.lean` defines $A=1-2X$, $D=1-X+X^2$, and $P_0=1$, $P_1=A$, $P_{n+2}=AP_{n+1}-DP_n$. It proves the polynomial derivative identities for the actual recurrence, not a separate assumed family:

\[
P_{n+1}'=-(n+2)P_n,
\qquad DP_n'+(n+1)AP_n=(n+1)P_{n+1}.
\]

The degree upper bound and the nonzero top coefficient $(-1)^n(n+1)$ establish exact degree $n$ over any characteristic-zero integral domain. The constant-coefficient sequence is proved six-periodic. For prime $p\ne3$, the residue argument includes $p=2$ and shows $P_{p-1}(0)=\pm1$.

### Prime indices and reversal

Comparing coefficients of $P_{p-1}'=-pP_{p-2}$ proves that $p$ divides every positive-degree coefficient of $P_{p-1}$; the proof cancels an integer index $j$ only after showing $0<j<p$ and $p\nmid j$. The top coefficient is $(-1)^{p-1}p$, so it is not divisible by $p^2$. The constant coefficient is a unit.

`ReverseEisenstein.lean` correctly converts these conditions into Eisenstein hypotheses for the reciprocal polynomial over the integers. Its leading coefficient is the original unit constant, and its constant coefficient is the original leading coefficient. Primitivity is proved from a unit coefficient, and the standard Gauss lemma transports integer irreducibility to rational irreducibility.

`ReverseTransfer.lean` explicitly requires the original constant coefficient to be nonzero, so reversal cannot silently discard a factor of $X$. Its factorization argument checks the corresponding nonzero constants of both factors and transfers unit status back from their reversals. This addresses the main reversal boundary condition.

### Composite indices and the exceptional prime

`LucasDivisibility.lean` proves the classical addition formula and index-divisibility property over a commutative ring, with the initial sequence $U_0=0$, $U_1=1$. The shifted bridge proves $P_{d-1}\mid P_{N-1}$ when positive $d\mid N$. The positive-index hypotheses justify the natural-number subtractions.

For composite $N=n+1$, `prime_of_irreducible` takes a proper prime divisor $d$ and obtains a divisor of degree $d-1$ strictly between zero and $n$. The proof excludes both possible unit factors using exact degree and nonzeroness. The remaining exceptional prime is handled by the exact factorization $P_2=X\,3(X-1)$, with both factors proved nonunits. The endpoint `irreducible_iff` contains both implications for every $n>0$.

### Literal derivatives, cancellation, and normalization

`RationalDerivative.lean` defines the ordinary quotient-rule derivative from a rational function's canonical numerator and denominator. It proves that the quotient rule is independent of the representing fraction and derives the iterated numerator recurrence. I reviewed this reused module as part of the complete chain.

`SourceBridge.lean` uses the actual rational function $1/D$ and proves

\[
\left(\frac1D\right)^{(n)}=\frac{n!P_n}{D^{n+1}}.
\]

It then proves coprimality, rather than assuming that this displayed numerator is reduced. The explicit rational Bezout identity $-A^2/3+4D/3=1$ gives $\gcd(A,D)=1$. Induction in the recurrence gives $\gcd(P_n,D)=1$, and multiplication by the nonzero rational factorial preserves coprimality with $D^{n+1}$.

The denominator $D$ is proved monic. The general canonical-numerator lemma includes the inverse leading-coefficient normalization; monicity makes that factor exactly one. Thus `derivative_numerator` proves exact equality of the canonical reduced numerator with $C(n!)P_n$, and `normalized_source_numerator` proves that multiplication by $C((n!)^{-1})$ yields precisely $P_n$.

The public endpoints `source_numerator_irreducible_iff` and `source_irreducible_iff` apply the classification respectively to the actual reduced numerator and to the exact factorial-normalized source row. Their only extra parameter assumption is the source condition $n>0$.

## Documentation, attribution, and scope

The README's proof, explicit sample polynomials, prime exception, degree statement, and normalization explanation agree with the Lean results and the preserved source. It credits the recurrence, closed form, roots, and strong divisibility observations to Peter Bala's source addendum and credits the classical addition/divisibility ingredient to Norfleet; no new general Eisenstein criterion is claimed.

I independently opened and read all four pages of Mark Norfleet's [2005 primary paper](https://www.fq.math.ca/Papers1/43-2/paper43-2-12.pdf). Theorem 1 and Corollary 1 are the addition and divisibility facts used here. That paper's stated results do not supply this source's prime-index irreducibility classification. The package's source report separately documents its wider, bounded prior-literature search. This review does not certify exhaustive historical priority or OEIS editorial acceptance.

## Fresh independent build and trust boundary

The complete project was copied into a new isolated directory with no local `.olean`, `.ilean`, C, or previous build objects. Only the pinned external mathlib/dependency cache was reused. The independent `lake build` compiled all eight local modules and completed with exit code 0. The complete transcript is [independent_build.log](independent_build.log).

Environment: Lean 4.19.0; mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The Lake target explicitly includes all eight local modules. The only informational tactic suggestion was `Try this: ring_nf`; it was not a warning or an error. No source edit was needed.

The source scan found no `sorry`, `admit`, added `axiom`, `unsafe`, or `native_decide` declaration. All reported endpoint dependencies are among the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. This review relies on Lean's kernel and the pinned trusted dependencies; the fresh build checks the exact supplied source modules under that standard trust boundary.

## Frozen source hashes

| File | SHA-256 |
| --- | --- |
| `SixthDerivative.lean` | `cc4a5b934c95bbdef350b6dfc76509fcbeed96c4132465e9d4218ee2c36d56ef` |
| `LucasDivisibility.lean` | `09e0e9583ce9ec67991f37908dbeb8862b7c2f5fa474a98f13faf69b0060bfca` |
| `ReverseTransfer.lean` | `69b80f8bfa5733d8a9bd01efc8a526b31ac9126587506d6af42f4fcf24d55d50` |
| `ReverseEisenstein.lean` | `768959523a44713ccbf8016cb6071d103fa54453c5cf9c0036254e05c8908bf9` |
| `Irreducibility.lean` | `82914cc4b12ab911319dd102cc273fef280036997b3c9539322ce27a0111f978` |
| `RationalDerivative.lean` | `54913422f586a5d2dacd6ab40d1f79faa1f2aeecddbe14a08811f1453c1ce5c2` |
| `SourceBridge.lean` | `28a5587cb931670825eacb75ec8e124d4f0b65028231f7030b0d2c9e52b78640` |
| `Proof.lean` | `34c19a3bf191757b932ff2b8111cffd2fd79e268f3cddfe39786fa294054decb` |

No unresolved mathematical, indexing, source-normalization, or build issue was found.
