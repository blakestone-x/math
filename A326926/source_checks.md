# A326926: source alignment and bounded prior-proof review

Checked on 27 November 2026. This report concerns one shared irreducibility
claim appearing in A326926 and A326933. It does not count these two entries as
two distinct conjectures, or claim an exhaustive historical novelty search.

## Exact primary sources and indexing

The [official A326926 entry](https://oeis.org/A326926) defines a row using the
numerator of the derivative of order `n` of `1/(1-x+x^2)`, divided by `n!`.
The source program starts at `n=0`; the first row is the constant polynomial
one. Its irreducibility comment concerns nonconstant rows. The conjectured
criterion is `n+1` prime and unequal to three. The
[A326933 entry](https://oeis.org/A326933) repeats that same criterion while
tabulating numbers of nonconstant irreducible factors. Its offset is zero,
with a recorded correction from one in March 2023.

The following immutable official export was retrieved and compared
byte-for-byte with the saved live files:

| Entry | Official export at commit `c5bd71de9eee0894df1301baa4f43f6431d8a08d` | SHA-256 |
|---|---|---|
| A326926 | [Pinned source](https://github.com/oeis/oeisdata/blob/c5bd71de9eee0894df1301baa4f43f6431d8a08d/seq/A326/A326926.seq) | `4336b193f72c83da94dea67f1ab47902593bdd875499508f6ac871bda534aa3a` |
| A326933 | [Pinned source](https://github.com/oeis/oeisdata/blob/c5bd71de9eee0894df1301baa4f43f6431d8a08d/seq/A326/A326933.seq) | `4a22e57a1a89fceb807ecd8e5b3de97dc5b9ced9add64f4aac6e8961f4645b12` |

The export commit is dated 24 November 2026. The entry revision timestamps
are 9 November 2026 for A326926 and 14 March 2023 for A326933. Both pinned
sources retain the tentative irreducibility comment at the time checked.

Peter Bala's November 2026 addition to A326926 already gives the recurrence,
closed form, cotangent roots, and strong divisibility. That addition uses
one-based row indexing: its `R(N,x)` is our `P_(N-1)(x)`. These observations
must be credited as source material, not presented as new discoveries.

## Mathematical interpretation verified in Lean

Write `D=1-X+X^2`, `A=1-2X`, and define

```
P_0=1,  P_1=A,  P_(n+2)=A P_(n+1)-D P_n.
```

The source bridge proves the derivative identity

```
(d/dX)^n (1/D) = n! P_n / D^(n+1),
```

and identifies the **reduced** numerator. In particular, `A^2=4D-3` gives a Bezout identity over the
rationals. The recurrence then proves every `P_n` coprime to `D`. Since `D`
is monic, the canonical rational-function numerator is exactly `n! P_n`.
The nonzero rational factor `n!` is a unit for polynomial irreducibility.

The proved classification is therefore

```
Irreducible(P_n in Q[X]) iff (n+1).Prime and n+1 != 3.
```

The degree-zero case is consistent: `P_0=1` is a unit, and one is not prime.
For the exceptional prime, `P_2=3X(X-1)` is reducible. This calculation also
fixes the indexing independently of prose descriptions.

## Norfleet: all four pages inspected

Mark Norfleet, [*Characterization of Second-Order Strong Divisibility
Sequences of Polynomials*](https://www.fq.math.ca/Papers1/43-2/paper43-2-12.pdf),
The Fibonacci Quarterly **43(2)** (2005), 166–169, is explicitly cited by the
current OEIS source. The entire paper, including the conclusion and
references, was read.

Theorem 1 gives the addition identity for a second-order polynomial
recurrence with initial values zero and one. Corollary 1 gives divisibility
when one index divides another. Theorem 3 proves strong divisibility under
the stated coprimality hypothesis. The paper does not give this target's
prime-index irreducibility classification. Its Corollary 1 already supplies
the mathematical ingredient needed to exclude composite indices; our
`LucasDivisibility.lean` formalizes that known ingredient and cites it.

## Semantic prior-art checks

Exact sequence identifiers alone are inadequate here: the row polynomials
are a specialization of a classical second-order recurrence. The following
primary sources were also inspected in the relevant sections.

**Generalized Fibonacci irreducibility.** Rigoberto Flórez and J. C.
Saunders, [*Irreducibility of Generalized Fibonacci
Polynomials*](https://math.colgate.edu/~integers/w69/w69.pdf), Integers
**22** (2022), #A69, treats prime-index irreducibility and gives several
Eisenstein criteria. Its standing degree condition is `deg(g)<deg(d)` for
the recurrence coefficients. Here `d=1-2X` has degree one and
`g=-(1-X+X^2)` has degree two, so the target specialization falls outside
that stated regime. The introduction, hypotheses, and relevant
irreducibility criteria were reviewed; this was not a full reading of all
sixteen pages. No exact A326926 classification was located there.

**Tangent and cotangent polynomials.** Jack S. Calcut,
[*The Tangent Analogues of the Chebyshev
Polynomials*](https://www2.oberlin.edu/faculty/jcalcut/arctan.pdf), dated
10 November 2008, factors the numerator and denominator families associated
with `tan(n arctan X)` using tangent minimal polynomials. The definitions,
factorization statements, and relevant square-root-of-three discussion
were inspected. This is significant related theory, but its unscaled
family differs from the source: `Im(1+iX)^3/X=3-X^2` is irreducible over the
rationals, whereas the source's degree-two row factors. Translating between
these families uses an irrational scaling as well as rational variable
changes. Thus rational irreducibility cannot simply be copied across that
translation. The paper does not state the target criterion. No claim is
made that its results could not yield another proof after further work.

**Recent Lucas observations.** Alexandr Martinevski,
[*Deformations and local arithmetic of Lucas polynomial
observations*](https://math.a-martinevski.com/publications/P09/), version
listed 14 October 2026, was checked through the primary linked manuscript.
Its Eisenstein classification concerns the zero-companion observation
`(V_n(2,1+X)-2)/X`. This is a different sequence and observation from our
`U`-type specialization. The relevant definitions and Eisenstein theorem
were inspected; no exact A326926 theorem was found. This source is a
preprint and is not needed as a premise of the proof.

## Search scope and outcome

Both available search engines were used. Query families included the exact
identifiers with `proof`, `proved`, `irreducible`, `Eisenstein`, and
`cyclotomic`; the literal denominator `1-x+x^2`; generalized Lucas/Fibonacci
polynomial irreducibility; and arctangent derivative, tangent, and
cotangent polynomial irreducibility. The live
[trureturing resolved-conjectures listing](https://www.trureturing.org/conjectures)
was also searched for both identifiers, with no match. No submission or
message was made to that service.

No earlier proof of this **exact** classification was found within that
bounded search. This is evidence about the checks performed, not proof of
historical novelty. The prime argument is an application of the classical
Eisenstein criterion to a reciprocal polynomial, and the composite
argument uses established Lucas divisibility. The defensible contribution
is a complete proof and formal source alignment of the currently tentative
OEIS claim, with the older ingredients explicitly attributed.

## Formal support modules

The support was checked with Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

| Module | Role | SHA-256 at support handoff |
|---|---|---|
| `LucasDivisibility.lean` | Generic recurrence addition and index divisibility | `09e0e9583ce9ec67991f37908dbeb8862b7c2f5fa474a98f13faf69b0060bfca` |
| `ReverseTransfer.lean` | Transfer irreducibility from the reciprocal polynomial when the constant coefficient is nonzero | `69b80f8bfa5733d8a9bd01efc8a526b31ac9126587506d6af42f4fcf24d55d50` |
| `ReverseEisenstein.lean` | Integer reciprocal Eisenstein criterion followed by Gauss's lemma over the rationals | `768959523a44713ccbf8016cb6071d103fa54453c5cf9c0036254e05c8908bf9` |

Each support module compiled successfully without admissions. This support
check is not a substitute for the separate final integrated build and
independent review of the full source theorem.
