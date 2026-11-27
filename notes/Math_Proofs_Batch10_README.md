# Batch 10: five assertions resolved in three families

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

[Read the nine-page manuscript](Math_Proofs_Batch10.pdf) · [Complete LaTeX source](Math_Proofs_Batch10.tex) · [Mathematical review](Math_Proofs_Batch10_math_review.md) · [Rendering and verification record](Math_Proofs_Batch10_review.md)

This batch contains **three proved assertions and two refutations**, organized into three complete Lean projects. Repeated comments in companion OEIS entries are counted once.

| Package | Exact result | Count |
|---|---|---:|
| [A326926](../A326926/README.md) | The nonconstant normalized derivative numerator of degree $n$ is irreducible over $\mathbb Q$ exactly when $n+1$ is prime and unequal to $3$. The repeated assertion in A326933 is the same classification. | 1 proof |
| [A211417](../A211417/README.md) | For every $k\in\{2,3,5\}$ and every shift range $r$, the explicit positive constant $((30r)!)^r$ clears the entire prescribed product of positive shifts, uniformly in every $n\ge0$. | 1 proof |
| [A289128](../A289128/README.md) | The literal replacement iterates have the A289131 length recurrence, including all initial values and the exact start at index six. | 1 proof |
| [A289129](../A289128/README.md) | The zero-position ratio has no real limit; two subsequences tend to $5/2$ and $7/3$. | 1 refutation |
| [A289130](../A289128/README.md) | The one-position ratio has no real limit; two subsequences tend to $5/3$ and $7/4$. | 1 refutation |

## Main statements

### A326926: complete prime-index classification

Set $D=1-X+X^2$, $A=1-2X$, and

$$
P_0=1,\quad P_1=A,\quad P_{n+2}=AP_{n+1}-DP_n.
$$

For every $n\ge0$,

$$
\left(\frac1D\right)^{(n)}=\frac{n!P_n}{D^{n+1}},\qquad
\gcd(P_n,D)=1,\qquad \deg P_n=n.
$$

The canonical reduced numerator is exactly $n!P_n$. For $n>0$,

$$
P_n\text{ irreducible over }\mathbb Q
\iff (n+1)\text{ prime and }n+1\ne3.
$$

The prime proof uses $P_{p-1}'=-pP_{p-2}$ to make every positive-degree coefficient divisible by $p$. The leading coefficient is $\pm p$ and the constant coefficient is $\pm1$, so the reciprocal is Eisenstein. Classical Lucas divisibility rules out composite indices. The exception is $P_2=3X(X-1)$.

### A211417: the full positive-shift family

For the original factorial ratio

$$
A(n)=\frac{(30n)!\,n!}{(15n)!\,(10n)!\,(6n)!},
$$

we prove, for every $k\in\{2,3,5\}$ and $r,n\ge0$,

$$
\prod_{\substack{1\le i\le r\\\gcd(i,k)=1}}(kn+i)
\mid ((30r)!)^r A(n).
$$

The proof counts prime-power divisibility across the whole product. Large prime powers can divide at most one selected shift, and force a matching unit contribution to the factorial-ratio valuation. Small prime powers are covered by $r\,v_p((30r)!)$. The formalization proves natural division exact and separately establishes the literal rational integrality statement.

The original factorial-ratio integrality, four previously proved fixed-factor assertions, and the separate negative-shift family are credited as prior work. The displayed multiplier is sufficient; its optimality is not claimed.

### A289128–A289131: lengths and two nonconvergence results

Starting from $w_0=00$, apply the literal nonoverlapping scan

$$
00\mapsto0010,\qquad01\mapsto011,\qquad10\mapsto010,
$$

copying unmatched input letters. The length recurrence is

$$
L_n=L_{n-1}+3L_{n-2}-3L_{n-3}-2L_{n-4}+2L_{n-5}
\quad(n\ge6),
$$

with $L_0,\ldots,L_5=2,4,7,11,18,28$.

An exact block decomposition proves nesting and constructs the unique infinite word. Write $Z_n,O_n$ for the zero and one counts in $w_n$, and $a(k),b(k)$ for the actual one-based infinite occurrence positions. Then $a(Z_n)=L_n$ and $b(O_n)=L_n-1$ for $n\ge1$. The strictly increasing odd/even rank subsequences give

$$
\frac{a(Z_{2m+1})}{Z_{2m+1}}\to\frac52,\quad
\frac{a(Z_{2m+2})}{Z_{2m+2}}\to\frac73,
$$

$$
\frac{b(O_{2m+1})}{O_{2m+1}}\to\frac53,\quad
\frac{b(O_{2m+2})}{O_{2m+2}}\to\frac74.
$$

The unequal limits refute both proposed convergence assertions. No claim is made to classify every cluster point or to give the corrected all-index inequalities.

## Formal verification

All three projects pin Lean **4.19.0** and mathlib **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. Run from each project directory:

```sh
lake exe cache get
lake build
sha256sum -c SHA256SUMS.txt
```

The projects contain **15 checked local proof modules**: eight, one, and six respectively. One module, `RationalDerivative.lean`, is reused byte for byte from the previous polynomial package. Every project passed both a fresh author build and a fresh independent build without reusing its local proof objects.

| Project | Main endpoints | Review |
|---|---|---|
| A326926 | `SixthDerivative.source_irreducible_iff`; `source_numerator_irreducible_iff` | [Independent review](../A326926/independent_review.md), [build](../A326926/independent_build.log) |
| A211417 | `ChebyshevShifts.bala_positive_shift_conjecture`; `positive_shift_rational_integrality` | [Independent audit](../A211417/AUDIT.md), [build](../A211417/audit-verification.txt) |
| A289128 | `Kimberling289128.original_length_conjecture`; `position_ratios_do_not_converge` | [Independent review](../A289128/independent_review.md), [build](../A289128/independent_build.log) |

All reported endpoint axioms are among `propext`, `Classical.choice`, and `Quot.sound`. There are no admitted statements, added axioms, unsafe declarations, or native-decision proof shortcuts. The independent reviews check the source definitions and mathematical interpretation as well as compilation.

## Source status, attribution, and reproduction

Seven exact primary-source exports are preserved across the packages. Each package documents its revision checks and bounded search for earlier proofs. The mathematical ingredients are credited, including the classical Eisenstein and Lucas results, the known factorial-ratio integrality, and Barker's pre-existing scalar length formulas.

No earlier proof of the exact five assertions claimed here was located in the checked sources. This bounded check does not certify historical priority, human peer review, or OEIS editorial acceptance.

The combined LaTeX source is self-contained. Compile twice in a normal TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Math_Proofs_Batch10.tex
pdflatex -interaction=nonstopmode -halt-on-error Math_Proofs_Batch10.tex
```

The final PDF contains nine letter-size pages with embedded fonts. Every page was rendered and visually inspected. The final log has no overfull or underfull boxes, unresolved references, missing glyphs, or package warnings. The accompanying notes checksum file identifies the exact manuscript, guide, and review records.
