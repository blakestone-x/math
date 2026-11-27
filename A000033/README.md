# Prime-shift divisibility for three ménage sequences

This package gives complete Lean proofs of the three divisibility assertions recorded by Mark van Hoeij on June 10, 2019 in [A000033](https://oeis.org/A000033), [A000159](https://oeis.org/A000159), and [A000181](https://oeis.org/A000181). A single polynomial congruence proves all three. The rational rook sum printed in the defining entry [A058087](https://oeis.org/A058087) is connected to the integral formal definition by a separate proved equality.

**Author:** Blake Stone. Developed with OpenAI Astra 6.2.

**Date:** November 27, 2026 (America/Chicago).

**Historical scope:** the source entries still label these statements as conjectures in the exact snapshots included here. The searched sources did not supply an exact earlier proof of these three assertions. However, the full texts of Carlitz's 1952 and 1954 papers on ménage congruences and Stevens's 1981 paper were not accessible during this review. Those papers are relevant prior work, and this package makes no first-publication claim for the congruence or its consequences. See [source_checks.md](source_checks.md) for the precise search scope and limitations.

## Exact statements

Let $U_0(t)=1$. For $n\geq1$, use the classical ménage hit polynomial

$$
U_n(t)=\sum_{k=0}^{n}
 \frac{2n}{2n-k}\binom{2n-k}{k}(n-k)!(t-1)^k.
$$

This is the defining finite polynomial formula in A058087. Put $h_d(n)=[t^d]U_n(t)$. A058087 lists coefficients in descending degree, so $h_d(n)=\mathrm{A058087}(n,n-d)$ when $d\leq n$. In particular, the degree is $d$, not $n-d$.

| Source assertion | Sequence identification | Domain | Result |
|---|---|---|---|
| A000033 | $a(n)=h_2(n)$ | $n\geq1$, every prime $p$ | $p\mid a(n)+2a(n+p)+a(n+2p)$ |
| A000159 | $a(n)=h_3(n)$ | $n\geq3$, every prime $p\ne3$ | $p\mid a(n)+2a(n+p)+a(n+2p)$ |
| A000181 | $a(n)=h_4(n)$ | $n\geq4$, every prime $p>3$ | $p\mid a(n)+2a(n+p)+a(n+2p)$ |

A000033 starts at $n=1$, where the explicit degree-two coefficient is zero; its coefficient formula covers this boundary even though the triangle notation $T(n,n-2)$ is outside the triangular domain at $n=1$. The proof uses the explicit coefficient formula. All primes and all indices in each displayed domain are covered.

There are three recorded assertions in this table and one shared formal module. The result does not address the separate recurrence conjecture in A000181 or the rounded Bessel expressions in the related entries. The separate A000159 recurrence has an earlier trureturing proof, credited in the source review.

## Uniform theorem

For every prime $p$ and every $n\geq1$, the following identity holds coefficientwise modulo $p$:

$$
\boxed{
 U_{n+2p}(t)-2(t^p-1)U_{n+p}(t)+(t^p-1)^2U_n(t)
 \equiv0\pmod p.
}
$$

Consequently, for every $d<p$,

$$
 h_d(n)+2h_d(n+p)+h_d(n+2p)\equiv0\pmod p.
$$

For $p=2$, the conclusion additionally holds for every $d<4$:

$$
 h_d(n)+2h_d(n+2)+h_d(n+4)\equiv0\pmod2.
$$

This extra range is needed for the prime 2 in A000033 and A000159.

## Complete elementary proof

### 1. An integral form of the source polynomial

For $n\geq1$ and $j\geq0$, set

$$
 R(n,j)=\binom{n+j}{2j}+\binom{n+j-1}{2j},
$$

with an ordinary binomial coefficient equal to zero when its lower argument exceeds its upper argument. If $0\leq j\leq n$, the elementary binomial identity

$$
 (n+j)\binom{n+j-1}{2j}=(n-j)\binom{n+j}{2j}
$$

gives

$$
 R(n,j)=\frac{2n}{n+j}\binom{n+j}{2j}.
$$

Substituting $j=n-k$ in the source formula, and using binomial symmetry, therefore gives

$$
 U_n(t)=\sum_{j=0}^{n} j!R(n,j)(t-1)^{n-j}. \tag{1}
$$

Thus every coefficient is an integer. This equality, including the special zero row $U_0=1$, is proved in Lean as `menage_eq_sourceMenage`; the passage to each coefficient is `hit_eq_sourceMenage`.

### 2. A binomial second-difference identity

Fix a prime $p$. Work in the polynomial ring over $\mathbb F_p$. Frobenius gives

$$
 (1+x)^p=1+x^p.
$$

Hence, for every integer $a\geq0$,

$$
\begin{aligned}
 &(1+x)^{a+2p}-2(1+x)^{a+p}+(1+x)^a\\
 &\qquad=(1+x)^a\bigl((1+x)^p-1\bigr)^2
 =x^{2p}(1+x)^a.
\end{aligned}
$$

Taking the coefficient of $x^r$, for $r<2p$, proves

$$
 \binom{a+2p}{r}-2\binom{a+p}{r}+\binom ar
 \equiv0\pmod p. \tag{2}
$$

For $0\leq j<p$, apply (2) twice, with $r=2j$ and respectively $a=n+j$ and $a=n+j-1$. The latter upper argument is nonnegative because $n\geq1$. This yields

$$
 R(n+2p,j)-2R(n+p,j)+R(n,j)\equiv0\pmod p. \tag{3}
$$

### 3. Truncation and the full polynomial congruence

In (1), every summand with $j\geq p$ vanishes modulo $p$, since $p\mid j!$. Also $R(n,j)=0$ whenever $j>n$. Thus each of the three sums for $U_n,U_{n+p},U_{n+2p}$ can be compared over the same index set $0\leq j<p$, including when $n<p$.

Multiply (3) by $j!(t-1)^{n+2p-j}$ and sum over $0\leq j<p$. Every exponent used here is nonnegative. The zero terms with $j>n$ justify completing the shorter sum; no negative powers or rational functions are needed. We obtain

$$
 U_{n+2p}(t)-2(t-1)^pU_{n+p}(t)+(t-1)^{2p}U_n(t)
 \equiv0\pmod p. \tag{4}
$$

A second application of Frobenius gives $(t-1)^p=t^p-1$ modulo $p$, proving the boxed theorem. This part of the argument is formalized as `menage_polynomial_shift`.

### 4. Coefficient extraction and the prime 2

If $d<p$, every term containing $t^p$ has zero coefficient in degree $d$. Taking that coefficient in (4) gives

$$
 h_d(n)+2h_d(n+p)+h_d(n+2p)\equiv0\pmod p.
$$

For $p=2$, the middle term of (4) is zero and

$$
 (t-1)^4=t^4+1 \quad\text{in }\mathbb F_2[t].
$$

Thus $U_{n+4}+(t^4+1)U_n=0$ modulo two. Taking any coefficient of degree $d<4$ gives the additional range claimed above.

For A000033, use $d=2$: odd primes satisfy $d<p$, and $p=2$ is covered by the extra range. For A000159, use $d=3$: primes other than $2,3$ satisfy $d<p$, and $p=2$ is again covered. For A000181, use $d=4$: every prime greater than 3 is at least 5, hence $d<p$. This proves all three source assertions.

## Formal verification and source correspondence

The proof is in [Proof.lean](Proof.lean), under namespace `Batch8Menage`.

| Formal declaration | Role |
|---|---|
| `sourceMenage` | Literal rational rook sum from A058087, with $U_0=1$ |
| `menage` | Integral polynomial (1) over $\mathbb Z$ |
| `menage_eq_sourceMenage` | Proved equality of the two definitions for every $n\geq0$ |
| `hit_eq_sourceMenage` | Proved coefficient correspondence |
| `choose_second_shift` | General binomial identity (2) in $\mathbb F_p$ |
| `scaled_menageMod` | Common finite summation range, including $n<p$ |
| `menage_polynomial_shift` | Full polynomial congruence (4) |
| `prime_shift_of_lt` | Integer divisibility for every coefficient degree $d<p$ |
| `two_shift_of_lt_four` | The exceptional prime 2, for $d<4$ |
| `A000033_prime_shift` | Exact A000033 domain and all primes |
| `A000159_prime_shift` | Exact A000159 domain and prime exception |
| `A000181_prime_shift` | Exact A000181 domain and prime restriction |

The three final statements are integer divisibility assertions. They contain no conjectural recurrence hypothesis and no finite upper cutoff. The source bridge proves equality with the stated classical polynomial definition; the package does not add a separate enumeration theorem about permutations or seating arrangements.

**Toolchain:** Lean `v4.19.0`; mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The package includes the complete dependency manifest.

```sh
lake exe cache get
lake build
```

The fresh isolated build is recorded in [verification.txt](verification.txt). The source and final theorems report only `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry`, `admit`, custom axiom, `native_decide`, or unchecked arithmetic oracle in the proof.

## Files and references

The `sources/` directory contains exact UTF-8 exports of A000033, A000159, A000181, and A058087. Their Git blob hashes are recorded in [source_checks.md](source_checks.md). The source formulas and conjecture attributions belong to the OEIS contributors; the proof here was developed from those formulas.

Relevant classical references are I. Kaplansky and J. Riordan, *The problème des ménages*, Scripta Mathematica **12** (1946), 113–124, and J. Riordan, *An Introduction to Combinatorial Analysis*, Wiley, 1958, pp. 197–198. Relevant congruence literature includes L. Carlitz, *Congruences for the ménage polynomials*, Duke Mathematical Journal **19** (1952), 549–552, [doi:10.1215/S0012-7094-52-01957-1](https://doi.org/10.1215/S0012-7094-52-01957-1); L. Carlitz, *Congruence properties of the ménage polynomials*, Scripta Mathematica **20** (1954), 51–57; and H. Stevens, *Arithmetic properties of the ménage polynomials*, Rocky Mountain Journal of Mathematics **11** (1981), 635–639, [doi:10.1216/RMJ-1981-11-4-635](https://doi.org/10.1216/RMJ-1981-11-4-635). Full-text limitations for these prior works are stated above and in the source review.
