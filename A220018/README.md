# Cyclotomic cosets modulo powers of ten

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

This package proves four related quadratic formulas conjectured by Colin Barker in 2013 in [A220018](https://oeis.org/A220018), [A220019](https://oeis.org/A220019), [A220020](https://oeis.org/A220020), and [A221855](https://oeis.org/A221855). They form one family of results with a common proof.

For an integer q coprime to 10, let C_q(n) count the distinct orbits of multiplication by q on all residues modulo 10^n. The orbit of x is

\[
\{x,qx,q^2x,\ldots\}\pmod {10^n}.
\]

The zero orbit is included, as it is in the OEIS examples. The proved formulas are:

| Source | Multiplier | Formula | Full range |
| --- | --- | --- | --- |
| A220018 | 3 | C₃(n) = 8n² − 14n − 1 | n ≥ 3 |
| A220019 | 7 | C₇(n) = 5(16n² − 60n + 37) | n ≥ 4 |
| A220020 | 9 | C₉(n) = 4(4n² − 7n − 1) | n ≥ 3 |
| A221855 | 13 | C₁₃(n) = 2n(4n − 7) | n ≥ 3 |

These are identities for every index in the stated ranges. The proof begins with the literal finite orbit sets and ends with the displayed polynomials.

## Mathematical proof

### Counting by additive order

In the additive cyclic group ℤ/mℤ, exactly φ(d) residues have additive order d, for each divisor d of m. For such a residue x,

\[
q^kx=x\quad\Longleftrightarrow\quad q^k\equiv1\pmod d.
\]

Every orbit in that stratum therefore has size ord_d(q), giving the classical divisor formula

\[
C_q(n)=\sum_{d\mid10^n}\frac{\varphi(d)}{\operatorname{ord}_d(q)}
=\sum_{i=0}^{n}\sum_{j=0}^{n}
\frac{\varphi(2^i5^j)}{\operatorname{ord}_{2^i5^j}(q)}.
\]

The conventions φ(1) = ord₁(q) = 1 account for the zero orbit. The Chinese remainder theorem identifies the order in the denominator as the least common multiple of the orders modulo 2^i and 5^j.

### Exact prime power orders

Write t₊ = max(t,0). For i ≥ 2 the two orders beginning with a factor 2 are

\[
\operatorname{ord}_{2^i}(3)=2\cdot2^{(i-3)_+},\qquad
\operatorname{ord}_{2^i}(7)=2\cdot2^{(i-4)_+}.
\]

Both equal 1 for i = 0,1. For all i ≥ 0,

\[
\operatorname{ord}_{2^i}(9)=2^{(i-3)_+},\qquad
\operatorname{ord}_{2^i}(13)=2^{(i-2)_+}.
\]

For j ≥ 1,

\[
\begin{array}{ll}
\operatorname{ord}_{5^j}(3)=4\cdot5^{j-1},&
\operatorname{ord}_{5^j}(7)=4\cdot5^{(j-2)_+},\\
\operatorname{ord}_{5^j}(9)=2\cdot5^{j-1},&
\operatorname{ord}_{5^j}(13)=4\cdot5^{j-1}.
\end{array}
\]

Each order at j = 0 is 1. These formulas follow from the lifting-the-exponent lemma, after checking the orders modulo 4 or 5. The exceptional factor in the base-7 case is essential: 7⁴−1 = 2400 has 5-adic valuation 2. The relevant 2-adic valuations are v₂(3²−1) = 3, v₂(7²−1) = 4, v₂(9−1) = 3, and v₂(13−1) = 2.

### The summand tables

Put T_q(i,j) = φ(2^i5^j)/ord_(2^i5^j)(q). Multiplicativity of φ and the order formulas give:

| Summand | i=0 | i=1 | i=2 | i=3 | i=4 | Every i≥5 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| T₃(i,0) | 1 | 1 | 1 | 2 | 2 | 2 |
| T₃(i,j), j≥1 | 1 | 1 | 2 | 4 | 8 | 8 |
| T₇(i,0) | 1 | 1 | 1 | 2 | 4 | 4 |
| T₇(i,1) | 1 | 1 | 2 | 4 | 8 | 16 |
| T₇(i,j), j≥2 | 5 | 5 | 10 | 20 | 40 | 80 |
| T₉(i,0) | 1 | 1 | 2 | 4 | 4 | 4 |
| T₉(i,j), j≥1 | 2 | 2 | 4 | 8 | 16 | 16 |
| T₁₃(i,0) | 1 | 1 | 2 | 2 | 2 | 2 |
| T₁₃(i,j), j≥1 | 1 | 1 | 2 | 4 | 8 | 8 |

For example, at i = r+4 and j = s+1, the base-3 denominator is lcm(4·2^r,4·5^s) = 4·2^r·5^s, while the numerator is 2^(r+3)·4·5^s. The quotient is 8 for every r,s ≥ 0. The other constant tails follow in the same way; each is proved for arbitrary exponents in Lean.

Let R(n) be the sum through index n of the profile 1,1,2,4,8,8,…, and S(n) the sum of 1,1,2,4,8,16,16,…. Then R(n) = 8n−16 for n ≥ 3 and S(n) = 16n−48 for n ≥ 4. Summing the table gives

\[
\begin{aligned}
C_3(n)&=(2n-1)+n(8n-16),\\
C_7(n)&=(4n-7)+(5n-4)(16n-48),\\
C_9(n)&=(4n-4)+2n(8n-16),\\
C_{13}(n)&=2n+n(8n-16).
\end{aligned}
\]

Expansion proves all four conjectured polynomials, with exactly their recorded index cutoffs.

## Formalization and reproduction

The six Lean modules prove the complete argument:

| Module | Role |
| --- | --- |
| [OrbitCount.lean](OrbitCount.lean) | Literal orbit quotient, equivalence with nonnegative powers, orbit periods, and the divisor count. |
| [Orders.lean](Orders.lean) | General order lifting from exact valuations, all eight prime power formulas, and the Chinese remainder step. |
| [DivisorGrid.lean](DivisorGrid.lean) | A proved bijection between divisors of 10^n and exponent pairs 0≤i,j≤n. |
| [ExplicitSums.lean](ExplicitSums.lean) | Exact values of every entry in the table, including its infinite tails. |
| [GridSums.lean](GridSums.lean) | Unbounded finite-sum evaluations and the four polynomial identities. |
| [Proof.lean](Proof.lean) | Literal source definitions, all four source endpoints, and axiom reports. |

The definitions `C3`, `C7`, `C9`, and `C13` are cardinalities of actual orbit quotients. The polynomial is never used as the definition of a source sequence. The main theorems are `CyclotomicCosets.A220018_conjecture`, `A220019_conjecture`, `A220020_conjecture`, and `A221855_conjecture`. Their conclusions are written in ℤ so that the source's subtractions retain their ordinary meaning.

The package pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Every proof module is an explicit default build root.

```sh
lake exe cache get
lake build
```

[verification.txt](verification.txt) records a fresh source-only author build. The proof uses no `sorry`, `admit`, custom axioms, or `native_decide`. All printed endpoint dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

## Attribution and scope

V. Raman supplied the sequences in January 2013, and Barker supplied the conjectural formulas on April 13–14, 2013. The divisor-sum programs already appear in the source entries and jOEIS, and related sequence generators already use the polynomial patterns. Orbit counting, the Chinese remainder theorem, Euler's totient, and lifting the exponent are classical.

Zhu, Liu, and Wu give a substantially more general classification of cyclotomic cosets and their sizes in [arXiv:2410.12122](https://arxiv.org/abs/2410.12122), published in *Finite Fields and Their Applications* 111 (2026), article 102761. This package supplies an elementary specialization and a complete formal proof of the four specific OEIS formulas; it makes no claim to new general cyclotomic-coset theory.

[source_checks.md](source_checks.md) records the exact source assertions, immutable snapshots, known related code and literature, and bounded exact and semantic prior-work searches. Those checks did not locate an earlier proof explicitly settling these four closed-form assertions. They do not establish worldwide priority. The package contains four related source assertions in one mathematical family; auxiliary lemmas and equivalent descriptions are not additional problems.

The human proof is also supplied as [manuscript-section.tex](manuscript-section.tex) for the Batch 13 manuscript.

## Completed independent review

The [independent review](independent_review.md) passed, with a separate [fresh source-only build](independent_build.log). Both build logs identify the exact proof and configuration hashes.
