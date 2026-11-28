# Gaps, primes and primitive rows in the Wythoff array

These two manuscripts answer seven conjectural statements of Clark Kimberling. Three concern the differences between consecutive indices in the Wythoff–Stolarsky comparison. Four concern primes and primitive rows in the ordinary Wythoff array. The strongest counterexample is a primitive row with **all entries composite**. Here $\varphi=(1+\sqrt5)/2$, and rows and columns start at 1.

| Question | Answer |
| --- | --- |
| Gaps between rows with second-column difference $0$ | Exactly $1,2,3$. [A387349](https://oeis.org/A387349) |
| Gaps between rows with second-column difference $+1$ | Exactly $2,3,5$. [A387350](https://oeis.org/A387350) |
| Gaps between rows with second-column difference $-1$ | Exactly $3,5,8$. [A387351](https://oeis.org/A387351) |
| Does every Wythoff column contain infinitely many primes? | Yes. The fraction of all primes in column $k$ tends to $\varphi^{-(k+1)}$. [A360378](https://oeis.org/A360378) |
| Does every primitive Wythoff row contain infinitely many primes? | No. Row $5{,}381{,}684{,}723{,}742{,}272{,}612{,}570$ contains none. [A360377](https://oeis.org/A360377) · [Related assumption in A333086](https://oeis.org/A333086) |
| What is the longest run of primitive rows? | Five. Rows 36 through 40 realize the maximum. [A332938](https://oeis.org/A332938) |
| What proportion of rows are primitive? | Exactly $6/\pi^2$. For any $g\ge1$, the proportion with gcd $g$ is $6/(\pi^2g^2)$. [A332937](https://oeis.org/A332937) · [A332938](https://oeis.org/A332938) |

## The manuscripts

**Three gap sequences from the Wythoff and Stolarsky arrays.** One first-return rule determines all three gap lists at successive Fibonacci scales. In each list, the short, middle and long gaps have relative frequencies $\sqrt5-2$, $5-2\sqrt5$ and $\sqrt5-2$. The map $m\mapsto\lfloor m\varphi\rfloor$ pairs the positive and negative lists in order. Their successive gaps correspond term by term under $2\mapsto3$, $3\mapsto5$, $5\mapsto8$. Kimberling's November 2026 comment on A387349 also points to Shallit's automata method. [Manuscript (PDF)](stolarsky-gaps.pdf) · [LaTeX](stolarsky-gaps.tex) · [Original array difference](https://oeis.org/A387348) · [Shallit](https://arxiv.org/abs/2502.03312)

**Prime columns and primitive rows in the Wythoff array.** Column membership is an interval test for the fractional part of $n/\varphi$. Vinogradov's prime equidistribution theorem then gives the column densities. For the row counterexample, a tail of Vsemirnov's 2004 composite sequence is located exactly in the array. Seventeen divisors cover every column index modulo 720. The primitive-row density also follows from Estermann's 1953 strip theorem. The manuscript gives a direct proof and uses its uniform divisor bound to exhibit a positive-density family of prime-free primitive rows. It also proves Antti Karttunen's observation that row $p+1$ is primitive for every prime $p>3$. [Manuscript (PDF)](primes-and-primitive-rows.pdf) · [LaTeX](primes-and-primitive-rows.tex) · [Vsemirnov](https://cs.uwaterloo.ca/journals/JIS/VOL7/Vsemirnov/vsem5.pdf) · [Estermann](https://doi.org/10.4153/CJM-1953-051-6) · [Prime equidistribution, §5](https://doi.org/10.1017/S0004972722000880)

## Formal proof

| Part | Lean modules and main results |
| --- | --- |
| Rotation and return times | [GoldenLattice](GoldenLattice.lean) and [ReturnMap](ReturnMap.lean) prove the unimodular basis and the first-return rule for every Fibonacci scale. |
| Actual signed row lists | [RowDifference](RowDifference.lean) derives the sign from the original floor and rounding definitions. [RowGaps](RowGaps.lean) proves the exact sets and witnesses. |
| Frequencies and matching | [OrbitDistribution](OrbitDistribution.lean) proves uniform distribution of the integer phases. [GapStatistics](GapStatistics.lean) proves the relative gap frequencies. [PairedGaps](PairedGaps.lean) proves the increasing correspondence and matched gaps. |
| Prime columns | [ColumnPhases](ColumnPhases.lean) proves the column interval in both directions. [Distributions](Distributions.lean) transfers equidistribution to the relative density and to primes beyond every bound. Its prime theorems take Vinogradov's result as the explicit hypothesis `UniformPhase (Nat.nth Nat.Prime)`. |
| Primitive rows and counterexample | [PrimitiveRows](PrimitiveRows.lean) proves gcd invariance, the sharp run bound and the prime-offset result. [CompositeRow](CompositeRow.lean) proves `prime_free_primitive_row` and the congruence certificate `covered_row` by kernel reduction. |
| Row gcd distribution | [DivisorCounts](DivisorCounts.lean) proves the limit for each divisor. [GcdSpacing](GcdSpacing.lean) gives a uniform summable bound. [GcdDensity](GcdDensity.lean) proves `row_gcd_density` and `primitive_density` by Möbius inversion. |

The restricted density for the prime-free family is proved in Corollary 5 of the second manuscript. The Lean project checks its modular certificate and the uniform divisor estimate. The residue-class limit in that corollary is a manuscript proof.

## Reproduce

Run these commands from this directory using the pinned Lean toolchain.

```sh
lake exe cache get
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

The independent Python verifier uses integer square roots and recurrence enumeration. It checks all row gaps through 250,000, every column assignment for integers through 1,000,000, row gcds through 1,000,000 and all 720 residues in the prime-free certificate. [Verifier](verify.py) · [Build and verification record](verification.txt)
