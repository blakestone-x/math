# Counterexamples to four conjectures on rider vertex denominators

Chaiken, Hanusa and Zaslavsky proposed that the largest denominator of a vertex comes from a golden parallelogram for a three-move rider (Conjecture 5.5) and from a twisted Fibonacci spiral for a four-move rider (Conjecture 6.7). Conjectures 5.8 and 5.10 give explicit formulas for the ordinary semiqueen and the trident, the standard piece with a vertical move and both diagonals. This paper refutes all four statements. [Original paper, §§5–6](https://doi.org/10.1016/j.disc.2019.111649) · [Author PDF](https://people.math.binghamton.edu/zaslav/Tpapers/qqs4.pdf)

[Proof manuscript (PDF)](manuscript.pdf) · [Editable LaTeX](manuscript.tex) · [Exact verifier](verify.py) · [Lean certificate for the seven tridents](Trident.lean) · [Lean certificate for the ten semiqueens](Semiqueen.lean)

| Piece | Proven result |
|---|---|
| Three moves $(1,1),(2,1),(3,1)$, three labels | The largest vertex denominator is 6. The proposed triangle has denominator 4. |
| Four moves $(1,1),(2,1),(3,1),(4,1)$, three labels | The largest vertex denominator is 12. The largest twisted-spiral triangle has denominator 9. |
| The ordinary semiqueen | Ten pieces realize denominator 9, exceeding the proposed 8. With $q$ pieces the maximum is at least a constant times $\rho^q$, where $\rho=1.324717\ldots$ satisfies $\rho^3=\rho+1$. This disproves the proposed maximum for all sufficiently large $q$. |
| The trident | A vertex of $2k+1$ pieces has denominator $2^k$. Seven tridents attain 8, exceeding the proposed 7. The proposed formula fails at seven pieces and every size from nine onward. |
| Consecutive primitive moves $(N,1),\ldots,(U,1)$, with $U\ge N+2$ | At three labels the exact maximum is $U(U-1)$. The largest move triangle has denominator $(U-1)(U-N)$. |
| One fixed three-move rider and one fixed four-move rider | The pieces with directions $(N+j,1)$, $N=1{,}000{,}001$, $0\le j<3$ or $0\le j<4$, respectively, violate the proposed maximizer for every $q\ge3$. The construction exceeds the denominator of every vertex determined by a configuration rigid up to translation and scale. |

For the three-label witnesses take one corner and the two points $(1,1/(U-1))$ and $(1,1/U)$. For the seven-trident witness start at the two bottom corners. Intersect one rising and one falling diagonal, project vertically back to the bottom edge, and repeat until the point $(1/8,1/8)$ appears. The equations uniquely determine all seven points.

## Verification

Run the Python verifier from this directory. It uses the standard library. It exhaustively solves all move and facet bases for the first two examples, verifies the triangle formula for 72 finite move sets, and tests the ten-semiqueen equations, 36 cyclic semiqueen shapes, ten trident vertices and 64 sheared boundary constructions using exact fractions, board bounds and full-rank systems.

```sh
python3 -B verify.py
```

The three-move example has 244 labelled vertices and triangle denominator set $\{4\}$. The four-move example has 448 labelled vertices and triangle denominator set $\{4,6,9\}$. Independent enumeration using integer determinants gave the same results.

In Lean 4.19.0 with Mathlib at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run the following from the Mathlib checkout.

```sh
lake env lean /absolute/path/to/Trident.lean
lake env lean /absolute/path/to/Semiqueen.lean
```

The trident file proves that the seven-piece equations uniquely specify the stated coordinates over every linearly ordered field, verifies unit-square containment, and computes the least common multiple of their reduced rational denominators as 8. The semiqueen file proves the six-variable system left after the shared axes and facets are imposed, verifies containment of all ten points and computes the exact denominator 9. The two broader conjecture counterexamples and the all-size comparison are proved in the manuscript.
