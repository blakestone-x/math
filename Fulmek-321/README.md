# Permutations with a fixed number of decreasing triples

A decreasing triple consists of three entries that appear in descending order, with arbitrary spacing. Let $a_r(n)$ count length-$n$ permutations with exactly $r$ such triples. The manuscript proves Fulmek’s Conjecture 6 for every $r$, gives the limiting ratio to the Catalan numbers, and supplies counterexamples to two sharper predictions of Conway and Guttmann. [Manuscript](fulmek-321.pdf) · [LaTeX source](fulmek-321.tex)

## What holds for every count

The generating function has the form

$$
\sum_{n\ge0}a_r(n)x^n =
\frac{P_r(x)+Q_r(x)\sqrt{1-4x}}{2x^{2r+1}},
$$

where $P_r,Q_r$ are explicitly computable integer polynomials. The denominator power is sharp. For every $n\ge r\ge1$ the count is a finite integer combination of shifted Catalan numbers. The proof identifies each middle entry of a decreasing triple and bounds the total length of the intervals it marks in a permutation diagram. Between marked intervals the diagram is an ordinary Dyck walk.

The ratio $a_r(n)/\mathrm{Cat}_n$ tends to a positive rational $\alpha_r$. The limit of $\alpha_r^{1/r}$ as $r$ grows exists and exceeds 3.19. The paper also proves the three explicit expressions Nakamura and Zeilberger proposed for $r=5,6,7$. [Earlier formulas](https://arxiv.org/abs/1209.2353)

## Where the sharper predictions fail

| Prediction in Conway and Guttmann, Section 4 | Exact result |
|---|---|
| At $r=7$ the proposed factorial normalization is an integer polynomial of degree 14. | At $n=28$ the count is $105460690841118844$, and the normalized value has denominator 23. The reduced rational function has denominator $(n-5)(n-6)$. |
| At $r=8$ both numerator polynomials have degree 20. | Their degrees are 21 and 20. The coefficient of $x^{21}$ in $P_8$ is 4. An independent count gives $-2$ in a finite identity that the proposed degrees would force to equal zero. |

Fulmek’s Remark 7 credits Toufik Mansour with an earlier reported proof of the general form. Waite established two-sided constant-factor bounds for the fixed-count asymptotics. The paper gives an independent construction and credits both results. [Fulmek, Conjecture 6 and Remark 7](https://arxiv.org/pdf/math/0112092) · [Conway and Guttmann](https://doi.org/10.37236/12963) · [Waite](https://arxiv.org/pdf/2506.05712v3)

## Reproducing the results

[Polynomial construction](enumerate_321.py) · [Polynomial pairs and amplitudes for counts 0 through 18](polynomials.json) · [Exact checks](verify.py) · [Independent subset count](subset_check.cpp)

From this directory, the following commands print the eight-triple formula and check the paper. Python uses only its standard library (3.9 or later). Polynomial coefficients in the JSON table run from the constant term to the leading term.

~~~sh
python3 enumerate_321.py 8 --terms 25
c++ -std=c++20 -O3 subset_check.cpp -o /tmp/fulmek-subset-check
python3 verify.py --subsets /tmp/fulmek-subset-check
~~~

The verifier regenerates all 19 polynomial pairs, counts every permutation through length nine directly, and verifies the three earlier formulas by polynomial identity. The C++ calculation independently counts by the set of values already used and checks the two counterexamples modulo 47 through length 25.
