# Gram determinants of honeycomb hexagons and Aztec rectangles

James Propp’s Problems 26 and 27 ask for the determinant of $KK^*$ on three families of planar bipartite graphs. Here $K$ is a unit-weight Kasteleyn–Percus matrix and the smaller color class indexes its rows. The manuscript gives formulas at every size, explains the square roots in the historical table, and determines the multiplicity of the eigenvalue $4$ on Aztec rectangles. [Manuscript (PDF)](propp-gram.pdf) · [LaTeX source](propp-gram.tex) · [Propp’s 1999 paper, pp. 282–283](https://library.slmath.org/books/Book38/files/propp.pdf)

| Family | Evaluation |
| --- | --- |
| Honeycomb hexagon with any admissible six side lengths | A MacMahon factor times a Gram determinant of order equal to the color imbalance $d$, divided by an explicit factorial product. The coefficient vectors come from products of three binomials. At $d=1$ the entire determinant reduces to one sum of squares. |
| $m$-by-$n$ Aztec rectangle, $m\le n$ | An explicit factor $2^{m(m+1)}$ times two integer Toeplitz determinants. A second formula evaluates each as a finite sum with $\binom{2\lfloor m/2\rfloor}{\lfloor m/2\rfloor}$ terms, independent of $n$. |
| Fool’s rectangle with $r$-by-$s$ cells | The complete spectrum is $4+4\cos(\pi j/(r+1))\cos(\pi k/(s+1))$, $1\le j\le r,\ 1\le k\le s$. Its product is always the square of a positive integer. |

### Two consequences

For the fool’s diamond of order three the eigenvalues are $3,3,5,5$. The determinant is $225$, and its positive square root is the published value $15$. All eight historical entries agree with the square roots. The parity products proposed by Seiichi Manyama in 2021 give these roots in every order. Knuth’s checkerboard spanning-tree theorem gives the roots a second interpretation. [A071102](https://oeis.org/A071102) · [OEIS source record](https://github.com/oeis/oeisdata/blob/main/seq/A071/A071102.seq) · [Knuth](https://arxiv.org/abs/math/9501234)

Saldanha observed a factor $(t-4)^{4k}$ in the singular polynomials of small Aztec diamonds of odd order $2k+1$. For the $m$-by-$n$ rectangle we obtain the exact multiplicity
$$
(m\bmod 2)(n-1)+(n\bmod 2)(m-1).
$$
On odd diamonds it gives exactly $4k$. On even diamonds the eigenvalue is absent. [Saldanha, Section 6](https://arxiv.org/pdf/math/0101002)

### Proof and verification

| Lean file | Uniform mathematical statement checked |
| --- | --- |
| [Fool.lean](Fool.lean) | Constructs the signed graph matrix, computes its Gram matrix, proves the path sine eigenbasis, and derives the full two-parameter determinant. |
| [Parity.lean](Parity.lean) | Proves both of Manyama’s squared product formulas directly for the graph determinant for all orders. |
| [Complement.lean](Complement.lean) | Proves the complementary Gram identity used for the other two graph families, over any commutative star ring. |
| [Honeycomb.lean](Honeycomb.lean) | Proves the coefficient columns obey the three-neighbor equation, including every clipped edge at the hexagon boundary. |
| [Aztec.lean](Aztec.lean) | Characterizes the entire polynomial kernel, proves its degree control and determinant-one boundary minor, and derives the division-free Toeplitz symbol identity. |
| [Boundary.lean](Boundary.lean) | Verifies the change of basis in the odd-length endpoint system and the dimension of the resulting paired constraints. |

The manuscript gives the honeycomb pivot and binomial determinant evaluations, the Aztec minor normalization and root-sum evaluation, and the full eigenvalue-multiplicity argument. The literature comparison establishes the dates and the earlier special cases. Priority for the general results remains unverified.

Run the following commands from this directory.

~~~sh
lake exe cache get Mathlib/Tactic.lean Mathlib/LinearAlgebra/Matrix/Block.lean Mathlib/LinearAlgebra/Matrix/SchurComplement.lean Mathlib/LinearAlgebra/Matrix/Kronecker.lean Mathlib/LinearAlgebra/Eigenspace/Matrix.lean Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean Mathlib/Algebra/MvPolynomial/PDeriv.lean
lake build
python -B verify.py
~~~

The Lean toolchain and mathlib revision are pinned. The Python check uses SymPy 1.14 and mpmath 1.3. It constructs the honeycombs from shared triangle sides and uses a real Kasteleyn signing for the square-grid graphs. It performs 373 exact determinant comparisons and 63 exact rank comparisons. Separate 160-digit calculations check 80 root-subset sums and 15 parity products. The $3,4,3,4,3,4$ hexagon gives $813\,189\,888$. [Verification program](verify.py)

Blake Stone · Proof developed with OpenAI Codex
