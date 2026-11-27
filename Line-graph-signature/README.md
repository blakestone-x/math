# The signature of line graphs at small cyclomatic number

Let $f(c)$ be the largest possible number of positive minus negative adjacency eigenvalues of the line graph $L(G)$, where $G$ ranges over all finite connected simple graphs with $|E(G)|-|V(G)|+1=c$.

| Cyclomatic number $c$ | Exact $f(c)$ | Order of an attaining example |
| --- | ---: | ---: |
| 2 | 1 | 9 |
| 3 | 2 | 14 |
| 4 | 2 | 18 |
| 5 | 3 | 23 |
| 6 | 3 | 27 |
| 7 | 4 | 32 |
| 8 | 4 | 36 |
| 9 | 5 | 41 |

The upper bounds allow every graph order and arbitrary pendant forests. The lower constructions are due to Andrea Paone and Marco Paone. Their Conjecture 5.4 predicts $f(c)=\lfloor(c+1)/2\rfloor$ for all positive $c$. Their earlier bounds already agree at $c=1$. The first two manuscripts give the cases through seven. The third proves the cases eight and nine, establishes $f(c)\le c-4$ for $c\ge8$, and proves that $\lim f(c)/c$ exists in $[1/2,5/6]$. The next case is $5\le f(10)\le6$. [New manuscript and verification](eight-nine.md) · [Original conjecture](https://doi.org/10.5281/zenodo.21706797)

The core of the proof is a reduction of arbitrary trees to a choice of at most one leaf per vertex of the 2-core. Bipartite path interiors then bound the signature in terms of the core's branch vertices. A singular principal submatrix rules out equality for cubic kernels with six or more vertices. [Manuscript PDF](manuscript.pdf) · [LaTeX source](manuscript.tex)

The accompanying Python program uses integer congruence elimination to check the six attaining examples and selected graphs directly on their line graphs. It checks the rooted-tree lemma on all 1,205 rooted tree types through order ten and checks the cubic multigraph obstruction with loops and parallel edges. Run `python3 verify.py` from this directory. The manuscript gives a mathematical proof, and the program provides independent finite checks. [Verifier](verify.py) · [Recorded output](verification.txt)

## Exact maxima at six and seven independent cycles

The addendum proves $f(6)=3$ and $f(7)=4$. It also shows that for every $c\ge2$ an extremal graph exists on at most $17c-17+14\lfloor(c-2)/2\rfloor$ vertices. The finite reduction turns each fixed-$c$ problem into an exhaustive search. For the two new cases the proof uses a smaller enumeration of kernel multigraphs and exact integer matrices. The general conjecture remains open. [Addendum (PDF)](addendum.pdf) · [LaTeX](addendum.tex) · [Exact verifier](addendum_verify.py) · [Recorded output](addendum_verification.txt)

An independent enumeration starting from simple subcubic graphs reproduced the 388 and 2,592 cubic kernel types and all four exceptional-kernel counts. A separate calculation using exact characteristic polynomials reproduced the four reduced signature maxima and excluded every rank-one candidate for a larger value.

```sh
python3 -B addendum_verify.py --cross-check
```
