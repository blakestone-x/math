# The signature of line graphs at small cyclomatic number

Let $f(c)$ be the largest possible number of positive minus negative adjacency eigenvalues of the line graph $L(G)$, where $G$ ranges over all finite connected simple graphs with $|E(G)|-|V(G)|+1=c$.

| Cyclomatic number $c$ | Exact $f(c)$ | Order of an attaining example |
| --- | ---: | ---: |
| 2 | 1 | 9 |
| 3 | 2 | 14 |
| 4 | 2 | 18 |
| 5 | 3 | 23 |

The manuscript proves the upper bounds over every graph order and allows arbitrary pendant forests. The lower constructions are due to Andrea Paone and Marco Paone. Their Conjecture 5.4 predicts $f(c)=\lfloor(c+1)/2\rfloor$ for all positive $c$. Their earlier bounds already agree at $c=1$. For every $c\ge4$, the manuscript also improves their general upper bound from $c$ to $c-2$. The next unresolved value from these bounds is $f(6)\in\{3,4\}$. [Source preprint, Proposition 5.2, Theorem 5.3 and Conjecture 5.4](https://doi.org/10.5281/zenodo.21706797)

The core of the proof is a reduction of arbitrary trees to a choice of at most one leaf per vertex of the 2-core. Bipartite path interiors then bound the signature in terms of the core's branch vertices. A singular principal submatrix rules out equality for cubic kernels with six or more vertices. [Manuscript PDF](manuscript.pdf) · [LaTeX source](manuscript.tex)

The accompanying Python program uses integer congruence elimination to check the four attaining examples and selected graphs directly on their line graphs. It checks the rooted-tree lemma on all 1,205 rooted tree types through order ten and checks the cubic multigraph obstruction with loops and parallel edges. Run `python3 verify.py` from this directory. The manuscript gives a mathematical proof, and the program provides independent finite checks. [Verifier](verify.py) · [Recorded output](verification.txt)

## Exact maxima at six and seven independent cycles

The addendum proves $f(6)=3$ and $f(7)=4$. It also shows that for every $c\ge2$ an extremal graph exists on at most $17c-17+14\lfloor(c-2)/2\rfloor$ vertices. The finite reduction turns each fixed-$c$ problem into an exhaustive search. For the two new cases the proof uses a smaller enumeration of kernel multigraphs and exact integer matrices. The general conjecture remains open. [Addendum (PDF)](addendum.pdf) · [LaTeX](addendum.tex) · [Exact verifier](addendum_verify.py) · [Recorded output](addendum_verification.txt)

```sh
python3 -B addendum_verify.py --cross-check
```
