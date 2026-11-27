# Acyclic matchings and the maximum line-graph signature

Write $f(c)$ for the largest line-graph adjacency signature of a connected simple root graph with $c$ independent cycles. The exact maxima are **5, 6 and 7** at 10, 11 and 13 independent cycles, respectively, at arbitrary graph order. We also improve the upper bound at every large cycle count. [Proof manuscript](forest-bounds.pdf) · [Editable LaTeX](forest-bounds.tex) · [Paone and Paone's Conjecture 5.4](https://doi.org/10.5281/zenodo.21706797)

| Scope | Result |
|---|---|
| All $c\ge2$ | $f(c)\le\lfloor 2c/3\rfloor$. The limit of $f(c)/c$ lies between $1/2$ and $2/3$. The preceding paper's upper limit was $5/6$. |
| Simple branch kernels | For $c\ge5$ the stronger bound $s(L(G))\le\lfloor(c-1)/2\rfloor$ holds for every subdivision and every collection of attached trees. The conjectured upper bound holds at every cycle rank for this class. |
| Other unrestricted-size classes | The conjectured upper bound holds when the compressed cubic skeleton is a path or cycle. For $c\ge9$, a counterexample must have at least six loop-vertex or double-edge reductions in every cubic expansion when $c$ is even, and at least eight when $c$ is odd. |
| Exact finite bounds | For all $c\ge10$, $f(c)\le c-5$, improving to $c-6$ for $c\ge13$. Alternating chains of pentagons and quadrilaterals attain the exact small-cycle values. |

An acyclic matching is a disjoint set of edges whose endpoints induce a forest. Each edge of such a matching in the cubic expansion forces one unit of signature loss. A new spanning-tree coloring argument gives an acyclic matching of size at least $(n-1-e)/3$ in any connected simple subcubic graph with $n$ vertices and cycle rank $e$. An infinite family of cubic kernels shows that the matching obstruction itself cannot give a coefficient below $2/3$. For the finite search we also use the order bound of Fürst and Rautenbach. [Original matching theorem](https://arxiv.org/abs/1710.10076) · [Previous line-graph manuscripts](README.md)

## Reproduction

Use Bash, a C++17 compiler with 128-bit integers, GMP and GMPXX, Python 3 with SymPy, and nauty's `geng` and `labelg` (the reference run used 2.9.0). The script creates a temporary working directory. Each enumerated signed matrix is checked with exact arithmetic. At the recorded stride the program also computes the entire characteristic polynomial. `FOREST_AUDIT_STRIDE=1` applies this second method to every tested matrix.

```sh
bash forest_reproduce.sh
```

`GENG`, `LABELG`, and `CXX` can be set to absolute paths. A practitioner can replay just the first group of cycle counts with `FOREST_LEVEL=3`. The group begins with the 1,040 ten-cycle and 324 eleven-cycle exceptional cubic types. Two structurally different generators give identical sets after canonical labeling. An additional checker validates the acyclic-matching test against independent enumeration of vertex subsets and perfect matchings on 45,866 graphs.

[Reproduction script](forest_reproduce.sh) · [Proof verifier](forest_verify.cpp) · [Independent matching check](forest_matching_audit.cpp) · [Constructive coloring](forest_coloring.py) · [Exact lower witnesses](forest_witnesses.py) · [Recorded verification](forest-verification.txt)
