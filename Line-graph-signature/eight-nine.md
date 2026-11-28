# Exact line-graph signatures at eight and nine independent cycles

For a finite connected simple graph, let its cyclomatic number be the number of edges minus the number of vertices plus one. Write $f(c)$ for the largest possible line-graph signature among all root graphs of cyclomatic number $c$. The signature counts positive adjacency eigenvalues minus negative ones, with multiplicity.

| Result | Strength of the bound |
|---|---|
| $f(8)=4$ and $f(9)=5$ | The Paone–Paone conjecture holds for these two cyclomatic numbers, at every graph order. Their examples supply the matching lower bounds. |
| $f(c)\le c-1-\lceil(c-2)/6\rceil$ for $c\ge4$ | The limit $\lim f(c)/c$ exists and lies between $1/2$ and $5/6$. For a simple cubic kernel the upper bound improves to $\lfloor2(c-1)/3\rfloor$. |
| $f(c)\le c-4$ for $c\ge8$ | An exact finite proof applies to all cyclomatic numbers. The next case satisfies $5\le f(10)\le6$. |

[Proof manuscript (PDF)](eight-nine.pdf) · [LaTeX source](eight-nine.tex) · [Original conjecture and lower construction](https://doi.org/10.5281/zenodo.21706797)

A cubic expansion lets an induced matching enforce a signature loss even in the presence of loops, parallel kernel edges and pendant trees. Removing loop leaves and contracting double edges gives a subcubic graph of order at least $c-2$. Applying the induced-matching theorem of Joos, Rautenbach and Sasse proves the analytic bound. A hypothetical example with signature above $c-4$ must have a compressed graph on at most twelve vertices. [Induced-matching theorem](https://doi.org/10.1137/130944424)

The attaining examples are alternating chains of five- and four-cycles. At eight cycles the 36-vertex root graph has line-graph inertia $(23,1,19)$, listed in positive, zero, negative order. At nine cycles the 41-vertex root graph gives $(27,0,22)$.

The finite calculation reduces subdivisions and leaves to signed edges, independent endpoint equations, branch charges and edge deletions. At most two such operations need be tested in any candidate kernel. An independent enumeration produced all 21,096 connected cubic multigraphs on fourteen vertices and all 204,638 on sixteen vertices, including loops and parallel edges. For the two sharp cases the two generators yielded identical exceptional graph sets under canonical labeling. Characteristic-polynomial sign changes and symmetric congruence agreed on all 416,772 signed matrices in this second enumeration.

## Reproduce the certificate

Use a C++17 compiler, the GMP C++ headers and libraries, Python 3, and nauty's `geng` and `labelg`. The reference run used nauty 2.9.0. Both nauty commands may be supplied as absolute paths through the `GENG` and `LABELG` environment variables. The script uses a temporary directory for graph catalogs. [Verification script](eight_nine_reproduce.sh) · [C++ source](eight_nine_verify.cpp) · [Independent rational path checks](eight_nine_paths.py) · [Recorded output](eight_nine_verification.txt) · [nauty distribution and documentation](https://pallini.di.uniroma1.it/)

```sh
bash eight_nine_reproduce.sh
```

The global calculation uses 27,505 simple connected input graphs on orders six through twelve. The two direct enumerations use 262,044 and 4,101,318 simple inputs. The recorded counts of tested operation patterns and signed matrices include repetitions. Each forbidden result makes the verifier exit with an error.

The general conjecture still asks for $f(c)=\lfloor(c+1)/2\rfloor$ at every $c$. The two earlier companion manuscripts give the finite-extremizer reduction and the preceding exact small cases. [Earlier manuscript](manuscript.pdf) · [Finite-extremizer addendum](addendum.pdf)
