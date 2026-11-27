# Counting the first corona of a rhombus

L. Edson Jeffery asked whether any column of his table of first coronas satisfies a recurrence. **Every column has the same least recurrence, of order 13.** The manuscript gives a closed formula for each entry, proves the proposed row congruence, and counts the patches up to all isometries preserving the central tile. Independent mathematical review is pending. [Manuscript (PDF)](rhombus-coronas.pdf) · [LaTeX source](rhombus-coronas.tex) · [Jeffery’s original paper](https://oeis.org/A233332/a233332_5.pdf)

Fix a unit-edge rhombus with angles $k\pi/n$ and $(n-k)\pi/n$. Its first corona consists of the tile and its immediate edge- and vertex-neighbors. In the labeled count the central tile has a fixed orientation. In the orbit count, rotations and reflections of the central tile identify patches. The center is a square at $n=2k$, where its symmetry group doubles in size.

| Object | Result |
| --- | --- |
| First corona in a fixed orientation, [A233332](https://oeis.org/A233332) | The least characteristic polynomial of every column is $(E-4)^5(E-2)^6(E-1)^2$, starting at $n=2k$. For fixed $k$, the count is asymptotic to $4^n n^4/64$. |
| Row congruence in [A233332](https://oeis.org/A233332) | Every entry in row $n\ge3$ is congruent to $n-2$ modulo $2^{n-3}$. In column one the next power of two fails exactly when $n\equiv4,6\pmod8$. |
| Core of four edge-neighbors, [A233330](https://oeis.org/A233330) | Every column is a quartic polynomial, proving Jeffery’s fifth-difference conjecture. |
| Core up to isometry, [A233331](https://oeis.org/A233331) | Every column has reduced generating-function denominator $(1-x)^5(1+x)^2$. The first column is [A233329](https://oeis.org/A233329) with offset $n-2$, and its even rows are [A076454](https://oeis.org/A076454). |
| First corona up to isometry, [A233333](https://oeis.org/A233333) | Every column has least eventual order 20, with polynomial $(E-4)^5(E-2)^6(E+2)^3(E^2-2)^3$. It holds for $n>2k$. The paper gives the square value explicitly and identifies when the recurrence extends to it. |
| Associated arithmetic progressions, [A235804](https://oeis.org/A235804) | The stated row and column generating functions follow, and antidiagonal $t$ sums to [A132925](https://oeis.org/A132925) at $t+1$, starting with $t=0$. |

Here $E$ raises $n$ by one at fixed $k$. The labeled count reduces to three terms, with bases $4$, $2$ and $1$. Their polynomial coefficients have exact degrees $4$, $5$ and $1$. The proof counts the ways a sector could use an oversized part. The four sector sizes sum to $2n$, so only configurations with zero, one or two oversized parts enter the calculation.

## The third entry of A233333

For $n=4$, $k=1$, the fixed-set sizes under the identity, the half-turn and the two diagonal reflections are $1452,38,16,34$. Their average is **385**. The sequence entry lists **414**. Direct enumeration in exact Cartesian-plane coordinates gives four orbits of size one, 38 of size two and 343 of size four. These orbits account for all 1,452 labeled patches. At $k=2$ the eight-element square symmetry group gives **247**, matching the fourth listed entry. [OEIS data and definition](https://oeis.org/A233333)

| $n$ | First-corona counts up to isometry for $k=1,\ldots,\lfloor n/2\rfloor$ |
| --- | --- |
| 2 | 1 |
| 3 | 28 |
| 4 | 385, 247 |
| 5 | 3,989 and 5,081 |
| 6 | 33,207, 42,840 and 23,003 |

## Reproduce the checks

Run the following commands in this directory. The Python scripts use the standard library.

```shell
python3 verify.py
python3 geometry_n4.py
lean Certificate.lean
```

- [verify.py](verify.py) compares the closed formulas with every four-edge tuple through $n=16$, every complete patch orbit through $n=6$, and the unreduced Burnside sums through $n=52$. It checks the order-13 and order-20 recurrences in 20 columns. Independently enumerated Hankel matrices certify the two lower bounds in the first three columns. With `--oeis-repo /path/to/oeisdata` it also compares the source terms and the 12 full A233332 example rows. [OEIS data revision](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b)
- [geometry_n4.py](geometry_n4.py) builds the $n=4$ rhombi in $\mathbb Z[e^{\pi i/4}]$, checks that every pair meets compatibly, and compares exact polygon vertex sets under the symmetries preserving the central tile.
- [Certificate.lean](Certificate.lean) exhausts the ordered sector fillings for both $n=4$ shapes. Lean 4.19’s kernel checks the fixed-set sizes and the resulting orbit counts of 385 and 247. It also checks two gap lemmas for arbitrary integral parameters. Sections 2–5 of the paper give the universal recurrence proofs.
