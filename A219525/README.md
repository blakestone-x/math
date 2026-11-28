# Integer diagonal forms for box sums and Hardin's king-neighbor table

For an $n\times k$ binary grid, mark each cell where its value equals the sum of its king-move neighbors modulo two. Hardin's empirical formula for the base-two logarithm of the number of possible marks simplifies to $(n-\mathbf1_{n\equiv2\pmod 3})(k-\mathbf1_{k\equiv2\pmod 3})$. [A219525](https://oeis.org/A219525)

The paper gives an integer diagonalization for additive box sums with independently chosen left and right radii, dimensions, and open or periodic boundary conditions. Its formula counts the outputs over any finite abelian group, as well as all preimages of each attainable output. A mixed-boundary example over the integers modulo six shows how cyclic torsion changes the count.

[Manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Verification script](verify.py)

## Provenance and scope

The binary radius-one OEIS formula is a consequence of the known nullity for paths and the strong-product matrix identity. Williams also proved the one-axis consecutive-ones circulant Smith form. The note gives one boundary-residue argument covering asymmetric open windows, incorporates the known cyclic factor, and assembles a formula for all mixed boxes. The extension concerns the additive sum map. In the binary case the equality indicator is its translate. The source catalogue and targeted prior-art searches do not establish historical priority for the general formulation. [Path nullity](https://doi.org/10.2140/involve.2019.12.181) · [Strong graph products](https://doi.org/10.13001/ela.2021.5601) · [Circulant Smith form, Corollary 3.3](https://doi.org/10.1016/j.laa.2013.11.006)

## Reproduce

Run from this directory with Python 3.10 or later and SymPy installed.

```sh
python3 verify.py
```

The script compares 550 directly constructed integer matrices with independent Smith reductions. It enumerates every input and output for four small boxes, then checks the printed empirical formula against the product on 10,000 size pairs.
