# Periodic directions in square chess billiards have full measure

**Almost every pair of directions admits a periodic orbit or fixed point on every parallelogram.** Hanusa and Mahankali predicted that this set has measure 3/4 for the square and strictly less than one for every polygon having at least four sides. The full-measure theorem refutes both Conjectures 6.14 and 6.15. Nogueira and Troubetzkoy had proved open density. Together with Hanusa and Mahankali's known regions, that already rules out exactly 3/4. The manuscript determines the measure and gives a periodicity criterion for all finite nonzero opposite slopes on the square. [Manuscript](manuscript.pdf) · [Editable source](manuscript.tex) · [Original conjectures and examples](https://arxiv.org/abs/1901.01917) · [Earlier open-density result](https://arxiv.org/abs/2007.14773)

For slopes $a,-b$ with $a,b>0$ and $a\ne b$, put $l=\min(a,b)/(a+b)$ and $t=l(1-l)$. Start with $u=ab/(a+b)$. Take $x$ to be the distance from $u$ to the nearest integer. Stop if $x=0$ or $x\ge l$. Otherwise replace $u$ by $t/x$ and repeat. Termination is equivalent to periodicity. If the test runs forever, every boundary orbit is dense and the two-chord boundary map is uniquely ergodic. At each fixed asymmetric slope ratio the exceptional scale parameters have Hausdorff dimension strictly below one. For equal magnitudes, periodicity is equivalent to rationality of the common slope magnitude.

| Slopes from the original paper | Exact outcome |
|---|---|
| $1/3,-2/3$ (Figure 9) | Every trajectory has period three under two-chord time. For $a+b=1/k$, the common period is $2k+1$. |
| $3/10,-4/10$ (Figure 10) | The two-chord period is four. All trajectories approach the same folded periodic trajectory set. |
| $1/3,-1/4$ (Figure 11) | Every boundary orbit is dense, including the corner orbit. The mean rise per unit horizontal motion in the unfolded square is $1-1/\sqrt2$. |

For each integer $k\ge2$ and rational $0<a<1/k$, the rational pair $a,-(1-ka)/(k-a)$ gives a dense-orbit example, with drift $k-\sqrt{k^2-1}$. The manuscript identifies its vertical return map with the two-break family studied in internal-wave billiards. The proof of the measure and dimension statements uses explicit interval contractions. [Related work of Lenci, Bonanno and Cristadoro](https://arxiv.org/abs/2102.01654)

Run the [independent exact verifier](verify.py) with Python 3. It traces the reflected grid one edge at a time, directly intersects chords with the original square, and reconstructs the complete piecewise affine boundary maps for the period tests. Finite calculations verify examples. The unbounded results follow from the manuscript. [Expected output](verification.txt)

```sh
python3 -B verify.py
```

## Hausdorff dimension of the exceptional pairs

The set of parameters with no periodic trajectory has angular measure zero and Hausdorff dimension two, on the square and every parallelogram. For fixed unequal slope magnitudes in ratio $a/b$, its slice dimension is the dimension of the limit set of the Hecke group with parameter $(a+b)/\sqrt{ab}$. The correspondence identifies the sets up to countably many points. Phillips–Sarnak's dimension law and Soares's expansion then give the strict range from $1/2$ to $1$ and the asymptotic behavior at extreme ratios.

[Dimension manuscript (PDF)](dimension.pdf) · [LaTeX source](dimension.tex) · [Exact coding verifier](check_dimension.py) · [Verification output](dimension-verification.txt)

```sh
python3 -B check_dimension.py
```
