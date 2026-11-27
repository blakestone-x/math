# Sharp position errors in three binary fixed points

The manuscript gives the exact infimum and supremum of the error in predicting the position of the $n$-th zero or one for each of three substitutions. It settles five stated inequalities of Clark Kimberling and the corrected A284895 inequality proposed by Michel Dekking.

[Manuscript (PDF)](discrepancy.pdf) · [LaTeX source](discrepancy.tex) · [Lean proof](Bounds.lean) · [Exact endpoint verifier](verify.py)

| Fixed point, with starting letter | Position sequences | Result |
| --- | --- | --- |
| $0\mapsto01,\;1\mapsto0111$, start at 0 | [A284894](https://oeis.org/A284894), [A284895](https://oeis.org/A284895) | For the ones, $0<a(n)-n\sqrt2<2$, with infimum 0 and supremum 2. Dekking gave the counterexample to the original upper bound of one. |
| $0\mapsto01,\;1\mapsto1000$, start at 0 | [A284902](https://oeis.org/A284902), [A284903](https://oeis.org/A284903) | The proposed zero and one inequalities both hold, with sharper endpoints in $\mathbb Q(\sqrt3)$. The title, worked word and numerical terms determine the substitution; an early Mathematica snippet for the zeros uses a different image. |
| $0\mapsto11,\;1\mapsto1101$, start at 1 | [A285669](https://oeis.org/A285669), [A285670](https://oeis.org/A285670) | Both proposed inequalities hold, with sharp endpoints in $\mathbb Q(\sqrt{17})$. Dekking previously established boundedness for A285669. |

The substitution scales a weighted prefix count by a real number of absolute value less than one. Its exact extrema satisfy four finite minimum/maximum equations. The supplied verifier substitutes the proposed values using exact quadratic arithmetic and exhibits an equality witness for every extremum. Its sign checks use integer squares. As a separate check, it tests all 65,536 initial positions in each word against the sharp endpoints.

## Verification and prior work

Lean 4.19.0 with pinned mathlib checks all six strict inequalities for every occurrence in every finite substitution iterate, using one-based occurrence counts and positions. Every occurrence in the corresponding infinite fixed point appears in one of these nested words. The manuscript proves uniqueness of the extrema equations, which is what turns their checked solution into infima and suprema.

```sh
lake exe cache get
lake build
python3 -m pip install 'sympy==1.14.0'
python3 verify.py
sha256sum -c SHA256SUMS
```

[Build and check output](verification.txt) · [OEIS source snapshot](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq)

The proof builds on the established prefix method for substitutions. Adamczewski gives the general discrepancy background. Jung used a contraction calculation in November 2026 for the related word with image $1110$. Those two previously solved cases are credited in the manuscript. [Adamczewski](https://doi.org/10.5802/aif.2079) · [Jung's A045672 comment](https://github.com/oeis/oeisdata/blob/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A045/A045672.seq)
