# Consecutive generalized binomial Eulerian polynomials

For any sequence of positive integer bounds, the generalized binomial Eulerian polynomials of consecutive prefixes interlace. **Their interlacing is strict exactly when every bound in the current prefix is at least two.** This covers increasing, constant, and decreasing bounds. [Manuscript (PDF)](manuscript.pdf) · [LaTeX](manuscript.tex)

| Case | Consequence |
|---|---|
| All bounds at least two | The polynomials have only simple negative roots and adjacent degrees strictly interlace. Bounds $2,3,\ldots,n$ give the ordinary binomial Eulerian polynomials. |
| A bound equals one | The corresponding inversion coordinate is forced to zero, so the polynomial factors into two independent blocks. The manuscript determines the exact greatest common divisor of consecutive polynomials. |

The ordinary consecutive-interlacing question is listed in the Symmetric Functions Catalog. Haglund and Zhang proved interlacing within the refined rows. The weak cross-degree result follows from the zero-terminal-coordinate identity and their addition lemma. The general strictness criterion uses an additional argument with partial sums at a root. Liu and Yan also studied diagonal generalized Sturm sequences for binomial transforms. [Catalog question](https://www.symmetricfunctions.com/realRootedOpenProblems.htm) · [Haglund and Zhang](https://arxiv.org/abs/1902.01278) · [Liu and Yan](https://doi.org/10.1016/j.aam.2024.102776)

Run the verifier with Python 3 and SymPy. It checks all prefixes of positive length at most five over bounds 1 through 4, computes the exact polynomial gcd, and verifies strict interlacing after cancellation by signed polynomial remainders. It independently counts inversion sequences through length four and all permutations through size eight. [Verifier](verify.py)

~~~sh
python3 -B verify.py
~~~
