# Joint counts of 1234 and 1243

For every fixed pair $(r,s)$, the length generating function for exactly $r$ occurrences of 1234 and $s$ occurrences of 1243 belongs to $\mathbb{Q}(x,\sqrt{1-6x+x^2})$. Every such count grows as $C_{r,s}(3+2\sqrt2)^n/n^{3/2}$ with a positive computable constant. In the conclusion of his 2013 paper, Nakamura anticipated a recurrence with polynomial coefficients for $r,s\le1$. The field result establishes one for every fixed pair. [Nakamura](https://arxiv.org/pdf/1301.5080) · [Previous cases](../A224292/README.md)

For two occurrences of each pattern, the paper gives the exact rational function in the parameter $v=x(1+v)(1+2v)$. The number of such permutations divided by the number avoiding both patterns tends to $(2759\sqrt2-2999)/64$, approximately 14.10649. [A224294](https://oeis.org/A224294)

| Length | Number with two occurrences of each |
|---:|---:|
| 26 | 180,240,125,360,405,272 |
| 27 | 1,059,325,053,614,793,050 |
| 28 | 6,211,431,964,216,596,976 |

[Manuscript](fixed-patterns.pdf) · [LaTeX source](fixed-patterns.tex) · [Exact certificate](verify.py)

Run `python3 verify.py` with the standard library. The finite system has 346 states. Its degree bound makes agreement through degree 1404 in $v$ sufficient to prove the rational identity. The script checks that many coefficients by integer arithmetic, all 25 published terms in $x$, and the permutations through length eight directly.
