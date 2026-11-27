# Binary arrays avoiding one oriented checkerboard

An $h\times w$ binary matrix is counted when it contains no contiguous block $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$. The manuscript proves all seven empirical strip recurrences in Hardin's A250956 and both empirical generating functions in the width-four and width-five entries. It gives exact minimal constant-coefficient orders through width 12. [A250956](https://oeis.org/A250956) · [A250951](https://oeis.org/A250951) · [A250952](https://oeis.org/A250952) · [A250953](https://oeis.org/A250953) · [A250954](https://oeis.org/A250954) · [A250955](https://oeis.org/A250955)

| Physical width | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Minimal order | 2 | 1 | 3 | 4 | 7 | 9 | 16 | 23 | 39 | 58 | 97 |

The proof groups rows by the positions of their rises. An independent gluing result gives at least $2^{\lceil h/2\rceil}$ admissible one-column separators for any two prescribed boundaries of height $h$, with equality possible. For the diagonal sequence A250950 this implies a certified interval for growth per cell, $1.855317<\lim_{N\to\infty}Z(N,N)^{1/N^2}<1.880675$. [A250950](https://oeis.org/A250950)

[Manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Recurrence verifier](verify.py) · [Growth-bound verifier](entropy.py)

## Provenance and scope

R. H. Hardin recorded the empirical coefficients in 2014. Colin Barker supplied the two smaller rational generating functions in 2018. The first two columns are already identified with shifts of A001353 and A003950 in the table. The note establishes the pattern-specific transfer formula, rectifies the empirical status of the listed formulas within the manuscript, and derives the additional width and gluing results. The scope for the square arrays is a two-sided bound on their growth constant.

The source catalog entries and targeted searches by sequence identifier and pattern were checked. A search of the upstream trureturing problem dossiers and library notes at the revision linked below found no matching A-number. Its related trace-avoidance work treats a different local condition. These checks establish the scope of the literature search and carry no claim of historical priority. [trureturing snapshot](https://github.com/the-omega-institute/trureturing/tree/1cdfa7ff9e256bfec72deb0a89c3b398bf299a59) · [related trace-avoidance dossier](https://the-omega-institute.github.io/trureturing-mdbook/Problems/hardin1857-traceavoid.html)

## Reproduce

Run from this directory with Python 3.10 or later. The polynomial calculation uses SymPy. The width-20 growth certificate uses the Python standard library.

```sh
python3 verify.py --max-width 12
python3 entropy.py
```

Add `--coefficients` to the first command to print the complete reduced numerator and denominator for each width. The verifier constructs the exact transition matrix, obtains the rational function by Cayley–Hamilton and polynomial gcd, tests all seven source coefficient lists, and checks the transition product by independently enumerating binary row words at widths through 10. The second program checks a pair of rational bounds by integer inequalities.
