# Minimal recurrences for the signed Deléham triangle

The first column, row sums, and antidiagonal sums of A174014 satisfy the three recurrences proposed by R. J. Mathar in 2012–2013. For A174013 the manuscript reduces the proposed order from seven to six, then proves that a recurrence with polynomial coefficients of any degree needs at least six shifts in span. The two order-four lower bounds follow from the same theorem. [A174013](https://oeis.org/A174013) · [A174015](https://oeis.org/A174015) · [A174016](https://oeis.org/A174016)

| Sequence | Specialization in the manuscript | Proposed order | Proved minimal order |
|---|---|---:|---:|
| A174015, first column | $u=1$ | 4 | 4 |
| A174016, row sums | $u=2$ | 4 | 4 |
| A174013, antidiagonal sums | $u=1+x$ | 7 | 6 |

[Manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Verification script](verify.py)

## Provenance and scope

Paul Barry supplied the entries. Mathar's published formula (28) gives the bivariate generating function. The recurrence identities here follow by differentiating this existing formula. The antidiagonal factorization and the lower bound against arbitrary polynomial-coefficient recurrences are additional results. The same argument gives minimal order four for every nonzero real constant specialization. [Mathar's formula, Example 20](https://oeis.org/A084938/a084938.pdf)

The OEIS entries and targeted searches by sequence identifier and recurrence were checked. A search of the upstream trureturing problem dossiers and library notes found no matching A-number at the revision linked below. These checks establish the scope of the literature search and carry no claim of historical priority. [trureturing snapshot](https://github.com/the-omega-institute/trureturing/tree/1cdfa7ff9e256bfec72deb0a89c3b398bf299a59)

## Reproduce

Run with Python 3.10 or later and SymPy installed.

```sh
python3 verify.py
```

The script checks rational-polynomial identities, the factorization of the order-seven relation, and the discriminant computations. As a separate check it generates each series from its quadratic equation and evaluates the proposed relations through index 96.
