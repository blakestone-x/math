# Eighty Choulet–Mathar recurrences from one identity

Christian Choulet's convolution starts with $a_0=1$, $a_1=b$ and satisfies $a_{n+1}=\sum_{i=0}^n a_i a_{n-i}+k(n+1)+\ell$ for every $n\ge1$. Differentiating its quadratic generating-function equation gives one explicit linear recurrence for arbitrary integer $b,k,\ell$. It implies the printed formulas in all 80 matching OEIS entries in the examined Left to Solve catalogue. Twenty-nine have $k=0$ and 51 have $k\ne0$. In A177126 Mathar's coefficients have the extra common factor $n$. The proof includes the first index where each printed formula is defined. [Proof (2 pages)](manuscript.pdf) · [Editable source](manuscript.tex) · [Table of all 80 entries](identities.csv)

The table records six polynomial coefficients by lag, padded with zeroes, and the SHA-256 digest of each source entry. The comparisons are polynomial identities, so they apply at every index in the stated range. The verifier also reconstructs the printed initial terms and tests the original convolution through index 39. Tong Niu previously proved A176677 by the differential-equation method. Several OEIS entries also credit Robert Israel. [Niu's paper](https://arxiv.org/abs/2605.04369) · [A177111](https://oeis.org/A177111) · [A177130](https://oeis.org/A177130)

## Reproduce the comparisons

Run `python3 -B verify.py` from this directory with SymPy installed. To check against the original OEIS text as well, give the verifier a directory containing the 80 files named in the first CSV column, each with the extension `.seq`. For example A177130 comes from `seq/A177/A177130.seq` at the pinned revision. [Verifier](verify.py) · [Pinned OEIS source archive](https://github.com/oeis/oeisdata/tree/091a90f51479669655f4e46343867ea2abd5d4ff)

```sh
python3 -B verify.py --source-dir /path/to/entries
```

Lean 4.33.1 checks the differentiated power-series equation for arbitrary series satisfying the input quadratic identity. The derivation of that input equation and coefficient extraction are given in the manuscript. The Lean theorem reports only `propext`, `Classical.choice` and `Quot.sound`. [Lean source](Transfer.lean)
