# Large irreducible factors of Sun’s Franel-number polynomials

Zhi-Wei Sun conjectured in March 2013 that $f_n(X)=\sum_{j=0}^{\lfloor n/2\rfloor}\binom nj^2\binom{2n-2j}{n}X^j$ is irreducible over the rationals for every $n\ge2$. The manuscript proves the conjecture for four infinite families and for every index through 2048. The general case remains open here. [Sun’s statement in OEIS A000172](https://oeis.org/A000172/internal)

[Manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Finite certificate checker](verify.cpp) · [Witness primes](primes.txt)

| Indices | Theorem |
|---|---|
| Every $n\ge2$ | With $d=\lfloor n/2\rfloor$ and $q$ the next prime after $n$, there is a unique irreducible factor of degree $D_n\ge n-(q-1)/2>d/2$. The fraction $D_n/d$ tends to 1. |
| $n=p-2,p-1,p,p+1$ for any prime $p$, within $n\ge2$ | $f_n$ is irreducible. This includes all prime indices. |
| $2\le n\le2048$ | All 2047 polynomials are irreducible. The prime-index theorem covers 1107, and 940 explicit residual-factor certificates cover the rest. |

The proof uses reduction modulo the next prime to force a single large factor. At $n=p,p+1$, reduction of the reciprocal polynomial modulo $p^2$ rules out a complementary factor. The finite checker additionally uses a witness prime to exclude each possible remaining factor degree. Its two-column input gives the index and the witness prime. A C++17 compiler suffices.

```sh
c++ -O2 -std=c++17 verify.cpp -o verify
./verify primes.txt
```

The 1994 Strehl identity accounts for $f_n(1)$, and Nagura’s bound on prime gaps gives an explicit uniform degree estimate. The conjecture is attributed to Sun’s OEIS comment. [Strehl](https://doi.org/10.1016/0012-365X(94)00118-3) · [Nagura](https://doi.org/10.3792/pja/1195570997)
