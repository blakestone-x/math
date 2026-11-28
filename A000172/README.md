# Large irreducible factors of Sun’s Franel-number polynomials

For every odd prime $p$ and $t\ge1$, the two indices $(p-1)p^t$ and $(p-1)p^t+1$ give irreducible polynomials. The new paper also proves irreducibility for both $2p^t$ and $2p^t+1$ at every prime $p\le10^7$ and every $t\ge1$. It classifies unshifted odd-prime Eisenstein tests and gives the shifted tests valid for arbitrary $p\ge5$. [Manuscript](digits.pdf) · [LaTeX](digits.tex) · [Verifier](verify_digits.py) · [Exact checks](digits-verification.txt)

For every $n\ge2$, all zeros are simple and negative. Their absolute values have limiting distribution function $2\arctan(\sqrt{s})/\pi$ on $s\ge0$. The paper also determines the limits of every fixed extreme root, with different constants at the large end for even and odd indices. [Zero distribution manuscript](zeros.pdf) · [LaTeX](zeros.tex) · [Sturm checks](verify_zeros.py) · [Recorded output](zeros-verification.txt)

The [dyadic continuation](dyadic.pdf) proves irreducibility whenever the odd part of $n$ or $n-1$ is at most 127. For fixed offset $c$ from a certified dyadic family, the total degree outside one irreducible factor is eventually at most $\lfloor c/2\rfloor$. This also holds for each fixed odd base with no adjacent binary ones. [LaTeX source](dyadic.tex) · [Exact polygon verifier](verify_dyadic.py) · [Certificate transcript](dyadic-verification.txt)

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
