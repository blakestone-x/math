# Unconditional growth and range bounds for A316994

Sigrist's rule selects the least unused positive integer whose binary word occurs in the new partial sum. Write $S_n$ for the sum of the first $n$ terms and $R_L$ for the number of values in the entire sequence lying in $[2^L,2^{L+1})$.

| Result | Consequence |
|---|---|
| $\sup_{n\ge1} k^{-1}\log(S_{n+k}/S_n)\to0$ as $k\to\infty$ | In particular $S_n^{1/n}\to1$. For every fixed $\varepsilon>0$, the proportion of steps with $a_{m+1}\ge\varepsilon S_m$ tends to zero uniformly over every block of $k$ consecutive steps. |
| $R_L/L\to\infty$ | If $R(X)$ counts range values up to $X$, then $R(X)/(\log X)^2\to\infty$. |
| $a_{n+1}/S_n\to0$ would imply a permutation | In that case the sums cannot skip every interval whose binary prefix is a fixed value $k$, so every $k$ eventually occurs. The permutation conjecture remains open. |

[Proof manuscript (PDF)](growth.pdf) · [LaTeX](growth.tex) · [Sigrist's original problem](https://oeis.org/A316994)

The proof uses the legal prefix $\lfloor S/(2^d-1)\rfloor$. Whenever the greedy choice is larger, that prefix was chosen earlier. Applying the substring condition at the earlier step forces a rational affine relation between the two normalized sums. Prime exponents $d$ then rule out every nonempty finite set of limiting mantissas for relative jumps bounded away from zero. This yields the growth bound. For the range bound, each of infinitely many limiting mantissas forces whole families of binary prefixes into the range.

## Reproduce the numerical checks

The formulas and limiting statements above have mathematical proofs. The standard-library Python program computes candidate terms from their binary length and the location of the occurrence. It independently checks all 130,816 pairs $1\le x\le S\le511$ by literal substring search, compares the first 2,000 choices against a direct greedy scan, and computes the first million terms. [Program](verify_growth.py) · [Recorded results](growth-verification.txt)

```sh
python3 -B verify_growth.py
```

At one million terms the sum is **506,007,688,844**, the largest value is **1,638,414**, and the least unused value is **525,676**. The earlier manuscript proves that omission of even one integer would force density zero for the range. [Omitted-value bound](omitted-values.md)

The [independent C++20 verifier](growth_direct.cpp) scans the unused positive candidates in order and slides a bit mask across the new sum at every bit position. It reproduces all one million terms. The Python and C++ sequences have the same SHA-256 digest, `3b46995a942b09dae0f3276fdbc431031dec396e64e2c5727bd313a0a99068b1`, when written as decimal integers separated and terminated by LF.

```sh
c++ -O3 -std=c++20 growth_direct.cpp -o /tmp/sigrist-direct
/tmp/sigrist-direct > /tmp/sigrist-terms.txt && sha256sum /tmp/sigrist-terms.txt
```
