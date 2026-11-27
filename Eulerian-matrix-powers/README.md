# Real zeros of powers of the Eulerian triangle

Mao and Wang conjectured that the row polynomials of the ordinary Eulerian matrix square have only real nonpositive roots. For every fixed positive power, the following two papers settle the asymptotic proportion and the locations of the largest roots. At the ordinary square they also give the locations of the smallest nonzero roots. Full real-rootedness in arbitrary degree remains open. [Original conjecture](https://arxiv.org/abs/2607.01572v1) · [Companion proof for the Delannoy clause](../Delannoy-square/README.md)

| Scope | Result |
|---|---|
| All fixed powers $A^r$ | Every degree-$n$ row has $n-O_r(n(\log\log n/\log n)^{1/3})$ simple negative zeros. For a simple negative root $x$, the numbers $-\log(-x)$ follow a centered Cauchy law of scale $\pi$, with the same error bound in the counts, uniformly in the interval. The limiting distribution was known for $r=1$. [Bulk manuscript](bulk.pdf) · [LaTeX](bulk.tex) |
| Largest roots, all fixed powers | The largest roots in absolute value occur in groups of $r$. For every fixed group number $s\ge0$ the roots are eventually simple and negative, have scale $((s+2)/(s+1))^n$, and have explicit distinct limiting constants. [Edge manuscript](edges.pdf) · [LaTeX](edges.tex) |
| Smallest and largest roots of the square | For every fixed $j$, the $j$th smallest nonzero root in magnitude is asymptotic to $-(m(j)/m(j+1))^{n+1}$ for $m(t)=(t-1)/\log t$ and $m(1)=1$. At the other end the two largest roots in magnitude are asymptotic to $-(1+1/\sqrt2)2^n$ and $-(1-1/\sqrt2)2^n$. |
| Finite full rows | Every row of the square through degree 256 has one simple zero at zero and $n-1$ simple negative zeros. The same holds for the cube through degree 100 and the fourth power through degree 80. The square calculation certifies 32,640 negative roots. [Verifier](verify.py) · [Recorded counts](bulk-verification.txt) |

The matrix uses $A(0,0)=1$ and $A(n,k)$ equal to the number of permutations with $k-1$ descents. The finite verifier forms the exact integer matrix powers. Rational sign brackets certify all zeros in the stated ranges. The edge checker independently enumerates permutations and checks the constants in the limiting polynomials by summing over maximizing compositions. [Edge checks](check_edges.py) · [Recorded output](edges-verification.txt)

Run with Python 3.11 or later and its standard library.

```sh
python3 -B verify.py --power 2 --rows 256
python3 -B verify.py --power 3 --rows 100
python3 -B verify.py --power 4 --rows 80
python3 -B check_edges.py
```
