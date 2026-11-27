# Independent verification of the three-prime classification

This verification starts with the theorem's exponent bounds and the subset inequality in the [manuscript](three-primes.pdf). It reconstructs the exponent sieve, proves its own prime-base intervals, and tests every remaining pair. The four possible minimum exponents give 122,347 ordered exponent triples. The interval proof leaves 2,992 candidates for the least prime with its exponent assignment. The arithmetic test finds no equality.

Run the Python driver with Python 3.8 or later, a C++20 compiler supporting unsigned 128-bit arithmetic, and the GMP C++ library. [Driver](three_prime_independent.py) · [Interval verifier](three_prime_independent.cpp) · [Expected output](three-prime-independent-output.txt)

~~~sh
python3 -B three_prime_independent.py
~~~

## Interval proof

Write $P=D+1$. For each modulus and every possible reciprocal residue $u$, the driver constructs the full normalized moment by $F_0=1$ and $F_e=e+1+uF_{e-1}$. It tests every distinct permutation of every surviving exponent triple.

For a hypothetical solution, choose an increasing order of the three numbers

$$
(e_i+2)\log p_i+\log(e_i+1).
$$

The subset inequality in the manuscript rearranges to

$$
(e_i+2)\log p_i+\log(e_i+1)
 \leq \log(P|I|)+\sum_j d_j\log p_j,
 \qquad d_j=2\ (j\in I),\quad d_j=e_j\ (j\notin I).
$$

The right side is independent of the choice of witness in $I$. The earliest index of each subset in the chosen order must therefore be a witness. For each of the six orders the verifier imposes seven witness inequalities and the two order comparisons. Each comparison gives a lower or upper bound for the logarithms. The verifier rejects an interval only after proving a contradiction for all six orders.

The initial intervals for $x$ have consecutive Fibonacci lengths and cover the integer range in the manuscript. Surviving intervals are bisected and each remaining prime $x$ is checked individually. All logarithm bounds enclose $64\log_2 v$ using the top thirteen binary digits of $v$ and the exact binary lengths of $h^{64}$ for $1\le h\le 8192$. Every variable update rounds outward. The full sweep rejects all but 2,992 prime-$x$ cases.

## Final arithmetic test

Put $K=(j+1)(k+1)$ and $g=P-KF_i(x)$. The paper's residual estimates bound all middle primes by

$$
 \max\{x,jD/(j+1),j(k+1)F_i(x)/g\}<y\le 1+\lfloor2P/g\rfloor .
$$

There are 6,518,125 prime pairs in these ranges. For each pair the driver checks whether a unit residue for the last prime can satisfy the full product equation at each of 23 moduli. The least prime exceeds all of them. Thirteen pairs survive.

Set $W=H_i(x)H_j(y)$, $N=Px^iy^j$, and $G=N-(k+1)W$. For $G>0$, equality requires $kW/G<z<1+kW/G$, since all exponents are at least four. Test $z=\lfloor kW/G\rfloor+1$. The polynomial in the last base has constant coefficient $-W$, so an integer solution requires $z\mid W$. None of the thirteen pairs has an ordered candidate satisfying this divisibility. The driver also evaluates the original product equality if any candidate survives.
