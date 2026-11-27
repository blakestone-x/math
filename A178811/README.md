# Consecutive powerful integers with the same prime signature

**Blake Stone · Computation and proof developed with OpenAI Codex.**

In 2010 Aaron Meyerowitz exhibited two consecutive 176-digit integers with the same prime signature, consisting of one exponent three and nine exponents two. That example already refutes a conjecture Jon E. Schoenfield recorded in OEIS A178811 in December 2023. We give a shorter pair with a different signature, identify the affected sequence index, and supply deterministic certificates for both pairs. [Meyerowitz's answer, August 11, 2010](https://mathoverflow.net/a/35204) · [OEIS A178811](https://oeis.org/A178811)

An integer is **powerful** if every prime in its factorization occurs with exponent at least two. Its **prime signature** is the multiset of those exponents. The conjecture proposed that no two consecutive integers share a powerful prime signature.

## An 80-digit counterexample

Let

$$
\begin{aligned}
A&=1361\cdot39157289\cdot13475265289\cdot43842128059343041,\\
B&=3\cdot13\cdot509\cdot61853469184829429986091801293807909.
\end{aligned}
$$

Direct integer multiplication gives

$$
2^3B^2-23^3A^2=1.
$$

The smaller integer $N=23^3A^2$ is

~~~
12060988175814077525103089858803400807061146388053160933788947402094570694643847
~~~

The four displayed factors in each of $A$ and $B$ are distinct primes. Also $23\nmid A$ and $2\nmid B$. Thus both $N$ and $N+1$ have signature $(3,2,2,2,2)$.

One can reproduce the construction starting with Golomb's pair $12167=23^3$, $12168=2^3\cdot3^2\cdot13^2$. The unit $24335+3588\sqrt{46}$ has norm one and real part $2\cdot12167+1$. Raising this unit to the seventeenth power gives real part $2N+1$. The verifier checks the powering by integer arithmetic. [Background on the seed pair and Pell constructions](https://www.primepuzzles.net/problems/prob_053.htm)

## Consequence for A178811

The least positive integer with this signature is $M=2^3(3\cdot5\cdot7\cdot11)^2=10672200$. For any prescribed signature, its least representative uses the smallest possible consecutive primes, with larger exponents assigned to smaller primes. These representatives in increasing order form A025487. Exactly 499 representatives are at most $M$, so $M$ is its 499th term. [OEIS A025487](https://oeis.org/A025487)

By definition A178811(499) is the least possible start of a longest run of this signature. The pair above gives a run of length at least two. But $M+1=10672201$ is prime, so $M$ starts a run of length only one. Therefore $\mathrm{A178811}(499)>10672200$. The corresponding maximum length in A178810 is either two or three, since among any four consecutive integers one is $2$ modulo $4$ and hence fails to be powerful. [OEIS A178810](https://oeis.org/A178810)

## Exact verification and the earlier example

The [standard-library Python verifier](verify.py) checks both displayed products, the Pell construction, and the enumeration of least representatives. To obtain the index it enumerates products of consecutive primes with weakly decreasing positive exponents, stopping each branch once its product exceeds $M$. It includes the empty product $1$.

The verifier also factors the two cofactors $X,Y$ given by Meyerowitz, certifies the nine distinct prime factors of each, and checks $2^3X^2-7^3Y^2=1$. Neither cofactor is divisible by its respective cubed prime. This confirms the matching ten-exponent signatures in the earlier example.

Primality is checked by trial division for the small factors. For every larger $p$, the file gives the complete, recursively certified factorization of $p-1$ and an integer $g$ such that $g^{p-1}=1\bmod p$ but $g^{(p-1)/q}\ne1\bmod p$ for each prime $q\mid p-1$. Hence $g$ has order $p-1$ among the invertible residue classes modulo $p$. A composite $p$ has fewer than $p-1$ such classes. This proves primality using only exact modular arithmetic.
