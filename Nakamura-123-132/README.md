# Nakamura’s conjecture for 123 and 132

In 2013 Brian Nakamura conjectured an exact formula for the number of length-$n$ permutations containing precisely $r$ occurrences of 123 and $s$ of 132. He reported checking all pairs with $r+s\le10$. Theorem 1 proves the stated degree and the stated starting index for every pair. [Original paper, Conjecture 1](https://arxiv.org/pdf/1301.5080)

Write $K=r+s$. The answer is $2^n P_{r,s}(n)$ for every $n\ge K+1$, where $P_{r,s}$ has degree $K$ and leading coefficient

$$
\frac{1}{2^{2K+1}r!s!}.
$$

The proof uses the rank of each element among the unused values. A finite collection of short rank words determines both pattern counts. The length bound for each word explains why the polynomial is already exact at $K+1$. For example, the overlapping case with two of each pattern gives $(n^4-18n^3+219n^2-994n+1504)2^n/2048$ for $n\ge5$. [A224288](https://oeis.org/A224288)

The second theorem covers arbitrary pattern length. For all patterns of length $b+1$ that begin with their smallest entry, prescribing each of the $b!$ counts gives a rational generating function with possible poles only at $1,1/2,\ldots,1/b$. The paper gives the leading asymptotic for each prescribed vector.

[Manuscript](prescribed-patterns.pdf) · [LaTeX source](prescribed-patterns.tex) · [Lean proof of the cluster bounds](ClusterBound.lean) · [Polynomial construction and direct checks](verify.py)

Run `python3 verify.py` with the standard library. It checks 66 joint classes against every permutation through length eight, all 25 listed terms of A224291, and the longer-pattern construction at tail sizes three and four. Robertson’s small cases and Mansour’s single-occurrence result for the longer family are cited in the manuscript.
