# Division counts in the generalized halving Recamán walk

[Read the manuscript (PDF)](division-counts.pdf) · [LaTeX source](division-counts.tex) · [Exact verifier](verify-divisions.py)

Damijanic's walk starts at 1. At index $n$, divide the current term by a fixed integer $k$ if the quotient is integral and has never appeared. Otherwise add $n+1$. The original walk takes $k=2$. [OEIS A400939](https://oeis.org/A400939)

* **Frequency of division.** For every fixed power of two $k\ge2$ and every $\varepsilon>0$, the number of successful divisions through index $N$ is at least $c_{k,\varepsilon}N^{1/2-\varepsilon}$ for all sufficiently large $N$. The proof counts the collisions that block a division between each pair of addition intervals.
* **A finite deadline for every divisor.** For every $k\ge2$ the first division occurs by index $2k+1$. If a second division ever occurs, its index is at most $\lceil4k^{3/2}\rceil+6k$. The manuscript also gives an exact congruence test using the offset immediately after the first division.
* **Prime powers.** For $k=p^e$ there is exactly one division precisely when $p$ is odd and congruent to 2 or 3 modulo 5, or when $p=5$ and $e\ge2$. Every other prime power produces at least two divisions.

The OEIS entry already states the triangular-residue stopping criterion. The [earlier formalized result](https://github.com/blakestone-x/math/blob/888d3b3f258bbc442c941a2c444bd8c0100a6963/A400939/README.md) proves the one-division assertion for primes in two residue classes. This follow-up gives mathematical proofs and reproducible finite checks. The questions of visiting every positive integer for $k=2$ and eventual stopping for every $k$ with an odd prime factor remain open in this work.

Run `python3 verify-divisions.py` for the exact comparison through $k=512$ and the blocked-division checks through index 100,000 on five power-of-two walks.
