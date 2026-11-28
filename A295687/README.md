# Peter Bala’s Fibonacci series for A295687

Research note for Blake Stone, developed with OpenAI Codex.

Let $F_0=0, F_1=1$ be the Fibonacci numbers, and let $a_j$ be Clark Kimberling’s fourth-order recurrence A295687. For every $n\ge1$,

$$
F_n^3\sum_{k\ge1}\frac{k^2F_{nk}}{F_{n+2}^{k+1}}
=F_{n+2}F_{n+6}+F_{2n+6}
=a_{2n+7}.
$$

This proves the series identity Peter Bala listed as a conjecture in 2021. For example, the case $n=1$ gives $F_3F_7+F_8=47=a_9$. [Original OEIS entry](https://oeis.org/A295687) · [OEIS source record](https://github.com/oeis/oeisdata/blob/main/seq/A295/A295687.seq)

The proof evaluates the series at both roots of the Fibonacci characteristic polynomial. Carlitz’s addition identity cancels its denominators. A third-order recurrence then identifies the result with Kimberling’s odd-indexed terms. The same argument evaluates every positive integer moment with an arbitrary positive even Fibonacci shift. The manuscript gives the finite Eulerian-number formula, its convergence domain, and the classical identities used. [Proof manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Adegoke on the Carlitz identity and the earlier generating function](https://doi.org/10.47443/ejm.2022.018)

The supplementary verifier takes exact rational derivatives of the generating function for the subsequence $F_{nk}$. It checks 3,360 moment evaluations and the first 60 instances against the independent A295687 recurrence. Run `python3 verify.py` from this directory. [Verifier](verify.py)
