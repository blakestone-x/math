# Forced predecessors in Sun’s coprime-power cycles

Zhi-Wei Sun asks about permutations of the integers from $0$ to $n$, beginning with $0$ and ending with $n$. Every cyclic edge from $x$ to $y$ must have $x^k+y$ coprime to both neighbors of $n$. He conjectured that the exceptional set $E(k)$ of sizes without such an ordering is finite for each fixed positive exponent $k$. [Sun’s formulation in OEIS A229130](https://oeis.org/A229130) · [Proof manuscript](manuscript.pdf) · [Editable LaTeX](manuscript.tex)

Let $r$ be the number of primes $p$ for which $p-1$ divides $k$. The proof exhibits at least $3\cdot2^{r-1}-3$ different exceptions. There are at least 45 when $k=12$, 381 when $k=60$, and 765 when $k=120$. At $k=2$ the construction gives all three predicted exceptions, $2,5,11$. Whether any other quadratic exceptions exist remains open in this work.

The construction also gives a set of sizes of natural density $7/\pi^2$. For any finite collection of those sizes, there is a single positive integer $K$ such that every size in the collection is exceptional for every positive multiple of $K$. The manuscript classifies exactly when the necessary first-step condition fails after every prime factor of $n+1$ has been included.

## Verification

- The Python verifier counts all qualifying orders for 390 exponent/size pairs by dynamic programming, recovers the 15 published quadratic counts at sizes 2 through 16, and checks the first-step classification at every size through 50,000. Run `python3 -B verify.py`. [Verifier](verify.py) · [Recorded output](verification.txt)
- Lean 4.19 with mathlib checks the local finite-field implication from Fermat’s theorem and the one-block and two-block predecessor impossibilities. The paper supplies their translation to the integer circles, squarefree product counts, and densities. Run `lake env lean /absolute/path/to/Forcing.lean` inside a mathlib 4.19 project. [Lean source](Forcing.lean)
