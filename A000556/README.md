# Exact modular periods of two Fibonacci-weighted sequences

Research manuscript for Blake Stone, developed with OpenAI Codex.

**Both period conjectures in Remark 4.15 of Kinlaw, Morris and Thiagarajan follow from a classification at every positive modulus.** The two sequences are the integer coefficients in $\operatorname{Li}_{-n}(1/\phi)=A_n+B_n\phi$, where $\phi$ is the golden ratio and $n\ge1$. The first begins $1,5,31,257$ and the second $2,8,50,416$. The authors proved that both least eventual periods divide Carmichael's function $\lambda(m)$ and reported checking the first conjecture through $m=200$. [Original paper, pp. 146–148](https://www.fq.math.ca/Papers/60-2/kinlaw03042021.pdf) · [OEIS A000556](https://oeis.org/A000556) · [OEIS A000557](https://oeis.org/A000557)

## The result

The least eventual period of $A_n$ modulo $m$ is **exactly $\lambda(m)$ for every $m$**. For $B_n$, write $m=2^e q$ with $q$ odd. Its least eventual period equals $\lambda(m)/2$ precisely when one of the following conditions holds.

- $m=3$ or $m=6$.
- $e\ge4$ and $v_2(\lambda(q))<e-2$, using $\lambda(1)=1$.

Every other modulus gives $B_n$ the full period $\lambda(m)$. Here $v_2(x)$ counts the factors of two in $x$. For example, at $112=16\cdot7$ the period is $6$ for $B$ and $12$ for $A$. At modulus $6$, every positive-index term of $B$ is $2$ modulo $6$. The first two small exceptions, $3$ and $6$, supplement the numerical list in the paper.

The proof writes both sequences as finite sums of powers modulo each prime power. Modulo a prime $p\ge7$, a quadratic recurrence forces more than half the nonzero residues to contribute to each sum. This forces a factor $p-1$ in the period. A second coefficient rules out keeping the same period when passing to $p^2$ and provides the factor $p^{e-1}$ at every higher power. The powers of two and the small odd primes give the exceptions. [Full manuscript (PDF)](periods.pdf) · [LaTeX source](periods.tex)

## Two more exact periods

The same proof method determines the least period at every modulus for the two central-binomial transforms A354242 and A354253. For both, every prime power $p^e$ with $p\ge5$ has period $(p-1)p^{e-1}$. Theorem 5.1 gives all powers of two and three. For example, A354253 has periods $1,3,9,27,81,486$ at $3,9,27,81,243,729$, respectively. [OEIS A354242](https://oeis.org/A354242) · [OEIS A354253](https://oeis.org/A354253) · [Earlier note on their continued fractions](../A354242/README.md)

## Verification

The manuscript contains the proof for unbounded moduli and the finite certificate algorithm. The Lean 4.19 file checks all 52 finite prime-power cases used in the proof by kernel reduction. The standard-library Python verifier recomputes the finite cases, checks the symbolic coefficient at every prime from 7 through 199, and uses independent generating-function recurrences to check all four sequences at each modulus through 500. [Lean certificate](SmallCases.lean) · [Python verifier](verify.py)

Run the following commands in this directory to reproduce the checks and typeset the manuscript.

```sh
lean SmallCases.lean
python3 verify.py
tectonic periods.tex
```
