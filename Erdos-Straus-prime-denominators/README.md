# Near-minimal denominators in three-term Egyptian fractions at primes

[Manuscript (PDF)](prime-denominators.pdf) · [LaTeX source](prime-denominators.tex) · [Exact count verifier](verify.py)

For almost every prime $p$, the Erdős–Straus equation $4/p=1/x+1/y+1/z$ has at least $(\log p)^{\log 3}$ representations of **each** of its two types at a **single** smallest denominator $x$. Given any function $H(p)$ tending to infinity, $x$ can be chosen with $0<4x-p\le H(p)$. Counts use $x<y\le z$. Exactly one denominator is divisible by $p$ in Type I and exactly two in Type II.

The manuscript proves the stronger threshold $3^{L+t\sqrt L}$ for every fixed real $t$, where $L=\log\log p$, and every fixed integer numerator $m\ge2$. For $s$ prescribed admissible offsets in one reduced prime progression, the limiting fraction of primes meeting this threshold at one or more of them is exactly $1-\Phi(t)^s$, where $\Phi$ is the standard normal distribution function.

The proof derives the residue-class counts from the known divisor parametrization, shows equidistribution of divisors at a fixed offset, and gives the joint normal law needed to combine offsets. The prime-density conclusion compares with the leading exponent $(\log 3)/2$ in Theorem 1.8 of [Elsholtz and Tao](https://arxiv.org/abs/1107.1010). The existence of a representation for every prime remains open.

Run `python3 verify.py` to compare the two divisor counts with direct enumeration in 4,642 finite cases. The asymptotic theorem is a written mathematical proof. The manuscript has not undergone external peer review or proof-assistant verification.
