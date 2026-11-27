# Every gcd occurs in infinitely many real quadratic fields

For any positive integer $n$, the paper constructs infinitely many distinct real quadratic fields with a radicand $k$ divisible by $n$ and fundamental unit $x+n\sqrt{k}$. This gives the required gcd exactly. It proves Artur Jasinski's existence conjecture for A197170, his infinitude conjecture for A197171, and the same infinitude result for every other gcd. Independent mathematical review is pending. [Manuscript (PDF)](fundamental-units.pdf) · [LaTeX](fundamental-units.tex) · [A197170](https://oeis.org/A197170) · [A197171](https://oeis.org/A197171)

The radicand can be chosen below $10^6n^{14}$. If $s^2$ is the largest square dividing $n$, the construction attains $k=s^2d$ with $d$ squarefree, the smallest possible square multiplier. For example $193+4\sqrt{2328}$ is the fundamental unit of $\mathbb Q(\sqrt{582})$. Existence answers the question of whether each minimum is defined. Determining the minimizing $k$ for a given $n$ is a further problem.

The proof works in the full ring of integers, compares against units of both norms, and proves squarefreeness for a positive proportion of its parameters. It uses a classical near-square Pell construction and cites Hideo Yokoi for its historical context. Run `python3 verify.py` to check 150 witnesses independently by continued fractions. [Verifier](verify.py)
