# A rounded triangle recurrence and the Pisot sequence E(5,7)

Colin Barker’s 2018 recurrence and generating function for Zak Seidov’s rounded triangle sequence hold at all stated indices. Starting at $n=7$, the sequence obeys $a_n=a_{n-1}+a_{n-3}-1$. At every $n\ge4$ it is the Pisot sequence E(5,7) shifted by four places, extending Georg Fischer’s comparison through 41. [A128424](https://oeis.org/A128424) · [A020711](https://oeis.org/A020711)

The cubic $x^3-x^2-1$ has two conjugate roots inside the unit circle. Bounding their contributions places the proposed integer strictly inside both rounding intervals for every sufficiently large index. For the initial terms Lean checks the two integer inequalities. The proof also identifies an inconsistent fourth-order formula in one A020711 comment.

[Manuscript](rounded-triangle.pdf) · [LaTeX source](rounded-triangle.tex) · [Lean finite certificate](FiniteCases.lean) · [Independent integer verifier](verify.py)

Run `lean FiniteCases.lean` with Lean 4.19.0 and `python3 verify.py`. The analytic argument is in the manuscript.
