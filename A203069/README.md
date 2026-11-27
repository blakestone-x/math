# Bounded displacement for greedy composite power-sum permutations

Start at $1$ and repeatedly take the smallest unused number of the opposite parity whose sum with the current number is composite. Every positive integer $m$ appears exactly once, between positions $m-1000$ and $m+2000$. This answers N. J. A. Sloane's 2021 question for Zak Seidov's A203069. Independent mathematical review is pending. [Manuscript (PDF)](greedy-permutations.pdf) · [LaTeX](greedy-permutations.tex) · [A203069](https://oeis.org/A203069)

The theorem allows any fixed positive exponent $d$ in the condition that $u^d+v^d$ be composite. In the square-sum case, $a(n)/n$ tends to one. The suggested six-place bound fails for the first time at $a(11917)=11925$. The sharp global displacement bounds in degrees one and two remain undetermined. [A203077](https://oeis.org/A203077)

The proof first bounds a greedy path on two ordered vertex classes whenever each vertex has few forbidden neighbors in every sufficiently long interval. A congruence sieve supplies this condition uniformly in the previous number. For the ordinary sum, a finite calculation with primes through 37 gives the stated numerical bound. Run `python3 verify.py` to reproduce that finite calculation and the first square-sum exception by trial division. [Verifier](verify.py)
