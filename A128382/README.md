# Zeros of iterated divisor sums of Ramanujan's tau function

Gary W. Adamson asked whether the 24th divisor-sum iterate is the only positive iterate with a zero and whether that iterate has infinitely many zeros. The 16,744th iterate vanishes at 7, disproving uniqueness. The 24th vanishes at every number congruent to 2 modulo 4, proving infinitude. Independent mathematical review is pending. [Manuscript (PDF)](tau-zeros.pdf) · [LaTeX](tau-zeros.tex) · [A128382](https://oeis.org/A128382)

At a prime $p$, each divisor-sum operation adds one to the previous value. A zero at $p$ propagates by multiplicativity to every number divisible by $p$ exactly once. Andrew Howroyd previously observed multiplicativity in the source entry. The Sato–Tate theorem for the modular form $\Delta$ further implies infinitely many distinct positive iteration counts with positive-density families of zeros.

Run `python3 verify.py` to expand the defining product for $\Delta$, reproduce the 24th iterate, and apply all 16,744 divisor-sum operations directly through index 7. [Verifier](verify.py)
