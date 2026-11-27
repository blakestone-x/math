# Prime-power congruences for trigonometric power sums

For each function $f$, take the exponential coefficients $A_f(n)$ of $\sum_{k\ge1} f(kx)^k$. For an odd prime power $p^a$ put $\phi=p^{a-1}(p-1)$. The formulas below hold at every $n\ge a$. Independent mathematical review is pending. [Manuscript (PDF)](trigonometric-periods.pdf) · [LaTeX](trigonometric-periods.tex)

| Functions | Shift by $\phi$ modulo $p^a$ | At $p=2$, starting at $n=1$ |
| --- | --- | --- |
| Hyperbolic sine and hyperbolic tangent | The value repeats. | Hyperbolic sine alternates 1, 0. Hyperbolic tangent is 1 followed by zeros. |
| Sine and tangent | The value repeats if $p\equiv1\pmod4$ and changes sign if $p\equiv3\pmod4$. | Sine alternates 1, 0. Tangent is 1 followed by zeros. |

This establishes the proposed odd-prime shifts in Peter Bala's questions, gives the sine parity law, and disproves pure periodicity modulo two for tangent. The results specify periods. Determining the least period for every odd prime is a separate question. The normalized A195415 also obeys the odd-prime-power shifts as a sequence with dyadic rational coefficients. The paper gives no universal divisibility claim for that normalization at two. [Sine](https://oeis.org/A245322) · [Tangent](https://oeis.org/A221078) · [Hyperbolic sine](https://oeis.org/A224899) · [Hyperbolic tangent](https://oeis.org/A221077) · [Normalized sequence](https://oeis.org/A195415)

The trureturing project previously treated the unscaled hyperbolic prime cases. The paper gives a common proof at odd prime powers using the operator $z\,d/dz$. Run `python3 verify.py` to check exact derivatives through degree 165. [Earlier hyperbolic-sine proof](https://www.trureturing.org/research/oeis-a224899-sinh-power-prime-period/) · [Earlier hyperbolic-tangent proof](https://www.trureturing.org/research/oeis-a221077-tanh-power-prime-period/) · [Verifier](verify.py)
