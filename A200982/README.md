# Power sums at prime-power divisors of the Carmichael exponent

Grau, Moree and Oller-Marcén already proved the density-zero assertion recorded in A200982, together with the exact classification and a finer asymptotic expansion for the half-exponent case. Propositions 5.2 and 5.3 give that result. [2016 paper](https://www.unioviedo.es/grau/ARTICULOS%20PUBLICADOS/articulo52.pdf) · [A200982](https://oeis.org/A200982)

Here the divisor 2 is replaced by **any fixed prime power**. We classify the moduli for which the power sum vanishes and obtain the leading asymptotic with a power saving in the logarithm relative to the main term. For divisor 3, for example, the count grows as a positive constant times $x/(\log x)^{2/3}$. The counting proof uses a theorem on integers supported on prescribed prime residue classes. [Chang and Martin](https://arxiv.org/abs/1908.00035)

[Manuscript](prime-power-exponents.pdf) · [LaTeX source](prime-power-exponents.tex) · [Exact verifier](verify.py)

Run `python3 verify.py` to compare the classification with direct modular power sums.
