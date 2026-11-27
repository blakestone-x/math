# Factorization of Kimberling's iterated rational functions

Start at $f_0=1$ and form $f_n=1+(x+c)/f_{n-1}$. For a rational shift $c$ and $n>2$, the reduced numerator is irreducible over the rationals exactly when $n+2$ is prime. This proves Clark Kimberling's prime test for A249303. Independent mathematical review is pending. [Manuscript (PDF)](cyclotomic-factors.pdf) · [LaTeX](cyclotomic-factors.tex) · [A249303](https://oeis.org/A249303)

The rational prime criterion follows from known cyclotomic factorizations of Lucas and path polynomials. The paper traces the different index in A128100, where tiling width $r=n+1$ represents iterate $n$. It also gives all irreducible factor degrees and multiplicities over every finite field, including characteristic two. [A128100](https://oeis.org/A128100) · [Sagan and Tirrell](https://arxiv.org/abs/1909.02593) · [Ng](https://arxiv.org/abs/2105.01592)

Run `python3 verify.py` with SymPy to compare the factorization rules with rational factorization and reductions over six prime fields through index 40. [Verifier](verify.py)
