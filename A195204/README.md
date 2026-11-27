# The Stieltjes fraction for Bala’s shift recurrence

Peter Bala recorded a continued fraction for the polynomials defined by $P_0(x)=1$ and $P_{n+1}(x)=x(P_n(x)+P_n(x+1))$. This note proves it directly by expressing the shift operator in a falling-factorial basis and pairing successive steps of a weighted Dyck path. [A195204](https://oeis.org/A195204)

**Prior result.** The fraction is a specialization of the cycle–excedance Eulerian fraction. Sokal and Zeng give the relevant parameters in equations (2.2), (2.3) and (2.11) and trace the fraction to Stieltjes, section 81. The manuscript identifies the OEIS conjecture with that classical result. It also gives the triangular factorization of the Hankel matrix and its first shift for two arbitrary shift weights. [Sokal and Zeng](https://doi.org/10.1016/j.aam.2022.102341) · [Miller and Stanton on Hankel Smith forms](https://arxiv.org/abs/1704.03539)

[Manuscript](continued-fraction.pdf) · [LaTeX source](continued-fraction.tex) · [Verification](verify.py)

Run `python3 verify.py` with SymPy to check symbolic moments through degree six, both Hankel factorizations at five integer specializations, and the permutation interpretation.
