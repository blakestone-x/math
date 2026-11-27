# Nonreal zeros for three-row transportation polytopes

A counterexample to Per Alexandersson’s conjecture on the Ehrhart numerator of a transportation polytope. The first example in the family has row sums $(12,1,1)$ and column sums $(2,1^{12})$. The formal manuscript proves the result by exact rational arithmetic and classifies the entire one-parameter family.

[Proof manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Exact verification](verify.py)

| Result | Statement |
|---|---|
| Enumerator | For margins $(m,1,1)$ and $(2,1^m)$, the Ehrhart numerator is $H_m(z)=\sum_{j=0}^{m}\binom mj^2z^j-mz$. |
| Counterexample | At $m=12$ and $z=-1/5$, $5^{22}((H'_m)^2-H_m H''_m)=-389210787898375728$. Every real-rooted polynomial satisfies the opposite weak inequality. |
| Classification | Among $m\ge2$, precisely $2\le m\le11$ have only real zeros. This gives counterexamples in every even dimension at least 24. |
| Growth | For $m\ge256$, at least $\lfloor\sqrt m/\pi\rfloor-4$ zeros are nonreal, with multiplicity. |

The conjecture requires an entry of at least two in each margin vector. The sharp threshold applies to the displayed family. [Conjecture, pinned source lines 631–635](https://github.com/PerAlexandersson/symmetricfunctions.com/blob/a3fef6450ca1a091e543c65d89b49a0d302c0a8d/tex-source/realRootedOpenProblems.tex#L631-L635) · [Published catalogue entry](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjTransportationHStar)

Run `python3 verify.py`. The program fills the columns directly for the 3-by-13 example, obtains the Ehrhart numerator in all 25 possible coefficients, checks the displayed rational certificate, brackets roots for the small cases, and gives negative certificates for $12\le m\le255$. The proof for every $m\ge256$ uses the Legendre differential equation and Bernstein’s inequality. [NIST DLMF, equation 18.14.3](https://dlmf.nist.gov/18.14.E3)
