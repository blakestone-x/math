# Compositions with a fixed number of smallest parts

Research notes for Blake Stone. Proof developed with OpenAI Codex.

Let $T(n,k)$ count the ordered compositions of $n$ in which the smallest part occurs exactly $k$ times. In 2014 Václav Kotěšovec proposed the following asymptotic for every fixed $k\ge1$, with the first ten columns already known. John Tyler Rascoe recorded a bivariate generating function in 2024. The argument below gives the leading term for every column and also determines the exponential rate of the exceptional compositions whose minimum exceeds one. [OEIS A238342](https://oeis.org/A238342) · [Knopfmacher and Munagi, *Smallest Parts in Compositions*](https://doi.org/10.1007/978-3-642-30979-3_11)

**Theorem.** With $\varphi=(1+\sqrt5)/2$ and $k\ge1$ fixed,

$$
T(n,k)\sim\frac{n^k\varphi^{\,n-2k-1}}{5^{(k+1)/2}k!}.
$$

**Proof.** Fix the value $m$ of the minimum. The $k$ copies of $m$ split a composition uniquely into $k+1$ ordered lists of larger parts. Either end list and any middle list can be empty. If

$$
D_m(x)=\sum_{j\ge m+1}x^j=\frac{x^{m+1}}{1-x},
\qquad B_m(x)=\frac1{1-D_m(x)},
$$

then the generating function for compositions with this exact minimum and multiplicity is $x^{km}B_m(x)^{k+1}$.

Write $\rho_m\in(0,1)$ for the unique solution of $D_m(\rho_m)=1$, and $\lambda_m=1/\rho_m$. The positive solution is simple. By the triangle inequality, a root of $1-D_m(x)$ of modulus $\rho_m$ must have all the consecutive powers $x^{m+1},x^{m+2},\ldots$ on the positive real axis. Hence $\rho_m$ is the only root on its circle and none lies inside it. The rational function $B_m$ has leading pole term $A_m/(1-x/\rho_m)$, where

$$
A_m=\frac{1}{\rho_m D'_m(\rho_m)}
    =\left(m+1+\frac{\rho_m}{1-\rho_m}\right)^{-1}.
$$

Partial fractions and $[x^n](1-x/\rho_m)^{-(k+1)}=\binom{n+k}{k}\lambda_m^n$ give

$$
[x^n]\,x^{km} B_m(x)^{k+1}
 \sim C_{m,k} n^k\lambda_m^n,\qquad
C_{m,k}=\frac{\rho_m^{km} A_m^{k+1}}{k!}.
$$

It remains to bound the **sum** over larger minima. For any integer $L\ge1$, the number $b_j$ of lists of total weight $j$ with all parts at least $L+1$ is at most $\lambda_L^j$. Indeed $b_0=1$, and the last-part recurrence gives the claim by induction using $\sum_{s\ge L+1}\lambda_L^{-s}=1$. Consequently, for $m\ge L$ and $j=n-km\ge0$, the coefficient of weight $j$ in $B_m^{k+1}$ is at most $\binom{j+k}{k}\lambda_L^j$. Summing over $m\ge L$ bounds the entire contribution by

$$
\binom{n+k}{k}\lambda_L^n\sum_{m\ge L}\lambda_L^{-km}
=O_{L,k}(n^k\lambda_L^n).
$$

The roots satisfy $\lambda_{m+1}<\lambda_m$ because $D_{m+1}(x)<D_m(x)$ on $(0,1)$. Thus for each fixed $m$ the exact-minimum-$m$ term gives the leading asymptotic even if all minima at least $m$ are admitted. Taking $m=1$ gives $\rho_1=1/\varphi$ and $A_1=\rho_1/\sqrt5$. Substitution gives the claimed constant. ∎

**How often is the minimum greater than one?** Choose uniformly among the compositions counted by $T(n,k)$. The same proof with $m=2$ gives

$$
\Pr(\min\ge2)\sim\frac{C_{2,k}}{C_{1,k}}\left(\frac{\lambda_2}{\varphi}\right)^n,
\qquad \lambda_2^3=\lambda_2^2+1,\quad \lambda_2>1.
$$

The verifier counts compositions twice, once by directly building all ordered lists and once by distributing the excess above a prescribed minimum. [Exact checks](verify.py)
