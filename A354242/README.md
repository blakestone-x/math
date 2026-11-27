# Two continued fractions and a sharp modular periodicity theorem

Research notes for Blake Stone. Proof developed with OpenAI Codex.

Peter Bala gave conjectural Stieltjes continued fractions for the sequences with exponential generating functions $(5-4e^t)^{-1/2}$ and $(9-8e^t)^{-1/2}$. One weighted-path calculation proves both. It recovers the classical Meixner recurrence for the moments of a negative binomial distribution. Formula (35) of the reference gives the same recurrence under the parameter change $a=r$, $\eta=c/(1+c)$. [OEIS A354242](https://oeis.org/A354242) · [OEIS A354253](https://oeis.org/A354253) · [Classical Meixner coefficients, Section 2.2.1](https://doi.org/10.1007/s13398-022-01296-4)

## The continued fractions

Define $m_n$ by the formal expansion

$$
F(t)=\sum_{n\ge0}m_n\frac{t^n}{n!}=(1-c(e^t-1))^{-r}.
$$

**Theorem.** The ordinary generating function $\sum_{n\ge0}m_n x^n$ is the Stieltjes continued fraction with successive numerators $\alpha_i x$ and unit denominators,

$$
\cfrac{1}{1-\cfrac{\alpha_1x}{1-\cfrac{\alpha_2x}{1-\cdots}}},
\qquad \alpha_{2j-1}=c(j+r-1),\quad \alpha_{2j}=(1+c)j\quad(j\ge1).
$$

For $r=1/2$, taking $c=4$ gives the alternating coefficient pair $(4j-2,5j)$ of A354242. Taking $c=8$ gives $(8j-4,9j)$ of A354253.

**Proof.** Put $h=(e^t-1)/(1-c(e^t-1))$ and $H_j=F h^j/j!$, with $H_{-1}=0$. Differentiation gives $h'=(1+ch)(1+(1+c)h)$ and $F'/F=rc(1+(1+c)h)$. Hence

$$
H'_j = H_{j-1} + b_j H_j + \ell_{j+1} H_{j+1},\qquad
b_j=rc+(1+2c)j,\quad \ell_j=c(1+c)j(j+r-1).
$$

At $t=0$ only $H_0$ is nonzero and its value is one. Induction on $n$ identifies $H_j^{(n)}(0)$ with the total weight of length-$n$ paths from height zero to $j$, staying nonnegative. An up step has weight $1$, a horizontal step at $j$ has weight $b_j$, and a down step from $j$ has weight $\ell_j$. These are the three possibilities for the final step. In particular $m_n=H_0^{(n)}(0)$ counts the weighted excursions.

Now take excursions of $2n$ up and down steps, weighting each down step from height $i$ by $\alpha_i$, and pair consecutive steps. Reading the heights between pairs divided by two, two ups give one up of weight one. Two downs from height $2j$ give one down of weight $\alpha_{2j}\alpha_{2j-1}=\ell_j$. The orders up-down and down-up together yield a horizontal step with total weight $\alpha_{2j+1}+\alpha_{2j}=b_j$, where $\alpha_0=0$ handles the bottom boundary. Thus the weighted totals are exactly $m_n$. An excursion above height $i$ is a list of first returns, each comprising an up step, an excursion above $i+1$, and a down step of weight $\alpha_{i+1}$. Its generating series by half-length satisfies $E_i=1/(1-\alpha_{i+1}xE_{i+1})$. Iterating proves the stated fraction coefficient by coefficient. ∎

## Sharp period and starting index for integral substitutions

Bala also proposed the Euler-totient period bound for every exponential generating function $G(e^t-1)$ with $G\in\mathbb Z[[z]]$. An existing Lean formalization establishes this bound from $n\ge m$. Payam Danesh's August 2026 preprint gives the stronger universal Carmichael period for this class. The following argument proves the optimal universal period and starting index. [Prior formalization, Theorem 1.8](https://the-omega-institute.github.io/trureturing-mdbook/Blueprint/D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.html) · [Danesh's preprint](https://doi.org/10.33774/coe-2026-4d6jr)

**Theorem.** Let $a_n=n![t^n]G(e^t-1)$. For $m\ge2$, let $\lambda(m)$ be the exponent of the multiplicative group of units modulo $m$, and $E(m)$ the largest exponent in the prime factorization of $m$. For every such $G$,

$$
a_{n+\lambda(m)}\equiv a_n\pmod m\qquad(n\ge E(m)).
$$

Both universal bounds are optimal. The case $m=1$ is constant from index zero.

**Proof.** Write $G(z)=\sum_{j\ge0}g_j z^j$. The $n$th exponential coefficient of $(e^t-1)^j$ is $j!{n\brace j}$, where the braces denote a Stirling number of the second kind. This follows by labeling the $j$ nonempty blocks of a partition of $n$ objects. Fix $J$ with $m\mid J!$. Every term with $j\ge J$ vanishes modulo $m$, uniformly in $n$. The binomial theorem on the remaining terms gives

$$
a_n\equiv\sum_{j=0}^{J-1}g_j\sum_{u=0}^j(-1)^{j-u}\binom{j}{u}u^n\pmod m
$$

with $0^0=1$. For each prime power $p^e$ exactly dividing $m$, a power $u^n$ with $p\mid u$ vanishes modulo $p^e$ once $n\ge e$. For $p\nmid u$, the order of $u$ modulo $p^e$ divides $\lambda(m)$ (lift the unit to be $1$ at the other prime powers by the Chinese remainder theorem). Thus each summand repeats with shift $\lambda(m)$ at every $n\ge E(m)$, and the Chinese remainder theorem finishes the proof. Lagrange's theorem gives $\lambda(m)\mid\varphi(m)$ as requested in the entries.

For sharpness choose $G(z)=(1+z)^u$, so $a_n=u^n$. Any period common to the whole class must be divisible by the order of each unit $u\bmod m$, so must be a multiple of $\lambda(m)$. For a prime $p$ with $p^{E(m)}$ exactly dividing $m$, take $u=p$. The term at $n=E(m)-1$ is nonzero modulo $p^{E(m)}$ and every later term is zero there. No positive shift can work universally at that earlier index. ∎

For the two entries, integrality of $G$ follows from $[z^j](1-4z)^{-1/2}=\binom{2j}{j}$ and the corresponding coefficient $2^j\binom{2j}{j}$ for $(1-8z)^{-1/2}$. The theorem and a single period's worth of coefficients also settle Bala's examples. Modulo 16, A354242 has terms $1,2,14$ and then repeats $14,6$ from index three. Indeed the universal shift is four from index four, and the displayed residues at indices four through seven are $6,14,6,14$. Modulo seven, A354253 starts at $1$ and repeats $4,3,2,3,0,0$ from index one. Each displayed block has minimal period as written, and inspecting the preceding entry gives the stated least onset.

The verifier compares exact expansions of the continued fraction against Stirling-number moments. It also checks the two least periods and starting indices and the common modular bound for several integral series. [Reproducible checks](verify.py)

The subsequent manuscript determines the **least** eventual period for each of these two individual sequences at every modulus. Theorem 5.1 gives the full prime-power formulas. [Manuscript](../A000556/periods.pdf) · [Finite certificates](../A000556/SmallCases.lean)
