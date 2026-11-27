# Rare and typical distances in convex sections of the square lattice

Blake Stone · Proof developed with OpenAI Codex.

For arbitrary subsets of a polynomial-size integer grid, including invertible affine images, the largest $n^{1-o(1)}$ distinct distances are rare. [Proof](arbitrary-subsets.md) · [Manuscript (PDF)](rare-distances-beyond-grids.pdf) · [Finite checks](verify-directions.py)

Let $K\subset\mathbb R^2$ be a fixed compact convex set with nonempty interior. Consider **all** the lattice points $P_t=tK\cap\mathbb Z^2$, with $N=|P_t|$ and $t\to\infty$. A distance is rare if it occurs between at least one and at most $N$ unordered pairs of points. Write $R_t$ for the number of distinct rare distances.

**Theorem.** For every fixed nonnegative integer $k$,

$$
R_t\gg_{K,k}\frac{N(\log\log N)^k}{\log N},
\qquad
R_t=o\!\left(\frac{N}{\sqrt{\log N}}\right).
$$

In particular, $R_t=N^{1-o(1)}$, although the fraction of all distinct distances that are rare tends to zero. More precisely, set $\beta=(\log 2)/2$. For every $\varepsilon>0$, the fraction of **realized distinct distances** whose multiplicity lies between $N(\log N)^{\beta-\varepsilon}$ and $N(\log N)^{\beta+\varepsilon}$ tends to one. All logarithms are natural.

This covers square, circular, triangular and other fixed convex regions filled with points of the integer lattice. The Erdős–Pach questions about arbitrary planar point sets remain open. In the theorem, each distinct distance receives equal weight when forming a fraction. [Problem 132](https://www.erdosproblems.com/132) · [Erdős and Fishburn, Conjecture 4](https://www.sciencedirect.com/science/article/pii/0166218X9400046G)

## Translation counts

Write $D$ for the diameter of $K$. Choose $p,q\in K$ with $q-p=De$ for a unit vector $e$, and choose a closed disk $B(c,\rho)\subset K$ with $\rho>0$. We have $N\sim \operatorname{area}(K)t^2$ by Riemann sums, since a convex body has boundary of area zero. For $v\in\mathbb Z^2$, put

$$
H_t(v)=\#\{x\in P_t:x+v\in P_t\}.
$$

For $s>0$ an integer, the multiplicity $\mu_t(s)$ of $\sqrt s$ is

$$
\mu_t(s)=\frac12\sum_{|v|^2=s}H_t(v).
$$

The factor one half accounts for the two orientations of each unordered pair. We need two consequences of convexity.

1. **Displacements below the diameter.** Fix $0<h<1$. The entire segment from $p_h=(1-h)p+hc$ to $q_h=(1-h)q+hc$ has a disk of radius $h\rho$ about each of its points contained in $K$. This follows by taking convex combinations with $B(c,\rho)$. If $0\le r\le(1-h)D$, then $p_h+re$ lies on this segment. Whenever $|v/t-re|\le h\rho/2$, all lattice points of the disk $tB(p_h,h\rho/2)$ give valid starting points for $v$. Hence $H_t(v)\gg_{K,h}t^2$ uniformly for such $v$ as $t\to\infty$. In particular this holds for all $v$ with $|v|/t\le(1-h)D$ and direction in a fixed arc about $e$, since $|r e'-r e|\le D|e'-e|$.

2. **Displacements near the diameter.** If $|v|\ge (D-\eta)t$ with $0<\eta<D$, then
   $$
   H_t(v)\ll_K \eta t^2+t+1.
   $$
   Project $tK$ onto the direction of $v$. Its projection has length at most $Dt$, and the projection of a valid starting point and its translate differ by $|v|$. Therefore all starting points occupy a strip of width at most $\eta t$. In the perpendicular direction their projection has length at most $Dt$. The disjoint unit squares centered at the starting points fit in a rectangle of side lengths at most $\eta t+\sqrt 2$ and $Dt+\sqrt 2$. Comparing areas gives the bound with a constant independent of $\eta$.

## The typical multiplicity

Write $X=D^2t^2$ and let $S(X)$ be the positive integers $s\le X$ representable as two squares. All grid distances have squared lengths in $S(X)$. Use these classical results.

- By Landau–Ramanujan, $B(X)=|S(X)|\sim bX/\sqrt{\log X}$ for a positive constant $b$. In particular $B(cX)/B(X)\to c$ for every fixed $c>0$. [Landau's theorem as stated by Kano](https://soar-ir.repo.nii.ac.jp/record/12264/files/Science04-02-02.pdf)
- For almost all sums of two squares, the directions of the representations equidistribute on the circle. For each fixed arc $I$ of positive length, the proportion of representations in $I$ tends to $|I|/(2\pi)$ outside a relative-density-zero exceptional set of representable integers. [Erdős and Hall](https://doi.org/10.1016/S0012-365X(98)00329-X) · [Rudnick's account of the Kátai–Környei and Erdős–Hall theorems](https://math.berkeley.edu/~fengt/Sarnak_60th.pdf)
- If $r_2(s)=\#\{v\in\mathbb Z^2:|v|^2=s\}$ counts signed, ordered representations, then $r_2(s)=(\log s)^{\beta+o(1)}$ on a relative-density-one subset of the representable integers. [Kurlberg and Ueberschär, Corollary 3.6 in the authors' PDF](https://people.kth.se/~kurlberg/eprints/QE_rational.pdf)

Fix $0<\delta<1/2$. For $\delta X\le s\le(1-\delta)X$, take $h=1-\sqrt{1-\delta}$ in the first translation estimate. Its arc $I$ is fixed while $t$ varies. Outside $o(B(X))$ exceptions, at least $|I|r_2(s)/(4\pi)$ representations have direction in $I$, and each contributes $\gg_{K,\delta}t^2$ starts. For all $s$ we also have $H_t(v)\le N$. Consequently, outside the exceptional set in this interval,

$$
c_{K,\delta} N r_2(s)\le \mu_t(s)\le \tfrac12N r_2(s)
$$

for a constant $c_{K,\delta}>0$. Here $\log s\sim\log N$ uniformly on the interval. The normal order of $r_2$ and the constant-factor bounds place $\mu_t(s)$ in the theorem's claimed range for every fixed $\varepsilon>0$, with $o(B(X))$ exceptions in this interval. These $s$ are all realized.

Landau–Ramanujan shows that the omitted end intervals together contain at most $(2\delta+o(1))B(X)$ values of $S(X)$. First let $t\to\infty$, then let $\delta\downarrow0$. It follows that all but $o(B(X))$ of $S(X)$ are realized and satisfy the multiplicity estimate. Thus the number of distinct realized distances is $(1+o(1))B(X)$, which justifies conditioning on the realized distances in the theorem. Taking $\varepsilon<\beta$ gives $R_t=o(B(X))$ and hence the stated upper bound.

## Many rare distances near the diameter

Fix $k$. We construct squared lengths $s$ that are products of $k+1$ distinct primes congruent to $1\bmod4$. For every such $s$, Jacobi's two-square formula gives exactly $M=4\cdot2^{k+1}$ signed, ordered representations. [NIST DLMF 27.13.7](https://dlmf.nist.gov/27.13.E7)

Choose $\eta>0$ so small that the second translation estimate gives $\tfrac12 M H_t(v)\le N$ for all $|v|\ge(D-\eta)t$ and all sufficiently large $t$. This choice is possible because $N/t^2\to\operatorname{area}(K)>0$. A squared length of the indicated arithmetic type in this range is therefore rare as soon as one representation occurs in $P_t$.

To guarantee this realization, take $h>0$ small enough that $(1-h)D>D-\eta$. The open disk of radius $h\rho/2$ about $(1-h)De$ meets the open annulus $D-\eta<|z|<D$ in a neighborhood of its center. Fix a closed annular sector inside this neighborhood with squared radii $0<A<B$ and an angular interval $I$ of positive width centered at the direction of $e$. By the first translation estimate at $r=(1-h)D$, any integer vector in the $t$-dilate of this sector is realized. All its lengths also satisfy the required near-diameter bound.

Identify $\mathbb Z^2$ with the Gaussian integers. Hecke's angular equidistribution and the prime number theorem imply the following fixed-sector fact. Given any fixed open angular interval $J$ of positive length and constants $0<A<B$, there are $\gg_{A,B,J}Y/\log Y$ rational primes $q\equiv1\bmod4$ in $[AY,BY]$ that have a Gaussian prime factor of norm $q$ and argument in $J$. Gaussian prime generators differing by units or conjugation have bounded multiplicity for each rational prime. All angular intervals and relative norm intervals used below are fixed. [Rudnick and Waxman, *Angles of Gaussian primes*](https://arxiv.org/abs/1705.07498) · [Huang, Liu and Rudnick, introduction](https://www.math.tau.ac.il/~rudnick/papers/aa190331-23-7.pdf)

Let $\gamma$ be the midpoint of $I$, and choose $\omega>0$ such that every angle within $2\omega$ of $\gamma$ lies in $I$. When $k\ge1$, choose $k$ distinct small primes $p_i\le t^{1/(2k)}$, each having a Gaussian factor with argument in $(0,\omega/k)$. The fixed-sector fact and partial summation give $\sum_{p\le y}1/p\gg \log\log y$ over these eligible primes. For clarity, sum over dyadic intervals $(2^{j-1},2^j]$: the count there is $\gg 2^j/j$, and each contributes $\gg1/j$ to the reciprocal sum.

Write $m=\prod_{i=1}^k p_i\le t^{1/2}$. For $k=0$ take $m=1$ and the empty product. Put $Y=t^2/m$. Choose a Gaussian prime of rational prime norm $q\in[AY,BY]$ whose argument is within $\omega$ of $\gamma$. There are $\gg Y/\log Y\gg t^2/(m\log t)$ choices of rational $q$, uniformly in $m$, since $Y\ge t^{3/2}$ and the constants in the fixed-sector fact are fixed. For large $t$ this $q$ exceeds every $p_i$. The product of the chosen Gaussian factors has squared length $mq\in[At^2,Bt^2]$ and direction in $I$, so $\sqrt{mq}$ is realized and rare.

Finally, different unordered sets of small primes and choices of $q$ give different $s=mq$ by unique factorization, since $q$ is the largest prime. For fixed $k$, the sum of $1/m$ over these unordered sets is $\gg_k(\log\log t)^k$. Indeed, for $k\ge2$, if $H$ is the reciprocal sum over eligible small primes, the ordered sum with repetitions is $H^k$, and repeated primes contribute at most $\binom{k}{2}H^{k-2}\sum_p p^{-2}$. Divide the distinct-prime sum by $k!$. The cases $k=0,1$ follow immediately. Summing over $m$ gives $\gg_{K,k}t^2(\log\log t)^k/\log t$ different squared lengths, proving the lower bound. $\square$

## Relation to earlier work

The arithmetic inputs describe lattice points on individual circles. The passage to actual pair multiplicities uses the number of allowed translations in a dilated convex body. Boldyriew et al. give the exact translation count for square grids. Clemen, Dumitrescu and Liu study high-multiplicity distances in grids and rare distances for other geometric classes. Lu and Meng estimate distance energies, which are moments of the multiplicities. The bounds here concern the number of distinct classes below a threshold and the multiplicity of a uniformly selected class. [Boldyriew et al.](https://arxiv.org/abs/2009.12450) · [Clemen, Dumitrescu and Liu](https://doi.org/10.1007/s10474-025-01562-y) · [Lu and Meng](https://cdm.ucalgary.ca/article/download/76744/58629/272969)
