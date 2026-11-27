# Rare distances in arbitrary subsets of planar lattices

Blake Stone · Proof developed with OpenAI Codex.

Call a distance *rare* in an $n$-point set if its multiplicity, counted in unordered pairs, lies between $1$ and $n$. Let $R(P)$ denote the number of distinct rare distances in $P$.

**Theorem.** Fix $C>0$. Choose any $n$ integer points in a square box of side $n^C$ with sides parallel to the coordinate axes, and apply any invertible real affine map. Among the Euclidean distances of the resulting point set, the largest $\lfloor n^{1-\varepsilon}\rfloor$ distinct values exist and are all rare for every fixed $\varepsilon>0$ and all sufficiently large $n$. The bound is uniform over the points and the affine map, which may vary with $n$. In particular, every $n$-point subset of the square lattice of diameter at most $n^C$ has at least $n^{1-o(1)}$ rare distances. This includes arbitrary subsets occupying a fixed positive fraction of a square grid. A second application locates linearly many rare distances at the top of the distance ordering for subsets of lattices of irrational shape, of arbitrary diameter.

Erdős and Pach ask whether every sufficiently large planar point set determines two rare distances, and whether the minimum number tends to infinity. The suggested stronger lower bound is $n^{1-o(1)}$. The theorem proves that bound for the stated lattice families. The unrestricted planar problem remains open. [Erdős Problem 132](https://www.erdosproblems.com/132)

## Counting segments of a prescribed length

Let $P$ be any planar set of $n\ge2$ points. For each realized positive distance $r$, let $g(r)$ be the number of different displacement vectors of length $r$ in $P-P$, counted up to sign. Thus parallel segments of length $r$ give the same displacement up to sign. Write $\mu(r)$ for the multiplicity of $r$ and $m$ for the number of realized distances.

**Lemma.** For every realized distance $r$,
$$
\mu(r)\le g(r)\left(1+\sum_{t>r}g(t)\right),
$$
where the sum runs over the larger realized distances.

*Proof.* Choose one representative $v$ of each pair $\{v,-v\}$ at distance $r$. The unordered segments giving this pair correspond one-to-one to starting points $x$ for which $x,x+v\in P$. For fixed $v$, choose a start $a$ minimizing $a\cdot v$. Every other start $x$ satisfies
$$
|x+v-a|^2=r^2+2v\cdot(x-a)+|x-a|^2>r^2.
$$
The vectors $x+v-a$ are distinct as $x$ varies. Moreover, their dot products with $v$ are at least $r^2>0$. For each larger distance $t$, at most one vector from each opposite pair of length $t$ can lie in this open half-plane. Hence there are at most $\sum_{t>r}g(t)$ starts besides $a$. Sum the resulting bound over the $g(r)$ choices of $v$. $\square$

Suppose $g(r)\le G$ for every $r$, where $2\le G\le n$ is an integer. A distance with exactly $j$ larger realized distances has multiplicity at most $G(1+jG)$. Consequently the largest
$$
L=1+\left\lfloor\frac{n-G}{G^2}\right\rfloor
$$
distinct distances are all rare. To see that at least $L$ distances exist, choose a linear functional taking distinct values on $P$, and take its minimum point $p$. The other $n-1$ displacements from $p$ lie in one open half-plane, which contains at most $G$ displacements per length. Thus $m\ge\lceil(n-1)/G\rceil$. Since $(n-G)/G^2<(n-1)/G$, this ensures $m\ge L$.

When $g(r)=1$ for a particular $r$, all edges of length $r$ lie on lines parallel to one vector $v$. On each such line the edges join successive points of arithmetic progressions with step $v$, forming disjoint finite paths. Thus $\mu(r)\le n-1$. In particular, when $g(r)=1$ for every distance, all the distances are rare and $m\ge n-1$ by the same projection argument.

## Arbitrary subsets of square grids

For $P\subset\mathbb Z^2$ of diameter $D$, every squared distance is an integer $s\le D^2$. The number $r_2(s)$ of signed, ordered integer representations $s=u^2+v^2$ satisfies $r_2(s)\le4\tau(s)$, where $\tau$ counts positive divisors. This follows from Jacobi's two-square formula. The divisor bound gives $\tau(s)\le C_\eta s^\eta$ for every $\eta>0$. [NIST DLMF, Eq. 27.13.7](https://dlmf.nist.gov/27.13.E7) · [Tao, *The divisor bound*](https://terrytao.wordpress.com/2008/09/23/the-divisor-bound/)

For $D\le n^C$, we therefore have
$$
g(\sqrt{s})\le \tfrac12 r_2(s)\le 2C_\eta n^{2C\eta}.
$$
As $\eta$ can be arbitrarily small, $G=\max(2,\max_r g(r))=n^{o(1)}$ uniformly over the point sets under consideration. For all sufficiently large $n$ the finite bound applies, giving $L\ge (n-G)/G^2=n^{1-o(1)}$. An $L_0\times L_0$ grid with $n\ge\delta L_0^2$ occupied points, for fixed $\delta>0$, has diameter at most $\sqrt{2n/\delta}$, as required. $\square$

**Affine images.** Let $P=T(S)+b$, where $T$ is an invertible real linear map and $S$ consists of $n$ integer points in an axis-parallel box of side $n^C$. For each distance $r>0$ of $P$, its displacements correspond to integer vectors $w\in[-n^C,n^C]^2$ on the nondegenerate ellipse $|Tw|^2=r^2$. The uniform ellipse lemma in the public research note cited below bounds the number of these vectors by $O_\eta((n^C)^\eta)$ for every $\eta>0$, with a constant independent of the ellipse. Hence $\max_r g(r)=n^{o(1)}$ uniformly even when the eccentricity and diameter of the image grow arbitrarily fast. The finite rank bound proves the theorem in full. [Uniform ellipse lemma in *Arithmetic-progression palettes and a uniform ellipse bound*](https://erdosproblems.ai/wiki/research/erdos_132/arithmetic_palettes)

**One arithmetic progression.** The same conclusion holds for every $n$-point planar set whose squared distances, including zero, lie in one arithmetic progression of at most $n^C$ terms. If the set has three noncollinear points $a,b,c$, the map
$$
z\longmapsto \bigl(|z-a|^2-|z-b|^2,\ |z-a|^2-|z-c|^2\bigr)
$$
is invertible affine, since its linear parts are $2(b-a)\cdot z$ and $2(c-a)\cdot z$. Divide its coordinates by the nonzero step of the progression. Every image point then has integer coordinates in $[-n^C,n^C]^2$, and the affine-image result applies (absorbing the factor $2$ in the box side). For collinear sets every distance has a graph of maximum degree at most two, so all distances are rare, and an extreme point realizes at least $n-1$ of them.

## Lattices of irrational shape

Choose a basis $e_1,e_2$ of a planar lattice. The squared length of $xe_1+ye_2$ is
$$
Q(x,y)=a x^2+b xy+c y^2,
$$
where $a=|e_1|^2$, $b=2e_1\cdot e_2$ and $c=|e_2|^2$. Say the lattice has *irrational shape* if $a,b,c$ span a vector space of dimension at least two over $\mathbb Q$. Changing the lattice basis preserves this dimension, since the change and its inverse express the new coefficients as rational linear combinations of the old ones.

**Corollary.** Every $n$-point subset of a planar lattice of irrational shape, for $n\ge2$, has at least $1+\lfloor(n-2)/4\rfloor$ rare distances. The largest that many distance values are all rare. If $a,b,c$ are linearly independent over $\mathbb Q$, every realized distance is rare.

*Proof.* Each nonzero squared length in a lattice of irrational shape has at most four signed representations. This shell-size bound also follows from Fu and Pendleton's classification of multiplicities for two-dimensional tori. Here is a direct argument. Choose a rational basis $\alpha_1,\ldots,\alpha_h$ of the span of $a,b,c$. Write $Q=\sum_i\alpha_i F_i$, with $F_i$ rational homogeneous quadratic forms. The $F_i$ are linearly independent over $\mathbb Q$, since the coordinate columns of $a,b,c$ span $\mathbb Q^h$. [Fu and Pendleton, *Multiplicities of eigenvalues and quadratic representations of integers*](https://arxiv.org/abs/2603.14748)

Fix a represented squared length $s>0$. At its integer representations the values $u_i=F_i(x,y)$ are fixed by uniqueness of the rational coordinates of $s$. Choose $i$ with $u_i\ne0$ and any $j\ne i$. All representations lie on the zero set of the nonzero homogeneous quadratic $u_i F_j-u_j F_i$. Its nonzero real zeros lie on at most two lines through the origin. Each line meets the positive-definite ellipse $Q=s$ in at most two points. Thus $g(\sqrt{s})\le2$, and the finite bound with $G=2$ proves the first assertion.

If $a,b,c$ are independent, equality of squared lengths fixes $x^2,xy,y^2$ separately. These three values determine $(x,y)$ up to a simultaneous change of sign, including when one coordinate is zero. Hence $g(r)=1$ for every realized $r$, giving the last assertion. $\square$

An earlier public research note proves an overall count $R(P)\ge\lceil n/4\rceil$ for sets admitting a nonsimilarity affine deformation that preserves all equalities of pair distances. This covers every irrational-shape lattice above. Indeed, choose $F_i$ not proportional to $Q$. The positive-definite form $Q+\epsilon F_i$, for sufficiently small nonzero $\epsilon$, gives such a deformation because every equality of $Q$ on integer vectors also fixes $F_i$. The corollary here specifies which ranks are rare, a distinction that matters even when the earlier count is numerically larger. [Erdős Problems research wiki, *Linear rarity under equality-preserving affine deformation*](https://erdosproblems.ai/wiki/research/erdos_132/affine_deformations)

## Related work

Vesztergombi studied the multiplicity of the $k$th largest distance in general planar configurations. Erdős and Fishburn's Lemma 1(b) bounds the number of points one can remove to eliminate the diameter. Clemen, Dumitrescu and Liu prove the existence of a second rare distance for sets in convex position and under a size condition on the first two convex layers. Their Corollary 1.4 covers sets whose diameter is at most $n/(3\pi)$ times their minimum separation. They also use square grids to exhibit many high-multiplicity distances. The direction count above controls how many pairs realize *each* of the largest distances in the original set. In a filled convex lattice region the additional translation counts give finer estimates on both the number of rare distances and the multiplicity of a typical distance. [Vesztergombi (1987)](https://doi.org/10.1016/0012-365X(87)90027-6) · [Erdős and Fishburn (1996), Lemma 1](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Erdos2.pdf) · [Clemen, Dumitrescu and Liu (2025)](https://doi.org/10.1007/s10474-025-01562-y)

An earlier public research note obtains $R(P)\ge\lceil\log_2 n\rceil$ for arbitrary rational-coordinate planar sets, with no diameter bound. It also observes that a fixed directed diameter displacement occurs at most once, the case of the lemma with an empty sum. A companion note proves divergence whenever all squared distances fit in a single arithmetic progression with polynomially many terms, which includes the polynomial-diameter integer grids here. A third note obtains rank bounds for sets covered by few lines by fixing an extreme endpoint on each pair of parallel lines. The theorem here gives a nearly linear number of consecutive rare ranks by counting displacement vectors over the whole set. [Dyadic distances](https://erdosproblems.ai/wiki/research/erdos_132/dyadic_distances) · [Arithmetic-progression palettes](https://erdosproblems.ai/wiki/research/erdos_132/arithmetic_palettes) · [Line covers](https://erdosproblems.ai/wiki/research/erdos_132/line_covers)
