# Counting four to seven toroidal semiqueens

Let $T(n,k)$ count unordered $k$-piece placements with distinct rows, columns, and diagonals of one fixed slope on the torus. Walter Trump asked for a formula when $k=4$ after deriving the first three columns of the triangle. We give a direct count for any Latin square, then evaluate the columns through $k=7$ for the addition table of any finite abelian group. Stones and Wanless already published the cyclic polynomials through six pieces, writing $\omega(n,n-k)$ for $T(n,k)$. The fourth-column argument below works for arbitrary Latin squares. The partition calculation recovers those cyclic columns, evaluates the seventh, and distinguishes noncyclic abelian groups through their torsion. [Stones and Wanless, *Annals of Combinatorics* (2012)](https://doi.org/10.1007/s00026-012-0137-6) [Trump's original question, p. 1](https://oeis.org/A342372/a342372_2.pdf) · [OEIS A342372](https://oeis.org/A342372)

## 1. Four pieces in a Latin square

For an order-$n$ Latin square $L$, write $M_j$ for the number of unordered size-$j$ partial transversals. Each such set occupies distinct rows, columns and symbols. Let $I(L)$ be the number of its $2\times2$ subsquares using two symbols, usually called *intercalates*.

**Theorem 1.** For every Latin square of order $n\ge1$,

$$
4M_4=(n^2-9n+24)M_3-n^2\big((n-2)^3+1\big)+4I(L),
\qquad
M_3=\frac{n^2(n-1)(n-2)(n^2-6n+10)}{6}.
$$

For the cyclic addition table, $M_j=T(n,j)$ and $4I(L)=n^2$ when $n$ is even, $0$ when $n$ is odd. In particular, the only periodic correction to $T(n,4)$ is a single parity term.

**Proof.** Given a partial transversal $S$ of size $j$, let $b(S)$ count cells whose three coordinates are all used by $S$. The cells excluded from extending $S$ form the union of its used rows, used columns, and used symbol classes. Each union of classes of a single kind has size $jn$. Intersecting two different kinds gives exactly $j^2$ cells, by the Latin property. Inclusion–exclusion leaves

$$n^2-3jn+3j^2-b(S)$$

possible extensions. Any cell counted by $b(S)$ outside $S$ meets different members of $S$ in its three coordinates, since any two coordinates identify a cell. Thus $b(S)=j$ for $j=1,2$. Dividing the extension counts by $j+1$ gives $M_2=n^2(n-1)(n-2)/2$ and the displayed $M_3$.

For $j=3$, write $b(S)=3+h(S)$. To sum $h(S)$, fix a cell $w$. A contribution consists of three mutually nonattacking cells $P,Q,R$ sharing respectively its row, column, and symbol, each different from $w$. There are initially $(n-1)^3$ choices. The only possible conflicts are $P,Q$ sharing a symbol, $P,R$ sharing a column, and $Q,R$ sharing a row. Each single conflict has $(n-1)^2$ choices. Each pair of conflicts has $n-1$ choices, since one of the three cells determines the other two by the Latin property. A triple conflict means that $w,P,Q,R$ are an intercalate. Summing over $w$ counts each intercalate four times. Hence

$$
\sum_{|S|=3} h(S)
=n^2\big((n-1)^3-3(n-1)^2+3(n-1)\big)-4I(L)
=n^2\big((n-2)^3+1\big)-4I(L).
$$

Summing the extension count and dividing by four proves the formula. In the cyclic addition table an intercalate through $(r,c)$ has other row $r+d$ and other column $c+d$, with $d\ne0$ and $2d=0$. Such a $d$ exists uniquely for even $n$ and never for odd $n$. $\square$

## 2. A fixed-size formula for finite abelian groups

Let $G$ be finite abelian of order $n$. Write $M_k(G)$ for the size-$k$ partial transversals in its addition table. Define $t_d=|\{g\in G:dg=0\}|$. For the cyclic board, $t_d=\gcd(d,n)$.

**Theorem 2.** For $4\le k\le7$,

$$
M_k(G)=\frac{n^2}{k!}\sum_D P_{k,D}(n)\prod_{d\in D}t_d.
$$

The table gives the coefficients of $P_{k,D}$ in ascending order of degree. A dash denotes the empty tuple, whose product is one. Unlisted terms vanish.

| $k$ | $D$ | Coefficients, constant term first |
|---:|:---|:---|
| 4 | — | 516, -1260, 1154, -534, 135, -18, 1 |
| 4 | 2 | 6 |
| 5 | — | 26112, -69840, 72580, -40740, 13862, -2970, 395, -30, 1 |
| 5 | 2 | 960, -360, 30 |
| 6 | — | 2227680, -6360480, 7131232, -4459740, 1773420, -475290, 87682, -11055, 915, -45, 1 |
| 6 | 2 | 168480, -106200, 24300, -2430, 90 |
| 6 | 3 | 1440 |
| 7 | — | 290897280, -876214080, 1032823344, -690701256, 301696192, -92076600, 20302524, -3275496, 385042, -32235, 1827, -63, 1 |
| 7 | 2 | 37336320, -30360960, 10099320, -1785420, 177660, -9450, 210 |
| 7 | 2, 2 | 20160 |
| 7 | 3 | 846720, -181440, 10080 |
| 7 | 4 | 40320 |

For example, the entry for $k=4$ says

$$24T(n,4)=n^2\left(n^6-18n^5+135n^4-534n^3+1154n^2-1260n+516+6\gcd(2,n)\right).$$

It gives $T(6,4)=1224$ and $T(7,4)=8869$. The nontrivial group parameters first appear at four pieces for $t_2$, six for $t_3$, and seven for $t_4$ and $t_2^2$.

**Proof.** Temporarily order the $k$ pieces. A cell can be written as three coordinates $x_i,y_i,z_i$ satisfying $x_i+y_i+z_i=0$. Let $A,B,C$ range independently over the set partitions of $\{1,\ldots,k\}$. For a partition $A$ put

$$w(A)=\prod_{U\in A}(-1)^{|U|-1}(|U|-1)!.$$

For any fixed tuple of $k$ coordinates, the sum of $w(A)$ over partitions on whose blocks the tuple is constant is one if the coordinates are distinct and zero otherwise. To see this, $w(A)$ is the sum of the signs of the permutations with cycle partition $A$. Permutations preserving all coordinate values form a product of symmetric groups. Their signs sum to zero as soon as one value occurs twice. Applying this identity to all three coordinates expresses $k!M_k(G)$ as a sum with weights $w(A)w(B)w(C)$.

Take one variable for each block of $A,B,C$. Each label $i$ supplies the equation $x_{A(i)}+y_{B(i)}+z_{C(i)}=0$. Eliminate one $z$ per block of $C$ by subtracting a representative equation from the others. The resulting integer matrix has $v=|A|+|B|$ columns. By integer row and column operations with determinant $\pm1$, put it in diagonal form with nonzero entries $d_1,\ldots,d_s$, chosen positive. Such operations induce automorphisms over $G$. Each unconstrained variable contributes $n$ choices and each nonzero diagonal contributes $t_{d_i}$. The count for the partition triple therefore equals

$$n^{v-s}\prod_{i=1}^s t_{d_i}.$$

This is a formula at every fixed $k$. To obtain the displayed coefficients, sum the weights of the triples giving each exponent and tuple of nonunit diagonal entries. The supplied standard-library program performs this finite integer calculation. It groups triples by simultaneous relabeling of their $k$ labels, multiplying the orbit sizes successively for $A$, for $B$ under the stabilizer of $A$, and for $C$ under the stabilizer of $(A,B)$. It verifies that their sum is the cube of the number of set partitions. Its diagonalization uses integer division and unimodular swaps, reducing the absolute pivot whenever there is a nonzero remainder. The complete calculation runs with `python3 partitions.py 7`. [Coefficient derivation](partitions.py) · [Independent counts and checks against the printed table](verify.py) $\square$

Specializing to $C_n$ gives quasipolynomials with respective periods dividing $2,2,6,12$ for $k=4,5,6,7$. The degree of the $k$th column is $2k$ and its leading coefficient is $1/k!$, as can also be read from the table.
