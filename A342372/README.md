# Three congruences for toroidal semiqueens

Walter Trump posed three congruence conjectures for the number $T(n,k)$ of unordered placements of $k$ mutually nonattacking semiqueens on an $n$ by $n$ torus. Theorem 1 proves his conjecture (8). Theorems 2 and 3 prove (9) and (10), respectively. Theorem 3 determines the parity of every entry. The companion paper gives a direct derivation of the known cyclic four-piece count and extends the fixed-size enumeration through seven pieces. [Original 2021 note, pp. 1–2](https://oeis.org/A342372/a342372_2.pdf) · [OEIS A342372](https://oeis.org/A342372) · [Fixed-size enumeration](enumeration.md)

Write $C_n=\mathbb Z/n\mathbb Z$. Negating the column coordinate converts the three attack coordinates into row $r$, column $c$, and symbol $r+c$. A placement is a set of cells in $C_n^2$ on which each of these three maps is injective. Equivalently, it is a partial transversal of the cyclic addition table. We use $1\le k\le n$, and $T(n,0)=1$ when an empty placement is needed.

[Proof manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex)

## 1. The residue modulo the board area

**Theorem 1.** For $1\le k\le n$,

$$
T(n,k)\equiv
\begin{cases}
(k-2)n^2/k &\text{if } k\text{ is an odd prime dividing }n,\\
0 &\text{otherwise}
\end{cases}
\pmod {n^2}.
$$

**Proof.** The translation group $C_n^2$ acts on placements. A translation fixing a marked cell is the identity. Since there are $k$ choices of marked cell in a placement, free orbits of marked placements give

$$ n^2\mid kT(n,k). \tag{1} $$

Projection of the stabilizer of any nonempty placement onto the row coordinate is injective. Indeed, a translation with zero row component must fix the unique occupied cell in each occupied row. Projection onto the column coordinate or onto the sum of the coordinates is injective for the same reason. In particular, each stabilizer is cyclic.

Fix a prime $p\mid n$. Write $p^a\parallel n$ and $m=n/p$. Let $P\le C_n^2$ be its subgroup of elements of $p$-power order, of size $p^{2a}$. Placements with trivial $P$-stabilizer occur in orbits of size $p^{2a}$. Every other placement is fixed by a unique subgroup of order $p$, because its stabilizer is cyclic. In the subgroup of elements killed by $p$, the order-$p$ groups that are injective on all three coordinates are exactly

$$ H_u=\langle (m,um)\rangle,\qquad u\in\mathbb F_p\setminus\{0,-1\}. $$

Indeed the row component of a generator can be normalized to $m$. The column and sum components then require $u\ne0,-1$. This gives $p-2$ groups, including zero choices at $p=2$.

For each admissible $H_u$, its cell orbits have size $p$. An orbit projects under reduction modulo $m$ to a single cell, and runs through all $p$ lifts of its row, its column, and its symbol. Each quotient cell has $p^2$ lifts and therefore splits into $p$ such orbits. Two different orbits can coexist precisely when their quotient cells have distinct rows, columns, and symbols. Consequently the number of placements fixed by $H_u$ is zero unless $k=pj$, in which case it is $p^jT(m,j)$. Distinct admissible subgroups have disjoint sets of fixed nonempty placements by the uniqueness above. We have proved

$$
T(n,k)\equiv
\begin{cases}
(p-2)p^jT(m,j)& k=pj,\\
0 &p\nmid k
\end{cases}
\pmod {p^{2a}}. \tag{2}
$$

For $p=2$ the residue is zero. Suppose $p$ is odd. If $k=p$, then $T(m,1)=m^2$, giving the residue $(p-2)n^2/p$. If $k=pj$ with $j\ge2$, equation (1) on the smaller board gives $p^{2(a-1)}\mid jT(m,j)$. We have $v_p(j)\le j-2$. For $j=2$ this holds since $p$ is odd. For $j\ge3$ it follows from $3^{j-2}\ge j$ and $3^{v_p(j)}\le p^{v_p(j)}\le j$. Hence $p^{2a}\mid p^jT(m,j)$. This proves the claimed congruence modulo each prime-power factor $p^{2a}$ of $n^2$. In the exceptional case $k=p$, $(p-2)n^2/p$ is a multiple of the square of every other prime-power divisor of $n$. The Chinese remainder theorem finishes the proof. $\square$

## 2. Divisibility by three

**Theorem 2.** If $3\mid n$ or $k\equiv2\pmod3$, then $3\mid T(n,k)$.

**Proof.** The cyclic group of column translations acts freely on nonempty placements. A translation preserving an occupied row must fix its sole piece if it preserves the placement. Thus $n\mid T(n,k)$ and the first case follows.

If $3\nmid n$, write a cell as a triple $(r,c,-r-c)$. Cycling its coordinates preserves nonattacking placements. A fixed cell has the form $(x,x,x)$ with $3x=0$, so the origin is the unique fixed cell. Every invariant placement is a union of three-cell orbits and possibly the origin. For $k\equiv2\pmod3$ there are no invariant placements, so all orbits of placements have size three. $\square$

## 3. Parity of each placement count

**Theorem 3.** For odd $n$ and $0\le k\le n$,

$$T(n,k)\equiv {n\choose k}\pmod2.$$

For even $n$, every positive-size count is even.

**Proof.** Transpose the addition table. If a transpose-invariant placement contained an off-diagonal cell $(r,c)$, it would also contain $(c,r)$, with the same symbol. Its cells must therefore be diagonal. For odd $n$, the diagonal symbols $2r$ are all distinct, so every $k$-subset of the diagonal is a valid fixed placement. All other placements occur in pairs. For even $n$ use $n\mid T(n,k)$ for $k>0$. $\square$

If $2^a\mid n+1$ with $a\ge1$, the lowest $a$ binary digits of $n$ are all one. Over $\mathbb F_2$ the identity $(1+x)^n=\prod_{i:n_i=1}(1+x^{2^i})$ for $n=\sum_i n_i2^i$ shows that ${n\choose h}$ is odd whenever $0\le h<2^a$. Taking $h=n-k$ proves oddness throughout $n-2^a<k\le n$, including the source's range $k>n-a$.

## Verification and related work

`python3 verify.py` checks all three statements by an independent row-by-row enumeration on small boards. It also checks the fixed-size formulas. The proofs of the congruences above are entirely mathematical. [Verifier](verify.py)

The full-transversal case $k=n$ has older results. McKay, McLeod and Wanless treated parity and divisibility by three for full transversals. Wanless records these as Theorems 10 and 11 in his 2007 survey. The statements proved here quantify over partial placements of every size and answer the numbered questions in Trump's note. [Wanless, *Transversals in Latin squares*, pp. 179–180](https://mfoi2017.math.md/files/qrs/v15-n1/v15-n1-%28pp169-190%29.pdf)

Stones and Wanless previously established the board-area residue for full placements via canonical orthomorphisms, and published the cyclic fixed-size polynomials through six pieces. Their general partial-placement divisibility gives $n^2/\gcd(n,k)\mid T(n,k)$ for $k<n$. Equation (2) supplies the prime-power count needed for the residue modulo the whole board area. [Full placements (2010)](https://doi.org/10.1016/j.ffa.2010.04.001) · [Partial orthomorphisms (2012)](https://doi.org/10.1007/s00026-012-0137-6)
