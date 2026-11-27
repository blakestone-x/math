# Counting matrix similarity classes with a prescribed determinant

**Blake Stone · Proof developed with OpenAI Codex.**

Let $C_\delta(n)$ be the number of similarity classes of $2\times2$ matrices with entries in $\mathbb Z/n\mathbb Z$ and determinant $\delta$, where $\gcd(\delta,n)=1$. Conjugation is by the full invertible matrix group. For $m\mid n$, write $r_\delta(m)$ for the number of residues $s$ with $s^2\equiv\delta\pmod m$, taking $r_\delta(1)=1$.

**Theorem.** For every unit determinant $\delta$,

$$
C_\delta(n)=\sum_{m\mid n}\frac{n}{m}\,r_\delta(m).
$$

At $\delta=1$ this proves Ridouane Oudra's February 2026 conjecture in Robin Visser's OEIS entry A364847. The arithmetic function $r_1$ is A060594. The similarity classification used below is classical. Theorem 2.2 of Avni, Onn, Prasad and Vaserstein gives the scalar-plus-companion normal form over local principal ideal rings. We include its two-dimensional argument and count the classes with each prescribed unit determinant. [A364847](https://oeis.org/A364847) · [A060594](https://oeis.org/A060594) · [Avni et al., §2](https://arxiv.org/abs/0708.1608)

## A normal form at a prime power

Fix $n=p^k$ and write $R_j=\mathbb Z/p^j\mathbb Z$. First, any $2\times2$ matrix $B$ over $R_j$ that is nonscalar modulo $p$ is classified up to similarity by its trace $t$ and determinant $u$. Indeed, over $\mathbb F_p$ there is a vector $v$ for which $v,Bv$ are linearly independent. Otherwise every nonzero vector would be an eigenvector, and testing the two coordinate vectors and their sum would make $B$ scalar. Lifting $v$ gives a basis $(v,Bv)$ over $R_j$, since its determinant is a unit. By Cayley–Hamilton the matrix in this basis is

$$
\begin{pmatrix}0&-u\\1&t\end{pmatrix}.
$$

Conversely this matrix is nonscalar modulo $p$ for every choice of $t,u\in R_j$ and has precisely those invariants.

For a matrix $A$ over $R_k$, let $i$ be the largest integer in $[0,k]$ such that $A$ is scalar modulo $p^i$. At $i=0$ there is no restriction modulo $1$. When $i<k$, choose the unique representative $s$ with $0\le s<p^i$ of the scalar modulo $p^i$. Then

$$
A=sI+p^iB,\qquad B\in M_2(R_{k-i}),
$$

and $B$ is nonscalar modulo $p$. The pair $(i,s)$ is invariant under similarity. At fixed $(i,s)$, two such matrices are similar exactly when their residual matrices $B$ are similar over $R_{k-i}$. For the forward direction reduce a conjugating matrix. For the converse lift any conjugating matrix entry by entry to $R_k$; its determinant remains a unit, and multiplication by $p^i$ converts the conjugacy modulo $p^{k-i}$ into the required conjugacy modulo $p^k$. The remaining case $i=k$ consists of scalar matrices.

## Counting with fixed determinant

For $i=0$ we are counting matrices nonscalar modulo $p$. Their determinant is prescribed and their trace is arbitrary, so there are $p^k$ classes. For $i=k$ each scalar $sI$ is its own class and contributes exactly when $s^2\equiv\delta\pmod{p^k}$.

Now take $0<i<k$. Write $t=\operatorname{tr}(B)$ and $u=\det(B)$ in $R_{k-i}$. Expanding a $2\times2$ determinant gives

$$
\delta\equiv s^2+p^ist+p^{2i}u\pmod{p^k}.
$$

Thus the necessary condition on $s$ is $s^2\equiv\delta\pmod{p^i}$. For any of the $r_\delta(p^i)$ residues satisfying it, $s$ is a unit since $\delta$ is. After division by $p^i$, the equation becomes

$$
st+p^iu\equiv(\delta-s^2)/p^i\pmod{p^{k-i}}.
$$

Every one of the $p^{k-i}$ choices of $u$ gives exactly one $t$. The normal form supplies one class for every such pair and no others. Combining all three cases gives

$$
C_\delta(p^k)=\sum_{i=0}^{k}p^{k-i}r_\delta(p^i).
$$

For coprime moduli the Chinese remainder theorem applies to matrix entries and conjugating matrices, so the numbers of classes multiply. The root counts $r_\delta$ likewise multiply. Expanding the product of the local formulas proves the theorem, including $n=1$ with its single class. $\square$

For example, modulo $8$ the successive root counts for determinant $1$ are $1,1,2,4$ at moduli $1,2,4,8$. This gives $8+4+4+4=20$ classes. For determinant $3$ the counts are $1,1,0,0$, giving $12$ classes.
