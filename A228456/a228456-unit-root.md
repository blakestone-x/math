# A unit-root reformulation of the split-prime branch of A228456

Let $p>3$ be prime, $p\equiv1\pmod3$ and $p=x^2+3y^2$ with $x\equiv1\pmod3$. Write
$$g=a+b+ab+a^{-1}+b^{-1}+(ab)^{-1},\qquad d_n=\operatorname{CT}g^n.$$
Then
$$\frac{d_{p^2-1}}{d_{p-1}}\equiv 2x-\frac{p}{2x}\pmod{p^2}.$$
Together with the split-prime result modulo $p$ in the companion manuscript, this gives a precise remaining determinant identity
$$(-1)^{(p-1)/2}H_{p-1}\stackrel{?}{\equiv} d_{p^2-1}/d_{p-1}\pmod{p^2}.$$
The equality marked with a question is open here.

## Proof of the unit-root evaluation

Take the projective curve $E$ cut out in $\mathbb P^1\times\mathbb P^1$ by the bihomogenization of the bidegree-$(2,2)$ polynomial
$$P(a,b)=abg=a(a+1)b^2+(a^2+1)b+a+1.$$
The projection to the first factor is a double cover. Its three homogeneous quadratic coefficients have no common zero, including at infinity. The branch quartic
$$a^4-4a^3-6a^2-4a+1$$
has discriminant $-2^{12}3^3$ and leading coefficient one. Thus $E$ is smooth and of genus one in every characteristic $p>3$. It has the rational point $(0,-1)$.

The interior lattice point of the anticanonical bidegree rectangle is $(1,1)$. The higher Hasse–Witt matrices in this case are the scalars
$$\alpha_s=[(ab)^{p^s-1}]P^{p^s-1}=d_{p^s-1},\qquad \alpha_0=1.$$
The anticanonical line bundle is generated at torus-fixed points, and the section $P$ itself is nonzero at the fixed point $(0,0)$. The Frobenius lift on $\mathbb Z_p$ is the identity. Theorems 5.1(2) and 5.3 of [Huang, Lian, Yau and Yu, Hasse–Witt matrices, unit roots and period integrals](https://arxiv.org/abs/1801.01189) consequently identify the limit of $\alpha_{s+1}/\alpha_s$ with the Frobenius unit root whenever $\alpha_1$ is a unit. They also give
$$\alpha_{s+1}/\alpha_s\equiv\alpha_s/\alpha_{s-1}\pmod{p^s}.$$
Thus $\alpha_2/\alpha_1$ gives that unit root modulo $p^2$, and $\alpha_1$ gives it modulo $p$.

Here $\alpha_1=d_{p-1}\equiv 2x\not\equiv0\pmod p$ by the Franel-sum congruence in the companion manuscript. The other Frobenius eigenvalue is divisible by $p$. Hence the Frobenius trace $t=p+1-\#E(\mathbb F_p)$ is $2x$ modulo $p$. Both $t$ and $2x$ lie in the interval $[-2\sqrt p,2\sqrt p]$, by the Hasse bound and the definition of $x$. Its length is less than $p$ for $p\ge17$, so $t=2x$. For $p=7,13$, the quartic model $v^2=a^4-4a^3-6a^2-4a+1$ has ten finite rational points and two points at infinity in each field, giving $t=-4,2$, respectively. The unit root $u$ now satisfies $u^2-2xu+p=0$, and so $u=2x-p/u\equiv 2x-p/(2x)\pmod{p^2}$.

## Scope of the determinant comparison

The higher Hasse–Witt matrix has size one here. Its definition gives no general identification with a $p\times p$ matrix of moments. For example, replace $g$ by $g'=g+(ab)^{-1}$ and use its unweighted moments $e_n=\operatorname{CT}(g')^n$. At $p=7$ the signed determinant of $(e_{i+j})_{0\le i,j<7}$ equals $25$ modulo 49, whereas $e_{48}/e_6$ equals $32$ modulo 49. Thus the missing comparison must use additional structure of the given moments.
