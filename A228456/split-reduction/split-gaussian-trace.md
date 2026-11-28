# Gaussian quadrature for the remaining Legendre trace

Write $p=3n+1>3$, $B=\binom{2n}{n}$, and $A(s)=P_n(1-2s)$. In the split-determinant reduction $C=(P_{2n}(1-2s)-A)/(3p)$, $D=\operatorname{quo}(C,A)$ over $\mathbb F_p$, and $E=D(0)+3\sum_{A(r)=0}D(r)$. The unresolved identity is $E=q_p(B)$, where $q_p(B)=(B^{p-1}-1)/p\bmod p$. An explicit expression using Gaussian integration nodes replaces the higher-degree Legendre polynomial.

In $\mathbb F_p$ put
$$
 L(s)=\sum_{j=1}^{p-1}s^j/j,\qquad
 R(s)=\int_0^1\frac{A(s)-A(t)}{s-t}\,dt .
$$
Integration of polynomials here means replacing $t^i$ by $1/(i+1)$. Only denominators $1,\ldots,n$ occur. Let $r_i$ be the $n$ roots of $A$ in the algebraic closure and $w_i=R(r_i)/A'(r_i)$. The roots are simple. Indeed $A(0)=A(1)=1$, and the Legendre differential equation at any other point excludes repeated roots since a root of multiplicity $2\le m\le n<p$ would force its second derivative to have order $m-2$, with the remaining terms having order at least $m-1$.

Then
$$
 3E=3\sum_i L(r_i)+
 \sum_i\frac{r_i^p}{A'(r_i)}
      \left(\frac{R(r_i)}{r_i}+3R'(r_i)\right).
$$
This field trace is in $\mathbb F_p$, even when individual nodes require an extension.

**Proof.** Write $A(s)=\sum a_i s^i$, with $a_i=(-1)^i\binom ni\binom{n+i}i$. Comparing residues gives
$$
 \sum_{i=0}^{n}\frac{a_i}{z-i}
 =(-1)^n\frac{(z+1)\cdots(z+n)}{z(z-1)\cdots(z-n)}.
$$
For $n<j<p$, evaluating at $z=j$ gives the coefficient of $s^j$ in $A L$. It also gives the coefficient of $s^j$ in $3C$. For $j\le 2n$, the numerator of the coefficient of the higher Legendre polynomial is $(-2n)_j(p-n)_j$, and removing its unique factor $p$ from the latter rising factorial leaves $(-1)^n n!(j-n-1)!\pmod p$. For $j>2n$ both sides vanish because $j+n\ge p$. For $0\le b<n$ one has $[s^{p+b}]A L=-[s^b]R$ by direct expansion of the integral. It follows that $3C-A L-s^p R$ has degree at most $n$. Thus, up to an additive constant,
$$
 3D(s)=L(s)+\sum_i w_i(s-r_i)^{p-1},
$$
using $R/A=\sum_iw_i/(s-r_i)$ and $\operatorname{quo}(s^p,s-r_i)=(s-r_i)^{p-1}$. Evaluation at zero plus three times the sum over roots annihilates the additive constant, since $1+3n=p$.

To simplify $\sum_{i,j}w_i(r_j-r_i)^{p-1}$, omit diagonal pairs, which contribute zero, and use $(r_j-r_i)^{p-1}=(r_j^p-r_i^p)/(r_j-r_i)$. The coefficient of $r_j^p$ then equals $\sum_{i\ne j}(w_i+w_j)/(r_j-r_i)$. The regular part of $R/A$ at $r_j$ is $R'(r_j)/A'(r_j)-w_j A''(r_j)/(2A'(r_j))$, and $\sum_{i\ne j}1/(r_j-r_i)=A''(r_j)/(2A'(r_j))$. Adding cancels the second derivative terms. This yields the displayed trace.

For the $p$-adic lifts of the Legendre roots, the finite-log trace satisfies $\sum_i L(r_i)\equiv(n-2\sum_i r_i^p)/p\bmod p$. This follows by expanding $[1-s^p-(1-s)^p]/p$ and using invariance of the roots under $s\mapsto1-s$. The general evaluation of the resulting trace as $q_p(B)$ remains open here.

**Verification.** The accompanying Python checker uses polynomial remainders and Newton sums to verify the proposed trace evaluation for every split prime through 997.
