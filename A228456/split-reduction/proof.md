# A Legendre-polynomial reduction for the split-prime branch of A228456

This note gives an exact reduction of the still-unproved split-prime congruence, including a proof that its Catalan weight may be removed. Write \(p=6k+1\) for a prime, \(L=2k=(p-1)/3\), and \(H_n\) for the original A228456 determinant. Define
\[
 A(s)=P_L(1-2s),\qquad C(s)=\frac{P_{2L}(1-2s)-P_L(1-2s)}{3p},
 \qquad a=54^L\binom{2L}{L},
\]
where \(P_j\) is the Legendre polynomial. Both polynomials are \(p\)-integral, and their reductions below are in \(\mathbb F_p[s]\). Let \(D\) be the polynomial quotient in the division of \(C\) by \(A\). Set
\[
 E=D(0)+3[s^{-1}]_{\infty}\frac{C'(s)}{A(s)}.
\]
The subscript denotes expansion in decreasing powers of \(s\) at infinity. Then
\[
 (-1)^{(p-1)/2}H_{p-1}\equiv a^p(1-pE)\pmod{p^2}.
\]
The same formula holds for the unweighted Hankel determinant formed from the numbers of closed walks on the triangular lattice.

## 1. Translated moments

Put \(u=x+x^{-1}\), \(W=(1+uy)(1+u/y)\), and \(g=W-3\). The constant term \(\operatorname{CT}_{x,y}(1-x^2)W^n\) is the A086618 moment by binomial expansion. Translation by 3 preserves every Hankel determinant by a monic triangular change of basis. The six terms of \(g=x^2+x^{-2}+xy+x/y+y/x+1/(xy)\) are permuted transitively by triangular lattice symmetries. Explicitly, set \(v=x/y,w=xy\), so the six terms become \(v,w,vw,v^{-1},w^{-1},(vw)^{-1}\). Exponent rotation cyclically permutes the vectors \((1,0),(1,1),(0,1),(-1,0),(-1,-1),(0,-1)\), preserving constant coefficients. If \(d_n=\operatorname{CT}g^n\), the translated moments are therefore \(b_n=d_n-d_{n+1}/6\).

The generating function of \(d_n\) is
\[
 \sum_{n\ge0} d_n z^n = \sum_{j\ge0} c_j z^{2j}(1+2z)^j,
 \quad c_j=\binom{2j}{j}\binom{3j}{j}.
\]
Indeed, \(g+2=(1+v)(1+w)(1+(vw)^{-1})\) has Franel moments \(f_n=\sum_j\binom nj^3\). Their expansion \(f_n=\sum_j c_j\binom{n+j}{3j}2^{n-2j}\) gives the generating function \(\sum_j c_j z^{2j}(1-2z)^{-3j-1}\) for the \(f_n\). The binomial translation by \(-2\) gives the displayed generating function for \(d_n\). The Franel expansion appears in [Mao and Liu, equation (2.4)](https://arxiv.org/abs/2111.08775).

## 2. A trace formula

Suppose \(m_i=[z^i](U+pV)\pmod{p^2}\) for \(0\le i\le2p-2\), where \(U,V\in\mathbb Z_{(p)}[z]\), \(\deg U=p-1\), \(u=[z^{p-1}]U\) is a unit, and \(\deg V\le2p-2\). Reverse columns of the \(p\)-square Hankel matrix to get the Toeplitz matrix with \(ij\)-entry \(m_{p-1+i-j}\), indexed from zero. Its upper triangular part has diagonal \(h=m_{p-1}\), and its strictly lower part has entries divisible by \(p\). First-order determinant expansion gives the determinant of the reversed matrix as
\[
 h^p\left(1+p\sum_{r=1}^{p-1}(p-r)v_r[z^{p-1+r}]V\right)\bmod p^2,
 \qquad v_r=[w^r]\frac1{w^{p-1}U(1/w)}\pmod p.
\]
Indeed each \(r\)-th diagonal in the trace of the inverse upper part times the lower part contributes \(p-r\) equal terms. We may replace \(h^p\) with \(u^p\). The sum in parentheses after the factor \(p\) is
\[
 -\operatorname{CT}_{w=0}w\left(\frac{1}{w^{p-1}U(1/w)}\right)'w^{p-1} V(1/w)
 =-\operatorname{CT}_{z=\infty}\frac{(zV(z))'}{U(z)}\pmod p.
\]
For the equality, substitute \(z=1/w\), use \(p-1\equiv-1\), and use the vanishing constant coefficient of \(z\,d(V/U)/dz\). Changing lower coefficients of \(U\) by multiples of \(p\), while adjusting \(V\) to compensate, preserves the result. In fact the derivative of \(z\) times any degree-at-most-\(p-1\) change to \(V\) has zero constant coefficient after division by \(U\) modulo \(p\). Thus it suffices for \(U+pV\) to match the desired moments modulo \(p\) up to degree \(p-1\) and modulo \(p^2\) from degree \(p\) through \(2p-2\).

## 3. The Legendre pair

Set \(s(z)=27z^2(1+2z)\). The unweighted generating function is \(\sum_{j\ge0}f_j s(z)^j\) with \(f_j=(1/3)_j(2/3)_j/(j!)^2\) and rising factorials. The Legendre identity gives \(P_m(1-2s)=\sum_{j=0}^m (-m)_j(m+1)_j s^j/(j!)^2\). The parameters for \(A\) may be written \((-L,L+1)\) and those for \(P_{2L}\) may be ordered \((2L+1,-2L)\). The two pairs coincide modulo \(p\), so \(C\) is \(p\)-integral. Also \(1/3=-L+p/3\) and \(2/3=-2L+2p/3\). Thus the unweighted moments have the low-degree residues of \(A(s(z))\). In the range \(L<j\le2L\), the rising factorial for the first parameter contains exactly one factor divisible by \(p\), equal to \(p/3\) in \(f_j\) and \(p\) in \(P_{2L}\). The other factors coincide modulo \(p\). Consequently \(f_j\equiv p[s^j]C\pmod{p^2}\) here. In \(2L<j<p\) both rising factorials are divisible by \(p\), so \(f_j\equiv0\pmod{p^2}\). No larger \(j\) contributes below degree \(2p\) in \(z\). Lower \(j\le L\) contribute only at degrees at most \(p-1\). These observations verify the weakened matching conditions of Section 2 for \(U=A(s(z)),V=C(s(z))\), also through degree \(2p-1\) where needed for the weight. Their constant coefficients are 1 and 0. The leading coefficient of \(U\) is \(a\), since \(L\) is even.

## 4. Removal of the Catalan weight

For moments \(d_n-\tau d_{n+1}\), take \(U_\tau=(1-\tau/z)U+\tau/z\) and \(V_\tau=(1-\tau/z)V\). These are polynomials with the same leading coefficients as \(U,V\). The difference of the constants appearing in the trace formula is
\[
 \operatorname{CT}_\infty\left(\frac{(zV_\tau)'}{U_\tau}-\frac{(zV)'}{U}\right)
 =\tau\operatorname{CT}_\infty\frac{V}{(z-\tau)U}.
\]
To verify this, the left integrand before extracting the constant is \(\tau(V(U-1)/z-V')/(U U_\tau)\). The terms involving \(V/z\) and \(V'\) have negative degree. The remaining term is \(\tau V/((z-\tau)U+\tau)\). Dropping the final \(\tau\) in this denominator affects only negative degrees, since \(\deg V\le2p-2\) and \(\deg((z-\tau)U)=p\).

Since \(V/U=C(s(z))/A(s(z))=D(s(z))+O(z^{-3})\), the right side equals \(D(s(\tau))-D(0)\) by polynomial division by \(z-\tau\). Both Legendre degrees are even, so \(A(1-s)=A(s)\) and \(C(1-s)=C(s)\). Polynomial division then gives \(D(1-s)=D(s)\). Since \(s(1/6)=1\), the difference vanishes for the required weight. The same holds at \(\tau=-1/3,-1/2\), for which \(s(\tau)=1,0\), respectively.

Finally \(\operatorname{CT}_{\infty}V/U=D(0)\). Polynomial division of \(C'/A\) gives a polynomial plus \(\gamma/s+O(s^{-2})\). The polynomial times \(z s'(z)\) has constant coefficient zero, and \(z s'(z)/s(z)\) tends to 3 at infinity. Hence \(\operatorname{CT}_{\infty}zV'/U=3\gamma\), proving the stated formula for \(E\).

## The remaining evaluation

If \(p=x^2+3y^2\) and \(x\equiv1\pmod3\), Sun predicts that this signed determinant is \(2x-p/(2x)\) modulo \(p^2\). Yeung’s binomial congruence makes the remaining assertion equivalent to
\[
 a^p(1-pE)\stackrel{?}{\equiv}\binom{3k}{k}
 \left(1+\frac{2^p-2}{3}-\frac{3^p-3}{4}\right)\pmod{p^2}.
\]
The reduction above does not evaluate this last residue. The companion standard-library script evaluates the Legendre expression and compares it directly with the original determinant for every split prime through 199. Yeung’s formula is recalled on page 2 of [Sun’s survey](https://arxiv.org/pdf/1103.4325).
