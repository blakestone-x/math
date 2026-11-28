# A binary digit formula for Sun’s Hankel determinants modulo 8

Christopher Beach proved positivity and the full residue law modulo four in 2026. He left the class of indices congruent to one modulo four open for Sun’s modulo-eight assertion. The proof below establishes a residue of three throughout that class. [Beach’s paper](https://doi.org/10.5281/zenodo.24438853)

Let \(C_k=\binom{2k}{k}/(k+1)\), \(h_j=\sum_{k=0}^j\binom jk^2C_k\), and \(H_n=\det(h_{i+j})_{0\le i,j\le n}\). This is [OEIS A228456](https://oeis.org/A228456/internal), whose first conjecture includes the assertion that 7 never occurs modulo 8.

**Theorem.** For \(m\ge0\),
\[
H_{4m+1}\equiv3,\qquad H_{4m+3}\equiv1\pmod8.
\]
Write \(m=\sum_{j\ge0}t_j2^j\), with binary digits \(t_j\). Then
\[
H_{2m}\equiv1+4\left(t_1(1-t_0)+\sum_{j\ge2}t_j(1-t_{j-2})\right)\pmod8.
\]
Among the first \(N\) determinants, residues 1, 3 and 5 have counts \(N/2+O(\sqrt N),N/4+O(1),N/4+O(\sqrt N)\), respectively. Every determinant is strictly positive.

## From Hankel determinants to a rational function

Use \(\operatorname{CT}\) for the constant coefficient in \(x,y\). Put \(u=x+x^{-1}\), \(W=(1+uy)(1+u/y)\). Then
\[
 h_j=\operatorname{CT}(1-x^2)W^j.
\]
Indeed the constant coefficient in \(y\) is \(\sum_k\binom jk^2u^{2k}\), and \(\operatorname{CT}_x(1-x^2)u^{2k}=C_k\). For positivity, put \(x=e^{i\theta},y=e^{i\phi}\). In the torus integral the weight \(1-x^2\) may be replaced by \(1-\cos(2\theta)=2\sin^2\theta\), by symmetry in \(\theta\). Thus \(h_j\) is the moment of the real variable \(W=|1+2\cos\theta\,e^{i\phi}|^2\) with a positive measure. It has infinite support, since near \(\theta=\pi/3\) the weight is positive and varying \(\phi\) over \((0,\pi)\) gives an interval of values. Consequently the integral of \(p(W)^2\) is strictly positive for every nonzero real polynomial \(p\), proving positivity of the Gram determinant \(H_n\).

Let \(L(X^j)=h_j\). Choose the monic integral polynomials \(P_i(X)=U_{2i}(\sqrt{X-1}/2)\), where \(U_r\) is the Chebyshev polynomial of the second kind. They obey
\[
P_0=1,\quad P_1=X-2,\quad P_{i+1}=(X-3)P_i-P_{i-1}\quad(i\ge1),
\qquad P_iP_j=\sum_{k=|i-j|}^{i+j}P_k.
\]
The product identity follows by multiplying \(U_{2i}((z+z^{-1})/2)=\sum_{a=-i}^{i}z^{2a}\) and the analogous sum for \(j\). Put \(d_k=L(P_k)\). Since \(\binom jk^2\equiv\binom jk\pmod2\), the functional obeys \(L(p(X))\equiv\operatorname{CT}_x(1-x^2)p(1+u^2)\pmod2\). Applying the Laurent formula for \(U_{2k}\) gives \(d_0=1\) and \(d_k\equiv0\pmod2\) for \(k>0\).

Transform the monomial basis to \(P_0,\ldots,P_n\), preserving the determinant by monicity. The resulting Gram matrix \(G\) has entries \(G_{ij}=\sum_{k=|i-j|}^{i+j}d_k\). Every truncation is the identity modulo 2. Let \(H_{-1}=1\) and \(R_n=H_n/H_{n-1}\) in \(\mathbb Z/8\mathbb Z\). Apply the Schur complement to the last row and column. The preceding inverse is the identity modulo 2, and the off-diagonal vector is even, so its quadratic contribution modulo 8 is the sum of squares of the vector entries. Every even \(v\) satisfies \(v^2\equiv2v\pmod8\), giving
\[
R_n\equiv\sum_{k=0}^{2n}d_k-2\sum_{i=0}^{n-1}\sum_{k=n-i}^{n+i}d_k
\equiv\sum_{k=0}^{2n}(-1)^k d_k\pmod8.
\]
In the double sum the multiplicity of \(k\) is \(\min(k,2n-k)\), congruent to \(k\) modulo 2. The evenness of each positive-index \(d_k\) proves the last congruence. The same formula holds at \(n=0\).

The recurrence gives \(\sum P_k(X)t^k=(1+t)/(1-(X-3)t+t^2)\). Accordingly \(R_n\) is the coefficient of \(t^{2n}\) in
\[
 \operatorname{CT}\frac{1-x^2}{Q},\qquad
 Q=1-t(x^2+x^{-2}+xy+x/y+y/x+1/(xy))+t^2.
\]
Indeed taking the even coefficient of \((\sum d_k t^k)/(1+t)\) gives the alternating sum above, and \(W-3=x^2+x^{-2}+xy+x/y+y/x+1/(xy)\).

## Finite certificate for every index

Work modulo 8. For \(b=0,1\), the operator \(\Lambda_b\) sends a term \(t^a x^c y^d\) to \(t^{(a-b)/2}x^{c/2}y^{d/2}\) if \(a\equiv b,\ c\equiv d\equiv0\pmod2\), and to zero otherwise. Each sequence state has a numerator \(A\) and means \(u(n)=[t^n]\operatorname{CT}(A/Q^4)\). Its digit-\(b\) successor denotes \(u(2n+b)\) and has numerator \(\Lambda_b(AQ^4)\). This follows from \(Q^8\equiv Q(t^2,x^2,y^2)^4\pmod8\). To see the congruence, write \(Q^2=Q(t^2,x^2,y^2)+2E\) and raise to the fourth power. The zero-index output of a state is its numerator’s constant coefficient in all three variables, since \(Q(0,x,y)=1\). The initial numerator for \(R_n\) is \(\Lambda_0((1-x^2)Q^7)\).

Starting from that numerator and repeatedly adjoining each of its two successors gives 33 distinct numerators \(A_j\), each with an odd output. Index each state in order of discovery, digit 0 first, and write \(T_b(j)\) for its successor. Let \(u_j(n)=[t^n]\operatorname{CT}(A_j/Q^4)\) and \(F_j(n)=\prod_{0\le k<n}u_j(k)\). Every \(u_j\) is a subsequence of the odd ratio sequence. Every odd residue has square 1 modulo 8, so repeated factors in a product cancel in pairs.

A pair \((P,V)\) of subsets of \(\{0,\ldots,32\}\) represents the sequence \(\prod_{j\in P}F_j(n)\prod_{j\in V}u_j(n)\). For a subset \(P\), let \(T_b P\) be the set image with even multiplicities removed, and write \(\triangle\) for symmetric difference. Substitution \(n\mapsto2n+b\) gives the new subsets
\[
 P'=T_0P\triangle T_1P,\qquad V'=\begin{cases}T_0V,& b=0,\\ T_1V\triangle T_0P,& b=1.\end{cases}
\]
This is the split of the prefix product into even and odd indices. The starting pair \((\{0\},\{0\})\) represents \(H_n=\prod_{k\le n}R_k\). Its closure has 128 states. Assign each state its value at zero, and repeatedly refine this partition by the classes of the digit-0 and digit-1 successors. The stabilized partition gives the following 13-state table. Reading binary digits from least significant to most significant, start in state 0 and output the value in the final row reached. Higher zero digits preserve each row’s output.

| State | Output | Digit 0 | Digit 1 |
|---:|---:|---:|---:|
|0|1|1|2|
|1|1|3|4|
|2|3|5|6|
|3|1|3|7|
|4|1|8|4|
|5|3|5|5|
|6|1|6|6|
|7|5|9|4|
|8|1|3|10|
|9|5|11|7|
|10|1|8|12|
|11|5|11|10|
|12|5|9|12|

All finite enumeration in this step is reproduced by `python3 verify.py`. The accompanying `certificate.json` includes the complete terms of every numerator (triples of exponents followed by the coefficient), both digit transitions and the output of every numerator and product state, both product-subset bit masks, and each product state’s minimized class. The standard-library verifier checks the entire certificate directly from \(Q\).

## Reading the binary formula and the frequencies

For odd \(n\) the first digit gives state 2. The next digit leads to absorbing state 5 or 6, proving the two odd residue classes. For \(n=2m\) the first digit gives state 1. Processing the low bit \(t_0\) of \(m\) gives state 3 or 4. Group the eight reachable states into pairs. In each pair the first state has residue 1 and the second has residue 5. Let a minus sign indicate that a transition exchanges the two positions within the destination pair.

| Pair | States | Remembered bits, older first | Digit 0 | Digit 1 |
|---|---|---|---|---|
| A | (3, 11) | 00 | A | −D |
| B | (4, 12) | 11 | C | B |
| C | (8, 9) | 10 | A | D |
| D | (10, 7) | 01 | C | −B |

The initial remembered digits are \((t_0,t_0)\), with positive sign, and subsequent updates shift in one new bit. The sign changes precisely when the new digit is 1 and the older remembered digit is 0. The first possible sign change contributes \(t_1(1-t_0)\), and the subsequent changes contribute \(t_j(1-t_{j-2})\). This proves the stated formula.

To count the even residues, attach sign \(+1\) to output 1 and \(-1\) to output 5. Summing the two digit transitions gives the signed matrix on \((A,B,C,D)\)
\[
 M=\begin{pmatrix}1&0&0&-1\\0&1&1&0\\1&0&0&1\\0&-1&1&0\end{pmatrix},\qquad MM^{\mathsf T}=2I.
\]
In an aligned interval of \(2^q\) consecutive values of \(m\), the bottom \(q\) digits range freely, and the higher digits form a fixed word. For \(q\ge1\), its signed sum is \((1,1,0,0)M^{q-1}g\), with \(g\in\{1,-1\}^4\) obtained by processing that fixed higher word from each positive state. Consequently the signed sum has absolute value at most \(2\cdot 2^{q/2}\). The same bound covers a singleton interval. Decompose the first \(K\) integers into aligned dyadic intervals using the binary expansion of \(K\); there is at most one interval of each size. Summing the geometric series gives signed excess \(O(\sqrt K)\). This splits even indices equally between 1 and 5 up to that error. The odd indices have their stated fixed classes modulo 4, proving the frequencies.
