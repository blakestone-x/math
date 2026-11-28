# Shifted Hankel determinants of Catalan powers

The manuscript proves Cigler’s Conjecture 4 on signed polynomiality for every positive power and every integer shift. It also proves the polynomiality, exact degree and reciprocal sign in Johann Cigler's Conjecture 15 for every even power and every proposed shift. It proves the corresponding assertions in Conjecture 16 for every odd power and shift, with the single degree correction at power one and shift zero. The numerator there is 1. That exception was recorded previously by TrureTuring. [Manuscript](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Cigler's original conjectures, version 2, Section 3](https://arxiv.org/abs/2308.07642v2) · [Earlier boundary counterexample](https://www.trureturing.org/research/cigler-sixteen-literal-numerator-degree/)

For large negative shifts the proof combines the earlier backward-shift identity of Fulmek and Cigler with reflection in matrix size. This accounts for every initial size, including the empty determinant. [Cigler on backward shifts](https://arxiv.org/abs/2403.11244)

For the odd power $r=2k-1$ and shift $m\ge 1-k$, set $a=k+m-1$. The proposed denominator exponent can be reduced by $a$. A confluent Christoffel determinant gives the signed quasipolynomials in the size of the Hankel matrix. A reflection identity yields the exact numerator degree and symmetry.

Chern and Shi previously evaluated low-shift determinants and selected size classes at generic shifts in a Catalan-like array that specializes to these powers. Their results overlap with the explicit special cases. The general degree and reciprocity theorem here treats every size class in the series. [Chern and Shi, Theorems 1.1–1.9](https://arxiv.org/abs/2608.27208)

Section 4 proves the three even and three odd explicit low-shift families displayed after the conjectures. The final odd formula printed on page 11 is the numerator for the smaller exponent. Under equation (30), it has the additional factor $(1+(-1)^kz^{2k-1})^2$. The comparison at power one after (30) uses $(1-z)^{m+1}$. The main degree exception and these two normalization details are distinguished in the manuscript.

Run the independent integer-matrix checker with Python 3. It computes the input coefficients from the binomial formula and uses fraction-free elimination on the original Hankel matrices. The infinite assertions follow from the manuscript. [Checker](verify.py) · [Reference output](verification.txt)
