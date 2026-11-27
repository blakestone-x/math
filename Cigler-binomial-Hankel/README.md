# Shifted binomial Hankel determinants

The manuscript evaluates the five size classes in Johann Cigler’s Conjecture 17 throughout the proposed range $m\ge0$. Four identities also hold for $m=-1$. For the fifth, an explicit determinant gives the correct polynomial at $m=-1$ for every $k$. Its degree is $3k-3$ for $k\ge2$, compared with the proposed degree $k$. At $k=2,m=-1,n=0$, the original determinant is $-21$ and the prediction is $-16$. [Manuscript](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Cigler’s 2023 preprint, Section 4](https://arxiv.org/abs/2308.07642v2)

Cigler and Tyson previously proved the unshifted cases $m=0$. The three odd formulas on their valid ranges are also specializations of Chern and Shi’s Theorem 1.9. Their equation (1.12) covers the first exceptional value family at $k=1$. The manuscript gives a common proof, the general shifted even evaluations, and the replacement on the entire exceptional boundary. [Cigler and Tyson](https://arxiv.org/abs/1807.08330) · [Chern and Shi](https://arxiv.org/abs/2608.27208)

For Conjecture 18 the manuscript proves both polynomial degrees and both Bernoulli leading coefficients for every $k\ge2,m\ge0$. The even coefficient is as printed. The odd coefficient requires $(2k+2m+1)^{2k-2}$ in place of $(2k+m+1)^{2k-2}$. At $k=2,m=1$ it equals $-196/3$ and the printed formula gives $-48$.

Run the verifier with Python 3. It computes the original Hankel determinants directly with fraction-free elimination and checks the boundary expression and Bernoulli leading terms. [Verification program](verify.py) · [Expected output](verification.txt)
