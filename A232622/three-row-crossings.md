# Four-domino meetings on a three-row rectangle

**Blake Stone · Proof developed with OpenAI Codex.**

Let $T_t(z,3)$ count domino tilings of the fixed $3\times n$ rectangle by width $n$ with precisely $t$ interior grid vertices at which four distinct dominoes meet. Each placement on the fixed board is counted separately. We prove Conjecture 4 in R. J. Mathar's 2013 paper and give the corrected generating function for Conjecture 3. The width variable is $z$, as in the paper. [Mathar, Table 2 and equations (16)–(17)](https://arxiv.org/pdf/1311.6135)

Set $x=z^2$ and $D=1-x-x^2$. Then

$$
\begin{aligned}
T_1(z,3)&=\frac{2x^2(3+3x-3x^2-2x^3)}{D^2},\\
T_2(z,3)&=x^2+\frac{2x^3(6+11x-9x^2-12x^3-x^4+x^5)}{D^3}.
\end{aligned}
$$

Equation (16) prints the first prefactor as $2z^6$; the correct prefactor is $2z^4$. Table 2 itself gives six one-meeting tilings at width four. The second identity is equation (17) as printed.

## Column construction

Index cells in a column from top to bottom by bits $1,2,4$. After a column has been placed, keep its state $(a,v)$. Here $a$ is the mask of its horizontal dominoes extending into the next column. The vertical mask $v$ is 0 for no vertical domino, 1 for a domino on the upper two cells, and 2 for a domino on the lower two cells. When adding the next column, choose its outgoing mask $b$ disjoint from $a$. The rows covered by neither mask must be empty, the upper pair, or the lower pair. Those three possibilities determine the next vertical mask $w$ as 0, 1, or 2, respectively. Each allowed choice determines the next column uniquely.

At the interface just crossed there are two candidate vertices, between rows one and two or between rows two and three. Four dominoes meet there precisely when all four adjoining cells are on distinct dominoes. This occurs when neither incident row is occupied by a horizontal domino crossing the interface and neither adjacent column has a vertical domino joining those two rows. Equivalently, for $r=0,1$ count the index $r$ if the mask $a$ has no bits in $3\cdot2^r$ and neither $v$ nor $w$ has bit $2^r$. If $j$ indices are counted, weight this transition by $y^j$.

Group states with their reflections across the horizontal midline. Reflection preserves the weights of transitions into every group, so the group counts retain all tilings with multiplicity. In the table below each pair is written (outgoing mask, vertical mask).

| Group | Possible states after an even number of columns | Group | Possible states after an odd number of columns |
|---|---|---|---|
| $E_1$ | $(0,0)$ | $O_1$ | $(1,0),(4,0)$ |
| $E_2$ | $(0,1),(0,2)$ | $O_2$ | $(1,2),(4,1)$ |
| $E_3$ | $(3,0),(6,0)$ | $O_3$ | $(7,0)$ |

The initial column has two choices in $O_2$ and one in $O_3$, with no interface weight on the left outer boundary. Applying the disjoint-mask rule to a representative of each group gives the even-to-odd and odd-to-even transition matrices, respectively,

$$
P=\begin{pmatrix}0&2y&y^2\\0&1+y&y\\1&0&0\end{pmatrix},
\qquad Q=\begin{pmatrix}0&1&y\\0&1&1\\1&0&0\end{pmatrix}.
$$

For example $(0,0)$ in $E_1$ permits outgoing masks 1 and 4, each leaving one vertical domino and one meeting; outgoing mask 7 leaves no vertical domino and gives two meetings. The displayed transitions stay within the listed groups; together with the initial choices, this also proves that the listed states suffice at every width.

After two columns the row vector of counts is $v=(0,2,1)Q=(1,2,2)$. Each further pair of columns multiplies it by

$$
M=PQ=\begin{pmatrix}y^2&2y&2y\\y&1+y&1+y\\0&1&y\end{pmatrix}.
$$

A complete tiling has zero outgoing mask, so the acceptance vector is $u=(1,1,0)^{\mathsf T}$. Odd widths have odd area. If $G(x,y)$ is the generating function by *half*-width and number of meetings, including the empty tiling, summing all even widths gives

$$
G(x,y)=1+xv(I-xM)^{-1}u.
$$

This expression also gives the distribution for every number of meetings.

## Extracting the two coefficients

Write $G=N/B$, with $B=\det(I-xM)$. Through degree two in $y$ the polynomials obtained by matrix multiplication are

$$
\begin{aligned}
B&=D-2xy-(x+x^3)y^2+O(y^3),\\
N&=1+2x-x^3+(4x^3-2x)y-(x+2x^2+6x^3)y^2+O(y^3).
\end{aligned}
$$

Put $G_j=[y^j]G$. Equating coefficients of $BG=N$ gives $G_0=(1+2x-x^3)/D$, then $DG_1=4x^3-2x+2xG_0$, and finally $DG_2=-(x+2x^2+6x^3)+2xG_1+(x+x^3)G_0$. Simplifying gives the two stated rational functions. At widths $4,6,8,10$ their first coefficients are $(6,18,36,74)$ and $(1,12,58,156)$, respectively.

Frank Ruskey and Jennifer Woodcock derived fixed-height generating functions for the zero-meeting (tatami) condition. The two positive-meeting formulas above concern Mathar's refinement. [Ruskey–Woodcock, *Counting Fixed-Height Tatami Tilings* (2009)](https://doi.org/10.37236/215)
