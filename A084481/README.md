# Fault-free L-tetromino tilings and binary arrays

Let $L_n$ count fault-free tilings of a $4\times2n$ rectangle by L-tetrominoes, including reflected orientations, where a fault is a straight cut between columns. Let $B_n$ be half the number of $n\times3$ binary arrays in which each cell agrees with at most half its orthogonal neighbors. Then
$$L_n=2B_{n-1}\qquad(n\ge4).$$
This proves the equality on the [A084481 LeftToSolve card](https://lefttosolve.com/p/oeis-a084481) by proving the generating function which R. J. Mathar identified as sufficient in 2022. The [tiling generating function](https://oeis.org/A084481) was already known. The [binary-array generating function](https://oeis.org/A183304) is marked empirical in OEIS.

## A six-state proof of the binary-array formula

Encode a row by an integer from 0 to 7, in binary. Keep a pair $(u,v)$ of consecutive rows. Appending $w$ gives a transition to $(v,w)$ exactly when every bit of $v$ agrees with at most half its orthogonal neighbors in these three rows. At the top/bottom, apply the same test and omit neighbors outside the array. Global bit complementation and reversal of all rows preserve the test. Group pairs by these symmetries, choosing the lexicographically first representative in each orbit, and discard states off all top-to-bottom paths. The surviving states are
$$(1,4),\ (1,5),\ (1,6),\ (2,2),\ (2,3),\ (2,5).$$
Checking the eight possible next rows gives the transition matrix $M$, initial row vector $s$ (halved by bit complementation), and final column vector $e$:
$$M=\begin{pmatrix}
0&0&1&0&0&0\\
0&0&0&0&1&1\\
1&1&1&0&0&0\\
0&0&0&0&0&1\\
0&0&1&0&0&0\\
0&0&0&1&2&1
\end{pmatrix},\qquad
s=(0,0,2,1,2,1),\quad e=(0,1,1,1,0,1)^t.$$
The single-row count is $B_1=1$ and $B_n=sM^{n-2}e$ for $n\ge2$. Direct multiplication gives $M^3e=2M^2e+e$. Also $B_2=4$, $B_3=9$, $B_4=19$. Thus $B_n=2B_{n-1}+B_{n-3}$ for $n\ge4$, with the fourth term checked by the given values. It follows that
$$B(x)=\sum_{n\ge1}B_nx^n=\frac{x(1+x)^2}{1-2x-x^3}.$$

The same formula proves Mathar's November 2026 observation $B_n=C_{n-1}+C_n$ for $n\ge1$, where $C_n$ is [A214260](https://oeis.org/A214260). Its listed generating function is $C(x)=x(1+x)/(1-2x-x^3)$, and $B(x)=(1+x)C(x)$.

## Independent transfer calculation for the tilings

Sweeping left to right, record occupied cells in the next two columns with an eight-bit mask. The bit at position $4c+r$ marks row $r$ in column $c$, with indices starting at zero. Fill the first free cell in the present column using any orientation of the tetromino that covers it, avoids occupied cells, lies inside the four rows, and stays in the present or following columns. Repeat until the present column is full, then shift the mask four bits to the right. No tetromino spans more than three columns, so the shifted mask again fits in eight bits. The prescribed first cell orders placements uniquely for any completed tiling.

Advance two columns at a time, identify a mask with its reflection in the midline between rows two and three, and discard masks off paths from the empty mask back to itself. The representatives are $0,23,29,43,46,255$ and the resulting matrix is
$$P=\begin{pmatrix}
2&0&2&2&4&4\\
1&0&0&0&1&0\\
1&1&1&0&1&0\\
0&0&0&0&0&1\\
0&0&1&0&1&0\\
1&0&0&0&0&0
\end{pmatrix}.$$
Thus the series for all tilings, including the empty tiling, is
$$T(x)=[(I-xP)^{-1}]_{1,1}=\frac{1-2x-x^3}{1-4x-2x^2+x^3+4x^4+4x^5+2x^6}.$$
Every tile has an excess of exactly two cells of one color when the rows are colored alternately black and white. Since any four-row rectangle has balanced row colors, it must contain an even number of tiles and hence an even number of columns. All faults therefore occur at even columns. Cutting at every fault gives a unique sequence of nonempty fault-free tilings, so
$$L(x)=1-T(x)^{-1}=\frac{2x(1+x)^2(1-x-x^3)}{1-2x-x^3}.$$
It follows that $L(x)-2xB(x)=2x(1+x)^2$, proving the claimed equality for every $n\ge4$.

The accompanying Python/SymPy program constructs both matrices from the local definitions and verifies the rational identity exactly.

## Two further empirical recurrences, for widths four and five

The same row-pair construction proves the order-14 recurrence in [A183305](https://oeis.org/A183305) for $n\ge16$ and the order-29 recurrence in [A183306](https://oeis.org/A183306) for $n\ge32$. Here is a finite all-indices certificate, implemented in the accompanying standard-library Python file `wider_strips.py`. For width $w$, build the $2^{2w}$ row pairs and transitions by the same local majority test. Restrict the first bit of the top row to zero to implement the factor one half. Keep the states reachable from an admissible start which can also reach an admissible end. The numbers of retained states are 66 for width four and 220 for width five.

For an order-$r$ recurrence with coefficients $c_j$, write $D_n=A_n-\sum_{j=1}^r c_jA_{n-j}$. Since $A_n=sM^{n-2}e$ for $n\ge2$, for every $n\ge n_0\ge r+2$ the residual is
$$D_n=sM^{n-n_0}\left(M^{n_0-2}-\sum_{j=1}^r c_jM^{n_0-2-j}\right)e.$$
By Cayley–Hamilton it satisfies a monic linear recurrence of degree at most the number of retained states. Using exact integer transfers, the program verifies $D_{16},\ldots,D_{81}=0$ at width four and $D_{32},\ldots,D_{251}=0$ at width five, proving both identities at every subsequent index. Multiplying the width-four series by its recurrence denominator gives numerator coefficients (ascending powers)
$$0,2,-4,1,-6,9,5,-22,54,-41,-14,25,-17,11,-4,1.$$
The program checks that this is precisely the numerator in Mathar's November 2026 empirical generating function after combining the two terms in his expression.
